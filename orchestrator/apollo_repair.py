"""Stage-2 APOLLO decomposition orchestration for Agent8 dispatch."""

from __future__ import annotations

import re
from pathlib import Path
from typing import Any

from orchestrator.apollo_sorrify import (
    apply_hint_repair,
    apply_sorrify,
    apply_syntax_correction,
    build_apollo_verify_callable,
    extract_sublemmas,
)


def _flatten_apollo_errors(verify_result: dict[str, Any]) -> str:
    parts: list[str] = []
    for bucket in ("errors", "warnings"):
        for msg in verify_result.get(bucket, []) or []:
            if isinstance(msg, dict):
                data = str(msg.get("data", "")).strip()
                pos = msg.get("pos") or {}
                line = int(pos.get("line", 0) or 0)
                if line > 0:
                    parts.append(f"{line}: {data}")
                elif data:
                    parts.append(data)
            elif str(msg).strip():
                parts.append(str(msg).strip())
    return "\n".join(parts)


def classify_failure_kind(errors_text: str) -> tuple[str, str, str]:
    """Classify failure into deterministic routing kinds for Agent8."""
    t = str(errors_text or "").strip()
    hay = t.lower()
    snippet = t.splitlines()[0][:240] if t else ""

    if any(
        m in hay
        for m in (
            "invalid field",
            "application type mismatch",
            "declaration",
            "unknown constant",
            "unknown identifier",
        )
    ):
        return "interface_failure", "declaration/API/type-shape mismatch markers found", snippet

    if "failed to synthesize instance" in hay:
        return "instance_failure", "typeclass synthesis failure markers found", snippet

    if any(
        m in hay
        for m in (
            "missing glue",
            "bridge lemma",
            "no such lemma",
            "not found in codebase",
            "unknown theorem",
        )
    ):
        return "glue_failure", "missing bridge/glue markers found", snippet

    if any(
        m in hay
        for m in (
            "tactic failed",
            "unsolved goals",
            "rewrite failed",
            "did not simplify",
            "no goals to be solved",
        )
    ):
        return "strategy_failure", "proof-body tactic/strategy failure markers found", snippet

    return "strategy_failure", "fallback strategy classification (insufficient structural evidence)", snippet


def _next_route_hint(failure_kind: str) -> str:
    return {
        "interface_failure": "agent7_signature",
        "instance_failure": "agent7_signature",
        "glue_failure": "agent7_then_agent6",
        "strategy_failure": "agent9_replan",
    }.get(failure_kind, "agent9_replan")


def run_apollo_decompose_repair(
    *,
    target_file: str,
    current_errors: str,
    error_subtype: str = "",
    policy_context: dict[str, Any] | None = None,
) -> dict[str, Any]:
    """Run bounded APOLLO decomposition pipeline and return structured result."""
    path = Path(target_file)
    if not path.is_absolute():
        from orchestrator.config import PROJECT_ROOT

        path = (PROJECT_ROOT / path).resolve()
    if not path.exists():
        return {
            "status": "failed",
            "failure_kind": "interface_failure",
            "classifier_reason": "target file does not exist",
            "raw_error_snippet": str(target_file),
            "next_route_hint": "agent7_signature",
            "summary": "APOLLO route aborted: target file missing.",
        }

    source = path.read_text(encoding="utf-8")
    verifier = build_apollo_verify_callable()
    metrics: dict[str, Any] = {
        "source_chars": len(source),
        "policy_context": policy_context or {},
        "error_subtype": error_subtype,
    }

    # Step 0: quick baseline verify
    try:
        base_verify = verifier(source)
    except Exception as exc:
        kind, reason, snippet = classify_failure_kind(str(exc) or current_errors)
        return {
            "status": "failed",
            "failure_kind": kind,
            "classifier_reason": f"apollo verifier bootstrap failed: {reason}",
            "raw_error_snippet": snippet,
            "next_route_hint": _next_route_hint(kind),
            "summary": f"APOLLO verifier unavailable: {exc}",
            "metrics": metrics,
        }

    working = source
    metrics["base_pass"] = bool(base_verify.get("pass", False))
    metrics["base_complete"] = bool(base_verify.get("complete", False))

    if bool(base_verify.get("complete", False)):
        return {
            "status": "success",
            "failure_kind": "",
            "classifier_reason": "",
            "raw_error_snippet": "",
            "next_route_hint": "",
            "summary": "Already complete under APOLLO verifier.",
            "metrics": metrics,
        }

    # Step 1: syntax correction
    working, syntax_meta = apply_syntax_correction(working)
    metrics["syntax"] = syntax_meta

    # Step 2: sorrify isolation
    working, sorrify_meta = apply_sorrify(working, verifier)
    metrics["sorrify"] = sorrify_meta

    # Step 3: hint-based repair
    working, hint_meta = apply_hint_repair(working, verifier)
    metrics["hint_repair"] = hint_meta

    # Step 4: final verify
    try:
        final_verify = verifier(working)
    except Exception as exc:
        kind, reason, snippet = classify_failure_kind(str(exc) or current_errors)
        return {
            "status": "failed",
            "failure_kind": kind,
            "classifier_reason": f"final verify failed: {reason}",
            "raw_error_snippet": snippet,
            "next_route_hint": _next_route_hint(kind),
            "summary": f"APOLLO final verify call failed: {exc}",
            "metrics": metrics,
        }

    metrics["final_pass"] = bool(final_verify.get("pass", False))
    metrics["final_complete"] = bool(final_verify.get("complete", False))
    metrics["verify_time"] = float(final_verify.get("verify_time", 0.0) or 0.0)
    flattened = _flatten_apollo_errors(final_verify)

    if bool(final_verify.get("complete", False)):
        if working != source:
            path.write_text(working, encoding="utf-8")
        return {
            "status": "success",
            "failure_kind": "",
            "classifier_reason": "",
            "raw_error_snippet": "",
            "next_route_hint": "",
            "summary": "APOLLO decomposition completed and file updated.",
            "metrics": metrics,
        }

    # Step 5: failure typing + optional sublemma extraction signal.
    lemmas, lemma_meta = extract_sublemmas(working, verifier)
    metrics["lemma_extraction"] = lemma_meta
    if lemma_meta.get("ok") and int(lemma_meta.get("count", 0)) > 0:
        inferred_error = f"{flattened}\nmissing glue bridge candidates: {lemma_meta.get('count')}"
    else:
        inferred_error = flattened or current_errors
    kind, reason, snippet = classify_failure_kind(inferred_error)
    return {
        "status": "failed",
        "failure_kind": kind,
        "classifier_reason": reason,
        "raw_error_snippet": snippet,
        "next_route_hint": _next_route_hint(kind),
        "summary": (
            "APOLLO decomposition did not reach complete proof; "
            f"failure_kind={kind}, lemmas={int(lemma_meta.get('count', 0))}."
        ),
        "metrics": metrics,
    }

