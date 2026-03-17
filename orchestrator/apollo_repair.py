"""Stage-2 APOLLO decomposition orchestration for Agent8 dispatch."""

from __future__ import annotations

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


_INTERFACE_MARKERS = (
    "invalid field",
    "application type mismatch",
    "unknown constant",
    "unknown identifier",
    "field notation",
    "invalid projection",
)
_INSTANCE_MARKERS = (
    "failed to synthesize instance",
    "typeclass instance problem is stuck",
)
_GLUE_MARKERS = (
    "missing glue",
    "bridge lemma",
    "no such lemma",
    "not found in codebase",
    "unknown theorem",
    "missing glue bridge candidates",
)
_STRATEGY_MARKERS = (
    "tactic failed",
    "unsolved goals",
    "rewrite failed",
    "did not simplify",
    "no goals to be solved",
)


def classify_failure_kind(errors_text: str) -> tuple[str, str, str]:
    """Classify failure into deterministic routing kinds for Agent8."""
    t = str(errors_text or "").strip()
    hay = t.lower()
    snippet = t.splitlines()[0][:240] if t else ""

    # Precedence: instance > interface > glue > strategy.
    # This avoids over-routing interface for clear typeclass failures.
    if any(m in hay for m in _INSTANCE_MARKERS):
        return "instance_failure", "typeclass synthesis failure markers found (confidence=0.95)", snippet

    if any(m in hay for m in _INTERFACE_MARKERS):
        return "interface_failure", "declaration/API/type-shape mismatch markers found (confidence=0.90)", snippet

    if any(m in hay for m in _GLUE_MARKERS):
        return "glue_failure", "missing bridge/glue markers found (confidence=0.85)", snippet

    if any(m in hay for m in _STRATEGY_MARKERS):
        return "strategy_failure", "proof-body tactic/strategy failure markers found (confidence=0.75)", snippet

    return "strategy_failure", "fallback strategy classification (confidence=0.40)", snippet


def _next_route_hint(failure_kind: str) -> str:
    return {
        "interface_failure": "agent7_signature",
        "instance_failure": "agent7_signature",
        "glue_failure": "agent7_then_agent6",
        "strategy_failure": "agent9_replan",
    }.get(failure_kind, "agent9_replan")


def build_subproblem_graph(
    *,
    current_errors: str,
    error_subtype: str = "",
    lemma_count: int = 0,
) -> list[dict[str, Any]]:
    """Build an APOLLO-aligned serial subproblem graph for Agent8."""
    errors_text = str(current_errors or "")
    kind, _, snippet = classify_failure_kind(errors_text)
    graph: list[dict[str, Any]] = []
    idx = 1

    def _push(kind_name: str, priority: int, target: str, evidence: str) -> None:
        nonlocal idx
        graph.append(
            {
                "id": f"sp-{idx:02d}-{kind_name}",
                "kind": kind_name,
                "priority": priority,
                "target": target,
                "evidence": evidence[:240],
            }
        )
        idx += 1

    # Compile blockers first.
    if error_subtype == "declaration_api_mismatch" or kind in {"interface_failure", "instance_failure"}:
        _push("interface_signature", 10, "declaration/proof header", snippet or "interface markers")
    if error_subtype == "proof_api_mismatch":
        _push("proof_api_shape", 20, "proof callsites", snippet or "proof API markers")

    # Glue blockers next.
    if kind == "glue_failure" or lemma_count > 0:
        _push("missing_glue", 30, f"bridge_lemmas(count={lemma_count})", snippet or "glue markers")

    # Local tactic and strategy tails.
    if kind == "strategy_failure":
        _push("local_tactic_repair", 40, "proof body", snippet or "tactic markers")
        _push("global_strategy", 50, "overall theorem strategy", "local route stalled")

    if not graph:
        _push("global_strategy", 50, "overall theorem strategy", snippet or "insufficient evidence")

    graph.sort(key=lambda n: int(n.get("priority", 999)))
    return graph


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
        graph = build_subproblem_graph(
            current_errors=current_errors,
            error_subtype=error_subtype,
            lemma_count=0,
        )
        return {
            "status": "failed",
            "failure_kind": "interface_failure",
            "classifier_reason": "target file does not exist",
            "raw_error_snippet": str(target_file),
            "next_route_hint": "agent7_signature",
            "summary": "APOLLO route aborted: target file missing.",
            "subproblem_graph": graph,
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
        graph = build_subproblem_graph(
            current_errors=str(exc) or current_errors,
            error_subtype=error_subtype,
            lemma_count=0,
        )
        return {
            "status": "failed",
            "failure_kind": kind,
            "classifier_reason": f"apollo verifier bootstrap failed: {reason}",
            "raw_error_snippet": snippet,
            "next_route_hint": _next_route_hint(kind),
            "summary": f"APOLLO verifier unavailable: {exc}",
            "metrics": metrics,
            "subproblem_graph": graph,
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
            "subproblem_graph": [],
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
        graph = build_subproblem_graph(
            current_errors=str(exc) or current_errors,
            error_subtype=error_subtype,
            lemma_count=0,
        )
        return {
            "status": "failed",
            "failure_kind": kind,
            "classifier_reason": f"final verify failed: {reason}",
            "raw_error_snippet": snippet,
            "next_route_hint": _next_route_hint(kind),
            "summary": f"APOLLO final verify call failed: {exc}",
            "metrics": metrics,
            "subproblem_graph": graph,
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
            "subproblem_graph": [],
        }

    # Step 5: failure typing + optional sublemma extraction signal.
    lemmas, lemma_meta = extract_sublemmas(working, verifier)
    metrics["lemma_extraction"] = lemma_meta
    if lemma_meta.get("ok") and int(lemma_meta.get("count", 0)) > 0:
        inferred_error = f"{flattened}\nmissing glue bridge candidates: {lemma_meta.get('count')}"
    else:
        inferred_error = flattened or current_errors
    kind, reason, snippet = classify_failure_kind(inferred_error)
    graph = build_subproblem_graph(
        current_errors=inferred_error,
        error_subtype=error_subtype,
        lemma_count=int(lemma_meta.get("count", 0)),
    )
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
        "subproblem_graph": graph,
    }

