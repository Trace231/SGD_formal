"""Search process: sample candidates, verify, persist APOLLO-style artifacts."""

from __future__ import annotations

import json
import multiprocessing as mp
import pickle
import time
from datetime import datetime
from pathlib import Path
from typing import Any

from ablation.apollo_only.adapters.output_parser import ParsedCandidate, indent_proof_body, parse_model_output
from ablation.apollo_only.algorithms import Sampling


def _find_theorem_body_region(source: str, theorem_name: str) -> tuple[int, int]:
    key = f"theorem {theorem_name}"
    start = source.find(key)
    if start < 0:
        raise ValueError(f"theorem_not_found: {theorem_name}")
    by_idx = source.find(":= by", start)
    if by_idx < 0:
        raise ValueError(f"theorem_missing_colon_eq_by: {theorem_name}")
    line_end = source.find("\n", by_idx)
    if line_end < 0:
        line_end = len(source)
    body_start = line_end + 1
    return body_start, len(source)


def _apply_candidate(source: str, theorem_name: str, parsed: ParsedCandidate) -> tuple[str, str]:
    if parsed.kind == "full_file":
        # Guardrail: reject broken full-file payloads with markdown wrappers.
        if "```" in parsed.payload:
            return "", ""
        return parsed.payload, ""
    if parsed.kind != "proof_body":
        return "", ""
    body_start, body_end = _find_theorem_body_region(source, theorem_name)
    body = indent_proof_body(parsed.payload, spaces=2)
    return source[:body_start] + body + source[body_end:], body


class SearchProcess(mp.Process):
    """APOLLO-style search process."""

    def __init__(
        self,
        *,
        idx: int,
        log_dir: str,
        scheduler: Any,
        data_loader: Any,
        cfg: dict[str, Any],
    ):
        super().__init__()
        self.idx = int(idx)
        self.log_dir = Path(log_dir)
        self.scheduler = scheduler
        self.data_loader = data_loader
        self.cfg = cfg
        self.execution_root = Path(str(cfg["execution_root"])).resolve()
        self.apply_best_candidate = bool(cfg.get("apply_best_candidate", False))
        sampler_cfg = dict(cfg.get("sampler", {}))
        sampler_cfg.setdefault("model_args", dict(cfg.get("model_args", {})))
        self.sampler = Sampling(
            scheduler=scheduler,
            process_print=self.process_print,
            cfg=sampler_cfg,
        )

    def _maybe_apply_best_candidate(
        self,
        *,
        row: dict[str, Any],
        target_path: Path,
        current_best: list[float] | None,
    ) -> tuple[list[float] | None, bool]:
        if not self.apply_best_candidate:
            return current_best, False
        result = row.get("result", {})
        full_code = str(row.get("full_code", ""))
        if not bool(result.get("complete", False)):
            return current_best, False
        if not full_code.strip():
            return current_best, False
        score = row.get("score", [])
        if not isinstance(score, list):
            return current_best, False
        if current_best is not None and tuple(score) <= tuple(current_best):
            return current_best, False
        target_path.write_text(full_code, encoding="utf-8")
        self.process_print(
            f"[ApplyBest] updated target file with score={score}",
            flush=True,
        )
        return list(score), True

    def process_print(self, logs: str, **kwargs: Any) -> None:
        print(f"[SearchProcess:{self.idx}] {logs}", **kwargs)

    def _score(self, verify_result: dict[str, Any], gen_error: str) -> list[float]:
        if gen_error:
            return [0.0, 0.0, -1e9, -1e9, -1e9]
        return [
            float(bool(verify_result.get("complete", False))),
            float(bool(verify_result.get("pass", False))),
            -float(int(verify_result.get("error_count", 0))),
            -float(int(verify_result.get("sorry_count", 0))),
            -float(verify_result.get("verify_time", 0.0) or 0.0),
        ]

    def run(self) -> None:
        while True:
            prob_idx, prob_runname, data = self.data_loader.get()
            if prob_idx is None:
                break

            self.process_print(f"start problem={prob_idx} run={prob_runname}", flush=True)
            prob_log_dir = self.log_dir / f"{prob_idx}_{prob_runname}"
            prob_log_dir.mkdir(parents=True, exist_ok=True)
            target_path = (self.execution_root / str(data["target_file"])).resolve()
            source = target_path.read_text(encoding="utf-8")
            theorem_name = str(data["theorem_name"])

            sample_start = time.time()
            candidate_records: list[dict[str, Any]] = []
            verify_request_ids: list[int] = []

            for sample_text, sample_info in self.sampler.sample(data=data, execution_root=self.execution_root):
                parsed = parse_model_output(sample_text)
                full_code, proof_body = _apply_candidate(source, theorem_name, parsed)
                generation_error = ""
                if not full_code:
                    generation_error = f"parse_failed:{parsed.reason}"
                rec = {
                    "problem_name": str(data.get("name", f"problem_{prob_idx}")),
                    "sample_info": sample_info,
                    "raw_output": sample_text,
                    "parse_kind": parsed.kind,
                    "parse_reason": parsed.reason,
                    "proof_code": proof_body,
                    "full_code": full_code,
                    "generation_error": generation_error,
                    "formal_statement": str(data.get("formal_statement", "")),
                }
                candidate_records.append(rec)
                if generation_error:
                    verify_request_ids.append(-1)
                else:
                    req_id = self.scheduler.verifier_submit_request(
                        {"code": full_code, "target_path": str(target_path)}
                    )
                    verify_request_ids.append(int(req_id))

            sample_time = time.time() - sample_start

            verify_start = time.time()
            verify_outputs: list[dict[str, Any]] = []
            for req_id in verify_request_ids:
                if req_id < 0:
                    verify_outputs.append(
                        {
                            "pass": False,
                            "complete": False,
                            "errors": ["generation_or_parse_failed"],
                            "warnings": [],
                            "error_count": 1,
                            "warning_count": 0,
                            "sorry_count": 0,
                            "sorries": [],
                            "verify_time": 0.0,
                        }
                    )
                else:
                    verify_outputs.append(self.scheduler.verifier_get_request_outputs(req_id))
            verify_time = time.time() - verify_start

            success_rows: list[dict[str, Any]] = []
            failure_rows: list[dict[str, Any]] = []
            best_applied_score: list[float] | None = None
            applied_updates = 0
            for rec, ver in zip(candidate_records, verify_outputs):
                score = self._score(ver, str(rec.get("generation_error", "")))
                row = {
                    "problem_name": rec["problem_name"],
                    "sample_info": rec["sample_info"],
                    "formal_statement": rec["formal_statement"],
                    "proof_code": rec["proof_code"],
                    "result": ver,
                    "score": score,
                    "algorithm": self.sampler.algorithm_name,
                    "raw_output": rec["raw_output"],
                    "full_code": rec["full_code"],
                    "parse_kind": rec["parse_kind"],
                    "parse_reason": rec["parse_reason"],
                    "generation_error": rec["generation_error"],
                }
                if bool(ver.get("complete", False)):
                    success_rows.append(row)
                else:
                    failure_rows.append(row)
                best_applied_score, changed = self._maybe_apply_best_candidate(
                    row=row,
                    target_path=target_path,
                    current_best=best_applied_score,
                )
                if changed:
                    applied_updates += 1

            success_count = len(success_rows)
            self.process_print(
                f"success={success_count}/{len(candidate_records)} "
                f"gen={sample_time:.2f}s verify={verify_time:.2f}s",
                flush=True,
            )

            # APOLLO-style artifact split
            stamp = datetime.utcnow().strftime("%Y%m%d_%H%M%S")
            run_id = str(prob_runname).replace("/", "_")
            base = self.log_dir / f"{prob_idx}_{data.get('name', 'problem')}"
            base.mkdir(parents=True, exist_ok=True)
            if success_rows:
                (base / f"success-{self.sampler.algorithm_name}-{run_id}-{stamp}.jsonl").write_text(
                    "\n".join(json.dumps(r, ensure_ascii=False) for r in success_rows) + "\n",
                    encoding="utf-8",
                )
                with (base / f"success-{self.sampler.algorithm_name}-{run_id}-{stamp}.pkl").open("wb") as f:
                    pickle.dump(success_rows, f)
            if failure_rows:
                (base / f"failure-{self.sampler.algorithm_name}-{run_id}-{stamp}.jsonl").write_text(
                    "\n".join(json.dumps(r, ensure_ascii=False) for r in failure_rows) + "\n",
                    encoding="utf-8",
                )
                with (base / f"failure-{self.sampler.algorithm_name}-{run_id}-{stamp}.pkl").open("wb") as f:
                    pickle.dump(failure_rows, f)

            # per-run summary
            summary = {
                "problem_idx": int(prob_idx),
                "problem_name": str(data.get("name", "")),
                "prob_runname": str(prob_runname),
                "sample_count": len(candidate_records),
                "success_count": success_count,
                "sample_time": sample_time,
                "verify_time": verify_time,
                "algorithm": self.sampler.algorithm_name,
                "apply_best_candidate": self.apply_best_candidate,
                "applied_updates": int(applied_updates),
                "best_applied_score": best_applied_score or [],
            }
            (prob_log_dir / "summary.json").write_text(
                json.dumps(summary, indent=2, ensure_ascii=False),
                encoding="utf-8",
            )
            (prob_log_dir / self.data_loader.finished_flag_filename).write_text(
                "finished\n",
                encoding="utf-8",
            )

