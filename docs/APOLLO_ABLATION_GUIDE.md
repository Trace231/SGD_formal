# APOLLO Ablation Guide (Parity Pipeline)

This guide explains how to run the high-fidelity APOLLO-parity ablation module
inside `SGD_APOLLO`.

## 0) Isolation Model

The ablation runner uses a dedicated snapshot workspace:

- `ablation/apollo_only/workspace/Algorithms`
- `ablation/apollo_only/workspace/Lib`
- `ablation/apollo_only/workspace/docs`
- `ablation/apollo_only/workspace/Main.lean`
- `ablation/apollo_only/workspace/lakefile.lean`

All candidate verification is constrained to this workspace. The runner rejects
targets or execution roots outside the workspace boundary.

## 1) Goal

The parity module reproduces APOLLO-style process topology (API-first backend):

1. `JsonlDataLoader` assigns problems/runs.
2. `SearchProcess` drives sampler-based candidate generation.
3. `GeneratorProcess` (API) / `GeneratorVllmProcess` (vLLM) consume generation requests.
4. `VerifierScheduler` workers verify candidates in parallel.
5. Results are split into success/failure artifacts with finished flags.

This module runs in isolation and does **not** modify `orchestrator/main.py`.

## 2) Module Layout

- `ablation/apollo_only/runner.py`: APOLLO-parity launcher
- `ablation/apollo_only/workers/`:
  - `task_queue.py`
  - `scheduler.py`
  - `data_loader.py`
  - `generator_process.py`
  - `generator_vllm_process.py`
  - `verifier_scheduler.py`
  - `search_process.py`
- `ablation/apollo_only/algorithms/`:
  - `base.py`
  - `sampling.py`
- `ablation/apollo_only/adapters/`:
  - `lean_adapter.py`
  - `output_parser.py`
- `ablation/apollo_only/reports/parity_report.py`
- `ablation/apollo_only/configs/apollo_api_parity.py`
- `ablation/apollo_only/configs/apollo_vllm_parity.py`
- `ablation/apollo_only/datasets/sample_single.jsonl`

## 3) Environment Requirements

## 3.1 Python

Use the same environment as `SGD_APOLLO` orchestrator.

Minimum packages used by this module:

- `python-dotenv`
- `openai` (for `api` backend)
- `vllm` (optional, only if `--model-backend vllm`)

## 3.2 Lean / REPL

The parity runner requires:

- isolated workspace root with `lakefile.lean`
- REPL binary at `<workspace_root>/.lake/build/bin/repl`
- APOLLO project path for fallback verification

`bootstrap_workspace.py` links a prebuilt REPL binary from `repl428` by default.

## 3.3 APOLLO path

The adapter expects APOLLO project path (default from `orchestrator.config`: `PROJECT_ROOT.parent / APOLLO`).

## 4) Dataset Schema

Each JSONL row should contain:

- `name`: experiment problem name
- `split`: free tag, usually `ablation`
- `target_file`: Lean file path relative to isolated `execution_root` (workspace)
- `theorem_name`: theorem to patch and solve
- `informal_prefix` (optional): prompt context

Example:

```json
{"name":"SampleMethod_scaffold_main_theorem","split":"ablation","target_file":"Algorithms/SampleMethod_scaffold.lean","theorem_name":"subgradient_convergence_convex","informal_prefix":"Goal: fill the main convex convergence theorem proof..."}
```

## 5) Run Commands

## 5.0 Bootstrap first (required)

```bash
cd /root/SGD/SGD_APOLLO
python ablation/apollo_only/scripts/bootstrap_workspace.py --force
```

This step snapshots `Lib/docs/Main` and migrates
`Algorithms/sorry.lean -> workspace/Algorithms/SampleMethod_scaffold.lean`.

## 5.1 Default parity run (API-first)

```bash
cd /root/SGD/SGD_APOLLO
python -m ablation.apollo_only.runner \
  --dataset ablation/apollo_only/datasets/sample_single.jsonl \
  --config ablation/apollo_only/configs/apollo_api_parity.py
```

## 5.2 vLLM parity run (optional)

```bash
python -m ablation.apollo_only.runner \
  --dataset ablation/apollo_only/datasets/sample_single.jsonl \
  --config ablation/apollo_only/configs/apollo_vllm_parity.py
```

## 5.3 Override backend/provider/model/samples

```bash
python -m ablation.apollo_only.runner \
  --dataset ablation/apollo_only/datasets/sample_single.jsonl \
  --config ablation/apollo_only/configs/apollo_api_parity.py \
  --model-backend api \
  --provider qwen \
  --model qwen3.5-plus \
  --n-samples 16
```

## 5.4 Build parity report

```bash
python -m ablation.apollo_only.reports.parity_report \
  --log-dir ablation_logs/parity_YYYYMMDD_HHMMSS
```

## 5.5 Build parity-vs-baseline report

```bash
python -m ablation.apollo_only.reports.parity_report \
  --log-dir ablation_logs/parity_YYYYMMDD_HHMMSS \
  --baseline-log-dir ablation_logs/simplified_YYYYMMDD_HHMMSS
```

## 6) CLI Parameters

- `--dataset`: JSONL dataset path
- `--config`: parity Python config path (`apollo_api_parity.py` / `apollo_vllm_parity.py`)
- `--node-rank`: distributed node rank
- `--world-size`: distributed world size
- `--n-samples`: override `sampler.sample_num`
- `--model-backend`: `api` or `vllm`
- `--provider`: provider for `api` backend
- `--model`: model for generation backend
- `--monitor-interval-sec`: verifier monitor polling interval
- `--monitor-stall-sec`: verifier stall threshold before worker restart
- `--request-timeout-sec`: per-request verifier timeout
- `--apply-best-candidate`: continuously write best verified candidate back to target Lean file
- `--log-dir`: parity log root
- `--quiet`: reduce launcher-level logs

## 7) Output Artifacts

For each run:

- `<log_dir>/config.json`: merged runtime config
- `<log_dir>/isolation.json`: isolation diagnostics
- `<log_dir>/<problem_idx>_<name>/run*/summary.json`: per-run summary
- `<log_dir>/<problem_idx>_<name>/success-*.jsonl|pkl`
- `<log_dir>/<problem_idx>_<name>/failure-*.jsonl|pkl`
- `<log_dir>/<problem_idx>_<name>/run*/finished_running.txt`
- `<log_dir>/fatal_error.json` on launcher failure

## 8) Metrics and Parity Report

`parity_report.py` aggregates:

- `problem_count`
- `sample_count`
- `success_count`
- `success_rate`
- `generation_time_total`
- `verification_time_total`
- `end_to_end_time_total`
- `samples_per_second`
- `failure_distribution`

With `--baseline-log-dir`, the report also includes parity-vs-baseline deltas.

## 9) Comparison Protocol (against Agent8/Agent3 pipeline)

To keep comparison fair:

1. Use the same `target_file`.
2. Keep timeout equal (`verify_timeout`).
3. Keep candidate budget aligned (`sampler.sample_num` vs equivalent attempt budget).
4. Use same REPL binary and Lean environment.
5. Compare on objective metrics:
   - complete rate
   - pass rate
   - errors/sorries remaining
   - total verify time

## 10) Troubleshooting

## 10.1 `repl_workspace_missing` / `repl_binary_missing`

- Check `repl_workspace` in config.
- Build REPL workspace and ensure `.lake/build/bin/repl` exists.

## 10.2 `execution_root_invalid: missing lakefile`

- Ensure `execution_root` points to isolated workspace:
  `ablation/apollo_only/workspace`.

## 10.3 `apollo_project_missing`

- Check `apollo_project_path` in config or env (`APOLLO_PROJECT_PATH`).

## 10.4 API generation failures

- Verify API keys in `.env`.
- Check provider/model mapping.
- Inspect `generation_error` in `summary.jsonl`.

## 10.5 Parsed output invalid (`parse_failed:*`)

- Open `candidates/cand_XXX.txt` to inspect raw output.
- Tighten system prompt or add stronger output-format constraints.

## 10.6 `vllm_backend_unavailable`

- Install `vllm`, or run with `--model-backend api`.

## 10.7 isolation hard-gate failures

Typical errors:

- `execution_root_outside_workspace`
- `target_file_outside_execution_root`
- `target_file_must_be_relative`

Fix:

1. Keep `execution_root` in `ablation/apollo_only/workspace`.
2. Keep `target_file` relative (example: `Algorithms/SampleMethod_scaffold.lean`).
3. Re-run bootstrap if workspace files are missing.

## 10.8 Queue/worker stalls

Symptoms:

- no `SearchProcess` progress logs
- no updates in run `summary.json`

Checks:

1. verify generator/verifier workers started in launcher output
2. reduce `n_search_procs` / `lean_max_concurrent_requests`
3. inspect queue monitor logs from `TaskQueue:*`
4. tune `monitor_interval_sec`, `monitor_stall_sec`, `request_timeout_sec`

## 10.9 Recovery playbook

1. API jitter / retry storms:
   - reduce `batch_size`
   - temporarily lower `sampler.sample_num`
2. Verifier timeout spikes:
   - increase `request_timeout_sec`
   - reduce `lean_max_concurrent_requests`
3. Worker freeze:
   - confirm launcher logs contain `worker_restarted`
   - increase `monitor_stall_sec` if false positives occur
4. Parsing instability:
   - switch sampler `prompt_formatter`
   - provide `few_shot_dataset` and `few_shot_num`

## 11) High-Fidelity Notes

- Process topology is APOLLO-style (queue + workers + search process), API-first by default.
- vLLM backend remains optional under the same scheduler interface.
- vLLM path uses dedicated persistent worker lifecycle.
- Sampler supports `mode`, `prompt_formatter`, `model_args`, and few-shot controls.
- Verifier scheduler includes timeout taxonomy and monitor-based worker restart.
- Isolation boundary is mandatory and enforced before run launch.

## 12) Audit verification checklist

After one run, verify:

1. `isolation.json` points to `ablation/apollo_only/workspace`.
2. per-problem `run*/finished_running.txt` exists.
3. `success-*.jsonl|pkl` and/or `failure-*.jsonl|pkl` are present.
4. source scaffold hash in workspace metadata is stable across reruns.
5. artifact names follow `<success|failure>-<algorithm>-<run_id>-<timestamp>`.
6. parity report includes failure taxonomy and optional baseline deltas.

## 13) Simplification fixes checklist

- [x] API and vLLM generation worker chains are separated.
- [x] vLLM worker keeps persistent model lifecycle.
- [x] sampler supports APOLLO-like mode/model_args/few-shot prompt controls.
- [x] verifier has request timeout, monitoring, and restart path.
- [x] artifact schema naming aligns with run_id/timestamp convention.
- [x] parity report supports parity-vs-baseline deltas.

## 14) Tuning guide

- API throughput tuning: increase `batch_size` gradually and watch generation errors.
- Verifier stability tuning: start with `lean_max_concurrent_requests=2~4`, then scale up.
- Sampler quality tuning: use `cot_goedel_v2`; add few-shot only after baseline is stable.
- Timeout tuning: keep `request_timeout_sec >= verify_timeout + transport buffer`.

