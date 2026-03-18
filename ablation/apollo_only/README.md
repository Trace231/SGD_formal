# APOLLO-Only Ablation Runner

This directory contains an isolated APOLLO-style ablation path:

- multi-candidate sampling
- parallel Lean verification
- candidate ranking and artifacts

It does not modify the main `orchestrator` flow.

## Quick Start

From `SGD_APOLLO` root:

```bash
python ablation/apollo_only/scripts/bootstrap_workspace.py --force

python -m ablation.apollo_only.runner \
  --dataset ablation/apollo_only/datasets/subgradient_single.jsonl \
  --config ablation/apollo_only/configs/subgradient_api.py
```

The runner enforces workspace isolation:

- `execution_root` must be inside `ablation/apollo_only/workspace`
- `target_file` must resolve inside the isolated workspace
- isolation metadata is persisted to run artifacts

Outputs are written to:

- `ablation_logs/<run_tag>/config.json`
- `ablation_logs/<run_tag>/summary.jsonl`
- `ablation_logs/<run_tag>/run_summary.json`
- `ablation_logs/<run_tag>/candidates/`
- `ablation_logs/<run_tag>/verifier/`

For full operator instructions, see `docs/APOLLO_ABLATION_GUIDE.md`.

