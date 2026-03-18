"""Default config for APOLLO-only SubgradientMethod ablation (API backend)."""

from orchestrator.config import (
    APOLLO_LAKE_PATH,
    APOLLO_PROJECT_PATH,
    APOLLO_VERIFY_TIMEOUT,
    PROJECT_ROOT,
)

# Sampling/search controls (APOLLO-style multi-candidate).
n_samples = 8
n_search_procs = 4

# Lean verification controls.
verify_timeout = APOLLO_VERIFY_TIMEOUT
apollo_project_path = str(APOLLO_PROJECT_PATH)
workspace_root = str(PROJECT_ROOT / "ablation" / "apollo_only" / "workspace")
repl_workspace = workspace_root
execution_root = workspace_root
lake_path = APOLLO_LAKE_PATH

# Model generation controls.
model_backend = "api"  # api | vllm
provider = "qwen"
model = "qwen3.5-plus"
max_tokens = 4096
temperature = 0.7
top_p = 0.95

system_prompt = (
    "You are an expert in Lean 4 formal proofs. "
    "Given a scaffold theorem, return Lean code only. "
    "Prefer concise, type-correct, compilable proof scripts."
)

