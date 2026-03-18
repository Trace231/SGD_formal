"""APOLLO parity config (API-first)."""

from orchestrator.config import APOLLO_LAKE_PATH, APOLLO_PROJECT_PATH, APOLLO_VERIFY_TIMEOUT, PROJECT_ROOT

workspace_root = str(PROJECT_ROOT / "ablation" / "apollo_only" / "workspace")
execution_root = workspace_root
repl_workspace = workspace_root
apollo_project_path = str(APOLLO_PROJECT_PATH)
lake_path = APOLLO_LAKE_PATH
verify_timeout = APOLLO_VERIFY_TIMEOUT

data_repeat = 1
data_split = None

n_search_procs = 4
batch_size = 8
lean_max_concurrent_requests = 4

model_backend = "api"
provider = "qwen"
model = "qwen3.5-plus"
max_tokens = 4096
temperature = 0.7
top_p = 0.95
system_prompt = "You are an expert in Lean 4 formal proofs. Return Lean code only."
model_args = {
    "provider": provider,
    "model": model,
    "max_tokens": max_tokens,
    "temperature": temperature,
    "top_p": top_p,
}

monitor_interval_sec = 5.0
monitor_stall_sec = 480.0
request_timeout_sec = 360.0
timeout_verify_sec = verify_timeout

sampler = {
    "sample_num": 8,
    "log_interval": 2,
    "mode": "cot_goedel_v2",
    "prompt_formatter": "cot_goedel_v2",
    "few_shot_dataset": "",
    "few_shot_num": 0,
    "model_args": model_args,
}

