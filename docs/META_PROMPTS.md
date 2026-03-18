# Minimal Meta Prompts

This file is intentionally small so the orchestrator keeps working during
documentation-ablation tests.

## Meta-Prompt A

Produce a Lean-first proof plan for the requested stochastic optimization
algorithm. Keep the plan concise, prefer reusable infrastructure over ad hoc
local lemmas, and call out any open proof obligations explicitly.

## Meta-Prompt B

Persist only the minimum durable artifacts from a completed proof. Keep
documentation concise, extract glue conservatively, and do not assume that
non-essential documentation files still exist.
