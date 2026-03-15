# Trae Agent Task Specification — SGD_coldstart Orchestrator Improvement

This document is for Trae Agent to read. It guides improvement of the StochOptLib Lean 4 formalization orchestration system until it can successfully complete the SubgradientMethod proof-filling task.

**Use English for all development work**: prompts, code comments, commit messages, and internal reasoning.

---

## 1. Background

### 1.1 Project Overview

**SGD_coldstart** is a Lean 4 formalization project that aims to formalize convergence proofs of stochastic optimization algorithms (SGD, Subgradient Method, Stochastic Mirror Descent, SVRG, etc.) on top of Mathlib. The project uses the **StochOptLib** methodology:

- **Gap Taxonomy**: Classifies formalization blockers as Level 1 (completely absent), Level 2 (composition missing), Level 3 (form mismatch)
- **Stub-Probe Protocol**: Write type signatures + `sorry` first, then fill proofs incrementally
- **Archetype A/B**: A reduces to SGD; B requires novel proof structure

### 1.2 Multi-Agent Orchestrator

The orchestrator (`orchestrator`) is a multi-phase pipeline:

| Phase | Role | Responsibility |
|-------|------|----------------|
| 1/7 | Agent1 (orchestrator) | Generate Prover Prompt |
| 2/7 | Agent2 (planner) | Plan & approve |
| 3/7 | Agent2 + Agent10 | Write scaffold (theorem signatures + sorry) and verify |
| 4/7 | Agent9 (strategy_planner) | Generate structured JSON proof plan |
| 5/7 | Agent8 (decision_hub) + Agent3/6/7 | Dispatch Agent3 (Sorry Closer), Agent6 (Glue Filler), Agent7 (Interface Auditor) to fill sorries |
| 6/7 | Agent4 (persister) | Persist documentation |
| 7/7 | Agent5 (diagnostician) | Diagnose on failure |

### 1.3 `--skip-to-agent9` Mode

When the target file (e.g. `Algorithms/SubgradientMethod.lean`) **already exists and contains a scaffold (theorem signatures + sorry)**, use `--skip-to-agent9`:

- Skip Phase 1/2 (Agent2 planning)
- Skip Phase 3a (scaffold writing + Agent10 verification)
- Jump directly to Phase 4 (Agent9 strategy planning) → Phase 5 (Agent8 dispatches Agent3/6/7 to fill sorries)

The orchestrator assumes: scaffold is already written; only sorries need to be filled.

### 1.4 Current Problem

**Note**: `Algorithms/SubgradientMethod.lean` is marked as fully proved in METHODOLOGY. If the current file has no sorries, first create a scaffold version with sorries for testing (e.g. comment out parts of proof bodies and replace with `sorry`), or use another pending algorithm (e.g. `Lib/Glue/Staging/SVRGOuterLoop.lean`) as the target.

The orchestrator has defects when running SubgradientMethod (or similar scaffold) in `--skip-to-agent9` mode, which may cause:

- Agent3 failing to fill some sorries correctly
- Agent8 making poor routing decisions
- Agent6/7 being triggered incorrectly or not triggered when needed
- `lake build` passing but `sorry_count > 0`, or type errors that cannot be recovered

---

## 2. Purpose

Improve, debug, and explore the orchestration system until success. Constraints:

1. The orchestrator must **stably complete** proof-filling given a SubgradientMethod scaffold
2. Improvements must be **generic**: no hardcoding; no modifying Lib or any .md (that would be giving the answer)
3. **Do not stop until success**: on failure, analyze → discover → reflect → fix → re-run → repeat until success

---

## 3. Goals

### 3.1 Primary Goal

Make the following command **stably succeed**:

```bash
cd /root/SGD/SGD_coldstart
python -m orchestrator \
  --algorithm SubgradientMethod \
  --update-rule "w_{t+1} = w_t - η·g_t" \
  --proof-sketch "Per-step norm descent via subgradient inequality, telescope sum, O(1/sqrt(T)) rate" \
  --archetype B \
  --target-file Algorithms/SubgradientMethod.lean \
  --skip-to-agent9
```

Or with a structured spec file (overrides the above):

```bash
python -m orchestrator --spec-file book/FOML/SubgradientMethod.json --target-file Algorithms/SubgradientMethod.lean --skip-to-agent9
```

### 3.2 Success Criteria

The orchestrator run finishes and satisfies:

- `lake build` (or `run_lean_verify`) on the target file returns:
  - **exit_code = 0**
  - **sorry_count = 0**
- Full project `lake build` passes (no type errors, no sorries)

### 3.3 Modifiable Scope

Trae may **only** modify:

| Scope | Description |
|-------|-------------|
| `orchestrator/*.py` | Orchestration logic, Agent calls, routing strategy, error handling |
| `orchestrator/prompts.py` | System prompts and guidance for each Agent |
| `orchestrator/config.py` | Hyperparameters, retry limits, routing thresholds (must be via config/params, no hardcoding) |
| `Algorithms/SubgradientMethod.lean` | Only when restoring a scaffold (with sorries) for testing |

### 3.4 Absolute Prohibitions

- **No hardcoding**: Hardcoding is **absolutely forbidden**. Algorithm names, file paths, proof steps, lemma names, specific tactics, line numbers, error message fragments, numeric constants, etc. must not be hardcoded in `orchestrator/` code. All variable content must come from config, parameters, CLI, environment variables, or runtime inference. Improvements must be **generic**, applicable to different algorithms and sorries, not SubgradientMethod-specific patches.
- **No modifying `Lib/`**: Do not add or modify any `.lean` files under `Lib/`. Modifying Lib is equivalent to giving the answer (adding glue lemmas) and defeats the purpose.
- **No modifying any `.md` files**: Do not modify `docs/` or any Markdown files in the project. Modifying docs is equivalent to changing the problem or hinting.
- **Existing proofs**: If `SubgradientMethod.lean` has no sorries, do not break its proof structure.
- **Mathlib dependency**: Do not change the Mathlib version in `lakefile.lean`.

---

## 4. Stop Conditions & Iteration Strategy

### 4.1 Only Stop Condition: Success

Task is complete and you may stop **only** when all of the following hold:

1. The above `python -m orchestrator ... --skip-to-agent9` command runs
2. The orchestrator exits normally (no uncaught exceptions)
3. `run_lean_verify` on `Algorithms/SubgradientMethod.lean` returns `exit_code=0` and `sorry_count=0`
4. Full project `lake build` passes

**Before that, do not stop.** No matter how many failures, continue analyzing, improving, and re-running until success.

### 4.2 Failure Iteration Loop (Mandatory)

When the orchestrator fails (`exit_code≠0` or `sorry_count>0`), **must**:

1. **Analyze**: Collect full error output, `lake build` logs, Agent execution traces; locate failure stage and specific error.
2. **Discover**: Identify root cause (e.g. Agent3 prompt insufficient, Agent8 routing wrong, logic bug, hyperparameter wrong).
3. **Reflect**: Think and record—**why did I discover this?** Was the error message clear? Did the log structure help? Did some design expose it? What does this imply for improving the system?
4. **Design fix**: Based on root cause, design changes to orchestrator/prompts/config so the system can automatically solve such cases (**no hardcoding**, must be generic).
5. **Implement**: Modify `orchestrator/` within allowed scope.
6. **Re-run**: Execute `python -m orchestrator ... --skip-to-agent9` again.
7. **If still failing**: Return to step 1. **No retry limit; do not stop due to "repeated ineffective attempts".**

### 4.3 Forbidden Stop Reasons

The following are **not** valid reasons to stop:

- "Multiple consecutive failed attempts" → try a different approach.
- "Problem too complex" → break it down and continue.
- "Need to rewrite architecture" → make maximum improvements within allowed scope and continue.
- "Dependency/API issues" → try to fix within scope (e.g. check `.env`, path config) and continue.

**Goal**: Through orchestration logic, prompts, and config, make the system **autonomously** complete proof-filling, not by modifying Lib or docs to "give the answer".

---

## 5. Runtime & Environment

### 5.1 Working Directory

**Must** run with the project root as working directory. If your project is at `/root/SGD/research/SGD_coldstart`, use:

```bash
--working-dir /root/SGD/research/SGD_coldstart
```

If at `/root/SGD/SGD_coldstart`, use:

```bash
--working-dir /root/SGD/SGD_coldstart
```

### 5.2 Environment Variables

Ensure `.env` exists with:

```
QWEN_API_KEY=sk-sp-...
```

The orchestrator loads via `python-dotenv`; Trae inherits the environment when running `python -m orchestrator`.

### 5.3 System Credentials (for sudo when needed)

If you encounter permission denied (e.g. when accessing `/root/SGD/trae-agent` or running commands), you may need to use `sudo`. The user password is in `.env` as `SUDO_PASSWORD` (create this file if needed; it is gitignored).

Use it only when necessary to fix permission issues; prefer running without sudo when possible.

### 5.4 Verification Commands

- Target file only: `lake build Algorithms.SubgradientMethod` (or `run_lean_verify` inside orchestrator)
- Full project: `lake build`

---

## 6. Reference Documents (Read-Only, Do Not Modify)

| File | Purpose |
|------|----------|
| `docs/METHODOLOGY.md` | Gap taxonomy, Stub-Probe protocol, Archetype description |
| `docs/CATALOG.md` | Index of existing lemmas for Agent reuse |
| `docs/GLUE_TRICKS.md` | Proof patterns, Pattern A–G, Mathlib search strategy |
| `docs/CONVENTIONS.md` | Theorem signature design rules |
| `orchestrator/config.py` | Agent config, retry limits, routing params |

These documents and Lib are for reading only; **do not modify**.

---

## 7. How to Start

### Option A: Use the run script (easiest)

From your SGD_coldstart project root:

```bash
./run_trae.sh
```

Or with bash: `bash run_trae.sh`

### Option B: Run trae-cli directly

If you have access to trae-agent:

```bash
cd /root/SGD/trae-agent
source .venv/bin/activate
trae-cli run "Read AGENT.md. Improve the orchestrator until SubgradientMethod proof-filling succeeds in --skip-to-agent9 mode. No hardcoding. No modifying Lib or any .md. On failure: analyze, discover, reflect, fix, re-run. Do not stop until success." --working-dir /root/SGD/research/SGD_coldstart
```

### Option C: Use full path to trae-cli (if cd permission denied)

```bash
/root/SGD/trae-agent/.venv/bin/trae-cli run "Read AGENT.md. Improve the orchestrator until SubgradientMethod proof-filling succeeds in --skip-to-agent9 mode. No hardcoding. No modifying Lib or any .md. On failure: analyze, discover, reflect, fix, re-run. Do not stop until success." --working-dir /root/SGD/research/SGD_coldstart
```

### Option D: Interactive mode

```bash
/root/SGD/trae-agent/.venv/bin/trae-cli interactive --working-dir /root/SGD/research/SGD_coldstart
```

Then paste the task from AGENT.md and work through it step by step.
