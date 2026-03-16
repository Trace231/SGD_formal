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

### 3.4 Absolute Prohibitions

- **No hardcoding**: Hardcoding is **absolutely forbidden**. Algorithm names, file paths, proof steps, lemma names, specific tactics, line numbers, error message fragments, numeric constants, etc. must not be hardcoded in `orchestrator/` code. All variable content must come from config, parameters, CLI, environment variables, or runtime inference. Improvements must be **generic**, applicable to different algorithms and sorries, not SubgradientMethod-specific patches.
- **No modifying any `.lean` files**: Do not modify any Lean source files (e.g. `Algorithms/*.lean`, `Lib/*.lean`). Only modify orchestrator Python code (`orchestrator/*.py`). Modifying Lib is equivalent to giving the answer; modifying algorithm files defeats the purpose of improving the orchestrator.
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
   - **Read the target algorithm file** (e.g. `Algorithms/SubgradientMethod_with_sorry.lean`) to find the main problems: which sorries are hardest, what structural patterns block the system, what the proof structure requires. This informs the root cause.
3. **Reflect**: Think and record—**why did I discover this?** **Why can I find the problem when the current system cannot?** What information or reasoning did I use that the orchestrator/agents lack? Was the error message clear? Did the log structure help? Did some design expose it? What does this imply for improving the system?
4. **Design fix**: Based on root cause, design changes to orchestrator/prompts/config so the system can automatically solve such cases (**no hardcoding**, must be generic).
5. **Implement**: Modify `orchestrator/` within allowed scope.
6. **Re-run**: Execute `python -m orchestrator ... --skip-to-agent9` again.
7. **If still failing**: Return to step 1. **No retry limit; do not stop due to "repeated ineffective attempts".**

### 4.3 Automated Background Execution & Monitoring with Smart Termination (MANDATORY)

**CRITICAL**: You MUST automate the entire workflow. Do NOT wait for the user to manually run anything.

**ALSO CRITICAL**: You MUST terminate early when it's clear the current approach is wasting time. Don't continue a doomed run.

#### Step 0: Optional Pre-Flight (When Starting a New Round)

**When LAST_RUN_SUMMARY.md exists** and indicates a specific module or component failed:

1. **Read the failing module first** before starting the orchestrator
2. Understand the code flow that produced the error
3. If you can identify an obvious fix (e.g., wrong threshold, missing condition), **fix it before starting**
4. This can save time by avoiding a doomed run

**When to do pre-flight**:
- Continuation round (Round 2+) with clear failure pattern
- Last round's summary says "Agent8 routing wrong" or "Agent3 prompt insufficient"
- You have a hypothesis about which file to change

**When to skip pre-flight**:
- First round (no prior context)
- Failure was ambiguous or infrastructure-related
- You need to see a fresh run to form a hypothesis

#### Step 1: Always Use Background Mode

**When you need to run the orchestrator:**

```bash
# DO THIS (automated):
./run_orchestrator_bg.sh --skip-to-agent9 --spec-file book/FOML/SubgradientMethod.json --target-file Algorithms/SubgradientMethod_with_sorry.lean
```

**NEVER** run `python -m orchestrator` directly (it will timeout after 120s).

#### Step 2: Automated Monitoring Loop with Early Termination

**Progress & running state**: LLM calls (Agent3, Agent8, etc.) take time. To judge whether the orchestrator is running and making progress, **use audit logs as the primary signal**: check if new audits are being created, if `phase3_attempts` is increasing, etc. Do not assume "stuck" just because `sorry_count` has not changed after a few minutes — proof filling often requires many attempts.

**Early termination** is appropriate only when: (a) the run has completed but failed (flow ended with build failure or sorries remaining), or (b) audit logs show clear stuck patterns: Lean proof repair/filling has many repeated attempts with the same error or no progress (e.g., same error 3+ consecutive audits, same agent failing same line 5+ times). Do NOT terminate early based solely on `sorry_count` unchanged for a few minutes — use audit-based evidence.

**Immediately after starting the orchestrator**, enter this monitoring loop:

```
START MONITORING LOOP
├─ Wait 2-3 minutes
├─ Run: ./check_orchestrator_status_enhanced.sh
├─ Analyze the output:
│   ├─ Check 1: Latest Audit Logs
│   │   ├─ Are new audits being created?
│   │   ├─ What errors are in phase3_attempt_failures?
│   │   ├─ Which agents are active?
│   │   └─ → CRITICAL: Same error repeating 3+ times?
│   │
│   ├─ Check 2: Target File Status
│   │   ├─ Has sorry_count decreased?
│   │   ├─ Which lines still have sorries?
│   │   ├─ Was the file modified recently?
│   │   └─ → CRITICAL: Sorry count unchanged for 3+ checks?
│   │
│   └─ Check 3: Background Output
│       ├─ What's the current phase?
│       ├─ What's the sorry_count trend?
│       ├─ Any errors in recent log lines?
│       └─ → CRITICAL: No phase progression for 15+ min?
│
├─ Decision Tree:
│
│   1. FIRST: Check for EARLY TERMINATION conditions:
│      ├─ ❌ Same exact error repeating 3+ consecutive audits?
│      │   └─ YES → TERMINATE EARLY (wasting time on broken approach)
│      │
│      ├─ ❌ Sorry count unchanged for 4+ checks (12+ min)?
│      │   └─ YES → TERMINATE EARLY (clearly stuck, not making progress)
│      │
│      ├─ ❌ No phase progression for 20+ min?
│      │   └─ YES → TERMINATE EARLY (system is hung)
│      │
│      ├─ ❌ Same agent failing on same line 5+ times?
│      │   └─ YES → TERMINATE EARLY (agent can't solve this)
│      │
│      └─ ❌ Error type = "timeout" or "hang" repeatedly?
│          └─ YES → TERMINATE EARLY (infrastructure issue, not code)
│
│   2. IF ANY early termination condition met:
│      └─ STOP monitoring immediately
│      └─ Go to Step 2B: Early Termination Protocol
│
│   3. IF NO early termination needed:
│      ├─ If progress detected (sorry_count ↓, new audits):
│      │   └─ Continue monitoring (go back to START)
│      │
│      └─ If stuck detected (same state for 2+ checks):
│          └─ Go to Step 3: Analyze & Fix
│
└─ Repeat until orchestrator completes OR early termination triggered
```

#### Step 2B: Early Termination Protocol (When Wasting Time)

When you detect an early termination condition:

1. **Immediately terminate** the orchestrator:
   ```bash
   kill $(cat orchestrator.pid)
   ```

2. **Document why you're terminating early**:
   ```bash
   cat > early_termination_reason.md << EOF
# Early Termination — Round $ROUND

## Reason for Termination
[Clearly state which condition triggered early termination]

## Evidence
- Check 1: [What you observed in audits]
- Check 2: [What you observed in target file]
- Check 3: [What you observed in logs]

## Analysis
Why this approach was clearly failing:
- [Specific pattern observed]
- [Why continuing would waste time]
- [What needs to change]

## Recommended Next Steps
What to try differently next round:
1. [Specific change 1]
2. [Specific change 2]
3. [Specific change 3]

## Time Saved
- Terminated after: X minutes
- Estimated time wasted if continued: Y minutes
- Net time saved: Y - X minutes
EOF
   ```

3. **Analyze the root cause** (read source code before fixing):
   - What specific pattern showed this was failing?
   - **Read the relevant orchestrator module(s)** (see Section 4.3.D below)
   - What does the code tell you about why it fails?
   - What fundamentally needs to change?
   - Time: 2-5 min for quick cases; up to 10 min when tracing complex code paths

4. **Implement a targeted fix** based on the analysis

5. **Restart orchestrator** with the new fix:
   ```bash
   rm -f orchestrator.log orchestrator.pid
   ./run_orchestrator_bg.sh --skip-to-agent9 [same args]
   ```

6. **Resume monitoring** (back to Step 2)

---

### 4.3.B Early Termination Conditions (Detailed)

**Condition 1: Same Error Repeating (3+ consecutive audits)**

```
Audit N:   "type mismatch at line 45"
Audit N+1: "type mismatch at line 45"
Audit N+2: "type mismatch at line 45"
Audit N+3: "type mismatch at line 45"
→ TERMINATE EARLY

Why: The current approach clearly cannot solve this error.
     Continuing to retry the same method will not work.
     Need a fundamentally different strategy.
```

**Condition 2: Sorry Count Unchanged (4+ checks = 12+ min)**

```
Check 1 (T+3 min):  sorry_count = 212
Check 2 (T+6 min):  sorry_count = 212
Check 3 (T+9 min):  sorry_count = 212
Check 4 (T+12 min): sorry_count = 212
→ TERMINATE EARLY

Why: Zero progress for 12+ minutes means the approach is completely blocked.
     This is not a temporary slowdown — it's a fundamental failure.
     Cut losses and try a different approach immediately.
```

**Condition 3: No Phase Progression (20+ min)**

```
T+0 min:  Phase 4
T+10 min: Phase 4
T+20 min: Phase 4
→ TERMINATE EARLY

Why: Should complete Phase 4 in 5-10 min max.
     20+ min in same phase = system is hung or in infinite loop.
     This is infrastructure failure, not proof failure.
     Restart with fresh state.
```

**Condition 4: Same Agent Failing on Same Line (5+ times)**

```
Attempt 1: Agent3 fails on line 45
Attempt 2: Agent3 fails on line 45
Attempt 3: Agent3 fails on line 45
Attempt 4: Agent3 fails on line 45
Attempt 5: Agent3 fails on line 45
→ TERMINATE EARLY

Why: Agent3 clearly cannot solve this specific sorry.
     Either need to:
     - Route to Agent6/7 instead
     - Change Agent3's prompt fundamentally
     - Fix the type signature so it's provable
     Continuing to let Agent3 retry is wasting time.
```

**Condition 5: Timeout/Hang Errors (Repeated)**

```
Log: "timeout: lake build did not complete"
Log: "timeout: lake build did not complete"
Log: "timeout: lake build did not complete"
→ TERMINATE EARLY

Why: This is infrastructure/tooling failure, not proof failure.
     The build system is hung, not the proof strategy.
     Need to kill and restart with clean state.
```

---

### 4.3.C Time Budget Awareness

**Maximum monitoring duration before forced termination:**

| Check # | Time Elapsed | Action |
|---------|--------------|--------|
| 1-2 | 3-6 min | Normal monitoring |
| 3-4 | 9-12 min | Watch for stuck patterns |
| 5-6 | 15-18 min | If still stuck → TERMINATE |
| 7-8 | 21-24 min | **MUST TERMINATE** if no progress |
| 9+ | 27+ min | **OVERDUE** — should have terminated already |

**Rule**: If you reach check #8 (24 min) with zero progress, you MUST terminate. No exceptions.

**Why**: 24 minutes with zero progress = approach is completely broken.
Continuing is just delaying the inevitable. Better to:
1. Terminate now (2 min)
2. Analyze (3 min)
3. Fix and restart (2 min)
4. Make progress in new round

Than:
1. Waste 30 more minutes in doomed round
2. Eventually fail anyway
3. Then analyze and fix

**Total time saved**: 25+ minutes per early termination.

#### Step 3: Automated Analysis & Fix (When Stuck)

When you detect a stuck pattern:

1. **Gather data** (automated):
   ```bash
   ./check_orchestrator_status_enhanced.sh --full
   cat orchestrator/audits/latest_audit.json | python3 -m json.tool
   tail -n 200 orchestrator.log
   ```

2. **Identify root cause** (MUST read orchestrator source code):
   - What error type keeps appearing?
   - Which sorry/location is blocked?
   - Which agent is failing?
   - **Read the orchestrator source code** for the failing component:
     - Use `grep`, `cat`, `head` on `orchestrator/*.py` to understand the logic
     - Trace the code path that produces this error
     - Understand *why* the current logic fails, not just *what* the error says
   - Implement fix based on **code understanding**, not just error messages

3. **Implement fix** in orchestrator code

4. **Restart orchestrator** (automated):
   ```bash
   # Stop current run (if still running)
   kill $(cat orchestrator.pid)
   
   # Clean up
   rm -f orchestrator.log orchestrator.pid orchestrator_status.json
   
   # Re-run with same args
   ./run_orchestrator_bg.sh --skip-to-agent9 [same args]
   ```

5. **Return to Step 2** (monitoring loop)

#### 4.3.D Check Specific Modules When Needed

When analysis points to a specific component, **read that module** before implementing a fix:

| Symptom / Error | Module(s) to Read | What to Look For |
|-----------------|-------------------|------------------|
| Agent8 routing wrong | `orchestrator/phase3_agent8.py` | Routing logic, decision thresholds |
| Agent3 failing | `orchestrator/agent3_executor.py`, `orchestrator/prompts.py` | Prompt content, tool usage |
| Agent6/7 not triggered | `orchestrator/phase3_agent8.py`, `orchestrator/config.py` | Routing conditions, thresholds |
| Config / hyperparameters | `orchestrator/config.py` | Retry limits, routing params |
| Main flow / phase logic | `orchestrator/main.py` | Phase transitions, skip logic |

**Commands to inspect modules**:
```bash
grep -n "keyword" orchestrator/phase3_agent8.py
head -150 orchestrator/phase3_agent8.py
cat orchestrator/prompts.py | grep -A 30 "Agent3"
```

You are **encouraged** to use `grep`, `cat`, `head` on any `orchestrator/*.py` file to understand the code before implementing fixes. Do not guess — read the code.

#### Step 4: Automated Completion Check

When orchestrator completes:

1. **Check final status**:
   ```bash
   ./check_orchestrator_status_enhanced.sh --full
   ```

2. **Verify success**:
   - exit_code = 0?
   - sorry_count = 0?
   - Full project builds?

3. **If success**: Task complete, you can stop

4. **If failure**: Go to Step 3 (analyze & fix)

---

### 4.4 Monitoring Frequency & Timing

**Default schedule** (follow when not doing deep analysis):

| Time After Start | Action |
|------------------|--------|
| T+0 min | Start orchestrator with `./run_orchestrator_bg.sh` |
| T+3 min | First status check: `./check_orchestrator_status_enhanced.sh` |
| T+6 min | Second status check |
| ... | Continue every 3 minutes |
| When stuck detected | Analyze, fix, restart, reset timer |
| When complete | Verify and stop |

**Flexible timing** (when doing deep analysis):
- **Default**: Check every 3 minutes
- **When analyzing root cause** (reading multiple files, tracing code paths):
  - You may take **5-10 minutes** for analysis before the next status check
  - Do not sacrifice analysis quality for rigid timing
  - Reading `phase3_agent8.py`, `prompts.py`, etc. takes time — that is expected
- **Maximum gap between checks**: 10 minutes (if analyzing, do not exceed 10 min without a check)
- **Never skip** a check when orchestrator is running — but analysis steps between checks are allowed

---

### 4.5 Stuck Pattern Detection (Automated)

**You MUST detect these patterns automatically:**

**Pattern 1: Sorry Count Stuck**
```
Check 1: sorry_count = 212
Check 2: sorry_count = 212
Check 3: sorry_count = 212
→ STUCK! Take action.
```

**Pattern 2: No New Audits**
```
Check 1: 3 audits
Check 2: 3 audits (no new in 3 min)
Check 3: 3 audits (no new in 6 min)
→ STUCK! Take action.
```

**Pattern 3: Same Error Repeating**
```
Audit 1: "type mismatch at line 45"
Audit 2: "type mismatch at line 45"
Audit 3: "type mismatch at line 45"
→ STUCK! Take action.
```

**Pattern 4: File Not Modified**
```
Check 1: file modified 1 min ago
Check 2: file modified 4 min ago
Check 3: file modified 7 min ago
→ STUCK! Take action.
```

**When you detect ANY stuck pattern:**
1. Stop waiting
2. Analyze the root cause
3. Implement a fix
4. Restart orchestrator
5. Resume monitoring

---

### 4.6 Forbidden Manual Actions

**DO NOT** ask the user to:
- ❌ "Please run this command to check status"
- ❌ "You should monitor the logs"
- ❌ "Wait for the orchestrator to finish"
- ❌ "Check if sorry_count decreased"

**INSTEAD, YOU MUST:**
- ✅ Automatically run `./check_orchestrator_status_enhanced.sh`
- ✅ Automatically analyze the output
- ✅ Automatically detect stuck patterns
- ✅ Automatically implement fixes
- ✅ Automatically restart orchestrator

**Your job**: Fully automate the entire run-monitor-fix cycle.
**User's job**: Nothing. The system runs autonomously.

### 4.4 Forbidden Stop Reasons

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

---

## 8. Automated Execution Protocol (CRITICAL)

### 8.1 The Golden Rule

**YOU MUST AUTOMATE EVERYTHING. THE USER SHOULD NOT MANUALLY RUN ANYTHING.**

Your workflow:
```
1. Start orchestrator (background)
   ↓
2. Wait 3 minutes
   ↓
3. Check status automatically
   ↓
4. Analyze: Progress or Stuck?
   ↓
5a. If progress: Continue monitoring
5b. If stuck: Fix code, restart orchestrator
   ↓
6. Repeat until success
```

### 8.2 Mandatory Commands

**Start orchestrator:**
```bash
./run_orchestrator_bg.sh --skip-to-agent9 --spec-file book/FOML/SubgradientMethod.json --target-file Algorithms/SubgradientMethod_with_sorry.lean
```

**Check status (every 3 minutes, automatically):**
```bash
./check_orchestrator_status_enhanced.sh
```

**Analyze stuck (when detected):**
```bash
./check_orchestrator_status_enhanced.sh --full
```

**Restart after fix:**
```bash
kill $(cat orchestrator.pid)
rm -f orchestrator.log orchestrator.pid
./run_orchestrator_bg.sh --skip-to-agent9 [same args]
```

### 8.3 Automated Decision Tree

```
After each status check, decide:

Has sorry_count decreased?
├─ YES → Continue monitoring (wait 3 min, check again)
└─ NO → Check next condition

Are new audits being created?
├─ YES → Continue monitoring
└─ NO → Check next condition

Is target file being modified?
├─ YES → Continue monitoring
└─ NO → STUCK DETECTED → Take action!

STUCK ACTION:
1. Run: ./check_orchestrator_status_enhanced.sh --full
2. Read last 200 lines: tail -n 200 orchestrator.log
3. Analyze latest audit: cat orchestrator/audits/latest.json
4. Identify root cause (error type, stuck location, failing agent)
5. Fix orchestrator code
6. Restart orchestrator
7. Resume monitoring
```

### 8.4 Timing Requirements

| Event | Required Action |
|-------|-----------------|
| T+0 min | Start orchestrator |
| T+3 min | Auto status check |
| T+6 min | Auto status check |
| T+9 min | Auto status check |
| T+12 min | Auto status check |
| ... | Continue every 3 min |
| Stuck detected | Analyze + Fix + Restart |
| Success | Verify + Stop |

**Maximum wait between checks**: 5 minutes

**Minimum checks before giving up**: 10 checks (30 minutes)

### 8.5 What NOT to Do

❌ **NEVER** run `python -m orchestrator` directly (will timeout)

❌ **NEVER** ask the user to manually check anything

❌ **NEVER** wait longer than 5 minutes without checking

❌ **NEVER** stop monitoring until success is verified

❌ **NEVER** assume timeout = failure (orchestrator may still be running)

### 8.6 Available Tools (Reference)

| Tool | When to Use |
|------|-------------|
| `run_orchestrator_bg.sh` | Start orchestrator (always use this) |
| `check_orchestrator_status_enhanced.sh` | Every 3 minutes for status |
| `check_orchestrator_status_enhanced.sh --full` | When stuck, for detailed analysis |
| `monitor_orchestrator_dashboard.sh` | Optional: real-time monitoring |
| `orchestrator_monitor.py status` | Programmatic JSON access |

---

**REMEMBER**: Your job is to fully automate the run-monitor-fix cycle. The user should not need to manually run any commands or check any logs. You are responsible for the entire workflow from start to success.
