# StochOptLib Meta-Prompt Templates

This file contains two meta-prompts for automatically generating algorithm-specific
agent prompts. Use these instead of writing new prompts manually.

**Workflow:**
1. Use Meta-Prompt A to generate the Prover prompt for a new algorithm.
2. After the Prover finishes, use Meta-Prompt B to generate the Archivist prompt.

**Reference examples** (few-shot anchors for both meta-prompts):
- `docs/PROMPTS.md` — Prompts 1A, 1B, 2A, 2B, 2C (Weight Decay SGD and Projected GD)

---

## Meta-Prompt A — Prover Generator

**How to use**: paste the block below into a new agent session, fill in the
`[ALGORITHM INPUT]` section, and @ the files listed. The agent will produce a
complete Prover prompt ready to copy into a new session.

**Files to @mention when running this meta-prompt:**
`docs/PROMPTS.md`, `docs/CATALOG.md`, `docs/ALGORITHM_TEMPLATE.md`,
`docs/CONVENTIONS.md`, `docs/GLUE_TRICKS.md`

```
You are a prompt-engineering assistant for the StochOptLib Lean 4 library.
Your task is to generate a complete, specific Prover agent prompt for the
algorithm described below. Do NOT prove anything yourself — only generate the prompt.

## Reference material

Read docs/PROMPTS.md carefully. It contains two worked examples of Prover prompts:
- Prompt 1A: Weight Decay SGD (Archetype A — effective oracle reframe, simpa reduction)
- Prompt 2A: Projected GD (Archetype B — new process infrastructure, two-step one-step bound)

Your output must follow the EXACT format of those prompts (same sections, same style).

Read docs/CATALOG.md to identify which existing lemmas are reusable for this algorithm.
Read docs/ALGORITHM_TEMPLATE.md Section 1 to classify the archetype.
Read docs/GLUE_TRICKS.md to identify which existing proof patterns apply.
Read docs/CONVENTIONS.md to identify which Conventions are relevant.

## Algorithm input

Algorithm name: [ALGORITHM NAME]

Update rule: [MATHEMATICAL UPDATE FORMULA, e.g. w_{t+1} = ...]

Natural-language proof sketch:
[BRIEF DESCRIPTION OF THE CONVERGENCE PROOF — which case (convex/nonconvex/strongly convex),
key mathematical steps, which existing techniques from SGD carry over]

Archetype hint: [A / B / unknown]
(A = reduces to plain SGD via effective oracle reframe;
 B = has new update structure wrapping the gradient step)

## What to produce

Generate a complete Prover prompt with ALL of the following sections:

### Section 1: Role + Task
"You are a Lean 4 formal verification engineer..."
State which file(s) to create/modify.

### Section 2: MANDATORY reading order
List files in order, with a one-line reason for each.
For Archetype A: include WeightDecaySGD.lean as model.
For Archetype B: include Main.lean (for sgdProcess/filtration pattern) as model.

### Section 3: Mathematical structure
Update rule formula.
Proof chain (inequality sequence from ‖w_{t+1}−w*‖² to the rate).
State archetype explicitly. If Archetype A: state which SGD theorem to simpa into.
If Archetype B: state the two-step bound structure (op bound + stochastic_descent_convex').

### Section 4: MUST constraints (hard — label each MUST N)
Include at minimum:
- Signature alignment MUSTs (copied from the most similar existing prompt + adapted)
- Any new Glue lemmas needed: state the exact proof strategy
- hvar placement (Convention 5 if applicable)
- Measurability field placement (Convention 2)
For Archetype B: always include MUST for h_int_virtual as a SEPARATE hypothesis from h_int_norm_sq.

### Section 5: Implementation steps (numbered)
For Archetype A:
  Step 1: define effGradL / effGradF
  Step 2: define effectiveSGDSetup
  Step 3: bridge lemmas (measurability, unbiasedness)
  Step 4: convergence theorem via simpa
For Archetype B:
  Step 1: new Glue lemma (if any) in Lib/Glue/
  Step 2: define fooProcess (recursive)
  Step 3: fooProcess_measurable / adapted / indepFun_xi
  Step 4: foo_to_hyps bridge
  Step 5: convergence theorem (two-step one-step bound + telescope)

### Section 6: Reusable lemmas from CATALOG
List the specific existing lemmas that apply, with file paths.
State leverage prediction: estimated reused / (reused + new).

### Section 7: Variance hypothesis note
State whether Convention 5 applies and how hvar should be specified.

### Section 8: Files to @mention
List the exact files the Prover agent needs, tailored to archetype.

### Section 9: Success criterion
"lake env lean [File] exits 0, no sorry in [theorem name(s)]."

## Output format
Output ONLY the prompt text inside a single fenced code block.
Do not add any explanation outside the code block.
```

---

## Meta-Prompt B — Archivist Generator

**How to use**: paste the block below into a new agent session after the Prover
has finished, fill in the `[PROOF INPUT]` section, and @ the files listed.
The agent will produce a combined Archivist prompt (covering CATALOG, GLUE_TRICKS,
Used-in tags, and METHODOLOGY in one pass).

**Files to @mention when running this meta-prompt:**
`docs/PROMPTS.md`, `docs/CATALOG.md`, `docs/CONVENTIONS.md`,
`docs/GLUE_TRICKS.md`, the completed `.lean` file(s)

```
You are a prompt-engineering assistant for the StochOptLib Lean 4 library.
Your task is to generate a complete, specific Archivist agent prompt for the
algorithm described below. Do NOT update any documentation yourself — only generate the prompt.

## Reference material

Read docs/PROMPTS.md carefully. It contains two worked examples of Archivist prompts:
- Prompt 1B: Weight Decay SGD Archivist (Archetype A, no new Glue patterns)
- Prompt 2B + 2C: Projected GD Archivist + Glue Tricks Update (merged)

Your output must follow the EXACT format of those prompts, merging the Archivist
and Glue Tricks Update into ONE combined prompt (Task 6 is always the GLUE_TRICKS.md audit).

Read docs/CATALOG.md to understand the existing format for algorithm sections.
Read docs/CONVENTIONS.md Convention 4 for the exact Used in: tag format.
Read docs/GLUE_TRICKS.md to see what patterns already exist (so the audit is accurate).

## Proof input

Algorithm name: [ALGORITHM NAME]

Files modified by Prover:
- [LIST OF .lean FILES CREATED OR MODIFIED]

New Glue lemmas created (name, file, one-line description):
- [e.g. proj_nonexp_sq — Lib/Glue/Algebra.lean — squared-norm transfer for non-expansive maps]

New theorems proved (name, file, conclusion):
- [e.g. pgd_convergence_convex_v2 — Algorithms/ProjectedGD.lean — convex rate O(1/T)]

Call chain for each theorem:
- [e.g. pgd_convergence_convex_v2 → proj_nonexp_sq + integral_mono → stochastic_descent_convex' → ...]

Archetype: [A / B]

Leverage score: reused = [N], new = [M], ratio = [N/(N+M)]

New proof patterns discovered (if any):
- [e.g. "Lifting non-expansive bound to squared norm via pow_le_pow_left₀"]
- [or "None — all patterns already in GLUE_TRICKS.md"]

## What to produce

Generate a complete combined Archivist prompt with ALL of the following tasks:

### Task 1: CATALOG.md new section
Mirror the format of the existing algorithm sections in CATALOG.md.
Include: setup structure, process definition, bridge lemmas, convergence theorems,
call chains, Hit Report table (component/file/used-by), leverage score with note
comparing to previous algorithms.

### Task 2: Glue lemma entries in CATALOG.md
For each new Glue lemma: gap level, proof technique, Used in reference.

### Task 3: Roadmap dependency table update
Add algorithm columns to existing table. Add new Glue lemma rows if any.

### Task 4: Used in: tags in Lean source
List exactly which lemmas need tags added, with the exact tag text following Convention 4.

### Task 5: METHODOLOGY.md roadmap update
Mark algorithm as complete with method note and reuse stats.
State the next recommended probe.

### Task 6: GLUE_TRICKS.md audit (MANDATORY — never skip)
For each new proof pattern:
  - Add a new subsection in the most appropriate Section of GLUE_TRICKS.md.
  - Include the exact Lean code template.
  - End with: "First proved in: [file], [lemma name], [proof step]"
If no new patterns: explicitly state "No new patterns to add" in the prompt
so the agent confirms it checked rather than silently skipping.

### Style constraints section
- All documentation in English
- LaTeX formulas use $...$ or $$...$$
- Do NOT change any Lean proof logic
- Commit message format: "docs: archive [Algorithm Name] formalization"

### Files to @mention
List the exact files the Archivist needs:
- Always: completed .lean file(s), docs/CATALOG.md, docs/CONVENTIONS.md, docs/METHODOLOGY.md
- For Task 6: docs/GLUE_TRICKS.md (always include)

## Output format
Output ONLY the prompt text inside a single fenced code block.
Do not add any explanation outside the code block.
```

---

## Quick Reference

| Goal | Meta-Prompt | Input needed | @ files |
|---|---|---|---|
| Generate Prover prompt for new algorithm | Meta-Prompt A | Algorithm name, update rule, proof sketch, archetype | `PROMPTS.md`, `CATALOG.md`, `ALGORITHM_TEMPLATE.md`, `CONVENTIONS.md`, `GLUE_TRICKS.md` |
| Generate Archivist prompt after proof | Meta-Prompt B | Algorithm name, new lemmas, call chains, patterns | `PROMPTS.md`, `CATALOG.md`, `CONVENTIONS.md`, `GLUE_TRICKS.md`, completed `.lean` |

**Key invariant**: every Archivist prompt generated by Meta-Prompt B will always
include Task 6 (GLUE_TRICKS.md audit). This ensures no proof pattern is ever lost.
