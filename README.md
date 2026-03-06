# StochOptLib — Stochastic Optimization Prerequisite Library

A Lean 4 library that formalizes stochastic optimization convergence proofs
by systematically identifying and proving the *glue lemmas* missing between
Mathlib and stochastic optimization mathematics.

**Core idea:** Rather than treating each algorithm's formalization as a
one-off effort, we use each algorithm as a *probe* that reveals specific
gaps in Mathlib's infrastructure. These gaps are filled with reusable glue
lemmas and catalogued for future proofs.

**Current status:** SGD (non-convex, convex, strongly convex) is the first
completed probe. Build: 2741 jobs, **0 sorry**, 0 warnings.

---

## Reading Order

Start here if you are an AI agent or new contributor:

| Step | Document | Purpose |
|------|----------|---------|
| 1 | [`docs/CONVENTIONS.md`](docs/CONVENTIONS.md) | **Read first.** Design rules for theorem signatures, measurability choices, and type coercions. Violating these causes circular proofs. |
| 2 | [`docs/CATALOG.md`](docs/CATALOG.md) | Searchable index of every proved lemma: gap level, proof steps, usage. Check here before writing a new lemma. |
| 3 | [`docs/GLUE_TRICKS.md`](docs/GLUE_TRICKS.md) | **HOW to prove things.** Universal proof patterns (Lipschitz addition, integral linearity, independence factorization, iterate-dependent variance). Algorithm-agnostic. |
| 4 | [`docs/ALGORITHM_TEMPLATE.md`](docs/ALGORITHM_TEMPLATE.md) | **HOW to add an algorithm.** Library-specific recipe: two archetypes, `StochasticDescentHyps` field reuse map, bridge lemma checklist. |
| 5 | [`docs/METHODOLOGY.md`](docs/METHODOLOGY.md) | WHY the library is structured this way: gap taxonomy, Stub-Probe protocol, algorithm probe selection, Mathlib PR criteria, roadmap. |
| 6 | Source code | Read in layer order: `Lib/Glue/` → `Lib/Layer0/` → `Lib/Layer1/` → `Algorithms/` |

---

## Module Map

| Directory | Role | No optimization content? |
|-----------|------|--------------------------|
| `Lib/Glue/` | General-purpose math primitives that fill Level 2/3 Mathlib gaps. Each lemma here could in principle be upstreamed to Mathlib. | Yes |
| `Lib/Layer0/` | Stochastic optimization building blocks: L-smooth descent lemma, convex/strongly-convex FOC, independence + expectation tools. | Partial |
| `Lib/Layer1/` | Algorithm-agnostic meta-theorems. The `StochasticDescentHyps` structure (15 fields) abstracts one stochastic gradient step; three meta-theorems cover non-convex, convex, and strongly convex settings. | No |
| `Algorithms/` | Concrete algorithm convergence proofs. Currently: `SGD.lean` instantiates the Layer 1 meta-theorems. | No |
| `Main.lean` | SGD process definition, measurability, filtration, and standard assumptions (`HasBoundedVariance`, `IsLSmooth`, `IsUnbiased`). | No |
| `docs/` | All persistent documentation (this file, CATALOG, CONVENTIONS, METHODOLOGY). | — |

---

## Proved Theorems

### SGD Convergence (`Algorithms/SGD.lean`)

| Theorem | Setting | Bound |
|---------|---------|-------|
| `sgd_convergence_nonconvex_v2` | L-smooth | $\frac{1}{T}\sum_{t<T}\mathbb{E}[\|\nabla f(w_t)\|^2] \leq \frac{2(f(w_0)-f^*)}{\eta T} + \eta L\sigma^2$ |
| `sgd_convergence_convex_v2` | L-smooth + convex | $\frac{1}{T}\sum_{t<T}(\mathbb{E}[f(w_t)]-f^*) \leq \frac{\|w_0-w^*\|^2}{2\eta T} + \frac{\eta\sigma^2}{2}$ |
| `sgd_convergence_strongly_convex_v2` | L-smooth + $\mu$-strongly convex | $\mathbb{E}[\|w_T-w^*\|^2] \leq (1-\eta\mu)^T\|w_0-w^*\|^2 + \frac{\eta\sigma^2}{\mu}$ |

All three proofs go through the Layer 1 meta-theorems via the `sgd_to_hyps` bridge.

---

## How to Add a New Algorithm

Follow these four steps. See [`docs/ALGORITHM_TEMPLATE.md`](docs/ALGORITHM_TEMPLATE.md)
for the concrete recipe and [`docs/METHODOLOGY.md`](docs/METHODOLOGY.md) for the
full methodology.

- [ ] **Step 1 — Find the mathematical proof.** Locate a textbook or survey paper
  with a clean convergence proof. The cleaner the proof, the easier the formalization.

- [ ] **Step 2 — Classify the algorithm.** Read `docs/ALGORITHM_TEMPLATE.md` §1:
  is this an **Archetype A** (oracle variant, same `w - η·g` update) or
  **Archetype B** (novel update structure)? Archetype A can reuse all Layer 2 SGD
  convergence theorems directly.

- [ ] **Step 3 — Fill gaps bottom-up.** For each proof obligation, check
  `docs/CATALOG.md` first. Consult `docs/GLUE_TRICKS.md` for proof patterns
  (Lipschitz composition, integral linearity, independence factorization,
  iterate-dependent variance). Follow `docs/CONVENTIONS.md` for all signature decisions.

- [ ] **Step 4 — Write the convergence theorem.** For Archetype A: define the
  effective oracle, build `effectiveSGDSetup`, prove bridge lemmas, then call
  `sgd_convergence_*` via `simpa`. See `Algorithms/WeightDecaySGD.lean` for the
  full worked example and `docs/ALGORITHM_TEMPLATE.md` §5 for the checklist.
  Update `docs/CATALOG.md` and `docs/METHODOLOGY.md` Roadmap when done.

---

## Build

```bash
lake build
```

Expected output: `Build completed successfully (2741 jobs).` with no warnings and no sorry.
