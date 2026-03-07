Algorithm name: SVRG（或你想证的任何算法）
Update rule: w_{t+1} = w_t - η·(∇f_i(w_t) - ∇f_i(w^s) + ∇f(w^s))
Proof sketch: 利用有限和结构，方差缩减到 O(1/T)
Archetype hint: B（有新的 snapshot 更新结构）


现在的完整自动化流程是这样的，分三步：
第一步：生成 Prover 提示词
你做的事：新开一个 agent 会话，粘贴 META_PROMPTS.md 里的 Meta-Prompt A，然后填入这四项：
Algorithm name: SVRG（或你想证的任何算法）Update rule: w_{t+1} = w_t - η·(∇f_i(w_t) - ∇f_i(w^s) + ∇f(w^s))Proof sketch: 利用有限和结构，方差缩减到 O(1/T)Archetype hint: B（有新的 snapshot 更新结构）
@ 的文件：docs/PROMPTS.md、docs/CATALOG.md、docs/ALGORITHM_TEMPLATE.md、docs/CONVENTIONS.md、docs/GLUE_TRICKS.md
agent 输出：一段完整的 Prover 提示词（格式与 Prompt 2A 一致）。
第二步：执行证明
你做的事：新开一个 agent 会话，粘贴上一步生成的 Prover 提示词，@ 提示词里列出的具体文件（通常是 Main.lean、SGD.lean、StochasticDescent.lean、Lib/Glue/ 下的文件等）。
agent 输出：完成的 .lean 文件，lake env lean 验证通过，无 sorry（或只剩允许的那一个）。
第三步：持久化
你做的事：新开一个 agent 会话，粘贴 Meta-Prompt B，填入：
Algorithm name: SVRGFiles modified: Algorithms/SVRG.lean（可能还有 Lib/Glue/SomeNewGlue.lean）New Glue lemmas: 名称 + 文件 + 一行描述New theorems proved: svrg_convergence_convex_v2Call chain: svrg_convergence_convex_v2 → ...New patterns discovered: （有则填，无则写 None）
@ 的文件：docs/PROMPTS.md、docs/CATALOG.md、docs/CONVENTIONS.md、docs/GLUE_TRICKS.md、完成的 .lean 文件
@Algorithms/SVRG.lean
@Lib/Glue/Probability.lean
@docs/CATALOG.md
@docs/CONVENTIONS.md
@docs/GLUE_TRICKS.md
@docs/METHODOLOGY.md
agent 输出：一段完整的 Archivist 提示词，你再把它发给另一个 agent 执行，它会自动更新 CATALOG.md、METHODOLOGY.md、GLUE_TRICKS.md，加 Used in: 标签。
总结
你输入算法描述    ↓ (Meta-Prompt A → 新 agent)自动生成 Prover 提示词    ↓ (粘贴给 Prover agent)自动完成 Lean 证明    ↓ (Meta-Prompt B → 新 agent)自动生成 Archivist 提示词    ↓ (粘贴给 Archivist agent)自动持久化所有文档
你自己全程只需要做三件事：①填算法描述 ②粘贴生成的提示词 ③确认每步结果正确。核心证明和文档工作全部由 agent 完成。