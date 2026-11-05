# 固定规格 v1：数学与 Lean 对应审查

目标与 2026-11-01 的 `TASKS.md` 及 round38 任务文件一致：
`c = exp(-6888)`、全体有限互异正整数速度、基数至少二、统一时刻、严格不等式。
没有发现需要选择较弱数学版本的冲突。新增验收要求收紧的是验证流程。

`LonelyRunnerSpec/V1.lean` 只导入锁定的 mathlib，不导入项目证明或内部目标。
最终 Comparator 题面还将直接重复完整量词，不通过实现中的 `mainStatement` 定义目标。
规格版本与哈希单独记录于 `validation/frozen-v1.sha256.json`；修改须形成新版本并说明影响。

| 自然语言要求 | 固定 Lean 表达式/来源 | 必要检查、等价或归约 |
| --- | --- | --- |
| 有限且互异的整数速度 | `V : Finset ℕ`，独立规格 `V1.Statement` | Finset 自带无重复；不把向量重复项当作不同速度 |
| 全部速度严格为正 | `(∀ v ∈ V, 0 < v)` | 原 `positive` 正是此式；原 `valid` 只再合取 `2 ≤ V.card` |
| 基数至少二且无上界 | `2 ≤ V.card`，无其他基数参数 | `admissible_of_any_card` 构造每个允许基数的合法集合，排除空定义域解释 |
| 同一个时刻适用于所有速度 | `∀ V, ... → ∃ t : ℝ, ... ∀ v ∈ V, ∀ k : ℤ, ...` | `t` 在速度和整数的全称量词之前；不允许逐速度选择时刻 |
| 时刻在半开单位区间 | `0 ≤ t ∧ t < 1` | `Set.Ico` 定义展开；`internalStatement_iff_frozen` 正式连接内部类型 |
| 固定统一正改进 | `Real.exp (-6888 : ℝ)`，不依赖 V、n | 标准 mathlib `Real.exp`，负号输入显式是实数；`c_pos` 已证明，不使用机器浮点 |
| 严格距离界 | `|(v : ℝ)*t-(k : ℝ)| > ...` | `>` 为 `<` 的反向记法，与既有目标一致；乘法、绝对值、减法均在 ℝ |
| 半径分母 | `2 * (V.card : ℝ)` 后才做 `/` | 为实数除法，没有先进行自然数整除；`valid_card_pos` 给出分母非零 |
| 任意整数 k | `∀ k : ℤ` | 未截断为有限样本；`exists_nearest_integer` 和 `strict_all_integers_iff_nearest` 给出取到的最近整数及严格等价，未交换未取到的下确界 |
| 圆周/覆盖内部形式 | `SingleSpeedMeasure.forbidden_eq_circle_preimage` | 已正式证明圆周闭球与“存在整数距离≤r”等价；`RadiusExpansion.radius_expansion` 得到所有整数的严格避让 |
| 内部标签状态 | `TaggedState` 的非空、正性、单侧单射、预算、标签边、正 scale 字段 | 这是证明中间状态，不能作为最终 V 的额外前提；初态到标签状态以及回到 Finset 的完整连接尚待完成 |
| 无隐藏额外前提 | 规格无 section 变量、隐式自由参数、自定义实例或结构参数 | `autoImplicit false`；`SemanticDump` 用 `pp.all` 输出规格和关键内部定义。最终定理尚不存在，其完整参数审计仍未完成 |
| 非真空成立 | 允许每个 n≥2 的实例 | 现有条件性外层定理仍带三个数学输入，不能通过固定规格验收；负向样例检查改变正性为 False 的版本会被拒绝 |

`internalStatement_iff_frozen` 是 Lean 等价证明，并不证明目标为真。
`frozen_uniform_of_explicit` 仅在显式固定目标已经证明后推出统一常数推论。
当前没有宣称完整孤跑者猜想的 `1/(n+1)` 界。

审核状态：以上是模型撰写并自查的规格说明与机器核对；独立人工语义审核尚未进行。
文件哈希不保证初始翻译正确。已编译等价引理也不能替代审阅者对自然语言含义的核对。
