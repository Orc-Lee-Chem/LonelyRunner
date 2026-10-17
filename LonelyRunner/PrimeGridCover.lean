import LonelyRunner.GridIntervalCount
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Field.ZMod

/-! 论文 `paper/lonely_runner_zh.tex` 第 617–633 行：素数平移与共同分母，
这里只处理式 `eq:prime` 的网格覆盖步骤。 -/

namespace LonelyRunner

/-- 论文第 74–83 行的闭 Bohr 集：圆周上的 `[-δ,δ]` 原像，端点均计入。 -/
def bohrSet (v : ℕ) (δ : ℝ) : Set UnitAddCircle :=
  {t | v • t ∈ closedArc (-δ) (2 * δ)}

/-- 论文第 74–83 行：`‖vt‖≤δ` 的闭区间表示；即 `vt` 有一个位于
`[-δ,δ]` 的实数代表。两个端点均属于 Bohr 集。 -/
theorem mem_bohrSet_iff (v : ℕ) (δ : ℝ) (t : UnitAddCircle) :
    t ∈ bohrSet v δ ↔
      ∃ y : ℝ, -δ ≤ y ∧ y ≤ δ ∧ (y : UnitAddCircle) = v • t := by
  simp only [bohrSet, Set.mem_ofPred_eq, closedArc, Set.mem_image, Set.mem_Icc]
  constructor
  · rintro ⟨y, ⟨hy₁, hy₂⟩, hyt⟩
    refine ⟨y, hy₁, ?_, hyt⟩
    convert hy₂ using 1; ring
  · rintro ⟨y, hy₁, hy₂, hyt⟩
    refine ⟨y, ⟨hy₁, ?_⟩, hyt⟩
    convert hy₂ using 1; ring

/-- 论文第 74–83 行：速度族的闭 Bohr 集覆盖整个圆周。 -/
def Covers (V : Finset ℕ) (δ : ℝ) : Prop :=
  ∀ t : UnitAddCircle, ∃ v ∈ V, t ∈ bohrSet v δ

/-- 论文第 617 行：覆盖不可约，即任何真子族均不能覆盖圆周。 -/
def IrreducibleCover (V : Finset ℕ) (δ : ℝ) : Prop :=
  Covers V δ ∧ ∀ W : Finset ℕ, W ⊂ V → ¬ Covers W δ

/-- 论文第 630 行：被素数 `p` 整除的速度族。 -/
def divisibleSpeeds (V : Finset ℕ) (p : ℕ) : Finset ℕ :=
  V.filter (p ∣ ·)

/-- 论文第 630 行：`r_p` 是未被 `p` 整除的速度数。 -/
def nondivisibleCount (V : Finset ℕ) (p : ℕ) : ℕ :=
  (V.filter (fun v => ¬ p ∣ v)).card

/-- 论文第 630 行：若 `C` 中所有速度都被 `G` 整除，且 `p∣G`，
则 `r_p≤m/2`。这是同一段中的辅助事实，网格下界本身只用 `gcd(V)=1`。 -/
theorem nondivisibleCount_le_half (V C : Finset ℕ) (m G p : ℕ)
    (hm : m = V.card) (hCV : C ⊆ V)
    (hCcard : (m : ℝ) / 2 ≤ (C.card : ℝ))
    (hGdiv : ∀ v ∈ C, G ∣ v) (hpG : p ∣ G) :
    (nondivisibleCount V p : ℝ) ≤ (m : ℝ) / 2 := by
  classical
  have hsub : C ⊆ V.filter (p ∣ ·) := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨hCV hv, hpG.trans (hGdiv v hv)⟩
  have hcard : C.card ≤ (V.filter (p ∣ ·)).card := Finset.card_le_card hsub
  have hpart := Finset.card_filter_add_card_filter_not (s := V) (p := (p ∣ ·))
  have hcardR : (C.card : ℝ) ≤ ((V.filter (p ∣ ·)).card : ℝ) := by
    exact_mod_cast hcard
  have hpartR : ((V.filter (p ∣ ·)).card : ℝ) +
      (nondivisibleCount V p : ℝ) = (m : ℝ) := by
    exact_mod_cast (hm ▸ hpart)
  linarith

/-- 论文第 630 行：`gcd(V)=1` 保证被 `p` 整除的速度只是一个真子族。 -/
theorem divisibleSpeeds_proper (V : Finset ℕ) (p : ℕ)
    (hp : p.Prime) (hgcd : V.gcd id = 1) : divisibleSpeeds V p ⊂ V := by
  classical
  apply (Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).2
  by_contra h
  push Not at h
  have hall : ∀ v ∈ V, p ∣ v := by
    intro v hv
    by_contra hnp
    exact hnp (Finset.mem_filter.mp (h v hv)).2
  have hpdvd : p ∣ V.gcd id := Finset.dvd_gcd hall
  rw [hgcd] at hpdvd
  exact hp.ne_one (Nat.dvd_one.mp hpdvd)

/-- 论文第 630–631 行：不可约覆盖给出所有 `p` 倍速共同漏掉的时刻。 -/
theorem exists_uncovered_divisible (V : Finset ℕ) (δ : ℝ) (p : ℕ)
    (hp : p.Prime) (hgcd : V.gcd id = 1)
    (hirr : IrreducibleCover V δ) :
    ∃ t₀ : UnitAddCircle, ∀ v ∈ V, p ∣ v → t₀ ∉ bohrSet v δ := by
  have hnc := hirr.2 (divisibleSpeeds V p) (divisibleSpeeds_proper V p hp hgcd)
  simp only [Covers, not_forall] at hnc
  obtain ⟨t₀, ht₀⟩ := hnc
  refine ⟨t₀, ?_⟩
  intro v hv hpv hmem
  exact ht₀ ⟨v, Finset.mem_filter.mpr ⟨hv, hpv⟩, hmem⟩

/-- 论文第 631 行：被 `p` 整除的速度在平移 `a/p` 后取值不变。 -/
theorem divisible_smul_grid (p v : ℕ) [NeZero p] (a : ZMod p) (hpv : p ∣ v) :
    v • ZMod.toAddCircle a = (0 : UnitAddCircle) := by
  have hv : (v : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff v p).2 hpv
  calc
    v • ZMod.toAddCircle a = ZMod.toAddCircle (v • a) := (map_nsmul _ _ _).symm
    _ = 0 := by simp [nsmul_eq_mul, hv]

/-- 论文第 631 行：共同漏点的所有 `p` 个素数平移仍不被 `p` 倍速覆盖。 -/
theorem divisible_uncovered_grid (p v : ℕ) [NeZero p] (δ : ℝ)
    (t₀ : UnitAddCircle) (a : ZMod p) (hpv : p ∣ v)
    (h : t₀ ∉ bohrSet v δ) :
    t₀ + ZMod.toAddCircle a ∉ bohrSet v δ := by
  simpa only [bohrSet, Set.mem_ofPred_eq, smul_add, divisible_smul_grid p v a hpv,
    add_zero] using h

/-- 论文第 631 行：速度 `v` 将平移网格映为以 `v • t₀` 为基点的网格。 -/
theorem smul_grid_point (p v : ℕ) [NeZero p] (t₀ : UnitAddCircle) (a : ZMod p) :
    v • (t₀ + ZMod.toAddCircle a) =
      v • t₀ + ZMod.toAddCircle ((v : ZMod p) * a) := by
  rw [smul_add, ← map_nsmul ZMod.toAddCircle v a, nsmul_eq_mul]

/-- 论文第 631–632 行：一个速度在 `p` 个平移时刻中覆盖的指标集合。 -/
noncomputable def coveredGridResidues (p v : ℕ) [NeZero p]
    (t₀ : UnitAddCircle) (δ : ℝ) : Finset (ZMod p) := by
  classical
  exact Finset.univ.filter fun a => t₀ + ZMod.toAddCircle a ∈ bohrSet v δ

/-- 论文第 631 行：若 `p ∤ v`，乘以 `v` 置换全部 `p` 个网格点。 -/
theorem nondivisible_grid_permutation (p v : ℕ) (hp : p.Prime) (hnp : ¬ p ∣ v) :
    Function.Bijective (fun a : ZMod p => (v : ZMod p) * a) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hv : (v : ZMod p) ≠ 0 := by
    intro h
    exact hnp ((ZMod.natCast_eq_zero_iff v p).1 h)
  constructor
  · intro a b hab
    exact mul_left_cancel₀ hv hab
  · intro b
    refine ⟨(v : ZMod p)⁻¹ * b, ?_⟩
    simp [hv]

/-- 论文第 631–632 行：未被 `p` 整除的速度的覆盖数等于已证圆周网格计数。 -/
theorem coveredGrid_card_eq_circleGrid (p v : ℕ) [NeZero p] (hp : p.Prime)
    (hnp : ¬ p ∣ v) (t₀ : UnitAddCircle) (δ : ℝ) :
    (coveredGridResidues p v t₀ δ).card =
      (circleGridResidues p (v • t₀) (-δ) (2 * δ)).card := by
  classical
  obtain ⟨hinj, hsurj⟩ := nondivisible_grid_permutation p v hp hnp
  refine Finset.card_bij (fun a _ => (v : ZMod p) * a) ?_ ?_ ?_
  · intro a ha
    change a ∈ Finset.univ.filter (fun a : ZMod p =>
      t₀ + ZMod.toAddCircle a ∈ bohrSet v δ) at ha
    change (v : ZMod p) * a ∈ Finset.univ.filter (fun b : ZMod p =>
      v • t₀ + ZMod.toAddCircle b ∈ closedArc (-δ) (2 * δ))
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, bohrSet,
      Set.mem_ofPred_eq, smul_grid_point] using ha
  · intro a _ b _ hab
    exact hinj hab
  · intro b hb
    obtain ⟨a, rfl⟩ := hsurj b
    refine ⟨a, ?_, rfl⟩
    change (v : ZMod p) * a ∈ Finset.univ.filter (fun b : ZMod p =>
      v • t₀ + ZMod.toAddCircle b ∈ closedArc (-δ) (2 * δ)) at hb
    change a ∈ Finset.univ.filter (fun a : ZMod p =>
      t₀ + ZMod.toAddCircle a ∈ bohrSet v δ)
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, bohrSet,
      Set.mem_ofPred_eq, smul_grid_point] using hb

/-- 论文第 632 行：每个未被 `p` 整除的速度至多覆盖 `2δp+1` 个平移点。 -/
theorem coveredGrid_card_le (p v : ℕ) [NeZero p] (hp : p.Prime) (hnp : ¬ p ∣ v)
    (t₀ : UnitAddCircle) (δ : ℝ) (hδ0 : 0 < δ) (hδhalf : δ < 1 / 2) :
    ((coveredGridResidues p v t₀ δ).card : ℝ) ≤ (p : ℝ) * (2 * δ) + 1 := by
  rw [coveredGrid_card_eq_circleGrid p v hp hnp]
  rw [← circleGridIndices_card_eq_residues p]
  exact (circleGridIndices_count p hp.pos (v • t₀) (-δ) (2 * δ)
    (by linarith) (by linarith)).2

/-- 论文第 632 行所用有限覆盖计数：覆盖 `S` 的各子集大小之和至少为 `|S|`。 -/
theorem card_le_sum_filter_card {α β : Type*}
    (S : Finset α) (T : Finset β) (P : β → α → Prop) [DecidableRel P]
    (hcover : ∀ a ∈ S, ∃ b ∈ T, P b a) :
    S.card ≤ ∑ b ∈ T, (S.filter (P b)).card := by
  classical
  have hsub : S ⊆ T.biUnion (fun b => S.filter (P b)) := by
    intro a ha
    obtain ⟨b, hb, hp⟩ := hcover a ha
    exact Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_filter.mpr ⟨ha, hp⟩⟩
  exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le

/-- 论文第 630–632 行，式 `eq:prime` 的网格覆盖步骤。设 `m=|V|`，
`0<δ<1/2`，`V` 为有限正整数速度集，其闭 Bohr 覆盖不可约且 `gcd(V)=1`。
`C⊆V`、`|C|≥m/2`、`G>0`、`G∣v` 对所有 `v∈C` 成立。则每个素数
`p∣G` 的非整除速度数 `r_p` 满足 `r_p(2δ+1/p)≥1`。 -/
theorem prime_grid_cover_bound (V C : Finset ℕ) (m G p : ℕ) (δ : ℝ)
    (_hm : m = V.card) (_hVpos : ∀ v ∈ V, 0 < v)
    (hδ0 : 0 < δ) (hδhalf : δ < 1 / 2)
    (hirr : IrreducibleCover V δ) (hgcd : V.gcd id = 1)
    (_hCV : C ⊆ V) (_hCcard : (m : ℝ) / 2 ≤ (C.card : ℝ))
    (_hGpos : 0 < G) (_hGdiv : ∀ v ∈ C, G ∣ v)
    (hp : p.Prime) (_hpG : p ∣ G) :
    (1 : ℝ) ≤ (nondivisibleCount V p : ℝ) * (2 * δ + 1 / (p : ℝ)) := by
  classical
  letI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨t₀, ht₀⟩ := exists_uncovered_divisible V δ p hp hgcd hirr
  let T : Finset ℕ := V.filter (fun v => ¬ p ∣ v)
  have hcover : ∀ a ∈ (Finset.univ : Finset (ZMod p)),
      ∃ v ∈ T, a ∈ coveredGridResidues p v t₀ δ := by
    intro a _
    obtain ⟨v, hv, hbohr⟩ := hirr.1 (t₀ + ZMod.toAddCircle a)
    have hnp : ¬ p ∣ v := by
      intro hpv
      exact (divisible_uncovered_grid p v δ t₀ a hpv (ht₀ v hv hpv)) hbohr
    refine ⟨v, Finset.mem_filter.mpr ⟨hv, hnp⟩, ?_⟩
    simp only [coveredGridResidues, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hbohr
  have hcard : p ≤ ∑ v ∈ T, (coveredGridResidues p v t₀ δ).card := by
    simpa using card_le_sum_filter_card (Finset.univ : Finset (ZMod p)) T
      (fun v a => a ∈ coveredGridResidues p v t₀ δ) hcover
  have hreal : (p : ℝ) ≤ ∑ v ∈ T, ((coveredGridResidues p v t₀ δ).card : ℝ) := by
    exact_mod_cast hcard
  have hbound : (p : ℝ) ≤
      (nondivisibleCount V p : ℝ) * ((p : ℝ) * (2 * δ) + 1) := by
    calc
      (p : ℝ) ≤ ∑ v ∈ T, ((coveredGridResidues p v t₀ δ).card : ℝ) := hreal
      _ ≤ ∑ v ∈ T, ((p : ℝ) * (2 * δ) + 1) := by
        apply Finset.sum_le_sum
        intro v hv
        exact coveredGrid_card_le p v hp (Finset.mem_filter.mp hv).2 t₀ δ hδ0 hδhalf
      _ = (nondivisibleCount V p : ℝ) * ((p : ℝ) * (2 * δ) + 1) := by
        simp only [Finset.sum_const, nsmul_eq_mul, T, nondivisibleCount]
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have heq : (nondivisibleCount V p : ℝ) * ((p : ℝ) * (2 * δ) + 1) =
      (p : ℝ) * ((nondivisibleCount V p : ℝ) * (2 * δ + 1 / (p : ℝ))) := by
    field_simp
  rw [heq] at hbound
  have hdiv : (p : ℝ) / (p : ℝ) ≤
      (nondivisibleCount V p : ℝ) * (2 * δ + 1 / (p : ℝ)) :=
    (div_le_iff₀ hpR).mpr (by simpa only [mul_comm] using hbound)
  simpa [div_self hpR.ne'] using hdiv

end LonelyRunner

#print axioms LonelyRunner.prime_grid_cover_bound
