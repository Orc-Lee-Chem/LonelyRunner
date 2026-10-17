import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Int.Interval
import Mathlib.Topology.Instances.AddCircle.Real

namespace LonelyRunner

/-- 实轴闭区间 `[u, v]` 中的整数集合。
论文位置：`paper/lonely_runner_zh.tex` 第 577 行，引理 `lem:gridcount` 的实轴计数步骤。 -/
noncomputable def integerPoints (u v : ℝ) : Finset ℤ := Finset.Icc ⌈u⌉ ⌊v⌋

/-- 整数 `n` 被计入，恰当且仅当它属于闭区间 `[u, v]`；两个端点都包含。
论文位置：`paper/lonely_runner_zh.tex` 第 577 行。 -/
theorem mem_integerPoints_iff (u v : ℝ) (n : ℤ) :
    n ∈ integerPoints u v ↔ u ≤ (n : ℝ) ∧ (n : ℝ) ≤ v := by
  simp only [integerPoints, Finset.mem_Icc, Int.ceil_le, Int.le_floor]

/-- 长度为 `v - u ≥ 0` 的实轴闭区间中，整数个数与区间长度之差至多为一。
论文位置：`paper/lonely_runner_zh.tex` 第 577 行，引理 `lem:gridcount` 的整数计数步骤。 -/
theorem integerPoints_count (u v : ℝ) (huv : u ≤ v) :
    v - u - 1 ≤ (integerPoints u v).card ∧
      ((integerPoints u v).card : ℝ) ≤ v - u + 1 := by
  have hceil : ⌈u⌉ ≤ ⌊v⌋ + 1 :=
    (Int.ceil_mono huv).trans (Int.ceil_le_floor_add_one v)
  have hcardZ : ((integerPoints u v).card : ℤ) = ⌊v⌋ + 1 - ⌈u⌉ := by
    exact Int.card_Icc_of_le _ _ hceil
  have hcard : ((integerPoints u v).card : ℝ) = (⌊v⌋ : ℝ) + 1 - (⌈u⌉ : ℝ) := by
    exact_mod_cast hcardZ
  have hfloor_lo : v - 1 < (⌊v⌋ : ℝ) := Int.sub_one_lt_floor v
  have hfloor_hi : (⌊v⌋ : ℝ) ≤ v := Int.floor_le v
  have hceil_lo : u ≤ (⌈u⌉ : ℝ) := Int.le_ceil u
  have hceil_hi : (⌈u⌉ : ℝ) < u + 1 := Int.ceil_lt_add_one u
  constructor <;> rw [hcard] <;> linarith

/-- 实轴中落入闭区间 `[s, s + ℓ]` 的 `y + n/q` 型网格点所对应的整数指标。
论文位置：`paper/lonely_runner_zh.tex` 第 577 行，引理 `lem:gridcount` 的提升步骤。 -/
noncomputable def realGridIndices (q : ℕ) (y s ℓ : ℝ) : Finset ℤ :=
  integerPoints ((q : ℝ) * (s - y)) ((q : ℝ) * (s + ℓ - y))

/-- 实轴闭区间中的间距 `1/q` 网格计数满足论文所需的 `qℓ ± 1` 界。
论文位置：`paper/lonely_runner_zh.tex` 第 577 行，引理 `lem:gridcount` 的实轴步骤。 -/
theorem realGridIndices_count (q : ℕ) (hq : 0 < q) (y s ℓ : ℝ) (hℓ : 0 ≤ ℓ) :
    (q : ℝ) * ℓ - 1 ≤ (realGridIndices q y s ℓ).card ∧
      ((realGridIndices q y s ℓ).card : ℝ) ≤ (q : ℝ) * ℓ + 1 := by
  have hqR : (0 : ℝ) ≤ q := (Nat.cast_pos.mpr hq).le
  have huv : (q : ℝ) * (s - y) ≤ (q : ℝ) * (s + ℓ - y) := by
    nlinarith [mul_nonneg hqR hℓ]
  have h := integerPoints_count _ _ huv
  dsimp [realGridIndices]
  convert h using 1 <;> ring_nf

/-- 实轴网格指标与闭区间成员关系的精确等价，包含两个端点。
论文位置：`paper/lonely_runner_zh.tex` 第 577 行，引理 `lem:gridcount` 的伸缩步骤。 -/
theorem mem_realGridIndices_iff (q : ℕ) (hq : 0 < q) (y s ℓ : ℝ) (n : ℤ) :
    n ∈ realGridIndices q y s ℓ ↔
      y + (n : ℝ) / (q : ℝ) ∈ Set.Icc s (s + ℓ) := by
  rw [realGridIndices, mem_integerPoints_iff]
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  constructor
  · rintro ⟨ha, hb⟩
    constructor
    · have hc : s - y ≤ (n : ℝ) / q :=
        (le_div_iff₀ hqR).mpr (by nlinarith [ha])
      linarith
    · have hc : (n : ℝ) / q ≤ s + ℓ - y :=
        (div_le_iff₀ hqR).mpr (by nlinarith [hb])
      linarith
  · rintro ⟨ha, hb⟩
    constructor
    · have hc : (s - y) * q ≤ (n : ℝ) :=
        (le_div_iff₀ hqR).mp (by linarith [ha])
      nlinarith
    · have hc : (n : ℝ) ≤ (s + ℓ - y) * q :=
        (div_le_iff₀ hqR).mp (by linarith [hb])
      nlinarith

/-- 从实轴闭区间 `[s, s + ℓ]` 投影得到的闭圆周弧；端点均计入。
论文位置：`paper/lonely_runner_zh.tex` 第 570–577 行，引理 `lem:gridcount`。 -/
def closedArc (s ℓ : ℝ) : Set UnitAddCircle :=
  (fun t : ℝ => (t : UnitAddCircle)) '' Set.Icc s (s + ℓ)

/-- 集合 `J` 是长度为 `ℓ` 的闭圆周区间：它是某个实轴闭区间
`[s, s + ℓ]` 在 `ℝ / ℤ` 中的像。
论文位置：`paper/lonely_runner_zh.tex` 第 570–577 行，引理 `lem:gridcount` 的区间定义。 -/
def IsClosedArcOfLength (J : Set UnitAddCircle) (ℓ : ℝ) : Prop :=
  ∃ s : ℝ, J = closedArc s ℓ

/-- 长度严格小于一的闭弧在实轴上的提升是单射，因此两个端点不会被重复计数。
论文位置：`paper/lonely_runner_zh.tex` 第 577 行，引理 `lem:gridcount` 的提升步骤。 -/
theorem closedArc_lift_injective (s ℓ : ℝ) (hℓ : ℓ < 1) :
    Set.InjOn (fun t : ℝ => (t : UnitAddCircle)) (Set.Icc s (s + ℓ)) := by
  intro a ha b hb hab
  have ha' : a ∈ Set.Ico s (s + 1) := by
    constructor
    · exact ha.1
    · linarith [ha.2]
  have hb' : b ∈ Set.Ico s (s + 1) := by
    constructor
    · exact hb.1
    · linarith [hb.2]
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico ha' hb').mp hab

/-- 两个实数给出同一个单位圆周点，当且仅当它们相差整数。
论文位置：`paper/lonely_runner_zh.tex` 第 577 行，圆周提升与整数平移的对应。 -/
theorem mk_eq_mk_iff_int_diff (u v : ℝ) :
    (u : UnitAddCircle) = (v : UnitAddCircle) ↔
      ∃ k : ℤ, u - v = (k : ℝ) := by
  rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
  simp only [zsmul_eq_mul, mul_one, eq_comm]

/-- 整数指标经过 `ZMod q` 后给出同一个圆周网格点。
论文位置：`paper/lonely_runner_zh.tex` 第 577 行，模 `q` 的网格对应。 -/
theorem circlePoint_intCast (q : ℕ) [NeZero q] (y : ℝ) (n : ℤ) :
    (y : UnitAddCircle) + ZMod.toAddCircle (n : ZMod q) =
      ((y + (n : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle) := by
  calc
    (y : UnitAddCircle) + ZMod.toAddCircle (n : ZMod q) =
        (y : UnitAddCircle) + (((n : ℝ) / (q : ℝ)) : UnitAddCircle) := by
          rw [ZMod.toAddCircle_intCast]
    _ = ((y + (n : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle) :=
      (AddCircle.coe_add (1 : ℝ) y ((n : ℝ) / (q : ℝ))).symm

/-- 给定圆周网格余数和圆周上的实轴提升，可以选出同余于该余数的整数指标。
论文位置：`paper/lonely_runner_zh.tex` 第 577 行，引理 `lem:gridcount` 的提升步骤。 -/
theorem exists_integer_lift (q : ℕ) [NeZero q] (y t : ℝ) (a : ZMod q)
    (heq : (t : UnitAddCircle) = (y : UnitAddCircle) + ZMod.toAddCircle a) :
    ∃ n : ℤ, (n : ZMod q) = a ∧ y + (n : ℝ) / (q : ℝ) = t := by
  have ha : ((a.val : ℕ) : ZMod q) = a := ZMod.natCast_zmod_val a
  have heq' : (t : UnitAddCircle) =
      ((y + (a.val : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle) := by
    calc
      (t : UnitAddCircle) = (y : UnitAddCircle) + ZMod.toAddCircle a := heq
      _ = (y : UnitAddCircle) + ZMod.toAddCircle ((a.val : ℕ) : ZMod q) := by rw [ha]
      _ = ((y + (a.val : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle) := by
        simpa using circlePoint_intCast q y (a.val : ℤ)
  obtain ⟨k, hk⟩ := (mk_eq_mk_iff_int_diff t (y + (a.val : ℝ) / (q : ℝ))).mp heq'
  refine ⟨(a.val : ℤ) + k * (q : ℤ), ?_, ?_⟩
  · simp
  · have hq : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
    have hdiv : (((a.val : ℤ) + k * (q : ℤ) : ℤ) : ℝ) / (q : ℝ) =
        (a.val : ℝ) / (q : ℝ) + (k : ℝ) := by
      push_cast
      field_simp
    rw [hdiv]
    linarith

/-- 用 `ZMod q` 表示同一个 `q` 点圆周网格，以便证明提升与余数的双射。
论文位置：`paper/lonely_runner_zh.tex` 第 570–577 行，引理 `lem:gridcount`。 -/
noncomputable def circleGridResidues (q : ℕ) [NeZero q] (x : UnitAddCircle)
    (s ℓ : ℝ) : Finset (ZMod q) := by
  classical
  exact Finset.univ.filter fun a => x + ZMod.toAddCircle a ∈ closedArc s ℓ

/-- 实轴闭弧中的整数提升与圆周网格余数一一对应。
论文位置：`paper/lonely_runner_zh.tex` 第 577 行，引理 `lem:gridcount` 的核心对应。 -/
theorem realGrid_card_eq_circleGridResidues (q : ℕ) [NeZero q] (hq : 0 < q)
    (y s ℓ : ℝ) (hℓ : ℓ < 1) :
    (realGridIndices q y s ℓ).card =
      (circleGridResidues q (y : UnitAddCircle) s ℓ).card := by
  classical
  refine Finset.card_bij (fun n _ => (n : ZMod q)) ?_ ?_ ?_
  · intro n hn
    have ht : y + (n : ℝ) / (q : ℝ) ∈ Set.Icc s (s + ℓ) :=
      (mem_realGridIndices_iff q hq y s ℓ n).mp hn
    change (n : ZMod q) ∈ Finset.univ.filter
      (fun a => (y : UnitAddCircle) + ZMod.toAddCircle a ∈ closedArc s ℓ)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨y + (n : ℝ) / (q : ℝ), ht, (circlePoint_intCast q y n).symm⟩
  · intro n hn m hm heq
    have hn' := (mem_realGridIndices_iff q hq y s ℓ n).mp hn
    have hm' := (mem_realGridIndices_iff q hq y s ℓ m).mp hm
    have hc : ((y + (n : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle) =
        ((y + (m : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle) := by
      calc
        _ = (y : UnitAddCircle) + ZMod.toAddCircle (n : ZMod q) :=
          (circlePoint_intCast q y n).symm
        _ = (y : UnitAddCircle) + ZMod.toAddCircle (m : ZMod q) := by rw [heq]
        _ = _ := circlePoint_intCast q y m
    have hr := (closedArc_lift_injective s ℓ hℓ) hn' hm' hc
    have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
    have hdiv : (n : ℝ) / (q : ℝ) = (m : ℝ) / (q : ℝ) := by linarith
    exact_mod_cast (div_left_inj' hqR).mp hdiv
  · intro a ha
    have hmem : (y : UnitAddCircle) + ZMod.toAddCircle a ∈ closedArc s ℓ := by
      simpa only [circleGridResidues, Finset.mem_filter, Finset.mem_univ, true_and] using ha
    obtain ⟨t, ht, htEq⟩ := hmem
    obtain ⟨n, hres, hn⟩ := exists_integer_lift q y t a htEq
    refine ⟨n, ?_, hres⟩
    exact (mem_realGridIndices_iff q hq y s ℓ n).mpr (hn ▸ ht)

/-- 论文中的圆周网格区间计数的精确有限集合定义，指标为 `0 ≤ a < q`。
论文位置：`paper/lonely_runner_zh.tex` 第 570–574 行，引理 `lem:gridcount`。 -/
noncomputable def circleGridIndices (q : ℕ) (x : UnitAddCircle) (s ℓ : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range q).filter fun a =>
    x + (((a : ℝ) / (q : ℝ)) : UnitAddCircle) ∈ closedArc s ℓ

/-- 对任意圆周集合 `J`，计数 `0 ≤ a < q` 且 `x + a/q ∈ J` 的指标。
论文位置：`paper/lonely_runner_zh.tex` 第 573 行，引理 `lem:gridcount`。 -/
noncomputable def circleGridIndicesIn (q : ℕ) (x : UnitAddCircle)
    (J : Set UnitAddCircle) : Finset ℕ := by
  classical
  exact (Finset.range q).filter fun a =>
    x + (((a : ℝ) / (q : ℝ)) : UnitAddCircle) ∈ J

/-- `ZMod q` 的规范代表恰是论文中的整数集合 `0 ≤ a < q`，且两种计数相同。
论文位置：`paper/lonely_runner_zh.tex` 第 573 行，引理 `lem:gridcount`。 -/
theorem circleGridIndices_card_eq_residues (q : ℕ) [NeZero q]
    (x : UnitAddCircle) (s ℓ : ℝ) :
    (circleGridIndices q x s ℓ).card = (circleGridResidues q x s ℓ).card := by
  classical
  refine Finset.card_bij (fun a _ => (a : ZMod q)) ?_ ?_ ?_
  · intro a ha
    change a ∈ (Finset.range q).filter
      (fun a : ℕ => x + (((a : ℝ) / (q : ℝ)) : UnitAddCircle) ∈ closedArc s ℓ) at ha
    change (a : ZMod q) ∈ Finset.univ.filter
      (fun b => x + ZMod.toAddCircle b ∈ closedArc s ℓ)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simpa only [ZMod.toAddCircle_natCast] using (Finset.mem_filter.mp ha).2
  · intro a ha b hb heq
    have ha' : a < q := by
      change a ∈ (Finset.range q).filter
        (fun a : ℕ => x + (((a : ℝ) / (q : ℝ)) : UnitAddCircle) ∈ closedArc s ℓ) at ha
      exact Finset.mem_range.mp (Finset.mem_filter.mp ha).1
    have hb' : b < q := by
      change b ∈ (Finset.range q).filter
        (fun b : ℕ => x + (((b : ℝ) / (q : ℝ)) : UnitAddCircle) ∈ closedArc s ℓ) at hb
      exact Finset.mem_range.mp (Finset.mem_filter.mp hb).1
    calc
      a = (a : ZMod q).val := (ZMod.val_natCast_of_lt ha').symm
      _ = (b : ZMod q).val := congrArg ZMod.val heq
      _ = b := ZMod.val_natCast_of_lt hb'
  · intro b hb
    have hb' : x + ZMod.toAddCircle b ∈ closedArc s ℓ := by
      simpa only [circleGridResidues, Finset.mem_filter, Finset.mem_univ, true_and] using hb
    refine ⟨b.val, ?_, ZMod.natCast_zmod_val b⟩
    change b.val ∈ (Finset.range q).filter
      (fun a : ℕ => x + (((a : ℝ) / (q : ℝ)) : UnitAddCircle) ∈ closedArc s ℓ)
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨ZMod.val_lt b, by simpa only [ZMod.toAddCircle_apply] using hb'⟩

/-- 圆周网格的闭区间计数：`qℓ - 1 ≤ N ≤ qℓ + 1`，其中 `N` 精确计数
`0 ≤ a < q` 且 `x + a/q` 落在闭弧 `[s, s + ℓ]` 的指标。
论文位置：`paper/lonely_runner_zh.tex` 第 570–577 行，引理 `lem:gridcount`。 -/
theorem circleGridIndices_count (q : ℕ) (hq : 0 < q) (x : UnitAddCircle)
    (s ℓ : ℝ) (hℓ0 : 0 ≤ ℓ) (hℓ1 : ℓ < 1) :
    (q : ℝ) * ℓ - 1 ≤ (circleGridIndices q x s ℓ).card ∧
      ((circleGridIndices q x s ℓ).card : ℝ) ≤ (q : ℝ) * ℓ + 1 := by
  classical
  haveI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [circleGridIndices_card_eq_residues q]
  rw [← realGrid_card_eq_circleGridResidues q hq y s ℓ hℓ1]
  exact realGridIndices_count q hq y s ℓ hℓ0

/-- 论文引理 `lem:gridcount`：对任意正整数 `q`、圆周点 `x`，以及长度
`0 ≤ ℓ < 1` 的闭圆周区间 `J`，计数误差不超过一；闭端点被计入。
论文位置：`paper/lonely_runner_zh.tex` 第 570–577 行，式 `eq:gridcount`。 -/
theorem circleGridInterval_count (q : ℕ) (hq : 0 < q) (x : UnitAddCircle)
    (J : Set UnitAddCircle) (ℓ : ℝ) (hℓ0 : 0 ≤ ℓ) (hℓ1 : ℓ < 1)
    (hJ : IsClosedArcOfLength J ℓ) :
    (q : ℝ) * ℓ - 1 ≤ (circleGridIndicesIn q x J).card ∧
      ((circleGridIndicesIn q x J).card : ℝ) ≤ (q : ℝ) * ℓ + 1 := by
  obtain ⟨s, rfl⟩ := hJ
  have hEq : circleGridIndicesIn q x (closedArc s ℓ) = circleGridIndices q x s ℓ := by
    rfl
  rw [hEq]
  exact circleGridIndices_count q hq x s ℓ hℓ0 hℓ1

end LonelyRunner

#print axioms LonelyRunner.integerPoints_count
#print axioms LonelyRunner.circleGridInterval_count
