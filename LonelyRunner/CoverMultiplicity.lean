import LonelyRunner.CircleMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! 论文 `paper/lonely_runner_zh.tex` 第 428–435 行：Bohr 覆盖重数及重复覆盖误差。 -/

namespace LonelyRunner

open MeasureTheory

/-- 论文第 428 行：原有闭 Bohr 集的实数值指示函数。 -/
noncomputable def bohrIndicator (v : ℕ) (δ : ℝ) (t : UnitAddCircle) : ℝ :=
  (bohrSet v δ).indicator 1 t

/-- 论文第 428 行：子族 `W` 的逐点实数值覆盖重数 `Y_W`。
取 `W=V` 时即为全族重数 `X`。 -/
noncomputable def coverMultiplicity (W : Finset ℕ) (δ : ℝ)
    (t : UnitAddCircle) : ℝ := ∑ v ∈ W, bohrIndicator v δ t

/-- 论文第 429 行：子族的重复覆盖误差 `e_W=∫max(Y_W-1,0)`。 -/
noncomputable def coverExcess (W : Finset ℕ) (δ : ℝ) : ℝ :=
  ∫ t, max (coverMultiplicity W δ t - 1) 0 ∂circleHaar

/-- 论文第 432 行：子族 Bohr 集的有限并。 -/
def bohrUnion (W : Finset ℕ) (δ : ℝ) : Set UnitAddCircle :=
  ⋃ v ∈ W, bohrSet v δ

/-- 论文第 428 行：在点 `t` 覆盖它的速度有限集。 -/
noncomputable def bohrHits (W : Finset ℕ) (δ : ℝ) (t : UnitAddCircle) : Finset ℕ := by
  classical
  exact W.filter (fun v => t ∈ bohrSet v δ)

/-- 论文第 428 行：一个 Bohr 集的实数指示函数可测且可积。 -/
theorem bohrIndicator_measurable_integrable (v : ℕ) (δ : ℝ)
    (hv : 0 < v) (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    Measurable (bohrIndicator v δ) ∧
      Integrable (bohrIndicator v δ) circleHaar := by
  have hs := (bohrSet_measurable_measure v δ hv hδ hδhalf).1
  constructor
  · exact measurable_const.indicator hs
  · exact (integrable_const 1).indicator hs

/-- 论文第 428 行：`Y_W` 可测且可积；也适用于全族重数 `X`。 -/
theorem coverMultiplicity_measurable_integrable (W : Finset ℕ) (δ : ℝ)
    (hWpos : ∀ v ∈ W, 0 < v) (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    Measurable (coverMultiplicity W δ) ∧
      Integrable (coverMultiplicity W δ) circleHaar := by
  constructor
  · exact Finset.measurable_sum W (fun v hv =>
      (bohrIndicator_measurable_integrable v δ (hWpos v hv) hδ hδhalf).1)
  · exact integrable_finsetSum W (fun v hv =>
      (bohrIndicator_measurable_integrable v δ (hWpos v hv) hδ hδhalf).2)

/-- 论文第 428 行：一个 Bohr 指示函数的积分是 `2δ`。 -/
theorem integral_bohrIndicator (v : ℕ) (δ : ℝ)
    (hv : 0 < v) (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    ∫ t, bohrIndicator v δ t ∂circleHaar = 2 * δ := by
  have hs := bohrSet_measurable_measure v δ hv hδ hδhalf
  have hi : (∫ t, bohrIndicator v δ t ∂circleHaar) =
      circleHaar.real (bohrSet v δ) := by
    simpa [bohrIndicator] using (integral_indicator_one (μ := circleHaar) hs.1)
  rw [hi]
  rw [Measure.real, hs.2, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * δ)]

/-- 论文第 428、432 行：任意正速度子族的重数积分为 `2δ|W|`。 -/
theorem integral_coverMultiplicity (W : Finset ℕ) (δ : ℝ)
    (hWpos : ∀ v ∈ W, 0 < v) (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    ∫ t, coverMultiplicity W δ t ∂circleHaar = 2 * δ * (W.card : ℝ) := by
  change (∫ t, ∑ v ∈ W, bohrIndicator v δ t ∂circleHaar) = _
  rw [integral_finsetSum W (fun v hv =>
    (bohrIndicator_measurable_integrable v δ (hWpos v hv) hδ hδhalf).2)]
  have hterm : (∑ v ∈ W, ∫ t, bohrIndicator v δ t ∂circleHaar) =
      ∑ _v ∈ W, 2 * δ := by
    apply Finset.sum_congr rfl
    intro v hv
    exact integral_bohrIndicator v δ (hWpos v hv) hδ hδhalf
  rw [hterm]
  simp [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- 论文第 428 行：实数值覆盖重数逐点等于命中的速度个数。 -/
theorem coverMultiplicity_eq_card_filter (W : Finset ℕ) (δ : ℝ)
    (t : UnitAddCircle) :
    coverMultiplicity W δ t = ((bohrHits W δ t).card : ℝ) := by
  classical
  unfold bohrHits
  simp only [coverMultiplicity, bohrIndicator, Set.indicator_apply, Pi.one_apply]
  exact Finset.sum_boole (fun v => t ∈ bohrSet v δ) W

/-- 论文第 74–83、428 行：覆盖是逐点条件，等价于每个点的实数重数至少为 1。 -/
theorem covers_iff_coverMultiplicity_ge_one (V : Finset ℕ) (δ : ℝ) :
    Covers V δ ↔ ∀ t : UnitAddCircle, 1 ≤ coverMultiplicity V δ t := by
  classical
  constructor
  · intro h t
    obtain ⟨v, hv, hvt⟩ := h t
    rw [coverMultiplicity_eq_card_filter]
    have hcard : 0 < (bohrHits V δ t).card :=
      Finset.card_pos.mpr ⟨v, by simp [bohrHits, hv, hvt]⟩
    exact_mod_cast hcard
  · intro h t
    have ht := h t
    rw [coverMultiplicity_eq_card_filter] at ht
    have hcard : 0 < (bohrHits V δ t).card := by
      exact_mod_cast ht
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hcard
    have hv' : v ∈ V ∧ t ∈ bohrSet v δ := by simpa [bohrHits] using hv
    exact ⟨v, hv'.1, hv'.2⟩

/-- 论文第 429 行：重复覆盖误差的被积函数可积。 -/
theorem coverExcess_integrable (W : Finset ℕ) (δ : ℝ)
    (hWpos : ∀ v ∈ W, 0 < v) (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    Integrable (fun t => max (coverMultiplicity W δ t - 1) 0) circleHaar := by
  have hY := (coverMultiplicity_measurable_integrable W δ hWpos hδ hδhalf).2
  exact (hY.sub (integrable_const 1)).sup (integrable_const 0)

/-- 论文第 432 行：有限 Bohr 并可测。 -/
theorem bohrUnion_measurable (W : Finset ℕ) (δ : ℝ)
    (hWpos : ∀ v ∈ W, 0 < v) (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    MeasurableSet (bohrUnion W δ) := by
  unfold bohrUnion
  exact Finset.measurableSet_biUnion W (fun v hv =>
    (bohrSet_measurable_measure v δ (hWpos v hv) hδ hδhalf).1)

/-- 论文第 432 行：一个点属于有限并，当且仅当至少一个速度命中它。 -/
theorem mem_bohrUnion_iff_hits_pos (W : Finset ℕ) (δ : ℝ) (t : UnitAddCircle) :
    t ∈ bohrUnion W δ ↔ 0 < (bohrHits W δ t).card := by
  classical
  constructor
  · intro h
    obtain ⟨v, hv, hvt⟩ : ∃ v ∈ W, t ∈ bohrSet v δ := by
      simpa [bohrUnion] using h
    exact Finset.card_pos.mpr ⟨v, by simp [bohrHits, hv, hvt]⟩
  · intro h
    obtain ⟨v, hv⟩ := Finset.card_pos.mp h
    have hv' : v ∈ W ∧ t ∈ bohrSet v δ := by simpa [bohrHits] using hv
    simp only [bohrUnion, Set.mem_iUnion]
    exact ⟨v, hv'.1, hv'.2⟩

/-- 论文第 432 行：逐点有限计数恒等式
`Y_W=(Y_W-1)_+ + 1_{⋃_{v∈W}B_v}`。 -/
theorem coverMultiplicity_eq_excess_add_unionIndicator
    (W : Finset ℕ) (δ : ℝ) (t : UnitAddCircle) :
    coverMultiplicity W δ t =
      max (coverMultiplicity W δ t - 1) 0 +
        (bohrUnion W δ).indicator (1 : UnitAddCircle → ℝ) t := by
  rw [coverMultiplicity_eq_card_filter]
  by_cases hhit : 0 < (bohrHits W δ t).card
  · have hmem : t ∈ bohrUnion W δ :=
      (mem_bohrUnion_iff_hits_pos W δ t).2 hhit
    simp only [Set.indicator_of_mem hmem, Pi.one_apply]
    have hcast : (1 : ℝ) ≤ ((bohrHits W δ t).card : ℝ) := by exact_mod_cast hhit
    rw [max_eq_left (by linarith : 0 ≤ ((bohrHits W δ t).card : ℝ) - 1)]
    ring
  · have hzero : (bohrHits W δ t).card = 0 := Nat.eq_zero_of_not_pos hhit
    have hnot : t ∉ bohrUnion W δ := by
      intro hmem
      exact hhit ((mem_bohrUnion_iff_hits_pos W δ t).1 hmem)
    simp only [Set.indicator_of_notMem hnot, hzero, Nat.cast_zero]
    norm_num

/-- 论文第 432 行：有限 Bohr 并的实数测度为重数积分减去重复覆盖误差。 -/
theorem bohrUnion_measureReal_eq_integral_sub_excess
    (W : Finset ℕ) (δ : ℝ)
    (hWpos : ∀ v ∈ W, 0 < v) (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    circleHaar.real (bohrUnion W δ) =
      2 * δ * (W.card : ℝ) - coverExcess W δ := by
  have hYint := (coverMultiplicity_measurable_integrable W δ hWpos hδ hδhalf).2
  have hEint := coverExcess_integrable W δ hWpos hδ hδhalf
  have hUint : Integrable (fun t =>
      (bohrUnion W δ).indicator (1 : UnitAddCircle → ℝ) t) circleHaar :=
    (integrable_const (1 : ℝ)).indicator (bohrUnion_measurable W δ hWpos hδ hδhalf)
  have hsum : (∫ t, coverMultiplicity W δ t ∂circleHaar) =
      coverExcess W δ + circleHaar.real (bohrUnion W δ) := by
    calc
      _ = ∫ t, (max (coverMultiplicity W δ t - 1) 0 +
            (bohrUnion W δ).indicator (1 : UnitAddCircle → ℝ) t) ∂circleHaar := by
        congr 1
        funext t
        exact coverMultiplicity_eq_excess_add_unionIndicator W δ t
      _ = coverExcess W δ + circleHaar.real (bohrUnion W δ) := by
        rw [integral_add hEint hUint, coverExcess,
          integral_indicator_one (bohrUnion_measurable W δ hWpos hδ hδhalf)]
  rw [integral_coverMultiplicity W δ hWpos hδ hδhalf] at hsum
  linarith

/-- 论文第 428 行：每个 Bohr 指示函数逐点非负。 -/
theorem bohrIndicator_nonneg (v : ℕ) (δ : ℝ) (t : UnitAddCircle) :
    0 ≤ bohrIndicator v δ t := by
  classical
  simp only [bohrIndicator, Set.indicator_apply]
  split_ifs <;> norm_num

/-- 论文第 428 行：任意子族的重数逐点非负。 -/
theorem coverMultiplicity_nonneg (W : Finset ℕ) (δ : ℝ) (t : UnitAddCircle) :
    0 ≤ coverMultiplicity W δ t := by
  unfold coverMultiplicity
  exact Finset.sum_nonneg (fun v hv => bohrIndicator_nonneg v δ t)

/-- 论文第 433 行：子族重数不超过全族重数。 -/
theorem coverMultiplicity_mono {W V : Finset ℕ} (hWV : W ⊆ V)
    (δ : ℝ) (t : UnitAddCircle) :
    coverMultiplicity W δ t ≤ coverMultiplicity V δ t := by
  unfold coverMultiplicity
  exact Finset.sum_le_sum_of_subset_of_nonneg hWV
    (fun v hv hne => bohrIndicator_nonneg v δ t)

/-- 论文第 433 行的有限算术事实：非负数列的超出 1 的部分之和，
不超过总和超出 1 的部分。 -/
theorem sum_excess_le_excess_sum {ι : Type*} (I : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ I, 0 ≤ f i) :
    (∑ i ∈ I, max (f i - 1) 0) ≤ max ((∑ i ∈ I, f i) - 1) 0 := by
  classical
  have hpair (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
      max (a - 1) 0 + max (b - 1) 0 ≤ max (a + b - 1) 0 := by
    rcases le_total (a - 1) 0 with ha1 | ha1 <;>
      rcases le_total (b - 1) 0 with hb1 | hb1
    · rw [max_eq_right ha1, max_eq_right hb1]
      simp only [zero_add]
      exact le_max_right (a + b - 1) (0 : ℝ)
    · rw [max_eq_right ha1, max_eq_left hb1]
      exact le_max_of_le_left (by linarith)
    · rw [max_eq_left ha1, max_eq_right hb1]
      exact le_max_of_le_left (by linarith)
    · rw [max_eq_left ha1, max_eq_left hb1]
      exact le_max_of_le_left (by linarith)
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i J hi ih =>
      have hfi : 0 ≤ f i := hf i (Finset.mem_insert_self i J)
      have hfJ : ∀ j ∈ J, 0 ≤ f j := by
        intro j hj
        exact hf j (Finset.mem_insert_of_mem hj)
      have hJsum : 0 ≤ ∑ j ∈ J, f j := Finset.sum_nonneg hfJ
      simp only [Finset.sum_insert hi]
      calc
        max (f i - 1) 0 + ∑ j ∈ J, max (f j - 1) 0 ≤
            max (f i - 1) 0 + max ((∑ j ∈ J, f j) - 1) 0 := by
              gcongr
              exact ih hfJ
        _ ≤ max ((f i + ∑ j ∈ J, f j) - 1) 0 :=
          hpair (f i) (∑ j ∈ J, f j) hfi hJsum

/-- 论文第 433 行：逐点全覆盖时，全族重复覆盖误差恰为
`ε=2δ|V|-1`。这里使用 `Covers` 的逐点形式。 -/
theorem coverExcess_eq_epsilon (V : Finset ℕ) (δ : ℝ)
    (hVpos : ∀ v ∈ V, 0 < v) (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hcover : Covers V δ) :
    coverExcess V δ = 2 * δ * (V.card : ℝ) - 1 := by
  have hXint := (coverMultiplicity_measurable_integrable V δ hVpos hδ hδhalf).2
  have hpoint : ∀ t : UnitAddCircle,
      max (coverMultiplicity V δ t - 1) 0 = coverMultiplicity V δ t - 1 := by
    intro t
    exact max_eq_left (sub_nonneg.mpr ((covers_iff_coverMultiplicity_ge_one V δ).1 hcover t))
  unfold coverExcess
  simp_rw [hpoint]
  rw [integral_sub hXint (integrable_const 1),
    integral_coverMultiplicity V δ hVpos hδ hδhalf]
  simp

/-- 论文第 433 行：每个子族的重复覆盖误差不超过全族的 `ε`。 -/
theorem coverExcess_le_epsilon (V W : Finset ℕ) (δ : ℝ)
    (hVpos : ∀ v ∈ V, 0 < v) (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hWV : W ⊆ V) (hcover : Covers V δ) :
    coverExcess W δ ≤ 2 * δ * (V.card : ℝ) - 1 := by
  have hWpos : ∀ v ∈ W, 0 < v := fun v hv => hVpos v (hWV hv)
  have hWint := coverExcess_integrable W δ hWpos hδ hδhalf
  have hVint := coverExcess_integrable V δ hVpos hδ hδhalf
  have hpoint : ∀ t : UnitAddCircle,
      max (coverMultiplicity W δ t - 1) 0 ≤
        max (coverMultiplicity V δ t - 1) 0 := by
    intro t
    gcongr
    exact coverMultiplicity_mono hWV δ t
  have hle := integral_mono hWint hVint hpoint
  change coverExcess W δ ≤ coverExcess V δ at hle
  rwa [coverExcess_eq_epsilon V δ hVpos hδ hδhalf hcover] at hle

/-- 论文第 433–435 行：有限个两两不交的速度子族，其重复覆盖误差
之和不超过全族的 `ε`。覆盖仍是每个圆周点上的逐点条件。 -/
theorem sum_coverExcess_le_epsilon {ι : Type*} (I : Finset ι)
    (W : ι → Finset ℕ) (V : Finset ℕ) (δ : ℝ)
    (hVpos : ∀ v ∈ V, 0 < v) (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hWI : ∀ i ∈ I, W i ⊆ V)
    (hdisj : (I : Set ι).PairwiseDisjoint W)
    (hcover : Covers V δ) :
    (∑ i ∈ I, coverExcess (W i) δ) ≤ 2 * δ * (V.card : ℝ) - 1 := by
  classical
  have hWpos : ∀ i ∈ I, ∀ v ∈ W i, 0 < v := by
    intro i hi v hv
    exact hVpos v (hWI i hi hv)
  have hbi : I.biUnion W ⊆ V := by
    intro v hv
    obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp hv
    exact hWI i hi hvi
  have hsumY (t : UnitAddCircle) :
      (∑ i ∈ I, coverMultiplicity (W i) δ t) ≤ coverMultiplicity V δ t := by
    calc
      (∑ i ∈ I, coverMultiplicity (W i) δ t) =
          ∑ i ∈ I, ∑ v ∈ W i, bohrIndicator v δ t := rfl
      _ = ∑ v ∈ I.biUnion W, bohrIndicator v δ t :=
        (Finset.sum_biUnion hdisj).symm
      _ ≤ ∑ v ∈ V, bohrIndicator v δ t :=
        Finset.sum_le_sum_of_subset_of_nonneg hbi
          (fun v hv hne => bohrIndicator_nonneg v δ t)
      _ = coverMultiplicity V δ t := rfl
  have hpoint (t : UnitAddCircle) :
      (∑ i ∈ I, max (coverMultiplicity (W i) δ t - 1) 0) ≤
        max (coverMultiplicity V δ t - 1) 0 := by
    have hsum := sum_excess_le_excess_sum I
      (fun i => coverMultiplicity (W i) δ t)
      (fun i hi => coverMultiplicity_nonneg (W i) δ t)
    exact hsum.trans (by gcongr; exact hsumY t)
  have hIint : ∀ i ∈ I,
      Integrable (fun t => max (coverMultiplicity (W i) δ t - 1) 0) circleHaar := by
    intro i hi
    exact coverExcess_integrable (W i) δ (hWpos i hi) hδ hδhalf
  have hsumInt : Integrable
      (fun t => ∑ i ∈ I, max (coverMultiplicity (W i) δ t - 1) 0) circleHaar :=
    integrable_finsetSum I hIint
  have hVint := coverExcess_integrable V δ hVpos hδ hδhalf
  have hle := integral_mono hsumInt hVint hpoint
  rw [integral_finsetSum I hIint] at hle
  change (∑ i ∈ I, coverExcess (W i) δ) ≤ coverExcess V δ at hle
  rwa [coverExcess_eq_epsilon V δ hVpos hδ hδhalf hcover] at hle

#print axioms LonelyRunner.integral_coverMultiplicity
#print axioms LonelyRunner.covers_iff_coverMultiplicity_ge_one
#print axioms LonelyRunner.bohrUnion_measureReal_eq_integral_sub_excess
#print axioms LonelyRunner.coverExcess_le_epsilon
#print axioms LonelyRunner.sum_coverExcess_le_epsilon

end LonelyRunner
