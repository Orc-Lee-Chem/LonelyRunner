import LonelyRunner.CircleFourierFinite
import LonelyRunner.RelationLatticeCount

/-! 论文 `paper/lonely_runner_zh.tex` 第 306–320 行：三重 Bohr 集相交估计。 -/

namespace LonelyRunner

open MeasureTheory
attribute [local instance] Classical.propDecidable

/-- 论文 `lem:fejer` 至 `lem:triple`：`gδ` 的精确有限频率集 `|k|<N`。 -/
noncomputable def tripleFrequencySet (δ : ℝ) : Finset ℤ :=
  Finset.Ioo (-(fejerOrder δ : ℤ)) (fejerOrder δ : ℤ)

/-- 论文 `lem:triple`：频率集的成员资格恰是严格不等式 `|k|<N`。 -/
theorem mem_tripleFrequencySet_iff (δ : ℝ) (k : ℤ) :
    k ∈ tripleFrequencySet δ ↔ k.natAbs < fejerOrder δ := by
  simp only [tripleFrequencySet, Finset.mem_Ioo]
  omega

private theorem sum_signed_frequency (N : ℕ) (f : ℤ → ℂ) :
    ∑ k ∈ Finset.Ioo (-(N + 1 : ℕ) : ℤ) (N + 1 : ℤ), f k =
      f 0 + (∑ j ∈ Finset.range N, f ((j + 1 : ℕ) : ℤ)) +
        (∑ j ∈ Finset.range N, f (-((j + 1 : ℕ) : ℤ))) := by
  induction N with
  | zero =>
    have hs : Finset.Ioo (-1 : ℤ) 1 = {0} := by
      ext k
      simp only [Finset.mem_Ioo, Finset.mem_singleton]
      omega
    simp [hs]
  | succ N ih =>
    have hdisj : Disjoint
        (Finset.Ioo (-(N + 1 : ℕ) : ℤ) (N + 1 : ℤ))
        ({(-((N + 1 : ℕ) : ℤ)), ((N + 1 : ℕ) : ℤ)} : Finset ℤ) := by
      apply Finset.disjoint_left.mpr
      intro k hk hkpair
      simp only [Finset.mem_Ioo] at hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hkpair
      rcases hkpair with rfl | rfl <;> omega
    have hstep := Finset.Ioo_succ_succ (N + 1) (N + 1)
    simp only [Nat.cast_add, Nat.cast_one] at hstep ih hdisj ⊢
    rw [hstep, Finset.sum_union hdisj, ih]
    simp only [Finset.sum_range_succ]
    have hnotmem : -((N : ℤ) + 1) ∉ ({(N : ℤ) + 1} : Finset ℤ) := by
      simp only [Finset.mem_singleton]
      omega
    rw [Finset.sum_insert hnotmem, Finset.sum_singleton]
    abel

/-- 论文 `lem:fejer` 第 294–295 行与 `lem:triple`：有限展开的实系数。 -/
noncomputable def tripleCoefficient (δ : ℝ) (k : ℤ) : ℝ :=
  Real.pi ^ 2 / (4 * (fejerOrder δ : ℝ)) *
    circleFejerCoefficient (fejerOrder δ) k

/-- 论文 `lem:triple` 第 314–318 行：将既有 Fejér 展开接入有限 Fourier
多项式；频率集恰为所有 `|k|<fejerOrder δ` 的整数。 -/
theorem circleFejerMajorant_eq_fourierPoly (δ : ℝ) (hδ : 0 < δ)
    (hδ4 : δ ≤ 1 / 4) (t : UnitAddCircle) :
    (circleFejerMajorant δ t : ℂ) =
      circleFourierPoly (tripleFrequencySet δ)
        (fun k => (tripleCoefficient δ k : ℂ)) t := by
  let N := fejerOrder δ
  have hN : 1 ≤ N := (fejerOrder_bounds δ hδ hδ4).1
  have hNsub : N - 1 + 1 = N := Nat.sub_add_cancel hN
  have hsum := sum_signed_frequency (N - 1)
    (fun k => (tripleCoefficient δ k : ℂ) * fourier k t)
  have hcast : (((N - 1 : ℕ) : ℤ) + 1) = (N : ℤ) := by
    exact_mod_cast hNsub
  rw [hNsub] at hsum
  rw [hcast] at hsum
  have hzero : tripleCoefficient δ 0 = Real.pi ^ 2 / (4 * (N : ℝ)) := by
    have hN0 : 0 < fejerOrder δ := hN
    simp [tripleCoefficient, circleFejerCoefficient, hN0, N]
  have hcoeff (k : ℤ) : (tripleCoefficient δ k : ℂ) =
      (Real.pi ^ 2 / (4 * (N : ℝ)) : ℂ) *
        (circleFejerCoefficient N k : ℂ) := by
    simp only [tripleCoefficient, N, Complex.ofReal_mul, Complex.ofReal_div,
      Complex.ofReal_pow, Complex.ofReal_natCast]
    norm_num
  have hfej : (circleFejerMajorant δ t : ℂ) =
      (Real.pi ^ 2 / (4 * (N : ℝ)) : ℂ) *
        (1 +
          (∑ j ∈ Finset.range (N - 1),
            (circleFejerCoefficient N ((j + 1 : ℕ) : ℤ) : ℂ) *
              fourier ((j + 1 : ℕ) : ℤ) t) +
          (∑ j ∈ Finset.range (N - 1),
            (circleFejerCoefficient N (-((j + 1 : ℕ) : ℤ)) : ℂ) *
              fourier (-((j + 1 : ℕ) : ℤ)) t)) :=
    circleFejerMajorant_expansion δ hδ hδ4 t
  rw [hfej]
  unfold circleFourierPoly tripleFrequencySet
  rw [hsum]
  rw [hzero]
  simp only [fourier_zero, mul_one]
  simp_rw [hcoeff]
  push_cast
  rw [mul_add, mul_add]
  rw [Finset.mul_sum, Finset.mul_sum]
  ring

/-- 论文 `lem:triple` 第 319 行：每个频率系数非负且至多 `π²δ`。 -/
theorem tripleCoefficient_bounds (δ : ℝ) (hδ : 0 < δ)
    (hδ4 : δ ≤ 1 / 4) (k : ℤ) :
    0 ≤ tripleCoefficient δ k ∧ tripleCoefficient δ k ≤ Real.pi ^ 2 * δ := by
  have h := circleFejerMajorant_coefficient_bounds δ hδ hδ4 k
  exact ⟨h.1, h.2.1⟩

/-- 论文 `lem:triple`：三重 Bohr 交集可测。 -/
theorem tripleBohr_measurable (a b c : ℕ) (δ : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) :
    MeasurableSet (bohrSet a δ ∩ bohrSet b δ ∩ bohrSet c δ) := by
  have hhalf : δ < 1 / 2 := by linarith
  exact ((bohrSet_measurable_measure a δ ha hδ hhalf).1.inter
    (bohrSet_measurable_measure b δ hb hδ hhalf).1).inter
    (bohrSet_measurable_measure c δ hc hδ hhalf).1

/-- 论文 `lem:triple`：Fejér 上界非负，包括闭弧端点。 -/
theorem tripleMajorant_nonneg (δ : ℝ) (hδ : 0 < δ)
    (hδ4 : δ ≤ 1 / 4) (t : UnitAddCircle) :
    0 ≤ circleFejerMajorant δ t := by
  have h := circleFejerMajorant_ge_indicator δ hδ hδ4 t
  split_ifs at h <;> linarith

/-- 论文 `lem:triple`：三重交集的逐点指示函数受三个核的乘积控制。 -/
theorem tripleBohr_indicator_le_majorants (a b c : ℕ) (δ : ℝ)
    (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) (t : UnitAddCircle) :
    (if t ∈ bohrSet a δ ∩ bohrSet b δ ∩ bohrSet c δ then (1 : ℝ) else 0) ≤
      circleFejerMajorant δ (a • t) * circleFejerMajorant δ (b • t) *
        circleFejerMajorant δ (c • t) := by
  classical
  have hhalf : δ < 1 / 2 := by linarith
  have ha0 := tripleMajorant_nonneg δ hδ hδ4 (a • t)
  have hb0 := tripleMajorant_nonneg δ hδ hδ4 (b • t)
  have hc0 := tripleMajorant_nonneg δ hδ hδ4 (c • t)
  by_cases ht : t ∈ bohrSet a δ ∩ bohrSet b δ ∩ bohrSet c δ
  · have hdist_a : dist (a • t) 0 ≤ δ :=
      (mem_bohrSet_iff_dist a δ hδ.le hhalf t).mp ht.1.1
    have hdist_b : dist (b • t) 0 ≤ δ :=
      (mem_bohrSet_iff_dist b δ hδ.le hhalf t).mp ht.1.2
    have hdist_c : dist (c • t) 0 ≤ δ :=
      (mem_bohrSet_iff_dist c δ hδ.le hhalf t).mp ht.2
    have ha := circleFejerMajorant_ge_indicator δ hδ hδ4 (a • t)
    have hb := circleFejerMajorant_ge_indicator δ hδ hδ4 (b • t)
    have hc := circleFejerMajorant_ge_indicator δ hδ hδ4 (c • t)
    simp only [if_pos hdist_a] at ha
    simp only [if_pos hdist_b] at hb
    simp only [if_pos hdist_c] at hc
    simp only [if_pos ht]
    calc
      (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ circleFejerMajorant δ (a • t) * circleFejerMajorant δ (b • t) *
          circleFejerMajorant δ (c • t) := by gcongr
  · simp only [if_neg ht]
    positivity

/-- 论文 `lem:triple`：Fejér 上界连续，故三个整数倍代入后的乘积可积。 -/
theorem tripleMajorant_continuous (δ : ℝ) :
    Continuous (circleFejerMajorant δ) := by
  have hsum : Continuous (fejerCharacterSum (fejerOrder δ)) := by
    unfold fejerCharacterSum
    exact continuous_finset_sum _ (fun j hj => map_continuous (fourier (j : ℤ)))
  unfold circleFejerMajorant circleFejerKernel
  fun_prop

/-- 论文 `lem:triple`：三个 Fejér 上界的逐点乘积可积。 -/
theorem tripleMajorant_product_integrable (a b c : ℕ) (δ : ℝ) :
    Integrable (fun t : UnitAddCircle =>
      circleFejerMajorant δ (a • t) * circleFejerMajorant δ (b • t) *
        circleFejerMajorant δ (c • t)) circleHaar := by
  have ha : Continuous (fun t : UnitAddCircle => circleFejerMajorant δ (a • t)) :=
    (tripleMajorant_continuous δ).comp (continuous_nsmul a)
  have hb : Continuous (fun t : UnitAddCircle => circleFejerMajorant δ (b • t)) :=
    (tripleMajorant_continuous δ).comp (continuous_nsmul b)
  have hc : Continuous (fun t : UnitAddCircle => circleFejerMajorant δ (c • t)) :=
    (tripleMajorant_continuous δ).comp (continuous_nsmul c)
  have h := ((ha.mul hb).mul hc).continuousOn.integrableOn_compact
    (μ := circleHaar) isCompact_univ
  exact integrableOn_univ.mp h

/-- 论文 `lem:triple`：三项有限 Fourier 积分只保留总频率为零的关系。 -/
theorem tripleMajorant_integral_eq_relationSum (a b c : ℕ) (δ : ℝ)
    (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) :
    (∫ t : UnitAddCircle,
      circleFejerMajorant δ (a • t) * circleFejerMajorant δ (b • t) *
        circleFejerMajorant δ (c • t) ∂circleHaar) =
      ∑ k ∈ tripleFrequencySet δ, ∑ l ∈ tripleFrequencySet δ,
        ∑ r ∈ tripleFrequencySet δ,
          if (a : ℤ) * k + (b : ℤ) * l + (c : ℤ) * r = 0 then
            tripleCoefficient δ k * tripleCoefficient δ l * tripleCoefficient δ r
          else 0 := by
  let S := tripleFrequencySet δ
  let coeff : ℤ → ℂ := fun k => (tripleCoefficient δ k : ℂ)
  have hpoint (t : UnitAddCircle) :
      ((circleFejerMajorant δ (a • t) * circleFejerMajorant δ (b • t) *
        circleFejerMajorant δ (c • t) : ℝ) : ℂ) =
        circleFourierPoly S coeff (a • t) *
          circleFourierPoly S coeff (b • t) *
            circleFourierPoly S coeff (c • t) := by
    simp only [Complex.ofReal_mul]
    rw [circleFejerMajorant_eq_fourierPoly δ hδ hδ4,
      circleFejerMajorant_eq_fourierPoly δ hδ hδ4,
      circleFejerMajorant_eq_fourierPoly δ hδ hδ4]
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [hpoint]
  rw [circleFourierPoly_integral_mul_three]
  simp only [S, coeff, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hrel : (a : ℤ) * k + (b : ℤ) * l + (c : ℤ) * r = 0
  · simp [hrel, Complex.ofReal_mul]
  · simp [hrel]

/-- 论文 `lem:triple`：有限频率立方体中满足整数关系的三元组。 -/
noncomputable def tripleRelationFrequencies (a b c : ℕ) (δ : ℝ) :
    Finset ((ℤ × ℤ) × ℤ) :=
  let S := tripleFrequencySet δ
  ((S.product S).product S).filter
    (fun p => (a : ℤ) * p.1.1 + (b : ℤ) * p.1.2 + (c : ℤ) * p.2 = 0)

/-- 论文 `lem:triple`：关系积分是有限关系频率集上的实系数和。 -/
theorem tripleMajorant_integral_eq_relationFrequencies (a b c : ℕ) (δ : ℝ)
    (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) :
    (∫ t : UnitAddCircle,
      circleFejerMajorant δ (a • t) * circleFejerMajorant δ (b • t) *
        circleFejerMajorant δ (c • t) ∂circleHaar) =
      ∑ p ∈ tripleRelationFrequencies a b c δ,
        tripleCoefficient δ p.1.1 * tripleCoefficient δ p.1.2 *
          tripleCoefficient δ p.2 := by
  rw [tripleMajorant_integral_eq_relationSum a b c δ hδ hδ4]
  simp only [tripleRelationFrequencies, Finset.sum_filter]
  rw [← Finset.sum_product', ← Finset.sum_product']
  rfl

/-- 论文 `lem:triple`：严格频率立方体注入已证明计数的闭关系立方体。 -/
theorem tripleRelationFrequencies_card_le_cube (a b c : ℕ) (δ : ℝ) :
    (tripleRelationFrequencies a b c δ).card ≤
      (relationCube a b c (fejerOrder δ : ℝ)).card := by
  classical
  let f : ((ℤ × ℤ) × ℤ) → (Fin 3 → ℤ) :=
    fun p => ![p.1.1, p.1.2, p.2]
  apply Finset.card_le_card_of_injOn f
  · intro p hp
    have hp' := (Finset.mem_filter.mp
      (show p ∈ tripleRelationFrequencies a b c δ from hp))
    have hcoord : p.1.1 ∈ tripleFrequencySet δ ∧
        p.1.2 ∈ tripleFrequencySet δ ∧ p.2 ∈ tripleFrequencySet δ := by
      have h' : (p.1.1 ∈ tripleFrequencySet δ ∧ p.1.2 ∈ tripleFrequencySet δ) ∧
          p.2 ∈ tripleFrequencySet δ := by
        simpa [tripleRelationFrequencies, Finset.mem_product] using hp'.1
      exact ⟨h'.1.1, h'.1.2, h'.2⟩
    have hbound (k : ℤ) (hk : k ∈ tripleFrequencySet δ) :
        |(k : ℝ)| ≤ (fejerOrder δ : ℝ) := by
      have h := (mem_tripleFrequencySet_iff δ k).mp hk
      have h' : ((k.natAbs : ℝ)) ≤ (fejerOrder δ : ℝ) := by exact_mod_cast (Nat.le_of_lt h)
      simpa using h'
    apply (mem_relationCube_iff a b c (fejerOrder δ : ℝ) (f p)).mpr
    constructor
    · simpa [f, relationLattice, tripleRelationFrequencies] using hp'.2
    · intro i
      fin_cases i
      · simpa [f] using hbound p.1.1 hcoord.1
      · simpa [f] using hbound p.1.2 hcoord.2.1
      · simpa [f] using hbound p.2 hcoord.2.2
  · intro p hp q hq heq
    rcases p with ⟨⟨k, l⟩, r⟩
    rcases q with ⟨⟨k', l'⟩, r'⟩
    have h0 := congrArg (fun w : Fin 3 → ℤ => w 0) heq
    have h1 := congrArg (fun w : Fin 3 → ℤ => w 1) heq
    have h2 := congrArg (fun w : Fin 3 → ℤ => w 2) heq
    simp only [f, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1 h2
    simp_all

/-- 论文 `lem:triple`：每个关系项非负，且不超过 `π⁶δ³`。 -/
theorem tripleRelationTerm_bounds (δ : ℝ) (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4)
    (p : (ℤ × ℤ) × ℤ) :
    0 ≤ tripleCoefficient δ p.1.1 * tripleCoefficient δ p.1.2 *
      tripleCoefficient δ p.2 ∧
    tripleCoefficient δ p.1.1 * tripleCoefficient δ p.1.2 *
      tripleCoefficient δ p.2 ≤ Real.pi ^ 6 * δ ^ 3 := by
  have hk := tripleCoefficient_bounds δ hδ hδ4 p.1.1
  have hl := tripleCoefficient_bounds δ hδ hδ4 p.1.2
  have hr := tripleCoefficient_bounds δ hδ hδ4 p.2
  rcases hk with ⟨hk0, hk1⟩
  rcases hl with ⟨hl0, hl1⟩
  rcases hr with ⟨hr0, hr1⟩
  constructor
  · positivity
  · calc
      _ ≤ (Real.pi ^ 2 * δ) * (Real.pi ^ 2 * δ) *
          (Real.pi ^ 2 * δ) := by gcongr
      _ = Real.pi ^ 6 * δ ^ 3 := by ring

/-- 论文 `lem:triple`：核的三重积分由闭关系立方体的基数控制。 -/
theorem tripleMajorant_integral_le_cube (a b c : ℕ) (δ : ℝ)
    (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) :
    (∫ t : UnitAddCircle,
      circleFejerMajorant δ (a • t) * circleFejerMajorant δ (b • t) *
        circleFejerMajorant δ (c • t) ∂circleHaar) ≤
      ((relationCube a b c (fejerOrder δ : ℝ)).card : ℝ) *
        (Real.pi ^ 6 * δ ^ 3) := by
  rw [tripleMajorant_integral_eq_relationFrequencies a b c δ hδ hδ4]
  have hterm : ∀ p ∈ tripleRelationFrequencies a b c δ,
      tripleCoefficient δ p.1.1 * tripleCoefficient δ p.1.2 *
        tripleCoefficient δ p.2 ≤ Real.pi ^ 6 * δ ^ 3 :=
    fun p hp => (tripleRelationTerm_bounds δ hδ hδ4 p).2
  have hsum := Finset.sum_le_card_nsmul (tripleRelationFrequencies a b c δ)
    (fun p => tripleCoefficient δ p.1.1 * tripleCoefficient δ p.1.2 *
      tripleCoefficient δ p.2) (Real.pi ^ 6 * δ ^ 3) hterm
  have hcard : ((tripleRelationFrequencies a b c δ).card : ℝ) ≤
      ((relationCube a b c (fejerOrder δ : ℝ)).card : ℝ) := by
    exact_mod_cast tripleRelationFrequencies_card_le_cube a b c δ
  have hpos : 0 ≤ Real.pi ^ 6 * δ ^ 3 := by positivity
  have hsum' :
      (∑ p ∈ tripleRelationFrequencies a b c δ,
        tripleCoefficient δ p.1.1 * tripleCoefficient δ p.1.2 *
          tripleCoefficient δ p.2) ≤
        ((tripleRelationFrequencies a b c δ).card : ℝ) *
          (Real.pi ^ 6 * δ ^ 3) := by
    simpa only [nsmul_eq_mul] using hsum
  exact hsum'.trans (mul_le_mul_of_nonneg_right hcard hpos)

/-- 论文 `lem:triple`：闭 Bohr 三重交的实测度由关系立方体计数控制。 -/
theorem tripleBohr_measure_le_cube (a b c : ℕ) (δ : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) :
    circleHaar.real (bohrSet a δ ∩ bohrSet b δ ∩ bohrSet c δ) ≤
      ((relationCube a b c (fejerOrder δ : ℝ)).card : ℝ) *
        (Real.pi ^ 6 * δ ^ 3) := by
  let s := bohrSet a δ ∩ bohrSet b δ ∩ bohrSet c δ
  have hs : MeasurableSet s := tripleBohr_measurable a b c δ ha hb hc hδ hδ4
  have hi : Integrable (s.indicator (fun _ => (1 : ℝ))) circleHaar :=
    (integrable_const (1 : ℝ)).indicator hs
  have hg := tripleMajorant_product_integrable a b c δ
  calc
    circleHaar.real s = ∫ t : UnitAddCircle, s.indicator (fun _ => (1 : ℝ)) t ∂circleHaar :=
      (integral_indicator_one hs).symm
    _ ≤ ∫ t : UnitAddCircle,
        circleFejerMajorant δ (a • t) * circleFejerMajorant δ (b • t) *
          circleFejerMajorant δ (c • t) ∂circleHaar := by
      apply integral_mono hi hg
      intro t
      simpa [s, Set.indicator] using tripleBohr_indicator_le_majorants a b c δ hδ hδ4 t
    _ ≤ _ := tripleMajorant_integral_le_cube a b c δ hδ hδ4

/-- 论文 `lem:triple`：闭 Bohr 三重交的绝对常数估计，取 `C=12π⁶`。 -/
theorem bohr_triple_intersection_bound (a b c : ℕ) (δ : ℝ)
    (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) :
    circleHaar.real (bohrSet a δ ∩ bohrSet b δ ∩ bohrSet c δ) ≤
      12 * Real.pi ^ 6 *
        (δ ^ 3 + δ ^ 2 / (relationLambda a b c : ℝ) +
          δ / (relationC a b c : ℝ)) := by
  let N := fejerOrder δ
  let L : ℝ := relationLambda a b c
  let H : ℝ := relationC a b c
  have hb : 0 < b := lt_trans ha hab
  have hc : 0 < c := lt_trans hb hbc
  have hL : 0 < L := by
    dsimp [L]
    exact_mod_cast (relationLambda_pos_and_attained a b c hb).1
  have hH : 0 < H := by
    dsimp [H]
    exact_mod_cast relationHeight_pos a b c hc
  have hN1 : 1 ≤ (N : ℝ) := by
    exact_mod_cast (fejerOrder_bounds δ hδ hδ4).1
  have hNbound : (N : ℝ) ≤ 1 / (2 * δ) :=
    (fejerOrder_bounds δ hδ hδ4).2.2
  have hNd : δ * (N : ℝ) ≤ 1 := by
    have htwo : 2 * δ * (N : ℝ) ≤ 1 := by
      calc
        _ ≤ 2 * δ * (1 / (2 * δ)) :=
          mul_le_mul_of_nonneg_left hNbound (by positivity)
        _ = 1 := by field_simp
    have hn : 0 ≤ δ * (N : ℝ) := by positivity
    linarith
  have hNd2 : (δ * (N : ℝ)) ^ 2 ≤ 1 := by
    have hn : 0 ≤ δ * (N : ℝ) := by positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hNd) (add_nonneg hn (by norm_num : (0:ℝ) ≤ 1))]
  have hterm1 : δ ^ 3 * ((N : ℝ) / L) ≤ δ ^ 2 / L := by
    calc
      _ = (δ ^ 2 / L) * (δ * (N : ℝ)) := by ring
      _ ≤ (δ ^ 2 / L) * 1 := mul_le_mul_of_nonneg_left hNd (by positivity)
      _ = δ ^ 2 / L := by ring
  have hterm2 : δ ^ 3 * ((N : ℝ) ^ 2 / H) ≤ δ / H := by
    calc
      _ = (δ / H) * (δ * (N : ℝ)) ^ 2 := by ring
      _ ≤ (δ / H) * 1 := mul_le_mul_of_nonneg_left hNd2 (by positivity)
      _ = δ / H := by ring
  have htarget : δ ^ 3 * (1 + (N : ℝ) / L + (N : ℝ) ^ 2 / H) ≤
      δ ^ 3 + δ ^ 2 / L + δ / H := by
    calc
      _ = δ ^ 3 + δ ^ 3 * ((N : ℝ) / L) +
          δ ^ 3 * ((N : ℝ) ^ 2 / H) := by ring
      _ ≤ δ ^ 3 + δ ^ 2 / L + δ / H :=
        add_le_add (add_le_add_right hterm1 _) hterm2
  have hcount := relationLattice_count a b c ha hab hbc (N : ℝ) hN1
  have hpos : 0 ≤ Real.pi ^ 6 * δ ^ 3 := by positivity
  calc
    circleHaar.real (bohrSet a δ ∩ bohrSet b δ ∩ bohrSet c δ) ≤
        ((relationCube a b c (N : ℝ)).card : ℝ) *
          (Real.pi ^ 6 * δ ^ 3) := tripleBohr_measure_le_cube a b c δ ha hb hc hδ hδ4
    _ ≤ (12 * (1 + (N : ℝ) / L + (N : ℝ) ^ 2 / H)) *
          (Real.pi ^ 6 * δ ^ 3) := mul_le_mul_of_nonneg_right hcount hpos
    _ = 12 * Real.pi ^ 6 *
          (δ ^ 3 * (1 + (N : ℝ) / L + (N : ℝ) ^ 2 / H)) := by ring
    _ ≤ 12 * Real.pi ^ 6 *
          (δ ^ 3 + δ ^ 2 / L + δ / H) :=
        mul_le_mul_of_nonneg_left htarget (by positivity)
    _ = _ := rfl

/-- 论文 `lem:triple`：存在独立于速度和弧长的正绝对常数。 -/
theorem bohr_triple_intersection_exists_absolute_constant :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b c : ℕ) (δ : ℝ), 0 < a → a < b → b < c →
        0 < δ → δ ≤ 1 / 4 →
        circleHaar.real (bohrSet a δ ∩ bohrSet b δ ∩ bohrSet c δ) ≤
          C * (δ ^ 3 + δ ^ 2 / (relationLambda a b c : ℝ) +
            δ / (relationC a b c : ℝ)) := by
  refine ⟨12 * Real.pi ^ 6, by positivity, ?_⟩
  intro a b c δ ha hab hbc hδ hδ4
  exact bohr_triple_intersection_bound a b c δ ha hab hbc hδ hδ4

#print axioms LonelyRunner.bohr_triple_intersection_bound
#print axioms LonelyRunner.bohr_triple_intersection_exists_absolute_constant

end LonelyRunner
