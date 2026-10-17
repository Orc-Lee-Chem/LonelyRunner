import LonelyRunner.CoverMoments
import LonelyRunner.BohrPairIntersection

/-! 论文 `paper/lonely_runner_zh.tex` 的 `lem:moments`，第 458–465 行：
二阶下降阶乘矩的有序对展开及其数值下界。 -/

namespace LonelyRunner

open MeasureTheory

private theorem bohrIndicator_sq (v : ℕ) (δ : ℝ) (t : UnitAddCircle) :
    bohrIndicator v δ t * bohrIndicator v δ t = bohrIndicator v δ t := by
  by_cases ht : t ∈ bohrSet v δ
  · simp [bohrIndicator, ht]
  · simp [bohrIndicator, ht]

private theorem coverSecondMoment_pointwise_offDiag (W : Finset ℕ) (δ : ℝ)
    (t : UnitAddCircle) :
    coverMultiplicity W δ t * (coverMultiplicity W δ t - 1) =
      ∑ p ∈ W.offDiag, bohrIndicator p.1 δ t * bohrIndicator p.2 δ t := by
  classical
  let f : ℕ → ℝ := fun v => bohrIndicator v δ t
  have hdiag :
      (∑ p ∈ W.diag, f p.1 * f p.2) = ∑ v ∈ W, f v := by
    rw [Finset.sum_diag]
    apply Finset.sum_congr rfl
    intro v hv
    exact bohrIndicator_sq v δ t
  have hsplit :
      (∑ p ∈ W ×ˢ W, f p.1 * f p.2) =
        (∑ p ∈ W.diag, f p.1 * f p.2) +
          (∑ p ∈ W.offDiag, f p.1 * f p.2) := by
    rw [← Finset.sum_union (Finset.disjoint_diag_offDiag W), Finset.diag_union_offDiag]
  change (∑ v ∈ W, f v) * ((∑ v ∈ W, f v) - 1) = _
  calc
    (∑ v ∈ W, f v) * ((∑ v ∈ W, f v) - 1) =
        (∑ v ∈ W, f v) * (∑ v ∈ W, f v) - (∑ v ∈ W, f v) := by ring
    _ = (∑ p ∈ W ×ˢ W, f p.1 * f p.2) -
          (∑ p ∈ W.diag, f p.1 * f p.2) := by
      rw [Finset.sum_mul_sum, Finset.sum_product, hdiag]
    _ = ∑ p ∈ W.offDiag, f p.1 * f p.2 := by rw [hsplit]; ring

private theorem bohrIndicator_mul_eq_inter_indicator (a b : ℕ) (δ : ℝ)
    (t : UnitAddCircle) :
    bohrIndicator a δ t * bohrIndicator b δ t =
      (bohrSet a δ ∩ bohrSet b δ).indicator (1 : UnitAddCircle → ℝ) t := by
  by_cases ha : t ∈ bohrSet a δ <;>
    by_cases hb : t ∈ bohrSet b δ <;>
      simp [bohrIndicator, ha, hb, Set.mem_inter_iff]

/-- 论文 `lem:moments` 第 458–460 行：二阶矩是有序异速对的交集测度和。 -/
theorem coverSecondMoment_eq_sum_pair_intersections (W : Finset ℕ) (δ : ℝ)
    (hWpos : ∀ v ∈ W, 0 < v) (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    coverSecondMoment W δ =
      ∑ p ∈ W.offDiag, circleHaar.real (bohrSet p.1 δ ∩ bohrSet p.2 δ) := by
  classical
  have hint (p : ℕ × ℕ) (hp : p ∈ W.offDiag) :
      Integrable (fun t : UnitAddCircle =>
        bohrIndicator p.1 δ t * bohrIndicator p.2 δ t) circleHaar := by
    rw [funext (fun t => bohrIndicator_mul_eq_inter_indicator p.1 p.2 δ t)]
    have hpa := (Finset.mem_offDiag.mp hp).1
    have hpb := (Finset.mem_offDiag.mp hp).2.1
    exact (integrable_const 1).indicator
      ((bohrSet_measurable_measure p.1 δ (hWpos p.1 hpa) hδ hδhalf).1.inter
        (bohrSet_measurable_measure p.2 δ (hWpos p.2 hpb) hδ hδhalf).1)
  unfold coverSecondMoment
  simp_rw [coverSecondMoment_pointwise_offDiag W δ]
  rw [integral_finsetSum W.offDiag hint]
  apply Finset.sum_congr rfl
  intro p hp
  rw [funext (fun t => bohrIndicator_mul_eq_inter_indicator p.1 p.2 δ t)]
  have hpa := (Finset.mem_offDiag.mp hp).1
  have hpb := (Finset.mem_offDiag.mp hp).2.1
  exact integral_indicator_one
    ((bohrSet_measurable_measure p.1 δ (hWpos p.1 hpa) hδ hδhalf).1.inter
      (bohrSet_measurable_measure p.2 δ (hWpos p.2 hpb) hδ hδhalf).1)

private theorem offDiag_card_real (W : Finset ℕ) :
    (W.offDiag.card : ℝ) = (W.card : ℝ) * ((W.card : ℝ) - 1) := by
  rw [Finset.offDiag_card]
  have hn : W.card ≤ W.card * W.card := by
    cases hn0 : W.card with
    | zero => simp
    | succ n =>
      nlinarith [Nat.zero_le n]
  rw [Nat.cast_sub hn]
  push_cast
  ring

/-- 论文 `lem:moments` 第 458–461 行：任意有限正速度子族的二阶矩下界；
`|W|−1` 在实数中计算，空集和单元素集亦包含在内。 -/
theorem coverSecondMoment_lower_card (W : Finset ℕ) (δ : ℝ)
    (hWpos : ∀ v ∈ W, 0 < v) (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    (W.card : ℝ) * ((W.card : ℝ) - 1) * δ ^ 2 ≤
      coverSecondMoment W δ := by
  rw [coverSecondMoment_eq_sum_pair_intersections W δ hWpos hδ hδhalf]
  have hsum :
      (∑ _p ∈ W.offDiag, δ ^ 2) ≤
        ∑ p ∈ W.offDiag, circleHaar.real (bohrSet p.1 δ ∩ bohrSet p.2 δ) := by
    apply Finset.sum_le_sum
    intro p hp
    have ⟨hpa, hpb, _⟩ := Finset.mem_offDiag.mp hp
    exact bohr_pair_intersection_bound p.1 p.2 (hWpos p.1 hpa)
      (hWpos p.2 hpb) δ hδ hδhalf.le
  have hsum' : (W.offDiag.card : ℝ) * δ ^ 2 ≤
      ∑ p ∈ W.offDiag, circleHaar.real (bohrSet p.1 δ ∩ bohrSet p.2 δ) := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using hsum
  rw [offDiag_card_real] at hsum'
  exact hsum'

/-- 论文 `lem:moments` 第 463 行：`m≥8`、`|W|≥m/4` 时取明确常数 `1/128`。
不要求 `W` 自身覆盖。 -/
theorem coverSecondMoment_lower_one_div_128 (W : Finset ℕ) (δ : ℝ)
    (hWpos : ∀ v ∈ W, 0 < v) (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (m : ℕ) (hm8 : 8 ≤ m) (hWlarge : m ≤ 4 * W.card)
    (hδlower : 1 / (2 * (m : ℝ)) ≤ δ) :
    (1 / 128 : ℝ) ≤ coverSecondMoment W δ := by
  have hm8R : (8 : ℝ) ≤ m := by exact_mod_cast hm8
  have hm : (0 : ℝ) < m := by linarith
  have hWlargeR : (m : ℝ) ≤ 4 * (W.card : ℝ) := by exact_mod_cast hWlarge
  have hn : (m : ℝ) / 4 ≤ W.card := by linarith
  have hnm : (m : ℝ) / 8 ≤ (W.card : ℝ) - 1 := by linarith
  have hprod : ((m : ℝ) / 4) * ((m : ℝ) / 8) ≤
      (W.card : ℝ) * ((W.card : ℝ) - 1) := by
    exact mul_le_mul hn hnm (by linarith) (by positivity)
  have hq : (0 : ℝ) ≤ 1 / (2 * (m : ℝ)) := by positivity
  have hδsq : (1 / (2 * (m : ℝ))) ^ 2 ≤ δ ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hδlower)
      (by linarith : 0 ≤ δ + 1 / (2 * (m : ℝ)))]
  calc
    (1 / 128 : ℝ) = ((m : ℝ) / 4) * ((m : ℝ) / 8) *
        (1 / (2 * (m : ℝ))) ^ 2 := by
      field_simp
      ring
    _ ≤ (W.card : ℝ) * ((W.card : ℝ) - 1) * δ ^ 2 := by
      exact mul_le_mul hprod hδsq (sq_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (by linarith))
    _ ≤ coverSecondMoment W δ := coverSecondMoment_lower_card W δ hWpos hδ hδhalf

/-- 论文 `lem:moments` 第 463 行：逐点覆盖给出 `1≤∫X=2δm`，
故 `δ≥1/(2m)`；这一下界由覆盖推导而来。 -/
theorem cover_delta_lower_of_covers (V : Finset ℕ) (δ : ℝ)
    (hVpos : ∀ v ∈ V, 0 < v) (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hcover : Covers V δ) (m : ℕ) (hm : m = V.card) (hmpos : 0 < m) :
    1 / (2 * (m : ℝ)) ≤ δ := by
  have hXi := (coverMultiplicity_measurable_integrable V δ hVpos hδ hδhalf).2
  have hpoint : ∀ t : UnitAddCircle, (1 : ℝ) ≤ coverMultiplicity V δ t :=
    (covers_iff_coverMultiplicity_ge_one V δ).mp hcover
  have hi : (1 : ℝ) ≤ ∫ t : UnitAddCircle,
      coverMultiplicity V δ t ∂circleHaar := by
    simpa using (integral_mono (integrable_const (1 : ℝ)) hXi hpoint)
  rw [integral_coverMultiplicity V δ hVpos hδ hδhalf, ← hm] at hi
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (m : ℝ))).2
  nlinarith

/-- 论文 `lem:moments` 第 463–465 行：覆盖族的二阶矩至少 `1/8`，
且由已有上界 `A₂(V)≤mε` 推得 `ε≥1/(8m)`。 -/
theorem coverSecondMoment_and_epsilon_lower_of_covers
    (V : Finset ℕ) (δ : ℝ)
    (hVpos : ∀ v ∈ V, 0 < v) (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hcover : Covers V δ) (m : ℕ) (hm : m = V.card) (hm2 : 2 ≤ m) :
    (1 / 8 : ℝ) ≤ coverSecondMoment V δ ∧
      1 / (8 * (m : ℝ)) ≤ 2 * δ * (m : ℝ) - 1 := by
  have hmpos : 0 < m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hm2R : (2 : ℝ) ≤ m := by exact_mod_cast hm2
  have hδlower := cover_delta_lower_of_covers V δ hVpos hδ hδhalf
    hcover m hm hmpos
  have hcard := coverSecondMoment_lower_card V δ hVpos hδ hδhalf
  rw [← hm] at hcard
  have hcoef : (m : ℝ) * ((m : ℝ) / 2) ≤
      (m : ℝ) * ((m : ℝ) - 1) := by
    exact mul_le_mul_of_nonneg_left (by linarith) hmR.le
  have hq : (0 : ℝ) ≤ 1 / (2 * (m : ℝ)) := by positivity
  have hδsq : (1 / (2 * (m : ℝ))) ^ 2 ≤ δ ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hδlower)
      (by linarith : 0 ≤ δ + 1 / (2 * (m : ℝ)))]
  have hA2 : (1 / 8 : ℝ) ≤ coverSecondMoment V δ := by
    calc
      (1 / 8 : ℝ) = (m : ℝ) * ((m : ℝ) / 2) *
          (1 / (2 * (m : ℝ))) ^ 2 := by
        field_simp
        ring
      _ ≤ (m : ℝ) * ((m : ℝ) - 1) * δ ^ 2 := by
        exact mul_le_mul hcoef hδsq (sq_nonneg _)
          (mul_nonneg hmR.le (by linarith))
      _ ≤ coverSecondMoment V δ := hcard
  have hupper := coverSecondMoment_le_card_mul_epsilon V δ
    hVpos hδ hδhalf hcover m (2 * δ * (m : ℝ) - 1) hm rfl
  constructor
  · exact hA2
  · have hdiv : (1 / 8 : ℝ) / (m : ℝ) ≤ 2 * δ * (m : ℝ) - 1 := by
      apply (div_le_iff₀ hmR).2
      linarith
    convert hdiv using 1
    ring

#print axioms LonelyRunner.coverSecondMoment_eq_sum_pair_intersections
#print axioms LonelyRunner.coverSecondMoment_lower_card
#print axioms LonelyRunner.coverSecondMoment_lower_one_div_128
#print axioms LonelyRunner.coverSecondMoment_and_epsilon_lower_of_covers

end LonelyRunner
