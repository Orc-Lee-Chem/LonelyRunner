import LonelyRunner.CircleTent
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! 论文 `paper/lonely_runner_zh.tex` 的 `lem:pair`：二重 Bohr 相交。 -/

namespace LonelyRunner

open Metric MeasureTheory

/-- 论文 `lem:pair`：二重 Fourier 展开的单个有限关系项。 -/
noncomputable def circleTentPairTerm (δ : ℝ) (a b : ℕ)
    (p : ℤ × ℤ) (t : UnitAddCircle) : ℂ :=
  (circleTentFourierCoeff δ p.1 * circleTentFourierCoeff δ p.2) *
    fourier ((a : ℤ) * p.1 + (b : ℤ) * p.2) t

private theorem pair_fourier_nsmul (v : ℕ) (k : ℤ) (t : UnitAddCircle) :
    fourier k (v • t) = fourier ((v : ℤ) * k) t := by
  simp only [fourier_apply]
  congr 1
  rw [← natCast_zsmul, mul_comm (v : ℤ) k, mul_zsmul]

private theorem pair_fourier_norm (k : ℤ) (t : UnitAddCircle) :
    ‖fourier k t‖ = 1 := by
  rw [fourier_apply]
  exact Circle.norm_coe _

private theorem pair_coeff_norm_prod_summable (δ : ℝ) (hδ : 0 < δ)
    (hδhalf : δ ≤ 1 / 2) :
    Summable (fun p : ℤ × ℤ =>
      ‖circleTentFourierCoeff δ p.1‖ * ‖circleTentFourierCoeff δ p.2‖) := by
  have hs := (circleTent_fourierCoeff_summable δ hδ hδhalf).norm
  apply (summable_prod_of_nonneg (fun p => mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
  constructor
  · intro k
    simpa only [Prod.fst, Prod.snd] using
      (hs.mul_left ‖circleTentFourierCoeff δ k‖)
  · simp_rw [tsum_mul_left]
    exact hs.mul_right _

/-- 论文 `lem:pair`：二重 Fourier 关系级数逐点可和。 -/
theorem circleTent_pairTerm_summable (δ : ℝ) (hδ : 0 < δ)
    (hδhalf : δ ≤ 1 / 2) (a b : ℕ) (t : UnitAddCircle) :
    Summable (fun p : ℤ × ℤ => circleTentPairTerm δ a b p t) := by
  apply (pair_coeff_norm_prod_summable δ hδ hδhalf).of_norm_bounded
  intro p
  simp only [circleTentPairTerm, norm_mul, pair_fourier_norm, mul_one]
  exact le_rfl

/-- 论文 `lem:pair`：两个帐篷的乘积等于绝对收敛的整数频率关系级数。 -/
theorem circleTent_pair_hasSum (δ : ℝ) (hδ : 0 < δ)
    (hδhalf : δ ≤ 1 / 2) (a b : ℕ) (t : UnitAddCircle) :
    HasSum (fun p : ℤ × ℤ => circleTentPairTerm δ a b p t)
      ((circleTent δ (a • t) * circleTent δ (b • t) : ℝ) : ℂ) := by
  have h1 := circleTent_fourier_hasSum_pointwise δ hδ hδhalf (a • t)
  have h2 := circleTent_fourier_hasSum_pointwise δ hδ hδhalf (b • t)
  have hpair : Summable (fun p : ℤ × ℤ =>
      (circleTentFourierCoeff δ p.1 * fourier p.1 (a • t)) *
        (circleTentFourierCoeff δ p.2 * fourier p.2 (b • t))) := by
    apply (pair_coeff_norm_prod_summable δ hδ hδhalf).of_norm_bounded
    intro p
    simp only [norm_mul, pair_fourier_norm, mul_one]
    exact le_rfl
  have h := h1.mul h2 hpair
  have hterm (p : ℤ × ℤ) :
      (circleTentFourierCoeff δ p.1 * fourier p.1 (a • t)) *
        (circleTentFourierCoeff δ p.2 * fourier p.2 (b • t)) =
          circleTentPairTerm δ a b p t := by
    simp only [circleTentPairTerm, pair_fourier_nsmul, fourier_add]
    ring
  simpa only [hterm, Complex.ofReal_mul] using h

private theorem pairTerm_integrable (δ : ℝ) (a b : ℕ) (p : ℤ × ℤ) :
    Integrable (circleTentPairTerm δ a b p) circleHaar := by
  unfold circleTentPairTerm
  exact (circleFourier_integrable _).const_mul _

private theorem pairTerm_norm (δ : ℝ) (a b : ℕ) (p : ℤ × ℤ)
    (t : UnitAddCircle) :
    ‖circleTentPairTerm δ a b p t‖ =
      ‖circleTentFourierCoeff δ p.1‖ * ‖circleTentFourierCoeff δ p.2‖ := by
  simp [circleTentPairTerm]

private theorem pairTerm_integral (δ : ℝ) (a b : ℕ) (p : ℤ × ℤ) :
    (∫ t : UnitAddCircle, circleTentPairTerm δ a b p t ∂circleHaar) =
      if (a : ℤ) * p.1 + (b : ℤ) * p.2 = 0 then
        circleTentFourierCoeff δ p.1 * circleTentFourierCoeff δ p.2 else 0 := by
  unfold circleTentPairTerm
  rw [integral_const_mul, integral_circleFourier]
  split_ifs <;> simp

private theorem pairTerm_integral_norm_summable (δ : ℝ) (hδ : 0 < δ)
    (hδhalf : δ ≤ 1 / 2) (a b : ℕ) :
    Summable (fun p : ℤ × ℤ =>
      ∫ t : UnitAddCircle, ‖circleTentPairTerm δ a b p t‖ ∂circleHaar) := by
  convert pair_coeff_norm_prod_summable δ hδ hδhalf using 1
  ext p
  simp_rw [pairTerm_norm]
  simp

/-- 论文 `lem:pair`：两个帐篷函数乘积的积分等于所有零频率关系项之和。 -/
theorem circleTent_pair_integral (δ : ℝ) (hδ : 0 < δ)
    (hδhalf : δ ≤ 1 / 2) (a b : ℕ) :
    (∫ t : UnitAddCircle,
      ((circleTent δ (a • t) * circleTent δ (b • t) : ℝ) : ℂ) ∂circleHaar) =
      ∑' p : ℤ × ℤ,
        if (a : ℤ) * p.1 + (b : ℤ) * p.2 = 0 then
          circleTentFourierCoeff δ p.1 * circleTentFourierCoeff δ p.2 else 0 := by
  have hswap := integral_tsum_of_summable_integral_norm
    (fun p : ℤ × ℤ => pairTerm_integrable δ a b p)
    (pairTerm_integral_norm_summable δ hδ hδhalf a b)
  calc
    (∫ t : UnitAddCircle,
      ((circleTent δ (a • t) * circleTent δ (b • t) : ℝ) : ℂ) ∂circleHaar) =
      ∫ t : UnitAddCircle,
          (∑' p : ℤ × ℤ, circleTentPairTerm δ a b p t) ∂circleHaar := by
      congr 1
      funext t
      exact (circleTent_pair_hasSum δ hδ hδhalf a b t).tsum_eq.symm
    _ = ∑' p : ℤ × ℤ,
          ∫ t : UnitAddCircle, circleTentPairTerm δ a b p t ∂circleHaar := hswap.symm
    _ = ∑' p : ℤ × ℤ,
          if (a : ℤ) * p.1 + (b : ℤ) * p.2 = 0 then
            circleTentFourierCoeff δ p.1 * circleTentFourierCoeff δ p.2 else 0 := by
      congr 1
      funext p
      exact pairTerm_integral δ a b p

private theorem pairTerm_integral_summable (δ : ℝ) (hδ : 0 < δ)
    (hδhalf : δ ≤ 1 / 2) (a b : ℕ) :
    Summable (fun p : ℤ × ℤ =>
      if (a : ℤ) * p.1 + (b : ℤ) * p.2 = 0 then
        circleTentFourierCoeff δ p.1 * circleTentFourierCoeff δ p.2 else 0) := by
  have h := (hasSum_integral_of_summable_integral_norm
    (fun p : ℤ × ℤ => pairTerm_integrable δ a b p)
    (pairTerm_integral_norm_summable δ hδ hδhalf a b)).summable
  simpa only [pairTerm_integral] using h

private theorem pair_real_coeff_nonneg (δ : ℝ) (hδ : 0 < δ)
    (a b : ℕ) (p : ℤ × ℤ) :
    0 ≤ (if (a : ℤ) * p.1 + (b : ℤ) * p.2 = 0 then
      circleTentRealCoeff δ p.1 * circleTentRealCoeff δ p.2 else 0) := by
  split_ifs
  · exact mul_nonneg (circleTentRealCoeff_nonneg δ hδ _) (circleTentRealCoeff_nonneg δ hδ _)
  · exact le_rfl

/-- 论文 `lem:pair`：两个帐篷函数乘积的积分至少为零频率贡献 `δ²`。 -/
theorem circleTent_pair_integral_lower (δ : ℝ) (hδ : 0 < δ)
    (hδhalf : δ ≤ 1 / 2) (a b : ℕ) :
    δ ^ 2 ≤ ∫ t : UnitAddCircle,
      circleTent δ (a • t) * circleTent δ (b • t) ∂circleHaar := by
  let f : ℤ × ℤ → ℝ := fun p =>
    if (a : ℤ) * p.1 + (b : ℤ) * p.2 = 0 then
      circleTentRealCoeff δ p.1 * circleTentRealCoeff δ p.2 else 0
  have hfc (p : ℤ × ℤ) :
      (if (a : ℤ) * p.1 + (b : ℤ) * p.2 = 0 then
        circleTentFourierCoeff δ p.1 * circleTentFourierCoeff δ p.2 else 0) =
        (f p : ℂ) := by
    dsimp [f]
    split_ifs <;> simp [circleTent_fourierCoeff_eq_real δ hδ hδhalf, Complex.ofReal_mul]
  have hs : Summable (fun p : ℤ × ℤ => (f p : ℂ)) := by
    simpa only [← hfc] using pairTerm_integral_summable δ hδ hδhalf a b
  have hmain := circleTent_pair_integral δ hδ hδhalf a b
  simp_rw [hfc] at hmain
  rw [integral_complex_ofReal] at hmain
  have hre := congrArg Complex.re hmain
  rw [Complex.re_tsum hs] at hre
  simp only [Complex.ofReal_re] at hre
  have hsum : Summable f := by
    exact Complex.summable_ofReal.mp hs
  have hnonneg : ∀ p, 0 ≤ f p := fun p => pair_real_coeff_nonneg δ hδ a b p
  have hsingle := Summable.sum_le_tsum {(0, 0)} (fun p hp => hnonneg p) hsum
  have hzero : f (0, 0) = δ ^ 2 := by
    simp [f, circleTentRealCoeff_zero, pow_two]
  simpa [hzero] using (hsingle.trans_eq hre.symm)

private theorem pair_bohr_measurable (δ : ℝ) (hδ : 0 < δ)
    (hδhalf : δ ≤ 1 / 2) (v : ℕ) :
    MeasurableSet (bohrSet v δ) := by
  have hset : bohrSet v δ =
      (fun t : UnitAddCircle => v • t) ⁻¹' closedBall (0 : UnitAddCircle) δ := by
    ext t
    exact mem_bohrSet_iff_dist_le_half v δ hδ.le hδhalf t
  rw [hset]
  exact (isClosed_closedBall.preimage (continuous_nsmul v)).measurableSet

private theorem pair_tent_integrable (δ : ℝ) (a b : ℕ) :
    Integrable (fun t : UnitAddCircle =>
      circleTent δ (a • t) * circleTent δ (b • t)) circleHaar := by
  have hc : Continuous (fun t : UnitAddCircle =>
      circleTent δ (a • t) * circleTent δ (b • t)) :=
    ((circleTent_continuous δ).comp (continuous_nsmul a)).mul
      ((circleTent_continuous δ).comp (continuous_nsmul b))
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- 论文 `lem:pair`：包括 `δ=1/2`、相同或不互素速度的闭 Bohr 集二重相交下界。 -/
theorem bohr_pair_intersection_bound (a b : ℕ) (_ha : 0 < a) (_hb : 0 < b)
    (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    δ ^ 2 ≤ circleHaar.real (bohrSet a δ ∩ bohrSet b δ) := by
  have hs : MeasurableSet (bohrSet a δ ∩ bohrSet b δ) :=
    (pair_bohr_measurable δ hδ hδhalf a).inter
      (pair_bohr_measurable δ hδ hδhalf b)
  have hind : Integrable
      ((bohrSet a δ ∩ bohrSet b δ).indicator (1 : UnitAddCircle → ℝ))
      circleHaar := (integrable_const 1).indicator hs
  have hpoint (t : UnitAddCircle) :
      circleTent δ (a • t) * circleTent δ (b • t) ≤
        (bohrSet a δ ∩ bohrSet b δ).indicator (1 : UnitAddCircle → ℝ) t := by
    by_cases ht : t ∈ bohrSet a δ ∩ bohrSet b δ
    · rw [Set.indicator_of_mem ht]
      change circleTent δ (a • t) * circleTent δ (b • t) ≤ 1
      have ha1 := circleTent_le_one δ hδ (a • t)
      have hb1 := circleTent_le_one δ hδ (b • t)
      have han := circleTent_nonneg δ (a • t)
      have hbn := circleTent_nonneg δ (b • t)
      nlinarith
    · rw [Set.indicator_of_notMem ht]
      have hor : t ∉ bohrSet a δ ∨ t ∉ bohrSet b δ := by
        simpa only [Set.mem_inter_iff, not_and_or] using ht
      rcases hor with hna | hnb
      · have hdist : δ < dist (a • t) 0 := lt_of_not_ge
          ((mem_bohrSet_iff_dist_le_half a δ hδ.le hδhalf t).not.mp hna)
        simp [circleTent_eq_zero_of_dist_gt δ hδ (a • t) hdist]
      · have hdist : δ < dist (b • t) 0 := lt_of_not_ge
          ((mem_bohrSet_iff_dist_le_half b δ hδ.le hδhalf t).not.mp hnb)
        simp [circleTent_eq_zero_of_dist_gt δ hδ (b • t) hdist]
  calc
    δ ^ 2 ≤ ∫ t : UnitAddCircle,
        circleTent δ (a • t) * circleTent δ (b • t) ∂circleHaar :=
      circleTent_pair_integral_lower δ hδ hδhalf a b
    _ ≤ ∫ t : UnitAddCircle,
        (bohrSet a δ ∩ bohrSet b δ).indicator (1 : UnitAddCircle → ℝ) t
          ∂circleHaar :=
      integral_mono (pair_tent_integrable δ a b) hind hpoint
    _ = circleHaar.real (bohrSet a δ ∩ bohrSet b δ) :=
      integral_indicator_one hs

#print axioms LonelyRunner.bohr_pair_intersection_bound

end LonelyRunner
