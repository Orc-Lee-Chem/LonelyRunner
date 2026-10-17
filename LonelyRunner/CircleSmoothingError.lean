import LonelyRunner.CircleIntervalTranslation

/-! # 圆周有限闭弧并的 Fejér 平滑误差 -/
namespace LonelyRunner
open MeasureTheory

private theorem circleSetIndicator_integrable_new {A : Set UnitAddCircle}
    (hA : MeasurableSet A) : Integrable (circleSetIndicator A) circleHaar := by
  exact (integrable_const (1 : ℝ)).indicator hA

private theorem circleFejerKernel_integrable_new (R : ℕ) :
    Integrable (circleFejerKernel R) circleHaar := by
  have hc : Continuous (circleFejerKernel R) := by
    unfold circleFejerKernel fejerCharacterSum
    fun_prop
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private theorem circleSetIndicator_bound_new (A : Set UnitAddCircle) (t : UnitAddCircle) :
    |circleSetIndicator A t| ≤ 1 := by
  by_cases ht : t ∈ A <;> simp [circleSetIndicator, ht]

private theorem circleFejerSmoothing_difference_joint_integrable {A : Set UnitAddCircle}
    (hA : MeasurableSet A) (R : ℕ) :
    Integrable (fun p : UnitAddCircle × UnitAddCircle =>
      (circleSetIndicator A (p.1-p.2) - circleSetIndicator A p.1) *
        circleFejerKernel R p.2) (circleHaar.prod circleHaar) := by
  have hshift := circleFejerSmoothing_joint_integrable hA R
  have hbase := (circleSetIndicator_integrable_new hA).mul_prod
    (circleFejerKernel_integrable_new R)
  convert hshift.sub hbase using 1
  funext p
  simp only [Pi.sub_apply, sub_mul]

private theorem circleFejerSmoothing_difference_integrable {A : Set UnitAddCircle}
    (hA : MeasurableSet A) (R : ℕ) (t : UnitAddCircle) :
    Integrable (fun u : UnitAddCircle =>
      (circleSetIndicator A (t-u) - circleSetIndicator A t) *
        circleFejerKernel R u) circleHaar := by
  have hk := circleFejerKernel_integrable_new R
  have hm : Measurable (fun u : UnitAddCircle => circleSetIndicator A (t-u)) := by
    exact (measurable_const.indicator hA).comp (measurable_const.sub measurable_id)
  have hb : ∀ᵐ u : UnitAddCircle ∂circleHaar,
      ‖circleSetIndicator A (t-u)‖ ≤ (1 : ℝ) := by
    filter_upwards [] with u
    simpa only [Real.norm_eq_abs] using circleSetIndicator_bound_new A (t-u)
  have hshift : Integrable (fun u : UnitAddCircle =>
      circleSetIndicator A (t-u) * circleFejerKernel R u) circleHaar := by
    simpa only [mul_comm] using hk.mul_bdd hm.aestronglyMeasurable hb
  have hbase : Integrable (fun u : UnitAddCircle =>
      circleSetIndicator A t * circleFejerKernel R u) circleHaar := hk.const_mul _
  convert hshift.sub hbase using 1
  funext u
  simp only [Pi.sub_apply, sub_mul]

private theorem circleFejerSmoothing_difference_eq_integral {A : Set UnitAddCircle}
    (hA : MeasurableSet A) (R : ℕ) (hR : 1 ≤ R) (t : UnitAddCircle) :
    circleFejerSmoothing A R t - circleSetIndicator A t =
      ∫ u : UnitAddCircle,
        (circleSetIndicator A (t-u) - circleSetIndicator A t) *
          circleFejerKernel R u ∂circleHaar := by
  have hk := circleFejerKernel_integrable_new R
  have hm : Measurable (fun u : UnitAddCircle => circleSetIndicator A (t-u)) := by
    exact (measurable_const.indicator hA).comp (measurable_const.sub measurable_id)
  have hb : ∀ᵐ u : UnitAddCircle ∂circleHaar,
      ‖circleSetIndicator A (t-u)‖ ≤ (1 : ℝ) := by
    filter_upwards [] with u
    simpa only [Real.norm_eq_abs] using circleSetIndicator_bound_new A (t-u)
  have hshift : Integrable (fun u : UnitAddCircle =>
      circleSetIndicator A (t-u) * circleFejerKernel R u) circleHaar := by
    simpa only [mul_comm] using hk.mul_bdd hm.aestronglyMeasurable hb
  have hbase : Integrable (fun u : UnitAddCircle =>
      circleSetIndicator A t * circleFejerKernel R u) circleHaar := hk.const_mul _
  simp only [sub_mul, integral_sub hshift hbase, integral_const_mul,
    circleFejerKernel_integral R hR, mul_one]
  rfl

private theorem circleFejerSmoothing_error_pointwise {A : Set UnitAddCircle}
    (hA : MeasurableSet A) (R : ℕ) (hR : 1 ≤ R) (t : UnitAddCircle) :
    |circleFejerSmoothing A R t - circleSetIndicator A t| ≤
      ∫ u : UnitAddCircle,
        |circleSetIndicator A (t-u) - circleSetIndicator A t| *
          circleFejerKernel R u ∂circleHaar := by
  rw [circleFejerSmoothing_difference_eq_integral hA R hR t]
  calc
    |∫ u : UnitAddCircle,
      (circleSetIndicator A (t-u) - circleSetIndicator A t) *
        circleFejerKernel R u ∂circleHaar| ≤
      ∫ u : UnitAddCircle,
        |(circleSetIndicator A (t-u) - circleSetIndicator A t) *
          circleFejerKernel R u| ∂circleHaar := abs_integral_le_integral_abs
    _ = _ := by
      congr 1
      funext u
      rw [abs_mul, abs_of_nonneg (circleFejerKernel_nonneg R hR u)]

private theorem circleFejerSmoothing_error_bound_of_translation {A : Set UnitAddCircle}
    (hA : MeasurableSet A) (L : ℝ) (hL : 0 ≤ L)
    (htrans : ∀ u : UnitAddCircle,
      (∫ t : UnitAddCircle,
        |circleSetIndicator A (t-u) - circleSetIndicator A t| ∂circleHaar) ≤
        L * dist u 0)
    (R : ℕ) (hR : 2 ≤ R) :
    (∫ t : UnitAddCircle,
      |circleFejerSmoothing A R t - circleSetIndicator A t| ∂circleHaar) ≤
      L * (∫ u : UnitAddCircle, dist u 0 * circleFejerKernel R u ∂circleHaar) := by
  have hR1 : 1 ≤ R := by omega
  let f : UnitAddCircle × UnitAddCircle → ℝ := fun p =>
    |circleSetIndicator A (p.1-p.2) - circleSetIndicator A p.1| *
      circleFejerKernel R p.2
  have hf : Integrable f (circleHaar.prod circleHaar) := by
    have h := (circleFejerSmoothing_difference_joint_integrable hA R).abs
    convert h using 1
    funext p
    simp only [f, abs_mul, abs_of_nonneg (circleFejerKernel_nonneg R hR1 p.2)]
  have hleft : Integrable (fun t : UnitAddCircle =>
      |circleFejerSmoothing A R t - circleSetIndicator A t|) circleHaar := by
    exact ((circleFejerSmoothing_integrable hA R).sub
      (circleSetIndicator_integrable_new hA)).abs
  have hright : Integrable (fun t : UnitAddCircle =>
      ∫ u : UnitAddCircle, f (t,u) ∂circleHaar) circleHaar := hf.integral_prod_left
  have hmoment : Integrable (fun u : UnitAddCircle =>
      dist u 0 * circleFejerKernel R u) circleHaar := by
    have hc : Continuous (fun u : UnitAddCircle =>
      dist u 0 * circleFejerKernel R u) := by
      apply Continuous.mul (continuous_id.dist continuous_const)
      unfold circleFejerKernel fejerCharacterSum
      fun_prop
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    (∫ t : UnitAddCircle,
      |circleFejerSmoothing A R t - circleSetIndicator A t| ∂circleHaar) ≤
        ∫ t : UnitAddCircle, ∫ u : UnitAddCircle, f (t,u) ∂circleHaar ∂circleHaar := by
          exact integral_mono hleft hright (fun t =>
            circleFejerSmoothing_error_pointwise hA R hR1 t)
    _ = ∫ u : UnitAddCircle, ∫ t : UnitAddCircle, f (t,u) ∂circleHaar ∂circleHaar :=
      integral_integral_swap hf
    _ ≤ ∫ u : UnitAddCircle,
        L * (dist u 0 * circleFejerKernel R u) ∂circleHaar := by
      apply integral_mono hf.integral_prod_right (hmoment.const_mul L)
      intro u
      change (∫ t : UnitAddCircle,
          |circleSetIndicator A (t-u) - circleSetIndicator A t| *
            circleFejerKernel R u ∂circleHaar) ≤ _
      rw [integral_mul_const]
      simpa only [mul_assoc] using
        (mul_le_mul_of_nonneg_right (htrans u) (circleFejerKernel_nonneg R hR1 u))
    _ = _ := by rw [integral_const_mul]

/-- 论文 `lem:smoothing`：有限闭弧并的 Fejér 平滑误差，绝对常数先于数据选取。 -/
theorem circleArcUnion_fejerSmoothing_error :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} (J : Finset ι) (s ℓ : ι → ℝ)
      (R : ℕ), (∀ j ∈ J, 0 ≤ ℓ j ∧ ℓ j < 1) → 2 ≤ R →
      (∫ t : UnitAddCircle,
        |circleFejerSmoothing (circleArcUnion J s ℓ) R t -
          circleSetIndicator (circleArcUnion J s ℓ) t| ∂circleHaar) ≤
        C * (J.card : ℝ) * Real.log (2 * (R : ℝ)) / (R : ℝ) := by
  obtain ⟨C₀, hC₀, hmoment⟩ := circleFejerKernel_distance_moment_bound
  refine ⟨2*C₀, by positivity, ?_⟩
  intro ι J s ℓ R hℓ hR
  have hA := circleArcUnion_measurable J s ℓ hℓ
  have htrans : ∀ u : UnitAddCircle,
      (∫ t : UnitAddCircle,
        |circleSetIndicator (circleArcUnion J s ℓ) (t-u) -
          circleSetIndicator (circleArcUnion J s ℓ) t| ∂circleHaar) ≤
        (2 * (J.card : ℝ)) * dist u 0 := by
    intro u
    exact circleArcUnion_translation_L1 J s ℓ u hℓ
  have hb := circleFejerSmoothing_error_bound_of_translation hA
    (2 * (J.card : ℝ)) (by positivity) htrans R hR
  have hm := hmoment R hR
  have hJ : 0 ≤ (J.card : ℝ) := by positivity
  have hRpos : 0 < (R : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hR)
  calc
    (∫ t : UnitAddCircle,
      |circleFejerSmoothing (circleArcUnion J s ℓ) R t -
        circleSetIndicator (circleArcUnion J s ℓ) t| ∂circleHaar) ≤
      (2 * (J.card : ℝ)) *
        (∫ u : UnitAddCircle, dist u 0 * circleFejerKernel R u ∂circleHaar) := hb
    _ ≤ (2 * (J.card : ℝ)) *
      (C₀ * Real.log (2 * (R : ℝ)) / (R : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hm (by positivity)
    _ = (2*C₀) * (J.card : ℝ) * Real.log (2 * (R : ℝ)) / (R : ℝ) := by ring

#print axioms circleArcUnion_fejerSmoothing_error
end LonelyRunner
