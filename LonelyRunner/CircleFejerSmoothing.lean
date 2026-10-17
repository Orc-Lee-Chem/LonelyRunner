import LonelyRunner.CircleFourierFinite
import Mathlib.Analysis.Convolution

/- 论文 Fejér 平滑步骤：圆周可测集的有限频率卷积。 -/
namespace LonelyRunner
open MeasureTheory

/-- 论文 `lem:smoothing`：集合 `A` 的实值指标函数。 -/
noncomputable def circleSetIndicator (A : Set UnitAddCircle) : UnitAddCircle → ℝ :=
  A.indicator (fun _ => 1)

private theorem circleSetIndicator_integrable {A : Set UnitAddCircle}
    (hA : MeasurableSet A) : Integrable (circleSetIndicator A) circleHaar := by
  exact (integrable_const (1 : ℝ)).indicator hA

private theorem circleFejerKernel_continuous (R : ℕ) :
    Continuous (circleFejerKernel R) := by
  unfold circleFejerKernel fejerCharacterSum
  fun_prop

private theorem circleFejerKernel_integrable (R : ℕ) :
    Integrable (circleFejerKernel R) circleHaar := by
  exact (circleFejerKernel_continuous R).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- 论文 Fejér 平滑步骤：用已证明的 Fejér 核对可测集合指标函数作卷积。 -/
noncomputable def circleFejerSmoothing (A : Set UnitAddCircle) (R : ℕ)
    (t : UnitAddCircle) : ℝ :=
  ∫ u : UnitAddCircle, circleSetIndicator A (t - u) * circleFejerKernel R u ∂circleHaar

private theorem circleFejerSmoothing_eq_convolution (A : Set UnitAddCircle) (R : ℕ) :
    circleFejerSmoothing A R =
      MeasureTheory.convolution (circleSetIndicator A) (circleFejerKernel R)
        (ContinuousLinearMap.mul ℝ ℝ) circleHaar := by
  funext t
  rw [MeasureTheory.convolution_mul_swap]
  unfold circleFejerSmoothing
  rfl

/-- 论文 Fejér 平滑步骤：任意可测集的平滑函数连续。 -/
theorem circleFejerSmoothing_continuous {A : Set UnitAddCircle}
    (hA : MeasurableSet A) (R : ℕ) : Continuous (circleFejerSmoothing A R) := by
  rw [circleFejerSmoothing_eq_convolution]
  have hbd : BddAbove (Set.range fun t : UnitAddCircle =>
      ‖circleFejerKernel R t‖) :=
    (isCompact_range (circleFejerKernel_continuous R).norm).bddAbove
  exact hbd.continuous_convolution_right_of_integrable
    (ContinuousLinearMap.mul ℝ ℝ) (circleSetIndicator_integrable hA)
    (circleFejerKernel_continuous R)

private theorem circleSetIndicator_bounds (A : Set UnitAddCircle) (t : UnitAddCircle) :
    0 ≤ circleSetIndicator A t ∧ circleSetIndicator A t ≤ 1 := by
  by_cases ht : t ∈ A <;> simp [circleSetIndicator, ht]

/-- 论文 Fejér 平滑步骤：平滑函数逐点取值于闭区间 `[0,1]`。 -/
theorem circleFejerSmoothing_bounds {A : Set UnitAddCircle}
    (hA : MeasurableSet A) (R : ℕ) (hR : 1 ≤ R) (t : UnitAddCircle) :
    0 ≤ circleFejerSmoothing A R t ∧ circleFejerSmoothing A R t ≤ 1 := by
  have hker := circleFejerKernel_integrable R
  have hi : Integrable (fun u : UnitAddCircle =>
      circleSetIndicator A (t - u) * circleFejerKernel R u) circleHaar := by
    have hm : Measurable (fun u : UnitAddCircle => circleSetIndicator A (t - u)) := by
      exact (measurable_const.indicator hA).comp (measurable_const.sub measurable_id)
    have hb : ∀ᵐ u : UnitAddCircle ∂circleHaar,
        ‖circleSetIndicator A (t - u)‖ ≤ (1 : ℝ) := by
      filter_upwards [] with u
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [(circleSetIndicator_bounds A (t-u)).1],
        (circleSetIndicator_bounds A (t-u)).2⟩
    simpa only [mul_comm] using hker.mul_bdd hm.aestronglyMeasurable hb
  constructor
  · unfold circleFejerSmoothing
    exact integral_nonneg (fun u => mul_nonneg (circleSetIndicator_bounds A _).1
      (circleFejerKernel_nonneg R hR u))
  · unfold circleFejerSmoothing
    calc
      (∫ u : UnitAddCircle,
        circleSetIndicator A (t - u) * circleFejerKernel R u ∂circleHaar) ≤
          ∫ u : UnitAddCircle, circleFejerKernel R u ∂circleHaar := by
            apply integral_mono hi hker
            intro u
            nlinarith [(circleSetIndicator_bounds A (t-u)).2,
              circleFejerKernel_nonneg R hR u]
      _ = 1 := circleFejerKernel_integral R hR

/-- 论文 Fejér 平滑步骤：Fubini 和 Haar 平移不变性给出积分守恒。 -/
theorem circleFejerSmoothing_integral {A : Set UnitAddCircle}
    (hA : MeasurableSet A) (R : ℕ) (hR : 1 ≤ R) :
    (∫ t : UnitAddCircle, circleFejerSmoothing A R t ∂circleHaar) =
      circleHaar.real A := by
  rw [circleFejerSmoothing_eq_convolution]
  rw [MeasureTheory.integral_convolution (ContinuousLinearMap.mul ℝ ℝ)
      (circleSetIndicator_integrable hA) (circleFejerKernel_integrable R)]
  rw [circleFejerKernel_integral R hR]
  have hind : (∫ t : UnitAddCircle, circleSetIndicator A t ∂circleHaar) =
      circleHaar.real A := by
    exact integral_indicator_one hA
  rw [hind]
  simp

/-- 可测集指标函数的实际 Fourier 积分；采用使卷积展开为正频率的符号约定。 -/
noncomputable def circleSetFourierCoeff (A : Set UnitAddCircle) (k : ℤ) : ℂ :=
  ∫ x : UnitAddCircle, (circleSetIndicator A x : ℂ) * fourier (-k) x ∂circleHaar

/-- 论文 `lem:smoothing` 第 350 行：零频率的实际 Fourier 积分等于集合测度。 -/
theorem circleSetFourierCoeff_zero {A : Set UnitAddCircle}
    (hA : MeasurableSet A) : circleSetFourierCoeff A 0 = circleHaar.real A := by
  unfold circleSetFourierCoeff
  simp only [neg_zero, fourier_zero, mul_one]
  rw [integral_complex_ofReal]
  exact_mod_cast integral_indicator_one hA

private theorem circleSetIndicator_complex_measurable {A : Set UnitAddCircle}
    (hA : MeasurableSet A) :
    Measurable (fun x : UnitAddCircle => (circleSetIndicator A x : ℂ)) := by
  exact Complex.measurable_ofReal.comp (measurable_const.indicator hA)

private theorem circleSetIndicatorFourierShift_integrable {A : Set UnitAddCircle}
    (hA : MeasurableSet A) (k : ℤ) (t : UnitAddCircle) :
    Integrable (fun u : UnitAddCircle =>
      (circleSetIndicator A (t-u) : ℂ) * fourier k u) circleHaar := by
  have hm : Measurable (fun u : UnitAddCircle =>
      (circleSetIndicator A (t-u) : ℂ)) :=
    (circleSetIndicator_complex_measurable hA).comp (measurable_const.sub measurable_id)
  have hb : ∀ᵐ u : UnitAddCircle ∂circleHaar,
      ‖(circleSetIndicator A (t-u) : ℂ)‖ ≤ (1 : ℝ) := by
    filter_upwards [] with u
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [(circleSetIndicator_bounds A (t-u)).1],
      (circleSetIndicator_bounds A (t-u)).2⟩
  exact (circleFourier_integrable k).bdd_mul hm.aestronglyMeasurable hb

private theorem circleSetIndicatorFourier_integrable {A : Set UnitAddCircle}
    (hA : MeasurableSet A) (k : ℤ) :
    Integrable (fun x : UnitAddCircle =>
      (circleSetIndicator A x : ℂ) * fourier k x) circleHaar := by
  have hm := circleSetIndicator_complex_measurable hA
  have hb : ∀ᵐ x : UnitAddCircle ∂circleHaar,
      ‖(circleSetIndicator A x : ℂ)‖ ≤ (1 : ℝ) := by
    filter_upwards [] with x
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [(circleSetIndicator_bounds A x).1],
      (circleSetIndicator_bounds A x).2⟩
  exact (circleFourier_integrable k).bdd_mul hm.aestronglyMeasurable hb

private theorem circleSetIndicatorFourierShift_integral {A : Set UnitAddCircle}
    (_hA : MeasurableSet A) (k : ℤ) (t : UnitAddCircle) :
    (∫ u : UnitAddCircle,
      (circleSetIndicator A (t-u) : ℂ) * fourier k u ∂circleHaar) =
      fourier k t * circleSetFourierCoeff A k := by
  let g : UnitAddCircle → ℂ := fun x =>
    (circleSetIndicator A x : ℂ) * fourier k (t-x)
  have hsubst := integral_sub_left_eq_self g circleHaar t
  have hlhs : (∫ u : UnitAddCircle,
      (circleSetIndicator A (t-u) : ℂ) * fourier k u ∂circleHaar) =
      ∫ x : UnitAddCircle, g x ∂circleHaar := by
    calc
      _ = ∫ u : UnitAddCircle, g (t-u) ∂circleHaar := by
        congr 1
        funext u
        simp [g]
      _ = _ := hsubst
  rw [hlhs]
  have hfour (x : UnitAddCircle) :
      fourier k (t-x) = fourier k t * fourier (-k) x := by
    rw [sub_eq_add_neg]
    change fourier k (t + -x) = fourier k t * fourier (-k) x
    simp only [fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul,
      zsmul_neg, neg_zsmul]
  simp_rw [g, hfour]
  have heq (x : UnitAddCircle) :
      (circleSetIndicator A x : ℂ) * (fourier k t * fourier (-k) x) =
      fourier k t * ((circleSetIndicator A x : ℂ) * fourier (-k) x) := by ring
  simp_rw [heq]
  rw [integral_const_mul]
  unfold circleSetFourierCoeff
  rfl

private theorem circleFejerSmoothing_complex (A : Set UnitAddCircle)
    (R : ℕ) (t : UnitAddCircle) :
    (circleFejerSmoothing A R t : ℂ) =
      ∫ u : UnitAddCircle,
        (circleSetIndicator A (t-u) : ℂ) * (circleFejerKernel R u : ℂ) ∂circleHaar := by
  unfold circleFejerSmoothing
  calc
    (↑(∫ u : UnitAddCircle,
      circleSetIndicator A (t-u) * circleFejerKernel R u ∂circleHaar) : ℂ) =
        ∫ u : UnitAddCircle,
          ((circleSetIndicator A (t-u) * circleFejerKernel R u : ℝ) : ℂ) ∂circleHaar := by
            rw [integral_complex_ofReal]
    _ = _ := by simp only [Complex.ofReal_mul]

/-- 论文 Fejér 平滑步骤：平滑结果的有限 Fourier 展开，系数来自集合指标函数的实际积分。 -/
theorem circleFejerSmoothing_finiteExpansion {A : Set UnitAddCircle}
    (hA : MeasurableSet A) (R : ℕ) (hR : 1 ≤ R) (t : UnitAddCircle) :
    (circleFejerSmoothing A R t : ℂ) =
      (circleHaar.real A : ℂ) +
      (∑ j ∈ Finset.range (R-1),
        ((circleFejerCoefficient R ((j+1 : ℕ) : ℤ) : ℂ) *
          circleSetFourierCoeff A ((j+1 : ℕ) : ℤ)) *
          fourier ((j+1 : ℕ) : ℤ) t) +
      (∑ j ∈ Finset.range (R-1),
        ((circleFejerCoefficient R (-((j+1 : ℕ) : ℤ)) : ℂ) *
          circleSetFourierCoeff A (-((j+1 : ℕ) : ℤ))) *
          fourier (-((j+1 : ℕ) : ℤ)) t) := by
  rw [circleFejerSmoothing_complex]
  have hN : R-1+1=R := Nat.sub_add_cancel hR
  have hker (u : UnitAddCircle) :
      (circleFejerKernel R u : ℂ) =
        1 +
          (∑ j ∈ Finset.range (R-1),
            (circleFejerCoefficient R ((j+1 : ℕ) : ℤ) : ℂ) *
              fourier ((j+1 : ℕ) : ℤ) u) +
          (∑ j ∈ Finset.range (R-1),
            (circleFejerCoefficient R (-((j+1 : ℕ) : ℤ)) : ℂ) *
              fourier (-((j+1 : ℕ) : ℤ)) u) := by
    simpa only [hN] using circleFejerKernel_expansion_coeff_succ (R-1) u
  simp_rw [hker]
  have hind : Integrable (fun u : UnitAddCircle =>
      (circleSetIndicator A (t-u) : ℂ)) circleHaar := by
    have h := circleSetIndicatorFourierShift_integrable hA 0 t
    simpa only [fourier_zero, mul_one] using h
  have hp (j : ℕ) : Integrable (fun u : UnitAddCircle =>
      (circleFejerCoefficient R ((j+1 : ℕ) : ℤ) : ℂ) *
        ((circleSetIndicator A (t-u) : ℂ) * fourier ((j+1 : ℕ) : ℤ) u))
        circleHaar :=
    (circleSetIndicatorFourierShift_integrable hA _ t).const_mul _
  have hn (j : ℕ) : Integrable (fun u : UnitAddCircle =>
      (circleFejerCoefficient R (-((j+1 : ℕ) : ℤ)) : ℂ) *
        ((circleSetIndicator A (t-u) : ℂ) * fourier (-((j+1 : ℕ) : ℤ)) u))
        circleHaar :=
    (circleSetIndicatorFourierShift_integrable hA _ t).const_mul _
  have hpoint (u : UnitAddCircle) :
      (circleSetIndicator A (t-u) : ℂ) *
        (1 + (∑ j ∈ Finset.range (R-1),
          (circleFejerCoefficient R ((j+1 : ℕ) : ℤ) : ℂ) * fourier ((j+1 : ℕ) : ℤ) u) +
          (∑ j ∈ Finset.range (R-1),
          (circleFejerCoefficient R (-((j+1 : ℕ) : ℤ)) : ℂ) * fourier (-((j+1 : ℕ) : ℤ)) u)) =
      (circleSetIndicator A (t-u) : ℂ) +
        (∑ j ∈ Finset.range (R-1),
          (circleFejerCoefficient R ((j+1 : ℕ) : ℤ) : ℂ) *
            ((circleSetIndicator A (t-u) : ℂ) * fourier ((j+1 : ℕ) : ℤ) u)) +
        (∑ j ∈ Finset.range (R-1),
          (circleFejerCoefficient R (-((j+1 : ℕ) : ℤ)) : ℂ) *
            ((circleSetIndicator A (t-u) : ℂ) * fourier (-((j+1 : ℕ) : ℤ)) u)) := by
    have hp' : (circleSetIndicator A (t-u) : ℂ) *
        (∑ j ∈ Finset.range (R-1),
          (circleFejerCoefficient R ((j+1 : ℕ) : ℤ) : ℂ) * fourier ((j+1 : ℕ) : ℤ) u) =
        ∑ j ∈ Finset.range (R-1),
          (circleFejerCoefficient R ((j+1 : ℕ) : ℤ) : ℂ) *
            ((circleSetIndicator A (t-u) : ℂ) * fourier ((j+1 : ℕ) : ℤ) u) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    have hn' : (circleSetIndicator A (t-u) : ℂ) *
        (∑ j ∈ Finset.range (R-1),
          (circleFejerCoefficient R (-((j+1 : ℕ) : ℤ)) : ℂ) * fourier (-((j+1 : ℕ) : ℤ)) u) =
        ∑ j ∈ Finset.range (R-1),
          (circleFejerCoefficient R (-((j+1 : ℕ) : ℤ)) : ℂ) *
            ((circleSetIndicator A (t-u) : ℂ) * fourier (-((j+1 : ℕ) : ℤ)) u) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [mul_add, mul_add, mul_one, hp', hn']
  simp_rw [hpoint]
  rw [integral_add, integral_add]
  · rw [integral_finsetSum _ (fun j hj => hp j),
      integral_finsetSum _ (fun j hj => hn j)]
    have hzero := circleSetIndicatorFourierShift_integral hA 0 t
    simp only [fourier_zero, mul_one, one_mul] at hzero
    rw [hzero, circleSetFourierCoeff_zero hA]
    simp_rw [integral_const_mul,
      circleSetIndicatorFourierShift_integral hA]
    apply congrArg₂ (fun p n : ℂ => (circleHaar.real A : ℂ) + p + n)
    · apply Finset.sum_congr rfl
      intro j hj
      ring
    · apply Finset.sum_congr rfl
      intro j hj
      ring
  · exact hind
  · exact integrable_finsetSum _ (fun j hj => hp j)
  · exact hind.add (integrable_finsetSum _ (fun j hj => hp j))
  · exact integrable_finsetSum _ (fun j hj => hn j)

/-- 论文 `lem:smoothing` 第 339–350 行：卷积的双变量被积函数联合可测。 -/
theorem circleFejerSmoothing_joint_measurable {A : Set UnitAddCircle}
    (hA : MeasurableSet A) (R : ℕ) :
    Measurable (fun p : UnitAddCircle × UnitAddCircle =>
      circleSetIndicator A (p.1-p.2) * circleFejerKernel R p.2) := by
  exact ((measurable_const.indicator hA).comp
    (measurable_fst.sub measurable_snd)).mul
    ((circleFejerKernel_continuous R).measurable.comp measurable_snd)

/-- 论文 `lem:smoothing` 第 339–350 行：联合被积函数在乘积 Haar 测度下可积。 -/
theorem circleFejerSmoothing_joint_integrable {A : Set UnitAddCircle}
    (hA : MeasurableSet A) (R : ℕ) :
    Integrable (fun p : UnitAddCircle × UnitAddCircle =>
      circleSetIndicator A (p.1-p.2) * circleFejerKernel R p.2)
      (circleHaar.prod circleHaar) := by
  have h := (circleFejerKernel_integrable R).convolution_integrand
    (ContinuousLinearMap.mul ℝ ℝ) (circleSetIndicator_integrable hA)
  convert h using 1 with p
  exact mul_comm _ _

/-- 论文 `lem:smoothing` 第 339–350 行：Fejér 平滑函数本身可积。 -/
theorem circleFejerSmoothing_integrable {A : Set UnitAddCircle}
    (hA : MeasurableSet A) (R : ℕ) :
    Integrable (circleFejerSmoothing A R) circleHaar := by
  exact (circleFejerSmoothing_continuous hA R).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- 论文 `lem:smoothing` 第 350 行：有限展开中正负频率严格满足 `|k|<R`。 -/
theorem circleFejerSmoothing_frequency_range (R j : ℕ)
    (hj : j ∈ Finset.range (R - 1)) :
    Int.natAbs ((j+1 : ℕ) : ℤ) < R ∧
      Int.natAbs (-((j+1 : ℕ) : ℤ)) < R := by
  have h : j+1 < R := by
    have := Finset.mem_range.mp hj
    omega
  simpa only [← Nat.cast_add, Int.natAbs_natCast,
    Int.natAbs_neg] using And.intro h h

end LonelyRunner
