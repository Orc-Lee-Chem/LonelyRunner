import LonelyRunner.CircleFourierFinite
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.PSeries

/-! 论文 `paper/lonely_runner_zh.tex` 的 `lem:pair`：圆周三角形函数。 -/

namespace LonelyRunner

open Metric MeasureTheory

/-- 论文 `lem:pair`：在 `UnitAddCircle` 上取距离到零的线性帐篷函数。 -/
noncomputable def circleTent (δ : ℝ) (t : UnitAddCircle) : ℝ :=
  max (1 - dist t 0 / δ) 0

/-- 论文 `lem:pair`：`δ>0` 时帐篷函数连续。 -/
theorem circleTent_continuous (δ : ℝ) : Continuous (circleTent δ) := by
  unfold circleTent
  fun_prop

/-- 论文 `lem:pair`：帐篷函数非负。 -/
theorem circleTent_nonneg (δ : ℝ) (t : UnitAddCircle) :
    0 ≤ circleTent δ t := by
  simp [circleTent]

/-- 论文 `lem:pair`：帐篷函数是偶函数。 -/
theorem circleTent_neg (δ : ℝ) (t : UnitAddCircle) :
    circleTent δ (-t) = circleTent δ t := by
  simp [circleTent, dist_zero_right]

/-- 论文 `lem:pair`：帐篷函数至多为一。 -/
theorem circleTent_le_one (δ : ℝ) (hδ : 0 < δ) (t : UnitAddCircle) :
    circleTent δ t ≤ 1 := by
  have hdiv : 0 ≤ dist t 0 / δ := div_nonneg dist_nonneg hδ.le
  simp only [circleTent, max_le_iff]
  constructor <;> linarith

/-- 论文 `lem:pair`：超出半径 `δ` 后帐篷函数为零。 -/
theorem circleTent_eq_zero_of_dist_gt (δ : ℝ) (hδ : 0 < δ)
    (t : UnitAddCircle) (ht : δ < dist t 0) :
    circleTent δ t = 0 := by
  have hdiv : 1 < dist t 0 / δ := (lt_div_iff₀ hδ).2 (by simpa using ht)
  unfold circleTent
  exact max_eq_right (by linarith)

/-- 论文 `lem:pair`：帐篷函数在闭支撑边界也为零。 -/
theorem circleTent_eq_zero_of_dist_ge (δ : ℝ) (hδ : 0 < δ)
    (t : UnitAddCircle) (ht : δ ≤ dist t 0) :
    circleTent δ t = 0 := by
  have hdiv : 1 ≤ dist t 0 / δ := (le_div_iff₀ hδ).2 (by simpa using ht)
  unfold circleTent
  exact max_eq_right (by linarith)

/-- 论文 `lem:pair`：帐篷函数逐点受原闭球指示函数控制，端点值为零。 -/
theorem circleTent_le_closedBall_indicator (δ : ℝ) (hδ : 0 < δ)
    (t : UnitAddCircle) :
    circleTent δ t ≤ (if dist t 0 ≤ δ then (1 : ℝ) else 0) := by
  by_cases ht : dist t 0 ≤ δ
  · rw [dist_zero_right] at ht ⊢
    simpa [ht] using circleTent_le_one δ hδ t
  · have hzero := circleTent_eq_zero_of_dist_gt δ hδ t (lt_of_not_ge ht)
    rw [dist_zero_right] at ht ⊢
    simp [ht, hzero]

/-- 论文 `lem:pair`：原闭弧与闭球在端点 `δ=1/2` 仍相同。 -/
theorem closedArc_symm_eq_closedBall_le_half (δ : ℝ) (_hδ0 : 0 ≤ δ)
    (hδhalf : δ ≤ 1 / 2) :
    closedArc (-δ) (2 * δ) = closedBall (0 : UnitAddCircle) δ := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, ⟨hylo, hyhi⟩, rfl⟩ := hx
    have hyhi' : y ≤ δ := by linarith
    have habs : |y| ≤ δ := abs_le.mpr ⟨hylo, hyhi'⟩
    have hhalf : |y| ≤ |(1 : ℝ)| / 2 := by
      rw [abs_one]
      linarith
    have hnorm : ‖(y : UnitAddCircle)‖ = |y| :=
      (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).2 hhalf
    simpa only [mem_closedBall, dist_zero_right, hnorm] using habs
  · intro hx
    induction x using Quotient.inductionOn with
    | _ z =>
      let y : ℝ := z - (round z : ℝ)
      have hnorm : ‖(z : UnitAddCircle)‖ = |y| := by
        simpa [y] using (AddCircle.norm_eq (1 : ℝ) (x := z))
      have habs : |y| ≤ δ := by
        simpa only [mem_closedBall, dist_zero_right, hnorm] using hx
      have hcast : (y : UnitAddCircle) = (z : UnitAddCircle) := by
        have hint : (((round z : ℤ) : ℝ) : UnitAddCircle) = 0 := by
          apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).2
          refine ⟨round z, ?_⟩
          simp [zsmul_eq_mul]
        simp [y, hint]
      change (z : UnitAddCircle) ∈ closedArc (-δ) (2 * δ)
      refine ⟨y, ?_, hcast⟩
      change -δ ≤ y ∧ y ≤ -δ + 2 * δ
      rcases abs_le.mp habs with ⟨hlo, hhi⟩
      constructor <;> linarith

/-- 论文 `lem:pair`：包括 `δ=1/2` 的原 Bohr 闭弧成员条件。 -/
theorem mem_bohrSet_iff_dist_le_half (v : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδhalf : δ ≤ 1 / 2) (t : UnitAddCircle) :
    t ∈ bohrSet v δ ↔ dist (v • t) 0 ≤ δ := by
  rw [bohrSet, closedArc_symm_eq_closedBall_le_half δ hδ0 hδhalf]
  simp only [Set.mem_ofPred_eq, mem_closedBall]

/-- 论文 `lem:pair`：真实圆周 Fourier 系数；后续公式须对此运算证明。 -/
noncomputable def circleTentFourierCoeff (δ : ℝ) (k : ℤ) : ℂ :=
  fourierCoeff (fun t : UnitAddCircle => (circleTent δ t : ℂ)) k

/-- 论文 `lem:pair`：在基本域 `[-1/2,1/2]` 上，圆周距离等于实数绝对值。 -/
theorem circleTent_coe_of_abs_le_half (δ x : ℝ) (hx : |x| ≤ 1 / 2) :
    circleTent δ (x : UnitAddCircle) = max (1 - |x| / δ) 0 := by
  have hnorm : dist (x : UnitAddCircle) 0 = |x| := by
    rw [dist_zero_right]
    exact (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).2 (by simpa using hx)
  simp [circleTent, hnorm]

/-- 论文 `lem:pair`：圆周帐篷函数的质量为 `δ`。 -/
theorem circleTent_integral (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    (∫ t : UnitAddCircle, circleTent δ t ∂circleHaar) = δ := by
  let f : ℝ → ℝ := fun x => circleTent δ (x : UnitAddCircle)
  have hf : Continuous f :=
    (circleTent_continuous δ).comp (AddCircle.continuous_mk' 1)
  have h_even (x : ℝ) : f (-x) = f x := by
    simp [f, circleTent, dist_zero_right]
  have hzero (x : ℝ) (hx : x ∈ Set.Icc δ (1 / 2)) : f x = 0 := by
    have hx0 : 0 ≤ x := le_trans hδ.le hx.1
    have habs : |x| ≤ 1 / 2 := by simpa [abs_of_nonneg hx0] using hx.2
    rw [show f x = circleTent δ (x : UnitAddCircle) from rfl,
      circleTent_coe_of_abs_le_half δ x habs, abs_of_nonneg hx0]
    rw [max_eq_right]
    have hdiv : 1 ≤ x / δ := (le_div_iff₀ hδ).2 (by simpa using hx.1)
    linarith
  have hlin (x : ℝ) (hx : x ∈ Set.Icc 0 δ) : f x = 1 - x / δ := by
    have habs : |x| ≤ 1 / 2 := by simpa [abs_of_nonneg hx.1] using hx.2.trans hδhalf
    rw [show f x = circleTent δ (x : UnitAddCircle) from rfl,
      circleTent_coe_of_abs_le_half δ x habs, abs_of_nonneg hx.1]
    rw [max_eq_left]
    have hdiv : x / δ ≤ 1 := (div_le_iff₀ hδ).2 (by simpa using hx.2)
    linarith
  have hhalfint : (∫ x in (0 : ℝ)..1 / 2, f x) = δ / 2 := by
    calc
      _ = (∫ x in (0 : ℝ)..δ, f x) + ∫ x in δ..1 / 2, f x :=
        (intervalIntegral.integral_add_adjacent_intervals
          (hf.intervalIntegrable 0 δ) (hf.intervalIntegrable δ (1 / 2))).symm
      _ = (∫ x in (0 : ℝ)..δ, (1 - x / δ : ℝ)) + ∫ x in δ..1 / 2, (0 : ℝ) := by
        have hlin' : Set.EqOn f (fun x : ℝ => 1 - x / δ) (Set.uIcc 0 δ) := by
          intro x hx
          exact hlin x (by simpa only [Set.uIcc_of_le hδ.le] using hx)
        have hzero' : Set.EqOn f (fun _ : ℝ => 0) (Set.uIcc δ (1 / 2)) := by
          intro x hx
          exact hzero x (by simpa only [Set.uIcc_of_le hδhalf] using hx)
        rw [intervalIntegral.integral_congr hlin', intervalIntegral.integral_congr hzero']
      _ = δ / 2 := by
        rw [intervalIntegral.integral_sub]
        · simp_rw [div_eq_mul_inv]
          rw [integral_one, intervalIntegral.integral_mul_const, integral_id]
          simp
          field_simp
          ring
        · exact intervalIntegrable_const
        · exact (continuous_id.div_const δ).intervalIntegrable _ _
  have hnegeq : (∫ x in (-1 / 2 : ℝ)..0, f x) =
      ∫ x in (0 : ℝ)..1 / 2, f x := by
    calc
      _ = ∫ x in (0 : ℝ)..1 / 2, f (-x) := by
        rw [intervalIntegral.integral_comp_neg]
        norm_num
      _ = _ := by simp only [h_even]
  calc
    (∫ t : UnitAddCircle, circleTent δ t ∂circleHaar) =
        ∫ x in (-1 / 2 : ℝ)..1 / 2, f x := by
      rw [circleHaar_eq_volume]
      have hpre := (UnitAddCircle.intervalIntegral_preimage
        (-1 / 2 : ℝ) (circleTent δ)).symm
      have hend : (-1 / 2 : ℝ) + 1 = 1 / 2 := by ring
      simpa only [hend, f] using hpre
    _ = (∫ x in (-1 / 2 : ℝ)..0, f x) + ∫ x in (0 : ℝ)..1 / 2, f x :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hf.intervalIntegrable (-1 / 2) 0) (hf.intervalIntegrable 0 (1 / 2))).symm
    _ = δ := by rw [hnegeq, hhalfint]; ring

/-- 论文 `lem:pair` 的 `k=0` 情形：真实 Fourier 系数等于帐篷面积 `δ`。 -/
theorem circleTent_fourierCoeff_zero (δ : ℝ) (hδ : 0 < δ)
    (hδhalf : δ ≤ 1 / 2) : circleTentFourierCoeff δ 0 = (δ : ℂ) := by
  unfold circleTentFourierCoeff fourierCoeff
  simp only [neg_zero, fourier_zero, one_smul]
  change (∫ t : UnitAddCircle, (circleTent δ t : ℂ) ∂circleHaar) = (δ : ℂ)
  rw [integral_complex_ofReal, circleTent_integral δ hδ hδhalf]

private theorem tent_integral_linear_exp (δ : ℝ) (hδ : 0 < δ)
    (z : ℂ) (hz : z ≠ 0) :
    (∫ x in (0 : ℝ)..δ,
      (1 - (x : ℂ) / (δ : ℂ)) * Complex.exp (z * (x : ℂ))) =
      (Complex.exp (z * (δ : ℂ)) - 1) / ((δ : ℂ) * z ^ 2) - 1 / z := by
  have hδC : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hδ.ne'
  let F : ℂ → ℂ := fun y =>
    Complex.exp (z * y) *
      ((1 - y / (δ : ℂ)) / z + 1 / ((δ : ℂ) * z ^ 2))
  have hF (x : ℂ) : HasDerivAt F
      ((1 - x / (δ : ℂ)) * Complex.exp (z * x)) x := by
    have harg : HasDerivAt (fun y : ℂ => z * y) z x := by
      simpa using (hasDerivAt_id x).const_mul z
    have hexp : HasDerivAt (fun y : ℂ => Complex.exp (z * y))
        (Complex.exp (z * x) * z) x := by
      simpa only [Function.comp_def] using (Complex.hasDerivAt_exp (z * x)).comp x harg
    have hlin : HasDerivAt (fun y : ℂ =>
        (1 - y / (δ : ℂ)) / z + 1 / ((δ : ℂ) * z ^ 2))
        (-1 / ((δ : ℂ) * z)) x := by
      convert (((hasDerivAt_id x).div_const (δ : ℂ)).const_sub 1).div_const z |>.add_const
        (1 / ((δ : ℂ) * z ^ 2)) using 1
      · funext y
        simp only [id_eq]
      · field_simp
    convert hexp.mul hlin using 1 <;> field_simp <;> ring
  have hreal (x : ℝ) : HasDerivAt (fun y : ℝ => F (y : ℂ))
      ((1 - (x : ℂ) / (δ : ℂ)) * Complex.exp (z * (x : ℂ))) x :=
    (hF x).comp_ofReal
  have hint : IntervalIntegrable
      (fun x : ℝ => (1 - (x : ℂ) / (δ : ℂ)) * Complex.exp (z * (x : ℂ)))
      volume 0 δ := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hreal x) hint
  simp only [F, Complex.ofReal_zero, mul_zero, sub_zero,
    Complex.exp_zero, one_mul, zero_div, sub_zero] at hfund
  rw [hfund]
  field_simp
  ring

private noncomputable def tentPhase (k : ℤ) : ℂ :=
  -2 * (Real.pi : ℂ) * Complex.I * (k : ℂ)

private theorem tentPhase_ne_zero (k : ℤ) (hk : k ≠ 0) : tentPhase k ≠ 0 := by
  simp [tentPhase, hk, Real.pi_ne_zero]

private theorem fourier_neg_eq_exp_tentPhase (k : ℤ) (x : ℝ) :
    fourier (-k) (x : UnitAddCircle) =
      Complex.exp (tentPhase k * (x : ℂ)) := by
  rw [fourier_coe_apply]
  congr 1
  simp only [tentPhase]
  push_cast
  ring

/-- 论文 `lem:pair`：真实 Fourier 系数可按基本域积分计算。 -/
theorem circleTent_fourierCoeff_eq_intervalIntegral (δ : ℝ) (k : ℤ) :
    circleTentFourierCoeff δ k =
      ∫ x in (-1 / 2 : ℝ)..1 / 2,
        fourier (-k) (x : UnitAddCircle) * (circleTent δ (x : UnitAddCircle) : ℂ) := by
  unfold circleTentFourierCoeff
  rw [fourierCoeff_eq_intervalIntegral (a := (-1 / 2 : ℝ))]
  norm_num [smul_eq_mul]

private theorem tent_exp_trig (θ : ℝ) :
    Complex.exp (((-2 * θ : ℝ) : ℂ) * Complex.I) +
      Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I) - 2 =
        -4 * (Real.sin θ : ℂ) ^ 2 := by
  rw [Complex.exp_mul_I, Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hc : Real.cos (-2 * θ) = Real.cos (2 * θ) := by
    simpa only [neg_mul] using Real.cos_neg (2 * θ)
  have hs : Real.sin (-2 * θ) = -Real.sin (2 * θ) := by
    simpa only [neg_mul] using Real.sin_neg (2 * θ)
  rw [hc, hs, Real.cos_two_mul]
  have htrigC : (Real.sin θ : ℂ) ^ 2 + (Real.cos θ : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq θ
  push_cast
  simp only [Complex.ofReal_sin, Complex.ofReal_cos] at htrigC ⊢
  ring_nf at htrigC ⊢
  linear_combination 4 * htrigC

private theorem circleTent_fourierCoeff_eq_two_integrals (δ : ℝ)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (k : ℤ) :
    circleTentFourierCoeff δ k =
      (∫ x in (0 : ℝ)..δ,
        (1 - (x : ℂ) / (δ : ℂ)) * Complex.exp (tentPhase k * (x : ℂ))) +
      (∫ x in (0 : ℝ)..δ,
        (1 - (x : ℂ) / (δ : ℂ)) * Complex.exp (-tentPhase k * (x : ℂ))) := by
  let f : ℝ → ℂ := fun x =>
    fourier (-k) (x : UnitAddCircle) * (circleTent δ (x : UnitAddCircle) : ℂ)
  have hf : Continuous f := by
    unfold f
    have hcoe : Continuous (fun x : ℝ => (x : UnitAddCircle)) :=
      AddCircle.continuous_mk' 1
    exact ((map_continuous (fourier (-k))).comp hcoe).mul
      ((Complex.continuous_ofReal.comp (circleTent_continuous δ)).comp hcoe)
  have hpos (x : ℝ) (hx : x ∈ Set.Icc 0 δ) :
      f x = (1 - (x : ℂ) / (δ : ℂ)) *
        Complex.exp (tentPhase k * (x : ℂ)) := by
    have habs : |x| ≤ 1 / 2 := by
      simpa [abs_of_nonneg hx.1] using hx.2.trans hδhalf
    have hlin : circleTent δ (x : UnitAddCircle) = 1 - x / δ := by
      rw [circleTent_coe_of_abs_le_half δ x habs, abs_of_nonneg hx.1]
      rw [max_eq_left]
      have hdiv : x / δ ≤ 1 := (div_le_iff₀ hδ).2 (by simpa using hx.2)
      linarith
    simp only [f, hlin, fourier_neg_eq_exp_tentPhase,
      Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_div]
    ring
  have hneg (x : ℝ) (hx : x ∈ Set.Icc 0 δ) :
      f (-x) = (1 - (x : ℂ) / (δ : ℂ)) *
        Complex.exp (-tentPhase k * (x : ℂ)) := by
    have ht : circleTent δ ((-x : ℝ) : UnitAddCircle) =
        circleTent δ (x : UnitAddCircle) := by
      simpa using circleTent_neg δ (x : UnitAddCircle)
    have hp := hpos x hx
    have hlin : circleTent δ (x : UnitAddCircle) = 1 - x / δ := by
      have habs : |x| ≤ 1 / 2 := by
        simpa [abs_of_nonneg hx.1] using hx.2.trans hδhalf
      rw [circleTent_coe_of_abs_le_half δ x habs, abs_of_nonneg hx.1]
      rw [max_eq_left]
      have hdiv : x / δ ≤ 1 := (div_le_iff₀ hδ).2 (by simpa using hx.2)
      linarith
    simp only [f, ht, hlin, fourier_neg_eq_exp_tentPhase,
      Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_div,
      Complex.ofReal_neg, neg_mul]
    ring
  have houtpos (x : ℝ) (hx : x ∈ Set.Icc δ (1 / 2)) : f x = 0 := by
    have hx0 : 0 ≤ x := le_trans hδ.le hx.1
    have habs : |x| ≤ 1 / 2 := by simpa [abs_of_nonneg hx0] using hx.2
    have ht : circleTent δ (x : UnitAddCircle) = 0 := by
      rw [circleTent_coe_of_abs_le_half δ x habs, abs_of_nonneg hx0]
      rw [max_eq_right]
      have hdiv : 1 ≤ x / δ := (le_div_iff₀ hδ).2 (by simpa using hx.1)
      linarith
    simp [f, ht]
  have houtneg (x : ℝ) (hx : x ∈ Set.Icc (-1 / 2) (-δ)) : f x = 0 := by
    have hx0 : x ≤ 0 := le_trans hx.2 (by linarith)
    have habs : |x| ≤ 1 / 2 := by
      rw [abs_of_nonpos hx0]
      linarith [hx.1]
    have ht : circleTent δ (x : UnitAddCircle) = 0 := by
      rw [circleTent_coe_of_abs_le_half δ x habs, abs_of_nonpos hx0]
      rw [max_eq_right]
      have hdiv : 1 ≤ -x / δ := (le_div_iff₀ hδ).2 (by linarith [hx.2])
      linarith
    simp [f, ht]
  have hzero_pos : (∫ x in δ..1 / 2, f x) = 0 := by
    have heq : Set.EqOn f (fun _ : ℝ => (0 : ℂ)) (Set.uIcc δ (1 / 2)) := by
      intro x hx
      exact houtpos x (by simpa only [Set.uIcc_of_le hδhalf] using hx)
    rw [intervalIntegral.integral_congr heq]
    simp
  have hzero_neg : (∫ x in (-1 / 2 : ℝ)..-δ, f x) = 0 := by
    have heq : Set.EqOn f (fun _ : ℝ => (0 : ℂ)) (Set.uIcc (-1 / 2) (-δ)) := by
      intro x hx
      exact houtneg x (by simpa only [Set.uIcc_of_le (by linarith : (-1/2:ℝ) ≤ -δ)] using hx)
    rw [intervalIntegral.integral_congr heq]
    simp
  have hmidpos : (∫ x in (0 : ℝ)..δ, f x) =
      ∫ x in (0 : ℝ)..δ,
        (1 - (x : ℂ) / (δ : ℂ)) * Complex.exp (tentPhase k * (x : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact hpos x (by simpa only [Set.uIcc_of_le hδ.le] using hx)
  have hmidneg : (∫ x in -δ..(0 : ℝ), f x) =
      ∫ x in (0 : ℝ)..δ,
        (1 - (x : ℂ) / (δ : ℂ)) * Complex.exp (-tentPhase k * (x : ℂ)) := by
    calc
      _ = ∫ x in (0 : ℝ)..δ, f (-x) := by
        rw [intervalIntegral.integral_comp_neg]
        simp
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact hneg x (by simpa only [Set.uIcc_of_le hδ.le] using hx)
  rw [circleTent_fourierCoeff_eq_intervalIntegral]
  change (∫ x in (-1 / 2 : ℝ)..1 / 2, f x) = _
  calc
    _ = (∫ x in (-1 / 2 : ℝ)..0, f x) + ∫ x in (0 : ℝ)..1 / 2, f x :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hf.intervalIntegrable (-1 / 2) 0) (hf.intervalIntegrable 0 (1 / 2))).symm
    _ = ((∫ x in (-1 / 2 : ℝ)..-δ, f x) + ∫ x in -δ..0, f x) +
        ((∫ x in (0 : ℝ)..δ, f x) + ∫ x in δ..1 / 2, f x) := by
      rw [intervalIntegral.integral_add_adjacent_intervals
        (hf.intervalIntegrable (-1 / 2) (-δ)) (hf.intervalIntegrable (-δ) 0),
        intervalIntegral.integral_add_adjacent_intervals
          (hf.intervalIntegrable 0 δ) (hf.intervalIntegrable δ (1 / 2))]
    _ = _ := by rw [hzero_neg, hzero_pos, hmidneg, hmidpos]; ring

/-- 论文 `lem:pair`、式 `eq:tentcoeff`：非零频率的真实圆周 Fourier 系数。 -/
theorem circleTent_fourierCoeff_nonzero (δ : ℝ) (hδ : 0 < δ)
    (hδhalf : δ ≤ 1 / 2) (k : ℤ) (hk : k ≠ 0) :
    circleTentFourierCoeff δ k =
      ((Real.sin (Real.pi * (k : ℝ) * δ) ^ 2 /
        (δ * Real.pi ^ 2 * (k : ℝ) ^ 2) : ℝ) : ℂ) := by
  let z := tentPhase k
  let θ : ℝ := Real.pi * (k : ℝ) * δ
  have hz : z ≠ 0 := tentPhase_ne_zero k hk
  have hδC : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hδ.ne'
  have harg : z * (δ : ℂ) = (((-2 * θ : ℝ) : ℂ) * Complex.I) := by
    dsimp [z, tentPhase, θ]
    push_cast
    ring
  have hargneg : (-z) * (δ : ℂ) = (((2 * θ : ℝ) : ℂ) * Complex.I) := by
    dsimp [z, tentPhase, θ]
    push_cast
    ring
  have hzsq : z ^ 2 = -4 * (Real.pi : ℂ) ^ 2 * (k : ℂ) ^ 2 := by
    dsimp [z, tentPhase]
    ring_nf
    simp only [Complex.I_sq]
    ring
  calc
    circleTentFourierCoeff δ k =
        ((Complex.exp (z * (δ : ℂ)) - 1) / ((δ : ℂ) * z ^ 2) - 1 / z) +
        ((Complex.exp ((-z) * (δ : ℂ)) - 1) / ((δ : ℂ) * (-z) ^ 2) - 1 / (-z)) := by
      rw [circleTent_fourierCoeff_eq_two_integrals δ hδ hδhalf k,
        tent_integral_linear_exp δ hδ z hz,
        tent_integral_linear_exp δ hδ (-z) (neg_ne_zero.mpr hz)]
    _ = (Complex.exp (z * (δ : ℂ)) +
          Complex.exp ((-z) * (δ : ℂ)) - 2) / ((δ : ℂ) * z ^ 2) := by
      field_simp
      ring
    _ = ((Real.sin θ : ℂ) ^ 2) /
          ((δ : ℂ) * (Real.pi : ℂ) ^ 2 * (k : ℂ) ^ 2) := by
      rw [harg, hargneg, tent_exp_trig θ, hzsq]
      field_simp
    _ = _ := by
      simp only [θ, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow,
        Complex.ofReal_intCast]

/-- 论文 `lem:pair`：实际 Fourier 系数在整数频率上绝对可和。 -/
theorem circleTent_fourierCoeff_summable (δ : ℝ) (hδ : 0 < δ)
    (hδhalf : δ ≤ 1 / 2) : Summable (circleTentFourierCoeff δ) := by
  have hs : Summable (fun k : ℤ =>
      (1 / (δ * Real.pi ^ 2)) * (1 / (k : ℝ) ^ 2)) :=
    (Real.summable_one_div_int_pow.mpr (by norm_num : 1 < (2 : ℕ))).mul_left _
  apply hs.of_norm_bounded_eventually
  filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with k hk
  rw [circleTent_fourierCoeff_nonzero δ hδ hδhalf k hk]
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hden : 0 < δ * Real.pi ^ 2 * (k : ℝ) ^ 2 := by positivity
  have hden0 : 0 < δ * Real.pi ^ 2 := by positivity
  simp only [Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (div_nonneg (sq_nonneg _) hden.le)]
  calc
    Real.sin (Real.pi * (k : ℝ) * δ) ^ 2 /
        (δ * Real.pi ^ 2 * (k : ℝ) ^ 2) ≤
      1 / (δ * Real.pi ^ 2 * (k : ℝ) ^ 2) :=
        div_le_div_of_nonneg_right (Real.sin_sq_le_one _) hden.le
    _ = (1 / (δ * Real.pi ^ 2)) * (1 / (k : ℝ) ^ 2) := by
      field_simp

/-- 论文 `lem:pair`：作为复值连续函数的同一个圆周帐篷。 -/
noncomputable def circleTentContinuousMap (δ : ℝ) : C(UnitAddCircle, ℂ) :=
  ⟨fun t => (circleTent δ t : ℂ),
    Complex.continuous_ofReal.comp (circleTent_continuous δ)⟩

/-- 论文 `lem:pair`：实际 Fourier 级数在连续函数一致范数下收敛到帐篷。
使用 Mathlib 的可和系数反演定理，前提已由显式系数界证明。 -/
theorem circleTent_fourier_hasSum_uniform (δ : ℝ) (hδ : 0 < δ)
    (hδhalf : δ ≤ 1 / 2) :
    HasSum (fun k : ℤ => circleTentFourierCoeff δ k • fourier k)
      (circleTentContinuousMap δ) := by
  have hs : Summable (fourierCoeff (circleTentContinuousMap δ)) := by
    change Summable (circleTentFourierCoeff δ)
    exact circleTent_fourierCoeff_summable δ hδ hδhalf
  have h := hasSum_fourier_series_of_summable (f := circleTentContinuousMap δ) hs
  change HasSum (fun k : ℤ => circleTentFourierCoeff δ k • fourier k)
    (circleTentContinuousMap δ) at h
  exact h

/-- 论文 `lem:pair`：对每个圆周点，Fourier 级数的和恰为帐篷函数。 -/
theorem circleTent_fourier_hasSum_pointwise (δ : ℝ) (hδ : 0 < δ)
    (hδhalf : δ ≤ 1 / 2) (t : UnitAddCircle) :
    HasSum (fun k : ℤ => circleTentFourierCoeff δ k * fourier k t)
      (circleTent δ t : ℂ) := by
  have hs : Summable (fourierCoeff (circleTentContinuousMap δ)) := by
    change Summable (circleTentFourierCoeff δ)
    exact circleTent_fourierCoeff_summable δ hδ hδhalf
  have h := has_pointwise_sum_fourier_series_of_summable
    (f := circleTentContinuousMap δ) hs t
  change HasSum (fun k : ℤ => circleTentFourierCoeff δ k * fourier k t)
    (circleTent δ t : ℂ) at h
  exact h

/-- 论文 `lem:pair`、式 `eq:tentcoeff`：真实 Fourier 系数的实值分段公式。 -/
noncomputable def circleTentRealCoeff (δ : ℝ) (k : ℤ) : ℝ :=
  if k = 0 then δ else
    Real.sin (Real.pi * (k : ℝ) * δ) ^ 2 /
      (δ * Real.pi ^ 2 * (k : ℝ) ^ 2)

/-- 论文 `lem:pair`：上述公式确实等于 `fourierCoeff` 运算。 -/
theorem circleTent_fourierCoeff_eq_real (δ : ℝ) (hδ : 0 < δ)
    (hδhalf : δ ≤ 1 / 2) (k : ℤ) :
    circleTentFourierCoeff δ k = (circleTentRealCoeff δ k : ℂ) := by
  by_cases hk : k = 0
  · subst k
    simpa [circleTentRealCoeff] using circleTent_fourierCoeff_zero δ hδ hδhalf
  · simpa [circleTentRealCoeff, hk] using
      circleTent_fourierCoeff_nonzero δ hδ hδhalf k hk

/-- 论文 `lem:pair`：每个实值 Fourier 系数均非负，含零频率。 -/
theorem circleTentRealCoeff_nonneg (δ : ℝ) (hδ : 0 < δ) (k : ℤ) :
    0 ≤ circleTentRealCoeff δ k := by
  by_cases hk : k = 0
  · simp [circleTentRealCoeff, hk, hδ.le]
  · have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    have hden : 0 < δ * Real.pi ^ 2 * (k : ℝ) ^ 2 := by positivity
    simp only [circleTentRealCoeff, if_neg hk]
    exact div_nonneg (sq_nonneg _) hden.le

theorem circleTentRealCoeff_zero (δ : ℝ) : circleTentRealCoeff δ 0 = δ := by
  simp [circleTentRealCoeff]

private theorem circleTent_coeff_norm_prod_summable (δ : ℝ) (hδ : 0 < δ)
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

#print axioms LonelyRunner.circleTent_fourierCoeff_nonzero
#print axioms LonelyRunner.circleTent_fourier_hasSum_uniform

end LonelyRunner
