import LonelyRunner.CircleFejer
import Mathlib.Analysis.Complex.Poisson

/-!
# 圆周 Poisson 核

这里沿用 `UnitAddCircle`、`fourier` 和 `circleHaar`。
-/

open MeasureTheory
open scoped Real
open scoped ComplexConjugate

namespace LonelyRunner

/-- 标准圆周 Poisson 核，`fourier 1 t` 即 `exp(2πit)`。 -/
noncomputable def circlePoisson (r : ℝ) (t : UnitAddCircle) : ℝ :=
  (1 - r ^ 2) / ‖(1 : ℂ) - (r : ℂ) * fourier 1 t‖ ^ 2

private theorem circlePoisson_fourier_norm (t : UnitAddCircle) :
    ‖fourier 1 t‖ = 1 := by
  rw [fourier_one]
  exact Circle.norm_coe _

private theorem circlePoisson_norm_bounds (r : ℝ) (hr0 : 0 ≤ r)
    (t : UnitAddCircle) :
    1 - r ≤ ‖(1 : ℂ) - (r : ℂ) * fourier 1 t‖ ∧
      ‖(1 : ℂ) - (r : ℂ) * fourier 1 t‖ ≤ 1 + r := by
  have hz : ‖(r : ℂ) * fourier 1 t‖ = r := by
    rw [norm_mul, Complex.norm_real, circlePoisson_fourier_norm, mul_one,
      Real.norm_eq_abs, abs_of_nonneg hr0]
  constructor
  · have h := norm_sub_norm_le (1 : ℂ) ((r : ℂ) * fourier 1 t)
    rw [norm_one, hz] at h
    linarith
  · have h := norm_sub_le (1 : ℂ) ((r : ℂ) * fourier 1 t)
    rw [norm_one, hz] at h
    linarith

/-- 当 `0≤r<1` 时，分母的范数至少为 `1-r`，因而严格为正。 -/
theorem circlePoisson_denominator_pos (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (t : UnitAddCircle) :
    0 < ‖(1 : ℂ) - (r : ℂ) * fourier 1 t‖ ^ 2 := by
  have hz : ‖(r : ℂ) * fourier 1 t‖ = r := by
    rw [norm_mul, Complex.norm_real, circlePoisson_fourier_norm, mul_one,
      Real.norm_eq_abs, abs_of_nonneg hr0]
  have hlow : 1 - r ≤ ‖(1 : ℂ) - (r : ℂ) * fourier 1 t‖ := by
    have h := norm_sub_norm_le (1 : ℂ) ((r : ℂ) * fourier 1 t)
    rw [norm_one, hz] at h
    linarith
  have hpos : 0 < ‖(1 : ℂ) - (r : ℂ) * fourier 1 t‖ := by
    linarith
  positivity

/-- Poisson 核在圆周上连续。 -/
theorem circlePoisson_continuous (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Continuous (circlePoisson r) := by
  unfold circlePoisson
  fun_prop (disch := intro t; exact (circlePoisson_denominator_pos r hr0 hr1 t).ne')

/-- Poisson 核非负。 -/
theorem circlePoisson_nonneg (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (t : UnitAddCircle) : 0 ≤ circlePoisson r t := by
  unfold circlePoisson
  have hnum : 0 ≤ 1 - r ^ 2 := by nlinarith [sq_nonneg (1 - r)]
  positivity

/-- 有界圆周上的连续 Poisson 核可积。 -/
theorem circlePoisson_integrable (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Integrable (circlePoisson r) circleHaar := by
  have hf := circlePoisson_continuous r hr0 hr1
  obtain ⟨M, hM⟩ := (isCompact_range hf).isBounded.exists_norm_le
  apply Integrable.of_bound hf.aestronglyMeasurable M
  filter_upwards [] with t
  exact hM _ ⟨t, rfl⟩

/-- 零半径时 Poisson 核恒为一。 -/
theorem circlePoisson_zero (t : UnitAddCircle) : circlePoisson 0 t = 1 := by
  simp [circlePoisson]

/-- `0≤r≤3/4` 时的显式一致界。 -/
theorem circlePoisson_sub_one_bound (r : ℝ) (hr0 : 0 ≤ r)
    (hr34 : r ≤ 3 / 4) (t : UnitAddCircle) :
    |circlePoisson r t - 1| ≤ 64 * r := by
  let d := ‖(1 : ℂ) - (r : ℂ) * fourier 1 t‖
  obtain ⟨hlo, hhi⟩ := circlePoisson_norm_bounds r hr0 t
  have hd0 : 0 ≤ d := norm_nonneg _
  have hd14 : 1 / 4 ≤ d := by dsimp [d] at *; linarith
  have hd2 : 1 / 16 ≤ d ^ 2 := by nlinarith [sq_nonneg (d - 1 / 4)]
  have hd2pos : 0 < d ^ 2 := by linarith
  have hdiff : |d - 1| ≤ r := by
    apply abs_le.mpr
    constructor <;> dsimp [d] at * <;> linarith
  have hplus : 0 ≤ d + 1 := by linarith
  have hplusBound : d + 1 ≤ 11 / 4 := by dsimp [d] at *; linarith
  have hdiff2 : |d ^ 2 - 1| ≤ (11 / 4) * r := by
    calc
      |d ^ 2 - 1| = |d - 1| * (d + 1) := by
        rw [show d ^ 2 - 1 = (d - 1) * (d + 1) by ring,
          abs_mul, abs_of_nonneg hplus]
      _ ≤ r * (d + 1) := mul_le_mul_of_nonneg_right hdiff hplus
      _ ≤ (11 / 4) * r := by nlinarith
  have hr2 : r ^ 2 ≤ (3 / 4) * r := by nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hr34)]
  have hnum : |(1 - r ^ 2) - d ^ 2| ≤ 4 * r := by
    have ht := abs_add_le (-(r ^ 2)) (1 - d ^ 2)
    have hident : (1 - r ^ 2) - d ^ 2 = -(r ^ 2) + (1 - d ^ 2) := by ring
    rw [hident]
    have habs : |1 - d ^ 2| = |d ^ 2 - 1| := by rw [abs_sub_comm]
    rw [abs_neg, abs_of_nonneg (sq_nonneg r), habs] at ht
    linarith
  change |(1 - r ^ 2) / d ^ 2 - 1| ≤ 64 * r
  have hrew : |(1 - r ^ 2) / d ^ 2 - 1| =
      |(1 - r ^ 2) - d ^ 2| / d ^ 2 := by
    rw [div_sub_one, abs_div, abs_of_nonneg (sq_nonneg d)]
    exact hd2pos.ne'
  rw [hrew]
  apply (div_le_iff₀ hd2pos).2
  nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hd2)]

/-- 归一化 Haar 积分与 Mathlib 的单位复圆 `circleAverage` 相同。 -/
private theorem circlePoisson_haar_eq_circleAverage (f : ℂ → ℂ) :
    (∫ t : UnitAddCircle, f (fourier 1 t) ∂circleHaar) =
      Real.circleAverage f 0 1 := by
  have hangle (x : ℝ) :
      fourier 1 (x : UnitAddCircle) = circleMap 0 1 (x * (2 * Real.pi)) := by
    rw [fourier_coe_apply]
    simp only [circleMap, zero_add, one_mul, div_one]
    congr 1
    push_cast
    ring
  calc
    (∫ t : UnitAddCircle, f (fourier 1 t) ∂circleHaar) =
        ∫ x in (0 : ℝ)..1, f (fourier 1 (x : UnitAddCircle)) := by
          rw [circleHaar_eq_volume]
          simpa using (UnitAddCircle.intervalIntegral_preimage 0
            (fun t : UnitAddCircle => f (fourier 1 t))).symm
    _ = ∫ x in (0 : ℝ)..1, f (circleMap 0 1 (x * (2 * Real.pi))) := by
      apply intervalIntegral.integral_congr
      intro x hx
      change f (fourier 1 (x : UnitAddCircle)) = f (circleMap 0 1 (x * (2 * Real.pi)))
      rw [hangle]
    _ = Real.circleAverage f 0 1 := by
      rw [Real.circleAverage_def]
      simpa using (intervalIntegral.integral_comp_mul_right
        (fun θ : ℝ => f (circleMap 0 1 θ))
        (by positivity : (2 * Real.pi : ℝ) ≠ 0)
        (a := 0) (b := 1))

/-- 在单位圆上，本文件的分母等于 Mathlib 复平面 Poisson 核的分母。 -/
private theorem circlePoisson_eq_complex_kernel (r : ℝ) (hr0 : 0 ≤ r)
    (t : UnitAddCircle) :
    circlePoisson r t = poissonKernel 0 (r : ℂ) (fourier 1 t) := by
  let z : ℂ := fourier 1 t
  have hz : ‖z‖ = 1 := circlePoisson_fourier_norm t
  have hzstar : z * star z = 1 := by
    have h := Complex.mul_conj z
    simpa [Complex.normSq_eq_norm_sq, hz] using h
  have heq : z - (r : ℂ) = z * (1 - (r : ℂ) * star z) := by
    calc
      z - (r : ℂ) = z - (r : ℂ) * (z * star z) := by rw [hzstar, mul_one]
      _ = _ := by ring
  have hnorm : ‖z - (r : ℂ)‖ = ‖(1 : ℂ) - (r : ℂ) * z‖ := by
    calc
      _ = ‖z * (1 - (r : ℂ) * star z)‖ := by rw [heq]
      _ = ‖1 - (r : ℂ) * star z‖ := by rw [norm_mul, hz, one_mul]
      _ = ‖1 - (r : ℂ) * z‖ := by
        have hc : star ((1 : ℂ) - (r : ℂ) * z) = 1 - (r : ℂ) * star z := by
          simp [map_sub, map_mul, Complex.conj_ofReal]
        rw [← hc, norm_star]
  unfold circlePoisson poissonKernel
  simp [z, hz, hnorm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  simpa only [z, fourier_one] using
    congrArg (fun x : ℝ => (1 - r ^ 2) / x ^ 2) hnorm.symm

private theorem circlePoisson_fourier_nat (n : ℕ) (t : UnitAddCircle) :
    fourier (n : ℤ) t = (fourier 1 t) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_succ, fourier_add, ih, pow_succ]

/-- 非负整数频率的 Poisson 积分公式；调用 Mathlib 的复圆 Poisson 公式。 -/
theorem circlePoisson_integral_fourier_nat (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (n : ℕ) :
    (∫ t : UnitAddCircle,
        (circlePoisson r t : ℂ) * fourier (n : ℤ) t ∂circleHaar) =
      (r : ℂ) ^ n := by
  have hw : (r : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    simpa [Metric.mem_ball, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr0] using hr1
  have hdiff : DiffContOnCl ℂ (fun z : ℂ => z ^ n) (Metric.ball 0 1) :=
    DifferentiableOn.diffContOnCl (by fun_prop)
  calc
    _ = ∫ t : UnitAddCircle,
        poissonKernel 0 (r : ℂ) (fourier 1 t) • (fourier 1 t) ^ n ∂circleHaar := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [circlePoisson_eq_complex_kernel r hr0 t,
        circlePoisson_fourier_nat]
      simp [smul_eq_mul]
    _ = Real.circleAverage
          (fun z : ℂ => poissonKernel 0 (r : ℂ) z • z ^ n) 0 1 :=
      circlePoisson_haar_eq_circleAverage
        (fun z : ℂ => poissonKernel 0 (r : ℂ) z • z ^ n)
    _ = (r : ℂ) ^ n := hdiff.circleAverage_poissonKernel_smul hw

private theorem circlePoisson_integral_fourier_neg_nat
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    (∫ t : UnitAddCircle,
        (circlePoisson r t : ℂ) * fourier (-(n : ℤ)) t ∂circleHaar) =
      (r : ℂ) ^ n := by
  calc
    _ = ∫ t : UnitAddCircle,
        conj ((circlePoisson r t : ℂ) * fourier (n : ℤ) t) ∂circleHaar := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [fourier_neg]
      simp [map_mul, Complex.conj_ofReal]
    _ = conj (∫ t : UnitAddCircle,
        (circlePoisson r t : ℂ) * fourier (n : ℤ) t ∂circleHaar) := integral_conj
    _ = (r : ℂ) ^ n := by
      rw [circlePoisson_integral_fourier_nat r hr0 hr1 n]
      simp [map_pow, Complex.conj_ofReal]

/-- 所有整数频率的积分，包括 `k=0` 与 `r=0`。 -/
theorem circlePoisson_integral_fourier (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (k : ℤ) :
    (∫ t : UnitAddCircle,
        (circlePoisson r t : ℂ) * fourier k t ∂circleHaar) =
      (r : ℂ) ^ k.natAbs := by
  rcases Int.natAbs_eq k with hk | hk
  · rw [hk]
    simpa only [Int.natAbs_natCast] using
      circlePoisson_integral_fourier_nat r hr0 hr1 k.natAbs
  · rw [hk]
    simpa only [Int.natAbs_neg, Int.natAbs_natCast] using
      circlePoisson_integral_fourier_neg_nat r hr0 hr1 k.natAbs

/-- Poisson 核相对于归一化 Haar 概率测度积分为一。 -/
theorem circlePoisson_integral_one (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∫ t : UnitAddCircle, circlePoisson r t ∂circleHaar) = 1 := by
  have h := circlePoisson_integral_fourier r hr0 hr1 0
  simp only [Int.natAbs_zero, pow_zero, fourier_zero, mul_one] at h
  rw [integral_complex_ofReal] at h
  exact_mod_cast h

private theorem circlePoisson_nat_le_pow50 (n : ℕ) : n ≤ 50 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hp : 1 ≤ 50 ^ n := pow_pos (by omega : 0 < 50) _
      calc
        n + 1 ≤ 50 ^ n + 1 := Nat.add_le_add_right ih 1
        _ ≤ 50 ^ (n + 1) := by
          rw [pow_succ]
          omega

/-- 有限幂的二次余项控制；归纳步明确使用
`x^(k+1)-1-(k+1)u = x(x^k-1-ku)+ku²`。 -/
private theorem circlePoisson_power_quadratic (k : ℕ) (x u r : ℝ)
    (hx : x = 1 + u) (hx0 : 0 ≤ x) (hx49 : x ≤ 49)
    (hr0 : 0 ≤ r) (hu : |u| ≤ 64 * r) :
    x ^ k ≤ 1 + (k : ℝ) * u + 4096 * (50 : ℝ) ^ k * r ^ 2 := by
  have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
  have hu2 : u ^ 2 ≤ 4096 * r ^ 2 := by
    have h64 : 0 ≤ 64 * r := by positivity
    have hh := mul_nonneg (sub_nonneg.mpr hu)
      (add_nonneg (abs_nonneg u) h64)
    nlinarith [sq_abs u]
  induction k with
  | zero => simp; nlinarith [hr2]
  | succ k ih =>
      have hk50 : (k : ℝ) ≤ (50 : ℝ) ^ k := by
        exact_mod_cast circlePoisson_nat_le_pow50 k
      have hrem : x ^ k - 1 - (k : ℝ) * u ≤
          4096 * (50 : ℝ) ^ k * r ^ 2 := by linarith
      have hremMul := mul_le_mul_of_nonneg_left hrem hx0
      have hboundMul :
          x * (4096 * (50 : ℝ) ^ k * r ^ 2) ≤
            49 * (4096 * (50 : ℝ) ^ k * r ^ 2) := by
        exact mul_le_mul_of_nonneg_right hx49 (by positivity)
      have hcoef :
          49 * (4096 * (50 : ℝ) ^ k * r ^ 2) +
            (k : ℝ) * (4096 * r ^ 2) ≤
              4096 * (50 : ℝ) ^ (k + 1) * r ^ 2 := by
        have hcoef' : 49 * (50 : ℝ) ^ k + (k : ℝ) ≤
            50 * (50 : ℝ) ^ k := by linarith
        calc
          _ = 4096 * (49 * (50 : ℝ) ^ k + (k : ℝ)) * r ^ 2 := by ring
          _ ≤ 4096 * (50 * (50 : ℝ) ^ k) * r ^ 2 := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hcoef' (by norm_num)) hr2
          _ = _ := by rw [pow_succ]; ring
      have hidentity :
          x ^ (k + 1) - 1 - ((k + 1 : ℕ) : ℝ) * u =
            x * (x ^ k - 1 - (k : ℝ) * u) + (k : ℝ) * u ^ 2 := by
        rw [pow_succ]
        push_cast
        rw [hx]
        ring
      have hk0 : (0 : ℝ) ≤ k := by positivity
      have hsmall := mul_le_mul_of_nonneg_left hu2 hk0
      nlinarith [hidentity, hremMul, hboundMul, hcoef, hsmall]

private theorem circlePoisson_pow_integrable (r : ℝ) (hr0 : 0 ≤ r)
    (hr1 : r < 1) (k : ℕ) :
    Integrable (fun t : UnitAddCircle => (circlePoisson r t) ^ k) circleHaar := by
  have hf : Continuous (fun t : UnitAddCircle => (circlePoisson r t) ^ k) :=
    (circlePoisson_continuous r hr0 hr1).pow k
  obtain ⟨M, hM⟩ := (isCompact_range hf).isBounded.exists_norm_le
  apply Integrable.of_bound hf.aestronglyMeasurable M
  filter_upwards [] with t
  exact hM _ ⟨t, rfl⟩

/-- Poisson 核的有限整数矩界，常数 `4096·50^k` 仅依赖 `k`。 -/
theorem circlePoisson_moment_bound (k : ℕ) (hk : 2 ≤ k) :
    ∃ Ck : ℝ, 0 < Ck ∧
      ∀ (r : ℝ), 0 ≤ r → r ≤ 3 / 4 →
        (∫ t : UnitAddCircle, (circlePoisson r t) ^ k ∂circleHaar) ≤
          1 + Ck * r ^ 2 := by
  let Ck : ℝ := 4096 * (50 : ℝ) ^ k
  have hCk : 0 < Ck := by dsimp [Ck]; positivity
  refine ⟨Ck, hCk, ?_⟩
  intro r hr0 hr34
  have hr1 : r < 1 := by linarith
  have hP := circlePoisson_integrable r hr0 hr1
  have hPow := circlePoisson_pow_integrable r hr0 hr1 k
  have hRhs : Integrable
      (fun t : UnitAddCircle =>
        1 + (k : ℝ) * (circlePoisson r t - 1) + Ck * r ^ 2) circleHaar := by
    have hf : Continuous (fun t : UnitAddCircle =>
        1 + (k : ℝ) * (circlePoisson r t - 1) + Ck * r ^ 2) := by
      have hPcont := circlePoisson_continuous r hr0 hr1
      have hUcont : Continuous (fun t : UnitAddCircle => circlePoisson r t - (1 : ℝ)) :=
        hPcont.sub continuous_const
      exact (continuous_const.add (continuous_const.mul hUcont)).add continuous_const
    obtain ⟨M, hM⟩ := (isCompact_range hf).isBounded.exists_norm_le
    apply Integrable.of_bound hf.aestronglyMeasurable M
    filter_upwards [] with t
    exact hM _ ⟨t, rfl⟩
  have hpoint (t : UnitAddCircle) :
      (circlePoisson r t) ^ k ≤
        1 + (k : ℝ) * (circlePoisson r t - 1) + Ck * r ^ 2 := by
    have hu := circlePoisson_sub_one_bound r hr0 hr34 t
    have hx0 := circlePoisson_nonneg r hr0 hr1 t
    have hx49 : circlePoisson r t ≤ 49 := by
      have := (abs_le.mp hu).2
      linarith
    simpa [Ck] using circlePoisson_power_quadratic k
      (circlePoisson r t) (circlePoisson r t - 1) r (by ring) hx0 hx49 hr0 hu
  have hInt :
      (∫ t : UnitAddCircle, (circlePoisson r t) ^ k ∂circleHaar) ≤
        ∫ t : UnitAddCircle,
          (1 + (k : ℝ) * (circlePoisson r t - 1) + Ck * r ^ 2) ∂circleHaar :=
    integral_mono_ae hPow hRhs (Filter.Eventually.of_forall hpoint)
  have huInt : Integrable
      (fun t : UnitAddCircle => circlePoisson r t - 1) circleHaar :=
    hP.sub (integrable_const (1 : ℝ))
  have huMean : (∫ t : UnitAddCircle, circlePoisson r t - 1 ∂circleHaar) = 0 := by
    rw [integral_sub hP (integrable_const (1 : ℝ)),
      circlePoisson_integral_one r hr0 hr1]
    simp
  have hRhsEq :
      (∫ t : UnitAddCircle,
        1 + (k : ℝ) * (circlePoisson r t - 1) + Ck * r ^ 2 ∂circleHaar) =
          1 + Ck * r ^ 2 := by
    rw [integral_add]
    · rw [integral_add]
      · rw [integral_const, integral_const_mul, huMean]
        simp
      · exact integrable_const (1 : ℝ)
      · exact huInt.const_mul _
    · exact (integrable_const (1 : ℝ)).add (huInt.const_mul _)
    · exact integrable_const (Ck * r ^ 2)
  exact hInt.trans_eq hRhsEq

end LonelyRunner
