import LonelyRunnerNew.KernelStepFunctions
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace LonelyRunnerNew.GreenVariation

def Phi (M u : ℝ) : ℝ := M^2/3*(1-(1-u^2/M^2)^(3/2:ℝ))

theorem Phi_zero (M : ℝ) : Phi M 0=0 := by simp [Phi]

theorem Phi_self {M : ℝ} (hM : 0 < M) : Phi M M=M^2/3 := by
  simp [Phi, hM.ne']

theorem Phi_deriv {M u : ℝ} (hM : 0 < M) :
    HasDerivAt (Phi M) (u*Real.sqrt (1-u^2/M^2)) u := by
  have hh := (((((hasDerivAt_id u).pow 2).div_const (M^2)).const_sub 1).rpow_const
    (Or.inr (by norm_num : (1:ℝ)≤3/2))).const_sub 1 |>.const_mul (M^2/3)
  convert hh using 1
  · rfl
  · rw [Real.sqrt_eq_rpow]
    norm_num
    field_simp [hM.ne']

theorem Phi_integral {M u : ℝ} (hM : 0 < M) :
    (∫ s in (0:ℝ)..u, s*Real.sqrt (1-s^2/M^2)) = Phi M u := by
  have hi : IntervalIntegrable (fun s : ℝ => s*Real.sqrt (1-s^2/M^2)) volume 0 u :=
    (by fun_prop : Continuous (fun s : ℝ => s*Real.sqrt (1-s^2/M^2))).intervalIntegrable _ _
  simpa only [Phi_zero, sub_zero] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => Phi_deriv (u := s) hM) hi

/-- The two sides of a maximum are treated by FTC and absolute integrals.
There is no monotonicity premise on U or on either side of the maximum. -/
theorem two_sided_variation (U V : ℝ → ℝ) (M c : ℝ) (hM : 0 < M)
    (hd : ∀ x, HasDerivAt U (V x) x) (hV : Continuous V)
    (hU : ∀ x, 0 ≤ U x) (hmax : U c=M)
    (hbot : Tendsto U atBot (𝓝 0)) (htop : Tendsto U atTop (𝓝 0))
    (hint : Integrable (fun x => |V x| *U x*Real.sqrt (1-(U x)^2/M^2))) :
    2*M^2/3 ≤ ∫ x, |V x| *U x*Real.sqrt (1-(U x)^2/M^2) := by
  let W := fun x => |V x| *U x*Real.sqrt (1-(U x)^2/M^2)
  let R := fun x => V x*U x*Real.sqrt (1-(U x)^2/M^2)
  have hc : Continuous U := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  have hRcont : Continuous R := by dsimp [R]; fun_prop
  have hRabs (x : ℝ) : |R x|=W x := by
    dsimp [R,W]
    rw [abs_mul, abs_mul, abs_of_nonneg (hU x), abs_of_nonneg (Real.sqrt_nonneg _)]
  have hRi : Integrable R := Integrable.mono' hint hRcont.aestronglyMeasurable (by
    filter_upwards with x
    rw [Real.norm_eq_abs,hRabs]
    )
  have hpd (x : ℝ) : HasDerivAt (fun x => Phi M (U x)) (R x) x := by
    convert (Phi_deriv (u := U x) hM).comp x (hd x) using 1 <;>
      (try simp only [R,Function.comp_def]) <;> ring
  have hlimB : Tendsto (fun x => Phi M (U x)) atBot (𝓝 0) := by
    simpa only [Phi_zero,Function.comp_def] using (Phi_deriv (u := 0) hM).continuousAt.tendsto.comp hbot
  have hlimT : Tendsto (fun x => Phi M (U x)) atTop (𝓝 0) := by
    simpa only [Phi_zero,Function.comp_def] using (Phi_deriv (u := 0) hM).continuousAt.tendsto.comp htop
  have hleft := integral_Iic_of_hasDerivAt_of_tendsto' (a := c)
    (fun x _ => hpd x) hRi.integrableOn hlimB
  have hright := integral_Ioi_of_hasDerivAt_of_tendsto' (a := c)
    (fun x _ => hpd x) hRi.integrableOn hlimT
  rw [hmax,Phi_self hM,sub_zero] at hleft
  rw [hmax,Phi_self hM,zero_sub] at hright
  have hl := abs_integral_le_integral_abs (f := R) (μ := volume.restrict (Set.Iic c))
  have hr := abs_integral_le_integral_abs (f := R) (μ := volume.restrict (Set.Ioi c))
  simp_rw [hRabs] at hl hr
  rw [hleft,abs_of_nonneg (by positivity : 0 ≤ M^2/3)] at hl
  rw [hright,abs_neg,abs_of_nonneg (by positivity : 0 ≤ M^2/3)] at hr
  have hs := integral_add_compl (s := Set.Iic c) measurableSet_Iic (show Integrable W from hint)
  rw [Set.compl_Iic] at hs
  change 2*M^2/3 ≤ ∫ x, W x
  linarith

theorem square_bound {a M u v : ℝ} (ha : 0 ≤ a) (hM : 0 < M)
    (hu : 0 ≤ u) (huM : u ≤ M) :
    2*a*|v| *u*Real.sqrt (1-u^2/M^2) ≤ v^2+a^2*u^2*(1-u^2/M^2) := by
  have hR : 0 ≤ 1-u^2/M^2 := by
    have hh := pow_le_pow_left₀ hu huM 2
    have hd := (div_le_one (sq_pos_of_pos hM)).mpr hh
    linarith
  have he : (a*u*Real.sqrt (1-u^2/M^2))^2 = a^2*u^2*(1-u^2/M^2) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hR]
  nlinarith only [sq_nonneg (|v|-a*u*Real.sqrt (1-u^2/M^2)), he, sq_abs v]

end LonelyRunnerNew.GreenVariation
