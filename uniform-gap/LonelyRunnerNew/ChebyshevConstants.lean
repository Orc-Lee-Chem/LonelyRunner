import LonelyRunnerNew.ChebyshevFactorial
import LonelyRunnerNew.SmallPrimeAnalytic

noncomputable section
set_option autoImplicit false
namespace LonelyRunnerNew.RCThirty

theorem constantC_positive_form : constantC=
    (7/15:ℝ)*Real.log 2+(3/10:ℝ)*Real.log 3+(1/6:ℝ)*Real.log 5 := by
  have h30 : Real.log (30:ℝ)=Real.log 2+Real.log 3+Real.log 5 := by
    rw [show (30:ℝ)=2*(3*5) by norm_num,Real.log_mul (by norm_num : (2:ℝ)≠0) (by norm_num : (3*5:ℝ)≠0),
      Real.log_mul (by norm_num : (3:ℝ)≠0) (by norm_num : (5:ℝ)≠0)]
    ring
  unfold constantC
  rw [h30]
  ring

theorem constantC_rational_certificate :
    (921/1000:ℚ)<(7/15:ℚ)*Certificate.logLowerQ 2 24+
      (3/10:ℚ)*Certificate.logLowerQ 3 24+(1/6:ℚ)*Certificate.logLowerQ 5 24 ∧
    (7/15:ℚ)*Certificate.logUpperQ 2 24+
      (3/10:ℚ)*Certificate.logUpperQ 3 24+(1/6:ℚ)*Certificate.logUpperQ 5 24<(922/1000:ℚ) := by
  norm_num [Certificate.logLowerQ,Certificate.logUpperQ,Finset.sum_range_succ]

theorem constantC_enclosure : (921/1000:ℝ)<constantC ∧ constantC<(922/1000:ℝ) := by
  have h2 := Certificate.rational_log_enclosure 2 (by norm_num) 24
  have h3 := Certificate.rational_log_enclosure 3 (by norm_num) 24
  have h5 := Certificate.rational_log_enclosure 5 (by norm_num) 24
  have hlo : (921/1000:ℝ)<(7/15:ℝ)*(Certificate.logLowerQ 2 24:ℝ)+
      (3/10:ℝ)*(Certificate.logLowerQ 3 24:ℝ)+(1/6:ℝ)*(Certificate.logLowerQ 5 24:ℝ) := by
    have hh := (Rat.cast_lt (K:=ℝ)).mpr constantC_rational_certificate.1
    push_cast at hh
    exact hh
  have hhi : (7/15:ℝ)*(Certificate.logUpperQ 2 24:ℝ)+
      (3/10:ℝ)*(Certificate.logUpperQ 3 24:ℝ)+(1/6:ℝ)*(Certificate.logUpperQ 5 24:ℝ)<(922/1000:ℝ) := by
    have hh := (Rat.cast_lt (K:=ℝ)).mpr constantC_rational_certificate.2
    push_cast at hh
    exact hh
  rw [constantC_positive_form]
  norm_num only [Rat.cast_ofNat] at h2 h3 h5
  constructor <;> linarith

end LonelyRunnerNew.RCThirty
