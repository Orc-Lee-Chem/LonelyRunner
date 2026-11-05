import LonelyRunnerNew.RationalAnalysis
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

noncomputable section
set_option autoImplicit false
namespace LonelyRunnerNew.Saturated

def Psi (t : ℝ) : ℝ := if 1≤t then 1 else 4*t-3*t^2+2*t^2*Real.log t
def t0 : ℝ := 19/100

theorem log_five_lower : (8/5:ℝ)<Real.log 5 := by
  have hh := (RationalAnalysis.log_series_enclosure (by norm_num : (1:ℝ)≤5) 8).1
  have hn : (8/5:ℝ)<RationalAnalysis.logSeriesLower 5 8 := by
    norm_num [RationalAnalysis.logSeriesLower,Finset.sum_range_succ]
  exact hn.trans_le hh

theorem Psi_small_polynomial {t : ℝ} (ht : 0<t) (hupper : t≤t0) :
    Psi t≤4*t-(31/5:ℝ)*t^2 := by
  have ht1 : t<1 := by dsimp [t0] at hupper;linarith
  have ht5 : t≤(5:ℝ)⁻¹ := by dsimp [t0] at hupper;norm_num;linarith
  have hlog := Real.log_le_log ht ht5
  rw [Real.log_inv] at hlog
  have hf := log_five_lower
  have hm := mul_le_mul_of_nonneg_left (show Real.log t≤-(8/5:ℝ) by linarith)
    (sq_nonneg t)
  simp only [Psi,if_neg (not_le.mpr ht1)]
  nlinarith only [hm]

theorem polynomial_root_comparison {t : ℝ} (ht : 0<t) (hupper : t≤t0) :
    4*t-(31/5:ℝ)*t^2≤(53618/100000:ℝ)*Real.sqrt (t/t0) := by
  let u := Real.sqrt (t/t0)
  have ht0 : (0:ℝ)<t0 := by norm_num [t0]
  have hu0 : 0≤u := Real.sqrt_nonneg _
  have hu1 : u≤1 := (Real.sqrt_le_one).mpr ((div_le_one ht0).mpr hupper)
  have husq : u^2=t/t0 := Real.sq_sqrt (div_pos ht ht0).le
  have heq : t=t0*u^2 := by rw [husq];field_simp
  have hc : 1+u+u^2≤3 := by nlinarith only [sq_nonneg u,hu0,hu1]
  have hb : 0≤4*t0-(31/5:ℝ)*t0^2*(1+u+u^2) := by norm_num [t0] at *;linarith
  have hn := mul_nonneg (mul_nonneg hu0 (sub_nonneg.mpr hu1)) hb
  have hid : u*(4*t0-(31/5:ℝ)*t0^2)-(4*(t0*u^2)-(31/5:ℝ)*(t0*u^2)^2)=
      u*(1-u)*(4*t0-(31/5:ℝ)*t0^2*(1+u+u^2)) := by ring
  rw [←hid] at hn
  conv_lhs => rw [heq]
  change 4*(t0*u^2)-(31/5:ℝ)*(t0*u^2)^2≤(53618/100000:ℝ)*u
  norm_num [t0] at hn ⊢
  linarith

theorem Psi_small_root {t : ℝ} (ht : 0<t) (hupper : t≤t0) :
    Psi t≤((27/50:ℝ)*(1-1/1000))*Real.sqrt (t/t0) := by
  have hh := (Psi_small_polynomial ht hupper).trans (polynomial_root_comparison ht hupper)
  exact hh.trans (mul_le_mul_of_nonneg_right (by norm_num) (Real.sqrt_nonneg _))

/-- Terminal fourth-power estimate, with the original t0=19/100 and actual
LC retention 27/50; the 1/1000 deletion allowance is explicit. -/
theorem fourth_power_bound {rho t : ℝ} (hr0 : 0≤rho) (hr1 : rho≤1) (ht : 0<t)
    (hret : (27/50:ℝ)*(1-1/1000)*rho≤Psi t) :
    rho^4/t^2≤1/t0^2 := by
  have ht0 : (0:ℝ)<t0 := by norm_num [t0]
  have hgoal : rho^4*t0^2≤t^2 := by
    by_cases hs : t≤t0
    · have hsmall := hret.trans (Psi_small_root ht hs)
      have hr : rho≤Real.sqrt (t/t0) := (mul_le_mul_iff_right₀ (by norm_num :
        (0:ℝ)<(27/50:ℝ)*(1-1/1000))).mp hsmall
      have hp := pow_le_pow_left₀ hr0 hr 4
      have hu := Real.sq_sqrt (div_pos ht ht0).le
      have he : (Real.sqrt (t/t0))^4=(t/t0)^2 := by rw [show (4:ℕ)=2*2 by decide,pow_mul,hu]
      rw [he] at hp
      have hm := mul_le_mul_of_nonneg_right hp (sq_nonneg t0)
      have hcancel : (t/t0)^2*t0^2=t^2 := by field_simp
      rwa [hcancel] at hm
    · have hp : rho^4≤1 := by simpa using pow_le_pow_left₀ hr0 hr1 4
      have hm := mul_le_mul_of_nonneg_right hp (sq_nonneg t0)
      have hsq : t0^2≤t^2 := (sq_le_sq₀ ht0.le ht.le).mpr (le_of_not_ge hs)
      nlinarith only [hm,hsq]
  apply (div_le_div_iff₀ (sq_pos_of_pos ht) (sq_pos_of_pos ht0)).mpr
  simpa only [one_mul] using hgoal

end LonelyRunnerNew.Saturated
