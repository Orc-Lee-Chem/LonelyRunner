import LonelyRunnerNew.LargePrimeTails
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

noncomputable section
set_option autoImplicit false
namespace LonelyRunnerNew.FiniteCore

def cutConstant : ℝ := 1-1/Real.sqrt 2
def coareaConstant : ℝ := 1+1/Real.sqrt 2
def cutDefect (z : ℝ) : ℝ := 1-z^(3/2:ℝ)-(1-z)^(3/2:ℝ)

theorem sqrt_two_data : 0<Real.sqrt 2 ∧ 1<Real.sqrt 2 ∧ Real.sqrt 2<2 ∧ (Real.sqrt 2)^2=2 := by
  have h0 := Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  refine ⟨h0,?_,?_,hs⟩ <;> nlinarith

theorem cutConstant_pos : 0<cutConstant := by
  unfold cutConstant
  have h := (div_lt_one sqrt_two_data.1).mpr sqrt_two_data.2.1
  linarith
theorem coareaConstant_identity : 2*cutConstant*coareaConstant=1 := by
  unfold cutConstant coareaConstant
  field_simp [sqrt_two_data.1.ne']
  nlinarith [sqrt_two_data.2.2.2]

theorem twice_cutConstant : 2*cutConstant=2-Real.sqrt 2 := by
  unfold cutConstant
  field_simp [sqrt_two_data.1.ne']
  nlinarith [sqrt_two_data.2.2.2]

theorem half_three_halves : (1/2:ℝ)^(3/2:ℝ)=Real.sqrt 2/4 := by
  have hr : Real.sqrt (1/2:ℝ)=Real.sqrt 2/2 := by
    have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤1/2)
    nlinarith [Real.sqrt_nonneg (1/2),sqrt_two_data.1,sqrt_two_data.2.2.2]
  rw [show (3/2:ℝ)=1+1/2 by norm_num,Real.rpow_one_add' (by norm_num : (0:ℝ)≤1/2) (by norm_num),← Real.sqrt_eq_rpow,hr]
  ring

theorem cutDefect_chord {z : ℝ} (hz : 0≤z) (hz1 : z≤1/2) :
    (2-Real.sqrt 2)*z≤cutDefect z := by
  have hc := convexOn_rpow (by norm_num : (1:ℝ)≤3/2)
  have h0 := hc.2 (show (0:ℝ)∈Set.Ici 0 by norm_num) (show (1/2:ℝ)∈Set.Ici 0 by norm_num)
    (show 0≤1-2*z by linarith) (show 0≤2*z by linarith) (show (1-2*z)+2*z=1 by ring)
  have h1 := hc.2 (show (1:ℝ)∈Set.Ici 0 by norm_num) (show (1/2:ℝ)∈Set.Ici 0 by norm_num)
    (show 0≤1-2*z by linarith) (show 0≤2*z by linarith) (show (1-2*z)+2*z=1 by ring)
  simp only [smul_eq_mul,Real.zero_rpow (by norm_num : (3/2:ℝ)≠0),Real.one_rpow,mul_zero,zero_add] at h0 h1
  rw [half_three_halves] at h0 h1
  have he0 : 2*z*(1/2)=z := by ring
  have he1 : (1-2*z)*1+2*z*(1/2)=1-z := by ring
  rw [he0] at h0
  rw [he1] at h1
  unfold cutDefect
  nlinarith only [h0,h1]

theorem cutDefect_power {z : ℝ} (hz : 0≤z) (hz1 : z≤1/2) :
    (2*Real.sqrt 2-2)*z^(3/2:ℝ)≤cutDefect z := by
  have hr : Real.sqrt z≤Real.sqrt 2/2 := by
    have hh := Real.sqrt_le_sqrt hz1
    have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤1/2)
    have he : Real.sqrt (1/2:ℝ)=Real.sqrt 2/2 := by
      nlinarith [Real.sqrt_nonneg (1/2),sqrt_two_data.1,sqrt_two_data.2.2.2]
    rwa [he] at hh
  have hzpow : z^(3/2:ℝ)=z*Real.sqrt z := by
    rw [show (3/2:ℝ)=1+1/2 by norm_num,Real.rpow_one_add' hz (by norm_num),← Real.sqrt_eq_rpow]
  have hh := mul_le_mul_of_nonneg_left hr (mul_nonneg (by linarith [sqrt_two_data.2.1] : 0≤2*Real.sqrt 2-2) hz)
  have he : (2*Real.sqrt 2-2)*z*(Real.sqrt 2/2)=(2-Real.sqrt 2)*z := by
    have hs := congrArg (fun t : ℝ => t*z) sqrt_two_data.2.2.2
    nlinarith only [hs]
  rw [he] at hh
  rw [hzpow]
  simpa only [mul_assoc] using hh.trans (cutDefect_chord hz hz1)

theorem half_cut_to_marginal {z e pi : ℝ} (hz : 0≤z) (hz1 : z≤1/2)
    (he : cutDefect z≤e) (hpi : pi≤z^(3/2:ℝ)+e/2) :
    (2-Real.sqrt 2)*pi≤e := by
  have hpow := (cutDefect_power hz hz1).trans he
  have hmul := mul_le_mul_of_nonneg_left hpow (sqrt_two_data.1.le : 0≤Real.sqrt 2)
  have hs := sqrt_two_data.2.2.2
  have hpic := mul_le_mul_of_nonneg_left hpi (show 0≤2-Real.sqrt 2 by linarith [sqrt_two_data.2.2.1])
  have hsZ := congrArg (fun t : ℝ => t*z^(3/2:ℝ)) hs
  nlinarith only [hmul,hpic,hsZ]

theorem cut_to_cheeger {z e inside outside : ℝ} (hz : 0≤z) (hz1 : z≤1)
    (hi : inside≤z^(3/2:ℝ)) (ho : outside≤(1-z)^(3/2:ℝ))
    (hpart : inside+outside+e=1) :
    cutConstant*min (inside+e/2) (outside+e/2)≤e/2 := by
  have he : cutDefect z≤e := by unfold cutDefect; linarith
  have hc : (2-Real.sqrt 2)*min (inside+e/2) (outside+e/2)≤e := by
    by_cases hhalf : z≤1/2
    · have hh := half_cut_to_marginal hz hhalf he (show inside+e/2≤z^(3/2:ℝ)+e/2 by linarith)
      exact (mul_le_mul_of_nonneg_left (min_le_left _ _) (by linarith [sqrt_two_data.2.2.1])).trans hh
    · have hec : cutDefect (1-z)≤e := by
        have heq : cutDefect (1-z)=cutDefect z := by unfold cutDefect; rw [show 1-(1-z)=z by ring]; ring
        rwa [heq]
      have hh := half_cut_to_marginal (show 0≤1-z by linarith) (show 1-z≤1/2 by linarith)
        hec (show outside+e/2≤(1-z)^(3/2:ℝ)+e/2 by linarith)
      exact (mul_le_mul_of_nonneg_left (min_le_right _ _) (by linarith [sqrt_two_data.2.2.1])).trans hh
  rw [← twice_cutConstant] at hc
  linarith

end LonelyRunnerNew.FiniteCore
