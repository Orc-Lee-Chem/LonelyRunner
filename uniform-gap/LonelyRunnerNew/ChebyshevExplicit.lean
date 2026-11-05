import LonelyRunnerNew.ChebyshevPsi

noncomputable section
set_option autoImplicit false
namespace LonelyRunnerNew.RCThirty

theorem exponential_errors {x : ℝ} (hx : 0<x) (hlog : 1000≤Real.log x) :
    30≤x ∧ 5+10*Real.log x≤x/10000 ∧
      2*Real.sqrt x*Real.log x≤x/10000 ∧ psiError x≤x/10000 := by
  let t := Real.log x
  have ht : 1000≤t := hlog
  have ht0 : 0≤t := by linarith
  have hex : Real.exp t=x := Real.exp_log hx
  have hx1000 : 1001≤x := by have h := Real.add_one_le_exp t;rw [hex] at h;linarith
  have hcube : 1000000*t≤t^3 := by
    have hsq : (1000000:ℝ)≤t^2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hsq ht0
    nlinarith only [hm]
  have hex3 := Real.pow_div_factorial_le_exp t ht0 3
  norm_num only [Nat.factorial, Nat.cast_ofNat, Nat.reduceMul, Nat.reduceAdd] at hex3
  rw [hex] at hex3
  have hJ : 5+10*t≤x/10000 := by nlinarith only [hex3,hcube,ht]
  have hh := Real.pow_div_factorial_le_exp (t/2) (by positivity) 3
  norm_num only [Nat.factorial,Nat.cast_ofNat,Nat.reduceMul,Nat.reduceAdd] at hh
  have htE : 20000*t≤Real.exp (t/2) := by nlinarith only [hh,hcube,ht0]
  have hE2 : Real.exp (t/2)^2=x := by
    rw [pow_two,←Real.exp_add,show t/2+t/2=t by ring,hex]
  have hroot : Real.sqrt x=Real.exp (t/2) := by
    have hs := Real.sq_sqrt hx.le
    have hr := Real.sqrt_nonneg x
    have he := Real.exp_pos (t/2)
    nlinarith
  have htail : 2*Real.sqrt x*t≤x/10000 := by
    have hm := mul_le_mul_of_nonneg_right htE (Real.exp_nonneg (t/2))
    rw [hroot]
    nlinarith only [hm,hE2]
  have hl2 : Real.log (2:ℝ)≤1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh
    exact hh
  have hlogx : Real.log (x+1)≤t+1 := by
    have hh := Real.log_le_log (by linarith : 0<x+1) (by linarith : x+1≤2*x)
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hx.ne'] at hh
    change Real.log (x+1)≤Real.log 2+t at hh
    linarith
  have hl0 : 0≤Real.log (x+1) := Real.log_nonneg (by linarith)
  have hErr : psiError x≤800*t^2 := by
    unfold psiError
    have hs : (1+Real.log (x+1))^2≤(2*t)^2 := by
      apply (sq_le_sq₀ (by linarith) (by linarith)).mpr
      linarith
    nlinarith
  have hpow : 1000000000*t^2≤t^5 := by
    have h3 : (1000000000:ℝ)≤t^3 := by
      have hh : (1000:ℝ)^3≤t^3 := by gcongr
      norm_num at hh
      exact hh
    have hm := mul_le_mul_of_nonneg_right h3 (sq_nonneg t)
    nlinarith only [hm]
  have hex5 := Real.pow_div_factorial_le_exp t ht0 5
  norm_num only [Nat.factorial,Nat.cast_ofNat,Nat.reduceMul,Nat.reduceAdd] at hex5
  rw [hex] at hex5
  have hPsi : psiError x≤x/10000 := by nlinarith only [hErr,hpow,hex5]
  exact ⟨by linarith,hJ,htail,hPsi⟩

/-- Explicit positive-real Chebyshev bounds needed by the medium-A row.
Positivity is essential: Real.log is also defined on negative reals. -/
theorem theta_explicit {x : ℝ} (hx : 0<x) (hlog : 1000≤Real.log x) :
    (92/100:ℝ)*x≤Chebyshev.theta x ∧ Chebyshev.theta x≤(1107/1000:ℝ)*x := by
  obtain ⟨hx30,hJ,hTail,hPsi⟩ := exponential_errors hx hlog
  have hc := constantC_enclosure
  have hclo := mul_le_mul_of_nonneg_right hc.1.le hx.le
  have hchi := mul_le_mul_of_nonneg_right hc.2.le hx.le
  have hj := (abs_le.mp (J_main_error hx30)).1
  have hp := J_le_psi x
  have ht := Chebyshev.psi_sub_theta_le (by linarith : 1≤x)
  have hpu := psi_upper hx.le
  have htu := Chebyshev.theta_le_psi x
  constructor <;> nlinarith

end LonelyRunnerNew.RCThirty
