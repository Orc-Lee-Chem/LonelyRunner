import LonelyRunnerNew.RoughRowPacking

noncomputable section
set_option autoImplicit false
namespace LonelyRunnerNew.RoughRational.Asymmetric

theorem exp_tenth_inverse_le {ell : ℝ} (hell : 4096≤ell) :
    Real.exp (-ell/10)≤240000/ell^4 := by
  have hp : 0<ell := by linarith
  have h := Real.pow_div_factorial_le_exp (ell/10) (by positivity : (0:ℝ)≤ell/10) 4
  norm_num at h
  have he : Real.exp (-ell/10)=1/Real.exp (ell/10) := by rw [show -ell/10=-(ell/10) by ring,Real.exp_neg,one_div]
  rw [he]
  apply (le_div_iff₀ (pow_pos hp _)).mpr
  rw [one_div_mul_eq_div]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  nlinarith only [h]

theorem large_B_error {ell : ℝ} (hell : 4096≤ell) :
    (1200/ell+3*ell)*Real.exp (-ell/10)<1/50000 := by
  have hp : 0<ell := by linarith
  have h4 : 1200/ell+3*ell≤4*ell := by
    have hh : 1200/ell≤ell := (div_le_iff₀ hp).mpr (by nlinarith)
    linarith
  have hc : (1200/ell+3*ell)*Real.exp (-ell/10)≤960000/ell^3 := by
    calc
      _ ≤ (4*ell)*(240000/ell^4) := mul_le_mul h4 (exp_tenth_inverse_le hell)
        (Real.exp_nonneg _) (by positivity)
      _ = _ := by field_simp;ring
  have hm : 960000/ell^3≤960000/(4096:ℝ)^3 := by gcongr
  exact (hc.trans hm).trans_lt (by norm_num)

/-- Exact final large-B scalar budget. It does not assert the analytic row
estimate that must precede it. -/
theorem large_B_budget {ell : ℝ} (hell : 4096≤ell) :
    (5/3:ℝ)*(7/20+17/(20*143))+(10/128:ℝ)*(1+3/(2*143))+
      (1200/ell+3*ell)*Real.exp (-ell/10)<673/1000 := by
  have h := large_B_error hell
  norm_num at *
  linarith

theorem large_A_budget {ell : ℝ} (hell : 4096≤ell) :
    ((1/2:ℝ)+1/143)/(4/5)+(50/ell+2*ell)*Real.exp (-ell/10)<127/200 := by
  have hp : 0<ell := by linarith
  have hle : 50/ell+2*ell≤1200/ell+3*ell := by
    have hh : 50/ell≤1200/ell := div_le_div_of_nonneg_right (by norm_num) hp.le
    linarith
  have h := (mul_le_mul_of_nonneg_right hle (Real.exp_nonneg _)).trans_lt (large_B_error hell)
  norm_num at *
  linarith

theorem moderate_A_budget {ell A : ℝ} (hell : 4096≤ell) (hA : Real.exp ell<A) :
    (647/1000:ℝ)*ell/(ell-1)+(92/100:ℝ)*ell/(A*(ell-1))+
      (1107/1000:ℝ)*ell/(143*((9/10:ℝ)*ell-1))+
      2*ell*Real.exp (-ell/10)<657/1000 := by
  have hp : 0<ell := by linarith
  have hden : 0<ell-1 := by linarith
  have hAell : ell<A := by have hh := Real.add_one_le_exp ell;linarith
  have hapos : 0<A := hp.trans hAell
  have h1 : ell/(ell-1)≤4096/4095 := (div_le_iff₀ hden).mpr (by nlinarith)
  have h2 : ell/(A*(ell-1))≤1/4095 := by
    apply (div_le_iff₀ (mul_pos hapos hden)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hAell.le hden.le]
  have h3 : ell/((9/10:ℝ)*ell-1)≤40960/36854 :=
    (div_le_iff₀ (by linarith)).mpr (by nlinarith)
  have he : 2*ell*Real.exp (-ell/10)<1/50000 := by
    have hm : 2*ell≤1200/ell+3*ell := by
      have hh : 0≤1200/ell := by positivity
      linarith
    exact (mul_le_mul_of_nonneg_right hm (Real.exp_nonneg _)).trans_lt (large_B_error hell)
  have h1' := mul_le_mul_of_nonneg_left h1 (by norm_num : (0:ℝ)≤647/1000)
  have h2' := mul_le_mul_of_nonneg_left h2 (by norm_num : (0:ℝ)≤92/100)
  have h3' := mul_le_mul_of_nonneg_left h3 (by norm_num : (0:ℝ)≤(1107/1000)/143)
  have heq1 : (647/1000:ℝ)*ell/(ell-1)=(647/1000)*(ell/(ell-1)) := by ring
  have heq2 : (92/100:ℝ)*ell/(A*(ell-1))=(92/100)*(ell/(A*(ell-1))) := by ring
  have heq3 : (1107/1000:ℝ)*ell/(143*((9/10)*ell-1))=((1107/1000)/143)*(ell/((9/10)*ell-1)) := by rw [div_mul_eq_div_div];ring
  rw [heq1,heq2,heq3]
  norm_num at h1' h2' h3'
  linarith

end LonelyRunnerNew.RoughRational.Asymmetric
