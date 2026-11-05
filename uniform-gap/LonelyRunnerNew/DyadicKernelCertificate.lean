import LonelyRunnerNew.DyadicScaleAlgebra
import LonelyRunnerNew.SmallPrimeAnalytic

noncomputable section
set_option autoImplicit false
namespace LonelyRunnerNew.DyadicPhysical

def lamLo : ℚ := 84162168428649/100000000000000
def lamHi : ℚ := 84162168428650/100000000000000
def aLo : ℚ := 17242467178108/100000000000000
def aHi : ℚ := 17242467178109/100000000000000
def aSqrtHi : ℚ := 4152404987247/10000000000000
def normUpper : ℚ := (Certificate.sqrt3Upper/2)*lamHi*aHi*aSqrtHi/(1-lamHi)^2+
  1-2*lamLo*(aLo-1+lamLo)/(1-lamLo)^2

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem rational_certificates :
    lamLo^201*(2:ℚ)^50≤1 ∧ 1≤lamHi^201*(2:ℚ)^50 ∧
    aLo*(201/50:ℚ)≤Certificate.logLowerQ 2 24 ∧
    Certificate.logUpperQ 2 24≤aHi*(201/50:ℚ) ∧
    aHi≤aSqrtHi^2 ∧ normUpper≤Certificate.Bbar := by
  norm_num [lamLo,lamHi,aLo,aHi,aSqrtHi,normUpper,Certificate.sqrt3Upper,Certificate.Bbar,
    Certificate.logUpperQ,Certificate.logLowerQ,Finset.sum_range_succ]

theorem lambda_enclosure : (lamLo:ℝ)≤lambda q ∧ lambda q≤(lamHi:ℝ) := by
  have hlo : (0:ℝ)<lamLo := by norm_num [lamLo]
  have hhi : (0:ℝ)<lamHi := by norm_num [lamHi]
  constructor
  · have hc : (lamLo:ℝ)^201*(2:ℝ)^50≤1 := by exact_mod_cast rational_certificates.1
    have hh := Real.log_le_log (mul_pos (pow_pos hlo _) (by positivity)) hc
    rw [Real.log_mul (pow_ne_zero _ hlo.ne') (by norm_num),Real.log_pow,Real.log_pow,Real.log_one] at hh
    apply (Real.log_le_log_iff hlo (lambda_pos q)).mp
    rw [lambda,Real.log_rpow (by norm_num : (0:ℝ)<2)]
    norm_num [q] at *
    linarith
  · have hc : (1:ℝ)≤(lamHi:ℝ)^201*(2:ℝ)^50 := by exact_mod_cast rational_certificates.2.1
    have hh := RationalAnalysis.root_bound (by norm_num : (0:ℝ)<2) hhi 50 201 (by norm_num) hc
    convert hh using 1 <;> norm_num [lambda,q]

theorem exponent_enclosure : (aLo:ℝ)≤-Real.log (lambda q) ∧ -Real.log (lambda q)≤(aHi:ℝ) := by
  have hh := Certificate.rational_log_enclosure 2 (by norm_num) 24
  have hl : (aLo:ℝ)*q≤(Certificate.logLowerQ 2 24:ℝ) := by
    have h : ((aLo*(201/50:ℚ):ℚ):ℝ)≤(Certificate.logLowerQ 2 24:ℝ) := by
      exact_mod_cast rational_certificates.2.2.1
    push_cast at h
    simpa only [q] using h
  have hu : (Certificate.logUpperQ 2 24:ℝ)≤(aHi:ℝ)*q := by
    have h : (Certificate.logUpperQ 2 24:ℝ)≤((aHi*(201/50:ℚ):ℚ):ℝ) := by
      exact_mod_cast rational_certificates.2.2.2.1
    push_cast at h
    simpa only [q] using h
  have hq : 0<q := by norm_num [q]
  have he : -Real.log (lambda q)=Real.log 2/q := by rw [lambda,Real.log_rpow (by norm_num : (0:ℝ)<2)];ring
  rw [he]
  have hlLog : (Certificate.logLowerQ 2 24:ℝ)≤Real.log 2 := by simpa only [Rat.cast_ofNat] using hh.1
  have huLog : Real.log 2≤(Certificate.logUpperQ 2 24:ℝ) := by simpa only [Rat.cast_ofNat] using hh.2
  constructor
  · exact (le_div_iff₀ hq).mpr (hl.trans hlLog)
  · exact (div_le_iff₀ hq).mpr (huLog.trans hu)

/-- The frozen Bbar bounds the actual dyadic kernel. No monotonicity of
kernelN is assumed: every positive and subtracted term is enclosed separately. -/
theorem dyadic_kernel_le_Bbar : kernelN (lambda q)≤(Certificate.Bbar:ℝ) := by
  let lam := lambda q
  let a := -Real.log lam
  have hl0 : 0<lam := lambda_pos q
  have hl1 : lam<1 := lambda_lt_one (by norm_num [q] : 0<q)
  have ha : 0<a := neg_pos.mpr (Real.log_neg hl0 hl1)
  have hL := lambda_enclosure.1
  have hU := lambda_enclosure.2
  have haL := exponent_enclosure.1
  have haU := exponent_enclosure.2
  have hLo0 : (0:ℝ)<lamLo := by norm_num [lamLo]
  have hHi0 : (0:ℝ)<lamHi := by norm_num [lamHi]
  have hHi1 : (lamHi:ℝ)<1 := by norm_num [lamHi]
  have hLo1 : (lamLo:ℝ)<1 := by norm_num [lamLo]
  have haHi0 : (0:ℝ)≤aHi := by norm_num [aHi]
  have hs0 : (0:ℝ)≤aSqrtHi := by norm_num [aSqrtHi]
  have hsq : (aHi:ℝ)≤(aSqrtHi:ℝ)^2 := by exact_mod_cast rational_certificates.2.2.2.2.1
  have hsqrt : Real.sqrt a≤(aSqrtHi:ℝ) := Real.sqrt_le_iff.mpr ⟨hs0,haU.trans hsq⟩
  have hpow : a^(3/2:ℝ)=a*Real.sqrt a := by
    rw [show (3/2:ℝ)=1+1/2 by norm_num,Real.rpow_one_add' ha.le (by norm_num),← Real.sqrt_eq_rpow]
  have hn : (Real.sqrt 3/2)*lam*a*Real.sqrt a≤
      ((Certificate.sqrt3Upper:ℝ)/2)*(lamHi:ℝ)*(aHi:ℝ)*(aSqrtHi:ℝ) := by
    have hs3 : (0:ℝ)≤Certificate.sqrt3Upper := by norm_num [Certificate.sqrt3Upper]
    gcongr <;> first | exact Certificate.sqrt_three_upper | exact hU | exact haU | exact hsqrt | positivity
  have hD : 0<(1-lam)^2 := sq_pos_of_pos (sub_pos.mpr hl1)
  have hDlo : 0<(1-(lamHi:ℝ))^2 := sq_pos_of_pos (sub_pos.mpr hHi1)
  have hDhi : 0<(1-(lamLo:ℝ))^2 := sq_pos_of_pos (sub_pos.mpr hLo1)
  have hdl : (1-(lamHi:ℝ))^2≤(1-lam)^2 :=
    pow_le_pow_left₀ (sub_pos.mpr hHi1).le (sub_le_sub_left hU 1) 2
  have hdu : (1-lam)^2≤(1-(lamLo:ℝ))^2 :=
    pow_le_pow_left₀ (sub_pos.mpr hl1).le (sub_le_sub_left hL 1) 2
  have hnU0 : 0≤((Certificate.sqrt3Upper:ℝ)/2)*(lamHi:ℝ)*(aHi:ℝ)*(aSqrtHi:ℝ) := by
    norm_num [Certificate.sqrt3Upper,lamHi,aHi,aSqrtHi]
  have hC := (div_le_div_of_nonneg_right hn hD.le).trans
    (div_le_div_of_nonneg_left hnU0 hDlo hdl)
  have hc0 : (0:ℝ)≤aLo-1+lamLo := by norm_num [aLo,lamLo]
  have hc : (aLo:ℝ)-1+(lamLo:ℝ)≤a-1+lam := by linarith
  have hnum := mul_le_mul (show (2:ℝ)*(lamLo:ℝ)≤2*lam by linarith) hc hc0 (by positivity : (0:ℝ)≤2*lam)
  have hneg := (div_le_div_of_nonneg_left (mul_nonneg (by positivity : (0:ℝ)≤2*(lamLo:ℝ)) hc0) hD hdu).trans
    (div_le_div_of_nonneg_right hnum hD.le)
  have hcert : (normUpper:ℝ)≤(Certificate.Bbar:ℝ) := by exact_mod_cast rational_certificates.2.2.2.2.2
  unfold normUpper at hcert
  push_cast at hcert
  unfold kernelN
  change (Real.sqrt 3/2)*lam*a^(3/2:ℝ)/(1-lam)^2+1-2*lam*(a-1+lam)/(1-lam)^2≤_
  rw [hpow,← mul_assoc]
  linarith only [hC,hneg,hcert]

end LonelyRunnerNew.DyadicPhysical
