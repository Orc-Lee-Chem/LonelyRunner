import LonelyRunnerNew.SaturatedIntegral

noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace LonelyRunnerNew.Saturated

/-- Successive one-dimensional integration. No product-space integral or
unproved interchange of two integrals is used. -/
theorem integral_inner {t : ℝ} (ht : 0<t) : (∫ v in (0:ℝ)..1,inner t v)=Psi t := by
  by_cases ht1 : 1≤t
  · have hs : (1:ℝ)≤t^2 := by nlinarith
    have heq : (∫ v in (0:ℝ)..1,inner t v)=∫ _ in (0:ℝ)..1,(1:ℝ) := by
      apply intervalIntegral.integral_congr
      intro v hv
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ)≤1)] at hv
      exact inner_low ht hv.1 (hv.2.trans hs)
    simpa [Psi,ht1] using heq
  · have hsmall : t<1 := lt_of_not_ge ht1
    let c := t^2
    have hc0 : 0<c := sq_pos_of_pos ht
    have hc1 : c≤1 := by dsimp [c];nlinarith
    have hi (a b : ℝ) (ha : 0≤a) (hab : a≤b) : IntervalIntegrable (inner t) volume a b := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
      exact ((inner_antitone ht).mono (fun _ hx => ha.trans hx.1)).integrableOn_isCompact isCompact_Icc
    have hleft : (∫ v in (0:ℝ)..c,inner t v)=c := by
      calc
        _ = ∫ _ in (0:ℝ)..c,(1:ℝ) := by
          apply intervalIntegral.integral_congr
          intro v hv
          rw [Set.uIcc_of_le hc0.le] at hv
          exact inner_low ht hv.1 hv.2
        _ = c := by simp
    have hpow : IntervalIntegrable (fun v : ℝ => v^(-(1/2):ℝ)) volume c 1 :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    have hinv : IntervalIntegrable (fun v : ℝ => 1/v) volume c 1 := by
      apply intervalIntegral.intervalIntegrable_one_div _ continuous_id.continuousOn
      intro v hv
      rw [Set.uIcc_of_le hc1] at hv
      exact (hc0.trans_le hv.1).ne'
    have hright : (∫ v in c..(1:ℝ),inner t v)=
        4*t*(1-t)+2*t^2*Real.log t := by
      have heq : (∫ v in c..(1:ℝ),inner t v)=
          ∫ v in c..(1:ℝ),2*t*v^(-(1/2):ℝ)-t^2*(1/v) := by
        apply intervalIntegral.integral_congr
        intro v hv
        rw [Set.uIcc_of_le hc1] at hv
        have hv0 : 0<v := hc0.trans_le hv.1
        change inner t v=2*t*v^(-(1/2):ℝ)-t^2*(1/v)
        rw [inner_high ht hv.1,Real.rpow_neg hv0.le,←Real.sqrt_eq_rpow]
        ring
      rw [heq,intervalIntegral.integral_sub (hpow.const_mul _) (hinv.const_mul _),
        intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
        integral_rpow (Or.inl (by norm_num)),integral_one_div_of_pos hc0 (by norm_num)]
      have hroot : c^(1/2:ℝ)=t := by
        rw [←Real.sqrt_eq_rpow,Real.sqrt_sq_eq_abs,abs_of_pos ht]
      have hlog : Real.log (1/c)= -2*Real.log t := by
        rw [one_div,Real.log_inv]
        dsimp [c]
        rw [Real.log_pow]
        ring
      norm_num only [show (-(1/2):ℝ)+1=1/2 by norm_num,Real.one_rpow,hroot,hlog]
      ring
    have he := intervalIntegral.integral_add_adjacent_intervals (hi 0 c (by norm_num) hc0.le)
      (hi c 1 hc0.le hc1)
    rw [hleft,hright] at he
    simp only [Psi,if_neg ht1]
    rw [←he]
    dsimp [c]
    ring

end LonelyRunnerNew.Saturated
