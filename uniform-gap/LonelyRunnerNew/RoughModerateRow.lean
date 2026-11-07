import LonelyRunnerNew.RoughPrimeIntervals
import LonelyRunnerNew.AsymmetricBudgets

noncomputable section
set_option autoImplicit false
namespace LonelyRunnerNew.RoughRational

theorem moderate_log_domains {ell R A : ℝ} (hell : 4096≤ell)
    (hA : Real.exp ell<A) (hRA : A/2≤R) :
    1<R ∧ 1000≤Real.log A ∧ 1000≤Real.log (R-1) ∧
      1000≤Real.log (A/143) ∧ ell-1≤Real.log R := by
  have hp : 0<ell := by linarith
  have hE := Real.add_one_le_exp (ell/2)
  have hEpos := Real.exp_pos (ell/2)
  have he : Real.exp (ell/2)^2=Real.exp ell := by
    rw [pow_two,←Real.exp_add,show ell/2+ell/2=ell by ring]
  have hRhalf : Real.exp (ell/2)<R-1 := by nlinarith
  have hAhalf : Real.exp (ell/2)<A/143 := by nlinarith
  have hApos : 0<A := (Real.exp_pos _).trans hA
  have hRpos : 0<R := by linarith
  have hR1 : 1<R := by nlinarith
  have hRlog := Real.log_le_log hEpos hRhalf.le
  have hAlow := Real.log_le_log hEpos hAhalf.le
  rw [Real.log_exp] at hRlog hAlow
  have hloga := Real.log_lt_log (Real.exp_pos _) hA
  rw [Real.log_exp] at hloga
  have hRbig : Real.exp ell<2*R := by linarith
  have hl := Real.log_lt_log (Real.exp_pos _) hRbig
  rw [Real.log_exp,Real.log_mul (by norm_num : (2:ℝ)≠0) hRpos.ne'] at hl
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  norm_num at h2
  exact ⟨hR1,by linarith,by linarith,by linarith,by linarith⟩

/-- The full medium-A single-row branch, including the closed left endpoint
and the +1 from the second interval. No prime-counting input is accepted. -/
theorem moderate_single_row_bound (S : Finset ℚ) {R T ell : ℝ} (hR : 0<R) (hT : 0<T)
    (hell : 4096≤ell) (hB : Real.sqrt (T/R)<128)
    (hAlo : Real.exp ell<min (2*R) T)
    (hAhi : min (2*R) T≤Real.exp ((17/10:ℝ)*ell))
    (hrough : ∀r∈S,roughPoint 142 r)
    (hsector : ∀r∈S,R≤(r:ℝ) ∧ (r:ℝ)<2*R) (hsep : separated (Real.exp ell) S) :
    (count S T:ℝ)<1+(657/1000:ℝ)*(min (2*R) T)/ell := by
  let A := min (2*R) T
  let X := Asymmetric.cutoff ell (9/10)
  have hApos : 0<A := by dsimp [A];positivity
  by_cases hz : count S T=0
  · rw [hz,Nat.cast_zero]
    have he : 0<ell := by linarith
    positivity
  have hRA : A/2≤R := by have hh : A≤2*R := min_le_left _ _;linarith
  have hRA' : R≤A := by
    have hn : (countedSet S T).Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero hz)
    obtain ⟨r,hr⟩ := hn
    have hm := Finset.mem_filter.mp hr
    have hd := small_B_denominator_one hR hT hB (hrough r hm.1) (hsector r hm.1).1 hm.2
    have he : (product r:ℝ)=(r:ℝ) := by
      rw [cast_eq_abs_num_div_den r (hrough r hm.1).1,product,hd]
      simp
    have hRT : R≤T := (hsector r hm.1).1.trans (by simpa only [he] using hm.2)
    exact le_min (by linarith) hRT
  obtain ⟨hRone,hlogA,hlogR,hlogSmall,hlogR'⟩ := moderate_log_domains hell hAlo hRA
  have hL : 0<ell-1 := by linarith
  have hL' : 0<(9/10:ℝ)*ell-1 := by linarith
  have hsq : A<(X:ℝ)^2 := Asymmetric.moderate_cutoff_square hell hAhi
  have hlogX : (9/10:ℝ)*ell-1≤Real.log (X:ℝ) :=
    (Asymmetric.cutoff_log_lower hell (alpha:=9/10) (by norm_num) (le_refl _)).le
  have hfirst := rough_interval_theta hRone hRA' hsq hL hlogR'
  have hthetaA := (RCThirty.theta_explicit hApos hlogA).2
  have hthetaR := (RCThirty.theta_explicit (by linarith : 0<R-1) hlogR).1
  have hfirst' : ((roughIntegerInterval X R A).card:ℝ)≤((647/1000:ℝ)*A+92/100)/(ell-1) := by
    apply hfirst.trans
    apply div_le_div_of_nonneg_right _ hL.le
    nlinarith
  have hsmallpos : 0<A/143 := by positivity
  have hs : A/143<(X:ℝ)^2 := (by linarith : A/143≤A).trans_lt hsq
  have hsecond := rough_interval_theta_upper (X:=X) hsmallpos.le hs hL' hlogX
  have hthetaS := (RCThirty.theta_explicit hsmallpos hlogSmall).2
  have hsecond' : ((roughIntegerInterval X 1 (A/143)).card:ℝ)≤
      1+(1107/1000:ℝ)*A/(143*((9/10:ℝ)*ell-1)) := by
    apply hsecond.trans
    have hd := div_le_div_of_nonneg_right hthetaS hL'.le
    have he : ((1107/1000:ℝ)*(A/143))/((9/10:ℝ)*ell-1)=
        (1107/1000:ℝ)*A/(143*((9/10:ℝ)*ell-1)) := by rw [div_mul_eq_div_div];ring
    rw [he] at hd
    linarith
  have hpack := Asymmetric.small_B_power_packing S hR hT hell (alpha:=9/10)
    (by norm_num) (le_refl _) hB hrough hsector hsep
  have hbudget := Asymmetric.moderate_A_budget hell hAlo
  have hmul := mul_lt_mul_of_pos_left hbudget (div_pos hApos (by linarith : 0<ell))
  have hel : ell≠0 := by linarith
  have he : (A/ell)*((647/1000:ℝ)*ell/(ell-1)+(92/100:ℝ)*ell/(A*(ell-1))+
      (1107/1000:ℝ)*ell/(143*((9/10:ℝ)*ell-1))+2*ell*Real.exp (-ell/10))=
      ((647/1000:ℝ)*A+92/100)/(ell-1)+
      (1107/1000:ℝ)*A/(143*((9/10:ℝ)*ell-1))+2*A*Real.exp (-ell/10) := by
    field_simp <;> ring
  rw [he] at hmul
  change (count S T:ℝ)≤(roughIntegerInterval X R A).card+
    (roughIntegerInterval X 1 (A/143)).card+2*A*Real.exp (-ell/10) at hpack
  change (count S T:ℝ)<1+(657/1000:ℝ)*A/ell
  have heq : (A/ell)*(657/1000:ℝ)=(657/1000)*A/ell := by ring
  rw [heq] at hmul
  linarith

theorem rc_small_B_moderate (S : Finset ℚ) {R T ell : ℝ} (hR : 0<R) (hT : 0<T)
    (hell : 4096≤ell) (hB : Real.sqrt (T/R)<128)
    (hAhi : min (2*R) T≤Real.exp ((17/10:ℝ)*ell))
    (hrough : ∀r∈S,roughPoint 142 r)
    (hsector : ∀r∈S,R≤(r:ℝ) ∧ (r:ℝ)<2*R) (hsep : separated (Real.exp ell) S) :
    (count S T:ℝ)≤1+(17/25:ℝ)*T/ell := by
  have he : 0<ell := by linarith
  by_cases hsmall : min (2*R) T≤Real.exp ell
  · have hc := row_singleton_of_small_upper S hR 0 (fun r hr => (hrough r hr).1) hsector hsep
      (by simpa only [Nat.cast_zero,zero_add,mul_one,div_one] using hsmall)
    rw [←small_B_count_one_row S hR hT hB hrough (fun r hr => (hsector r hr).1)] at hc
    have hcr : (count S T:ℝ)≤1 := by exact_mod_cast hc
    exact hcr.trans (le_add_of_nonneg_right (by positivity))
  · have hc := moderate_single_row_bound S hR hT hell hB (lt_of_not_ge hsmall) hAhi hrough hsector hsep
    have hmin := min_le_right (2*R) T
    have hm : (657/1000:ℝ)*(min (2*R) T)/ell≤(17/25:ℝ)*T/ell := by
      apply div_le_div_of_nonneg_right _ he.le
      nlinarith
    linarith

end LonelyRunnerNew.RoughRational
