import LonelyRunnerNew.RCSelbergRows
import LonelyRunnerNew.AsymmetricBudgets

noncomputable section
set_option autoImplicit false
namespace LonelyRunnerNew.RoughRational

theorem small_B_count_nonzero_R_le (S : Finset ℚ) {R T : ℝ} (hR : 0<R) (hT : 0<T)
    (hB : Real.sqrt (T/R)<128) (hrough : ∀r∈S,roughPoint 142 r)
    (hsector : ∀r∈S,R≤(r:ℝ) ∧ (r:ℝ)<2*R) (hc : count S T≠0) : R≤min (2*R) T := by
  have hn : (countedSet S T).Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero hc)
  obtain ⟨r,hr⟩ := hn
  have hm := Finset.mem_filter.mp hr
  have hd := small_B_denominator_one hR hT hB (hrough r hm.1) (hsector r hm.1).1 hm.2
  have he : (product r:ℝ)=(r:ℝ) := by
    rw [cast_eq_abs_num_div_den r (hrough r hm.1).1,product,hd]
    simp
  have hRT : R≤T := (hsector r hm.1).1.trans (by simpa only [he] using hm.2)
  exact le_min (by linarith) hRT

/-- The remaining small-B large-A branch, with the original RC constant. -/
theorem rc_small_B_large_A (S : Finset ℚ) {R T ell : ℝ} (hR : 0<R) (hT : 0<T)
    (hell : 4096≤ell) (hB : Real.sqrt (T/R)<128)
    (hA : Real.exp ((17/10:ℝ)*ell)<min (2*R) T)
    (hrough : ∀r∈S,roughPoint 142 r)
    (hsector : ∀r∈S,R≤(r:ℝ) ∧ (r:ℝ)<2*R) (hsep : separated (Real.exp ell) S) :
    (count S T:ℝ)≤1+(17/25:ℝ)*T/ell := by
  have he0 : 0<ell := by linarith
  by_cases hz : count S T=0
  · rw [hz,Nat.cast_zero];positivity
  let A := min (2*R) T
  have hApos : 0<A := by dsimp [A];positivity
  have hRA := small_B_count_nonzero_R_le S hR hT hB hrough hsector hz
  have hpack := Asymmetric.small_B_power_packing S hR hT hell (alpha:=4/5)
    (by norm_num) (by norm_num) hB hrough hsector hsep
  have hs := two_interval_power_sieve hell (alpha:=4/5) (by norm_num) (by norm_num) hR hRA
  have hm : (A-R+A/143)/((4/5:ℝ)*ell)≤((1/2:ℝ)+1/143)*A/((4/5:ℝ)*ell) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hh : A≤2*R := min_le_left _ _
    nlinarith
  have hexp : Real.exp ((8/5:ℝ)*ell)≤A*Real.exp (-ell/10) := by
    have hi := mul_le_mul_of_nonneg_right hA.le (Real.exp_nonneg (-ell/10))
    rw [←Real.exp_add] at hi
    have he : (17/10:ℝ)*ell+-ell/10=(8/5:ℝ)*ell := by ring
    simpa only [he] using hi
  have herr : 32*Real.exp (2*(4/5:ℝ)*ell)/((4/5:ℝ)*ell)^2≤
      50*A*Real.exp (-ell/10)/ell^2 := by
    have hh : 32*Real.exp (2*(4/5:ℝ)*ell)/((4/5:ℝ)*ell)^2=
        50*Real.exp ((8/5:ℝ)*ell)/ell^2 := by
      rw [show 2*(4/5:ℝ)*ell=(8/5:ℝ)*ell by ring]
      ring
    rw [hh]
    apply div_le_div_of_nonneg_right _ (sq_nonneg ell)
    nlinarith
  have hraw : (count S T:ℝ)≤((1/2:ℝ)+1/143)*A/((4/5:ℝ)*ell)+
      50*A*Real.exp (-ell/10)/ell^2+2*A*Real.exp (-ell/10) := by
    change (count S T:ℝ)≤(roughIntegerInterval (Asymmetric.cutoff ell (4/5)) R A).card+
      (roughIntegerInterval (Asymmetric.cutoff ell (4/5)) 1 (A/143)).card+2*A*Real.exp (-ell/10) at hpack
    change ((roughIntegerInterval (Asymmetric.cutoff ell (4/5)) R A).card:ℝ)+
      (roughIntegerInterval (Asymmetric.cutoff ell (4/5)) 1 (A/143)).card≤
      (A-R+A/143)/((4/5:ℝ)*ell)+32*Real.exp (2*(4/5:ℝ)*ell)/((4/5:ℝ)*ell)^2 at hs
    linarith
  have hb := Asymmetric.large_A_budget hell
  have hmul := mul_lt_mul_of_pos_left hb (div_pos hApos he0)
  have hidentity : (A/ell)*(((1/2:ℝ)+1/143)/(4/5)+(50/ell+2*ell)*Real.exp (-ell/10))=
      ((1/2:ℝ)+1/143)*A/((4/5:ℝ)*ell)+50*A*Real.exp (-ell/10)/ell^2+2*A*Real.exp (-ell/10) := by
    field_simp <;> ring
  rw [hidentity] at hmul
  have hmin : A≤T := min_le_right _ _
  have hbudget : (A/ell)*(127/200:ℝ)≤(17/25:ℝ)*T/ell := by
    have he : (A/ell)*(127/200:ℝ)=(127/200)*A/ell := by ring
    rw [he]
    apply div_le_div_of_nonneg_right _ he0.le
    nlinarith
  linarith

end LonelyRunnerNew.RoughRational
