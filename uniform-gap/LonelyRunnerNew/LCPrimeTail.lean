import LonelyRunnerNew.LCNumericIntervals
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
open scoped BigOperators
namespace LonelyRunnerNew.LCNumeric

/-- Elementary arithmetic-progression integral comparison. It bounds every
finite selection, so it applies directly to the state's finite prime support. -/
theorem progression_tail {alpha b : ℝ} (ha : 1 < alpha) (hb : 0 < b) (F : Finset ℕ) :
    (∑ k ∈ F,((30:ℝ)*k+b)^(-alpha)) ≤ b^(-alpha)+b^(1-alpha)/(30*(alpha-1)) := by
  let m := F.sup id
  let f : ℝ → ℝ := fun x => (30*x+b)^(-alpha)
  have hanti : AntitoneOn f (Set.Icc (0:ℝ) (m:ℝ)) := by
    intro x hx y hy hxy
    have hbase : 0 < 30*x+b := by linarith [hx.1]
    exact Real.rpow_le_rpow_of_nonpos hbase (by linarith) (by linarith)
  have hsum : (∑ i ∈ Finset.range m,f (0+((i+1:ℕ):ℝ))) ≤
      ∫ x in (0:ℝ)..0+(m:ℝ),f x := by
    apply AntitoneOn.sum_le_integral
    simpa only [zero_add] using hanti
  have heval : (∫ x in (0:ℝ)..(m:ℝ),f x) =
      (b^(1-alpha)-(30*(m:ℝ)+b)^(1-alpha))/(30*(alpha-1)) := by
    dsimp [f]
    rw [intervalIntegral.integral_comp_mul_add (f := fun x : ℝ => x^(-alpha))
      (c := 30) (a := 0) (b := (m:ℝ)) (by norm_num) b]
    simp only [mul_zero,zero_add,smul_eq_mul]
    have hnon : (0:ℝ) ∉ Set.uIcc b (30*(m:ℝ)+b) := by
      rw [Set.uIcc_of_le (by linarith [show (0:ℝ) ≤ (m:ℝ) from Nat.cast_nonneg m] : b ≤ 30*(m:ℝ)+b)]
      intro h
      exact (not_le_of_gt hb) h.1
    rw [integral_rpow (Or.inr ⟨(by linarith : -alpha ≠ -1),hnon⟩)]
    have hne : alpha-1 ≠ 0 := by linarith
    rw [show -alpha+1=1-alpha by ring]
    rw [show 30*(m:ℝ)+b=(m:ℝ)*30+b by ring]
    field_simp [hne,show 1-alpha ≠ 0 by linarith]
    ring
  have hI : (∫ x in (0:ℝ)..(m:ℝ),f x) ≤ b^(1-alpha)/(30*(alpha-1)) := by
    rw [heval]
    exact div_le_div_of_nonneg_right (sub_le_self _ (Real.rpow_nonneg (by positivity) _)) (by positivity)
  have hsub : F ⊆ Finset.range (m+1) := by
    intro k hk
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hk))
  calc
    _ ≤ ∑ k ∈ Finset.range (m+1),f (k:ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => Real.rpow_nonneg (by positivity) _)
    _ = f 0+∑ k ∈ Finset.range m,f ((k:ℝ)+1) := by
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_add,Nat.cast_one,Nat.cast_zero]
      ring
    _ ≤ f 0+(∫ x in (0:ℝ)..(m:ℝ),f x) := by
      apply add_le_add (le_refl (f 0))
      simpa only [zero_add,Nat.cast_add,Nat.cast_one] using hsum
    _ ≤ _ := by
      have hf0 : f 0=b^(-alpha) := by simp [f]
      rw [hf0]
      exact add_le_add le_rfl hI

/-- A prime above the cut belongs to one of the eight mod-30 residues.
No asymptotic prime-distribution theorem is used. -/
theorem prime_mod_thirty {p : ℕ} (hp : Nat.Prime p) (h5 : 5 < p) :
    p % 30 ∈ ({1,7,11,13,17,19,23,29}:Finset ℕ) := by
  have hp2 : ¬ 2 ∣ p := by
    intro h
    have hh := hp.eq_one_or_self_of_dvd 2 h
    omega
  have hp3 : ¬ 3 ∣ p := by
    intro h
    have hh := hp.eq_one_or_self_of_dvd 3 h
    omega
  have hp5 : ¬ 5 ∣ p := by
    intro h
    have hh := hp.eq_one_or_self_of_dvd 5 h
    omega
  have h2 : p%2≠0 := by simpa only [Nat.dvd_iff_mod_eq_zero] using hp2
  have h3 : p%3≠0 := by simpa only [Nat.dvd_iff_mod_eq_zero] using hp3
  have h5' : p%5≠0 := by simpa only [Nat.dvd_iff_mod_eq_zero] using hp5
  have hlt : p%30 < 30 := Nat.mod_lt _ (by decide)
  have hm2 : (p%30)%2=p%2 := Nat.mod_mod_of_dvd p (by decide : 2 ∣ 30)
  have hm3 : (p%30)%3=p%3 := Nat.mod_mod_of_dvd p (by decide : 3 ∣ 30)
  have hm5 : (p%30)%5=p%5 := Nat.mod_mod_of_dvd p (by decide : 5 ∣ 30)
  interval_cases h : p%30 <;> norm_num [h] at hm2 hm3 hm5 ⊢ <;> omega

def wheelResidues : Finset ℕ := {1,7,11,13,17,19,23,29}
def wheelBase (r : ℕ) : ℕ := 30*33333+r

theorem prime_wheel_sum (P : Finset ℕ)
    (hP : ∀ p ∈ P,Nat.Prime p ∧ 1000000 < p) :
    (∑ p ∈ P,(p:ℝ)^(-(100:ℝ)/67)) ≤
      ∑ r ∈ wheelResidues,
        ((wheelBase r:ℝ)^(-(100:ℝ)/67)+
        (wheelBase r:ℝ)^(1-(100:ℝ)/67)/(30*((100:ℝ)/67-1))) := by
  have hmaps : ∀ p ∈ P,p%30 ∈ wheelResidues := by
    intro p hp
    exact prime_mod_thirty (hP p hp).1 (by have := (hP p hp).2; omega)
  have hsplit : (∑ p ∈ P,(p:ℝ)^(-(100:ℝ)/67)) =
      ∑ r ∈ wheelResidues,∑ p ∈ P.filter (fun p => p%30=r),(p:ℝ)^(-(100:ℝ)/67) := by
    exact (Finset.sum_fiberwise_of_maps_to hmaps _).symm
  rw [hsplit]
  apply Finset.sum_le_sum
  intro r hr
  let Pr := P.filter (fun p => p%30=r)
  let idx := fun p : ℕ => p/30-33333
  have hquot (p : ℕ) (hp : p ∈ Pr) : 33333 ≤ p/30 := by
    have h := (hP p (Finset.mem_filter.mp hp).1).2
    omega
  have hinj : Set.InjOn idx (Pr:Set ℕ) := by
    intro p hp q hq heq
    have hpr := (Finset.mem_filter.mp hp).2
    have hqr := (Finset.mem_filter.mp hq).2
    have hpm := Nat.mod_add_div p 30
    have hqm := Nat.mod_add_div q 30
    have hpq := hquot p hp
    have hqq := hquot q hq
    dsimp [idx] at heq
    omega
  have he (p : ℕ) (hp : p ∈ Pr) : 30*idx p+wheelBase r=p := by
    have hpr := (Finset.mem_filter.mp hp).2
    have hpm := Nat.mod_add_div p 30
    have hpq := hquot p hp
    dsimp [idx,wheelBase]
    omega
  calc
    (∑ p ∈ Pr,(p:ℝ)^(-(100:ℝ)/67)) =
        ∑ p ∈ Pr,((30:ℝ)*idx p+(wheelBase r:ℝ))^(-(100:ℝ)/67) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hh := congrArg (fun n : ℕ => (n:ℝ)) (he p hp)
      norm_num only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at hh
      rw [hh]
    _ = ∑ k ∈ Pr.image idx,((30:ℝ)*k+(wheelBase r:ℝ))^(-(100:ℝ)/67) :=
      (Finset.sum_image (s := Pr) (g := idx)
        (f := fun k : ℕ => ((30:ℝ)*k+(wheelBase r:ℝ))^(-(100:ℝ)/67)) hinj).symm
    _ ≤ _ := by
      simpa only [neg_div] using progression_tail (by norm_num : (1:ℝ) < 100/67)
        (by unfold wheelBase; positivity : (0:ℝ) < (wheelBase r:ℝ)) (Pr.image idx)

end LonelyRunnerNew.LCNumeric
