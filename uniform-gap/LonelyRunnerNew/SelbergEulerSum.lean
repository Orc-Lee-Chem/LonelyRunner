import LonelyRunnerNew.SelbergEuler

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew.FiniteSelberg
attribute [local instance] Classical.propDecidable

theorem subset_primes_iff_prod_dvd {P s : Finset ℕ} (hP : ∀p∈P,Nat.Prime p)
    (hs : s⊆P) {n : ℕ} (hn : 0<n) :
    s⊆n.primeFactors ↔ (∏p∈s,p)∣n := by
  constructor
  · intro h
    exact (Finset.prod_dvd_prod_of_subset _ _ _ h).trans (Nat.prod_primeFactors_dvd n)
  · intro h p hp
    exact Nat.mem_primeFactors.mpr ⟨hP p (hs hp),
      (Finset.dvd_prod_of_mem (fun p : ℕ => p) hp).trans h,hn.ne'⟩

theorem euler_expansion (P : Finset ℕ) (h : ℕ → ℝ) {n : ℕ} (hn : 0<n)
    (hP : ∀p∈P,Nat.Prime p) (hnP : n.primeFactors⊆P) :
    (∏p∈n.primeFactors,(1+h p))=
      ∑s∈P.powerset,if (∏p∈s,p)∣n then ∏p∈s,h p else 0 := by
  rw [Finset.prod_one_add]
  have he : P.powerset.filter (fun s => s⊆n.primeFactors)=n.primeFactors.powerset := by
    ext s
    simp only [Finset.mem_filter,Finset.mem_powerset]
    exact ⟨fun h => h.2,fun h => ⟨h.trans hnP,h⟩⟩
  rw [←he,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s hs
  have hi := subset_primes_iff_prod_dvd hP (Finset.mem_powerset.mp hs) hn
  simp only [hi]

/-- Finite divisor expansion and exact multiples count, with an arbitrary
nonnegative prime weight. No density estimate is assumed. -/
theorem finite_euler_average (X : ℕ) (P : Finset ℕ) (h : ℕ → ℝ)
    (hP : ∀p∈P,Nat.Prime p) (hh : ∀p∈P,0≤h p)
    (hcover : ∀n∈Finset.Icc 1 X,n.primeFactors⊆P) :
    (∑n∈Finset.Icc 1 X,∏p∈n.primeFactors,(1+h p))≤
      (X:ℝ)*∏p∈P,(1+h p/(p:ℝ)) := by
  have hex : (∑n∈Finset.Icc 1 X,∏p∈n.primeFactors,(1+h p))=
      ∑s∈P.powerset,(∏p∈s,h p)*((X/(∏p∈s,p):ℕ):ℝ) := by
    have he : (∑n∈Finset.Icc 1 X,∏p∈n.primeFactors,(1+h p))=
        ∑n∈Finset.Icc 1 X,∑s∈P.powerset,if (∏p∈s,p)∣n then ∏p∈s,h p else 0 :=
      Finset.sum_congr rfl (fun n hn => euler_expansion P h (Finset.mem_Icc.mp hn).1 hP (hcover n hn))
    rw [he,Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s hs
    rw [←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
    have hI : Finset.Icc 1 X=Finset.Ioc 0 X := by ext n;simp;omega
    rw [hI,Nat.Ioc_filter_dvd_card_eq_div,mul_comm]
  rw [hex]
  have hi (s : Finset ℕ) (hs : s∈P.powerset) :
      (∏p∈s,h p)*((X/(∏p∈s,p):ℕ):ℝ)≤
        (X:ℝ)*∏p∈s,h p/(p:ℝ) := by
    have hsP := Finset.mem_powerset.mp hs
    have hd : 0<∏p∈s,p := Finset.prod_pos (fun p hp => (hP p (hsP hp)).pos)
    have hdR : (0:ℝ)<∏p∈s,(p:ℝ) := by rw [←Nat.cast_prod];exact_mod_cast hd
    have hhR : ((X/(∏p∈s,p):ℕ):ℝ)≤(X:ℝ)/(∏p∈s,(p:ℝ)) := by
      apply (le_div_iff₀ hdR).mpr
      rw [←Nat.cast_prod]
      exact_mod_cast Nat.div_mul_le_self X (∏p∈s,p)
    have hnon : 0≤∏p∈s,h p := Finset.prod_nonneg (fun p hp => hh p (hsP hp))
    calc
      _ ≤ (∏p∈s,h p)*((X:ℝ)/(∏p∈s,(p:ℝ))) := mul_le_mul_of_nonneg_left hhR hnon
      _ = _ := by rw [Finset.prod_div_distrib];ring
  calc
    _ ≤ ∑s∈P.powerset,(X:ℝ)*∏p∈s,h p/(p:ℝ) := Finset.sum_le_sum hi
    _ = _ := by rw [←Finset.mul_sum,←Finset.prod_one_add]

theorem actual_euler_average (X : ℕ) :
    (∑n∈Finset.Icc 1 X,∏p∈n.primeFactors,(1+2/((p:ℝ)-1)))≤(X:ℝ)*eulerProduct X := by
  have hc (n : ℕ) (hn : n∈Finset.Icc 1 X) : n.primeFactors⊆primes X := by
    intro p hp
    have hh := Nat.mem_primeFactors.mp hp
    have hnX := Finset.mem_Icc.mp hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hh.1.two_le,(Nat.le_of_dvd hnX.1 hh.2.1).trans hnX.2⟩,hh.1⟩
  have he := finite_euler_average X (primes X) (fun p => 2/((p:ℝ)-1))
    (fun p hp => (Finset.mem_filter.mp hp).2)
    (fun p hp => by
      have hh : (2:ℝ)≤p := by exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
      exact div_nonneg (by norm_num) (by linarith)) hc
  have hp : (∏p∈primes X,(1+(2/((p:ℝ)-1))/(p:ℝ)))=eulerProduct X := by
    unfold eulerProduct
    apply Finset.prod_congr rfl
    intro p hp
    rw [div_div]
    ring
  rw [hp] at he
  exact he

end LonelyRunnerNew.FiniteSelberg
