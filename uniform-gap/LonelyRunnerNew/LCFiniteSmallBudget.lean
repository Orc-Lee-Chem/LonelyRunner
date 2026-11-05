import LonelyRunnerNew.LCNumericSmallIndex

noncomputable section
open scoped BigOperators
namespace LonelyRunnerNew.LCNumeric

theorem small_prime_budget (P : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ p∈P,0≤w p) (hP : ∀ p∈P,Nat.Prime p ∧ 142<p ∧ p≤10000)
    (hpoint : ∀ i : Fin 141,∀ p∈P,Index.smallLo i≤p → p<Index.smallHi i →
      w p ≤ (Index.smallCoefficient i:ℝ)*(p:ℝ)^(-(100:ℝ)/67)) :
    (∑ p∈P,w p) < (21/50:ℝ) := by
  have hbound (i : Fin 141) :
      (∑ p∈P.filter (fun p => Index.smallLo i≤p ∧ p<Index.smallHi i),w p) ≤
        (Index.smallCoefficient i:ℝ)*(Index.smallMoment i:ℝ) := by
    let Pr := P.filter (fun p => Index.smallLo i≤p ∧ p<Index.smallHi i)
    have hPr : ∀ p∈Pr,Nat.Prime p ∧ Index.smallLo i≤p ∧ p<Index.smallLo i+(Index.smallRows i).length := by
      intro p hp
      have hm := Finset.mem_filter.mp hp
      have hprime := (hP p hm.1).1
      have hlen := Index.small_sieve_length i
      exact ⟨hprime,hm.2.1,by omega⟩
    have hweight := weighted_sieve_upper (Index.smallLo i) (Index.smallRows i)
      (Index.small_sieve_valid i) Pr hPr
    rw [Index.small_sieve_sum] at hweight
    have hc : (0:ℝ)≤Index.smallCoefficient i := by
      have hh := lastCoefficient_nonneg (Index.smallBand i).steps (Index.smallBand i).scale
        (Index.small_band_valid i).2.2.2.2.2.1
      rw [Index.small_coefficient_eq] at hh
      exact_mod_cast hh
    calc
      (∑ p∈Pr,w p) ≤ ∑ p∈Pr,(Index.smallCoefficient i:ℝ)*(p:ℝ)^(-(100:ℝ)/67) := by
        apply Finset.sum_le_sum
        intro p hp
        have hm := Finset.mem_filter.mp hp
        exact hpoint i p hm.1 hm.2.1 hm.2.2
      _ = (Index.smallCoefficient i:ℝ)*(∑ p∈Pr,(p:ℝ)^(-(100:ℝ)/67)) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hweight hc
  have hcover : ∀ p∈P,∃ i∈(Finset.univ:Finset (Fin 141)),Index.smallLo i≤p ∧ p<Index.smallHi i := by
    intro p hp
    obtain ⟨i,hi⟩ := Index.small_cover (hP p hp).2.1 (hP p hp).2.2
    exact ⟨i,Finset.mem_univ _,hi⟩
  have hh := sum_le_cover P Finset.univ w Index.smallLo Index.smallHi
    (fun i => (Index.smallCoefficient i:ℝ)*(Index.smallMoment i:ℝ)) hw hcover (fun i _ => hbound i)
  have hq : (50:ℚ)*(∑ i : Fin 141,Index.smallCoefficient i*Index.smallMoment i) < 21 := by
    linarith [Index.small_budget]
  have hr : (50:ℝ)*(∑ i : Fin 141,(Index.smallCoefficient i:ℝ)*(Index.smallMoment i:ℝ)) < 21 := by
    exact_mod_cast hq
  linarith

end LonelyRunnerNew.LCNumeric
