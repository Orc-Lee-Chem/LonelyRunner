import LonelyRunnerNew.LCFiniteBudgets

noncomputable section
open scoped BigOperators
namespace LonelyRunnerNew.TaggedState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

/-- Shared finite accounting lemma. Its pointwise inputs are supplied from
the checked tables and each score's actual L04/L05 below. -/
theorem numerical_budget_of_pointwise (s : TaggedState Label n) (hM : 0<s.edgeMass)
    (centers : ℕ → ℕ)
    (hsmall : ∀ i : Fin 141,∀ p,Nat.Prime p → 142<p →
      LCNumeric.Index.smallLo i≤p → p<LCNumeric.Index.smallHi i →
      s.primeException p (centers p) ≤
        (LCNumeric.Index.smallCoefficient i:ℝ)*(p:ℝ)^(-(100:ℝ)/67))
    (htail : ∀ p,Nat.Prime p → 10000≤p → s.primeException p (centers p) ≤
      (LCNumeric.tailCoefficient:ℝ)*(p:ℝ)^(-(100:ℝ)/67))
    (P : Finset ℕ) (hP : ∀ p∈P,Nat.Prime p ∧ 142<p) :
    (∑ p∈P,s.primeException p (centers p)) < (451/1000:ℝ) := by
  let w := fun p => s.primeException p (centers p)
  let Ps := P.filter (·≤10000)
  let Pm := P.filter (fun p => 10000<p ∧ p≤1000000)
  let Pt := P.filter (1000000<·)
  have hs : (∑ p∈Ps,w p) < (21/50:ℝ) := by
    apply LCNumeric.small_prime_budget Ps w (fun p _ => s.primeException_nonneg hM p _)
    · intro p hp
      have hm := Finset.mem_filter.mp hp
      exact ⟨(hP p hm.1).1,(hP p hm.1).2,hm.2⟩
    · intro i p hp hlo hhi
      have hm := (Finset.mem_filter.mp hp).1
      exact hsmall i p (hP p hm).1 (hP p hm).2 hlo hhi
  have hm : (∑ p∈Pm,w p) < (23/1000:ℝ) := by
    apply LCNumeric.middle_prime_budget Pm w (fun p _ => s.primeException_nonneg hM p _)
    · intro p hp
      have hr := Finset.mem_filter.mp hp
      exact ⟨(hP p hr.1).1,hr.2⟩
    · intro p hp
      have hr := Finset.mem_filter.mp hp
      exact htail p (hP p hr.1).1 hr.2.1.le
  have hPt : ∀ p∈Pt,Nat.Prime p ∧ 1000000<p := by
    intro p hp
    have hr := Finset.mem_filter.mp hp
    exact ⟨(hP p hr.1).1,hr.2⟩
  have ht : (∑ p∈Pt,w p) < (1/125:ℝ) := by
    have hbound : (∑ p∈Pt,w p) ≤ (LCNumeric.tailCoefficient:ℝ)*(∑ p∈Pt,(p:ℝ)^(-(100:ℝ)/67)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro p hp
      exact htail p (hPt p hp).1 (by have := (hPt p hp).2; omega)
    exact hbound.trans_lt (LCNumeric.prime_tail_numeric_budget Pt hPt)
  have heq : (∑ p∈P,w p)=(∑ p∈Ps,w p)+(∑ p∈Pm,w p)+(∑ p∈Pt,w p) := by
    dsimp [Ps,Pm,Pt]
    simp only [Finset.sum_filter]
    rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases h1 : p≤10000
    · have h2 : p≤1000000 := by omega
      simp [h1,h2,show ¬10000<p by omega,show ¬1000000<p by omega]
    · by_cases h2 : p≤1000000
      · simp [h1,h2,show 10000<p by omega,show ¬1000000<p by omega]
      · simp [h1,h2,show 10000<p by omega,show 1000000<p by omega]
  change (∑ p∈P,w p) < (451/1000:ℝ)
  rw [heq]
  linarith

theorem tsum_large_exception_eq (s : TaggedState Label n) (centers : ℕ → ℕ)
    (hoff : ∀ p∉s.primeSupport,centers p=0) :
    (∑' p : ℕ,if Nat.Prime p ∧ 142<p then s.primeException p (centers p) else 0) =
      ∑ p∈s.largePrimeSupport,s.primeException p (centers p) := by
  classical
  have hz : ∀ p∉s.largePrimeSupport,
      (if Nat.Prime p ∧ 142<p then s.primeException p (centers p) else 0)=0 := by
    intro p hp
    by_cases h : Nat.Prime p ∧ 142<p
    · have hoffp : p∉s.primeSupport := by
        intro hm
        exact hp (Finset.mem_filter.mpr ⟨hm,h.2⟩)
      rw [if_pos h,hoff p hoffp,s.primeException_zero_off_primeSupport h.1 hoffp]
    · exact if_neg h
  rw [tsum_eq_sum hz]
  apply Finset.sum_congr rfl
  intro p hp
  have hm := Finset.mem_filter.mp hp
  exact if_pos ⟨s.prime_of_mem_primeSupport hm.1,hm.2⟩

/-- Concrete quantitative retention: only actual ordinary-score stability and
positive mass are inputs. No interval bound or numerical budget is a premise. -/
theorem stable_large_prime_retention (s : TaggedState Label n)
    (hs : ∀ t,Step s t → t.quality≤s.quality) (hM : 0<s.edgeMass) :
    ∃ centers : ℕ → ℕ,
      (∀ p∉s.primeSupport,centers p=0) ∧
      (∑ p∈s.largePrimeSupport,s.primeException p (centers p)) ≤ (23/50:ℝ) ∧
      (∑' p : ℕ,if Nat.Prime p ∧ 142<p then s.primeException p (centers p) else 0) ≤ (23/50:ℝ) ∧
      s.retainedLargeEdges centers ⊆ s.edges ∧
      (27/50:ℝ) ≤ ∑ e∈s.retainedLargeEdges centers,s.edgeProbability e ∧
      (∀ e∈s.retainedLargeEdges centers,∀ p,Nat.Prime p → 142<p →
        s.centerBrackets p (centers p) e) := by
  obtain ⟨centers,hc,hoff⟩ := s.select_large_centers (s.stable_prime_center hs hM)
  have hsmall (i : Fin 141) (p : ℕ) (hp : Nat.Prime p) (h142 : 142<p)
      (hlo : LCNumeric.Index.smallLo i≤p) (hhi : p<LCNumeric.Index.smallHi i) :
      s.primeException p (centers p) ≤
        (LCNumeric.Index.smallCoefficient i:ℝ)*(p:ℝ)^(-(100:ℝ)/67) := by
    have h := hc p hp h142
    have hB := LCNumeric.Index.small_band_lower i
    have hh := s.ordinary_band_numeric hs hM (LCNumeric.Index.smallBand i)
      (LCNumeric.Index.small_band_valid i) p hp (by omega) _ h.1 h.2
    rwa [LCNumeric.Index.small_coefficient_eq] at hh
  have htail (p : ℕ) (hp : Nat.Prime p) (hB : 10000≤p) :
      s.primeException p (centers p) ≤ (LCNumeric.tailCoefficient:ℝ)*(p:ℝ)^(-(100:ℝ)/67) := by
    have h := hc p hp (by omega)
    exact s.actual_numeric_tail hs hM p hp hB _ h.1 h.2
  have hP : ∀ p∈s.largePrimeSupport,Nat.Prime p ∧ 142<p := by
    intro p hp
    have hm := Finset.mem_filter.mp hp
    exact ⟨s.prime_of_mem_primeSupport hm.1,hm.2⟩
  have hbudget := s.numerical_budget_of_pointwise hM centers hsmall htail s.largePrimeSupport hP
  have hmass := s.retainedLargeEdges_mass hM centers
  refine ⟨centers,hoff,by linarith,?_,s.retainedLargeEdges_subset centers,by linarith,?_⟩
  · rw [s.tsum_large_exception_eq centers hoff]
    linarith
  · intro e he p hp h142
    exact s.retainedLargeEdges_all_large_primes centers hoff he p hp h142

theorem universal_large_prime_retention (s : TaggedState Label n)
    (hs : ∀ t,Step s t → t.universalQuality≤s.universalQuality) (hM : 0<s.edgeMass) :
    ∃ centers : ℕ → ℕ,
      (∀ p∉s.primeSupport,centers p=0) ∧
      (∑ p∈s.largePrimeSupport,s.primeException p (centers p)) ≤ (23/50:ℝ) ∧
      (∑' p : ℕ,if Nat.Prime p ∧ 142<p then s.primeException p (centers p) else 0) ≤ (23/50:ℝ) ∧
      s.retainedLargeEdges centers ⊆ s.edges ∧
      (27/50:ℝ) ≤ ∑ e∈s.retainedLargeEdges centers,s.edgeProbability e ∧
      (∀ e∈s.retainedLargeEdges centers,∀ p,Nat.Prime p → 142<p →
        s.centerBrackets p (centers p) e) := by
  obtain ⟨centers,hc,hoff⟩ := s.select_large_centers (s.universal_prime_center hs hM)
  have hsmall (i : Fin 141) (p : ℕ) (hp : Nat.Prime p) (h142 : 142<p)
      (hlo : LCNumeric.Index.smallLo i≤p) (hhi : p<LCNumeric.Index.smallHi i) :
      s.primeException p (centers p) ≤
        (LCNumeric.Index.smallCoefficient i:ℝ)*(p:ℝ)^(-(100:ℝ)/67) := by
    have h := hc p hp h142
    have hB := LCNumeric.Index.small_band_lower i
    have hh := s.universal_band_numeric hs hM (LCNumeric.Index.smallBand i)
      (LCNumeric.Index.small_band_valid i) p hp (by omega) _ h.1 h.2
    rwa [LCNumeric.Index.small_coefficient_eq] at hh
  have htail (p : ℕ) (hp : Nat.Prime p) (hB : 10000≤p) :
      s.primeException p (centers p) ≤ (LCNumeric.tailCoefficient:ℝ)*(p:ℝ)^(-(100:ℝ)/67) := by
    have h := hc p hp (by omega)
    exact s.actual_universal_numeric_tail hs hM p hp hB _ h.1 h.2
  have hP : ∀ p∈s.largePrimeSupport,Nat.Prime p ∧ 142<p := by
    intro p hp
    have hm := Finset.mem_filter.mp hp
    exact ⟨s.prime_of_mem_primeSupport hm.1,hm.2⟩
  have hbudget := s.numerical_budget_of_pointwise hM centers hsmall htail s.largePrimeSupport hP
  have hmass := s.retainedLargeEdges_mass hM centers
  refine ⟨centers,hoff,by linarith,?_,s.retainedLargeEdges_subset centers,by linarith,?_⟩
  · rw [s.tsum_large_exception_eq centers hoff]
    linarith
  · intro e he p hp h142
    exact s.retainedLargeEdges_all_large_primes centers hoff he p hp h142

end LonelyRunnerNew.TaggedState

namespace LonelyRunnerNew

/-- The original speed set supplies ONE stable state, one family of centers,
and original labelled retained edges of mass at least 27/50. Large primes only. -/
theorem original_universal_quantitative_retention (V : Finset ℕ) (hV : valid V) :
    ∃ (s : TaggedState ℕ V.card) (centers : ℕ → ℕ),
      Relation.ReflTransGen TaggedState.Step (initialTaggedState V hV) s ∧
      (initialTaggedState V hV).universalQuality≤s.universalQuality ∧
      (∀ t,TaggedState.Step s t → t.universalQuality≤s.universalQuality) ∧
      0<s.edgeMass ∧
      (∑' p : ℕ,if Nat.Prime p ∧ 142<p then s.primeException p (centers p) else 0) ≤ (23/50:ℝ) ∧
      s.retainedLargeEdges centers ⊆ s.edges ∧
      (27/50:ℝ) ≤ ∑ e∈s.retainedLargeEdges centers,s.edgeProbability e ∧
      (∀ e∈s.retainedLargeEdges centers,∀ p,Nat.Prime p → 142<p →
        s.centerBrackets p (centers p) e) := by
  obtain ⟨s,hr,hq,hs,hM⟩ := original_universal_stable_state_exists V hV
  obtain ⟨centers,hoff,hfinite,htsum,hsub,hmass,hbr⟩ := s.universal_large_prime_retention hs hM
  exact ⟨s,centers,hr,hq,hs,hM,htsum,hsub,hmass,hbr⟩

end LonelyRunnerNew
