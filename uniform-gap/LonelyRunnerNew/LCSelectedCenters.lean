import LonelyRunnerNew.LCDirectionalTails

noncomputable section
open scoped BigOperators
namespace LonelyRunnerNew.TaggedState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

theorem center_zero_off_primeSupport (s : TaggedState Label n) {p k : ℕ}
    (hp : Nat.Prime p) (hoff : p ∉ s.primeSupport) (hk : k ∈ s.valuationSupport p) : k = 0 := by
  rcases Finset.mem_union.mp hk with hk | hk
  · obtain ⟨x,hx,hval⟩ := Finset.mem_image.mp hk
    rw [s.left_valuation_zero_off_primeSupport hp hoff hx] at hval
    exact hval.symm
  · obtain ⟨y,hy,hval⟩ := Finset.mem_image.mp hk
    rw [s.right_valuation_zero_off_primeSupport hp hoff hy] at hval
    exact hval.symm

/-- Choose centers for all large primes of ONE state. Outside its finite prime
support the chosen center is provably zero, not an additional hypothesis. -/
theorem select_large_centers (s : TaggedState Label n)
    (hc : ∀ p : ℕ,Nat.Prime p → 142 < p →
      ∃ k ∈ s.valuationSupport p,1-(s.alpha p k+s.beta p k)/2 ≤ (121/1000:ℝ)) :
    ∃ centers : ℕ → ℕ,
      (∀ p,Nat.Prime p → 142 < p → centers p ∈ s.valuationSupport p ∧
        s.zMinus p (centers p)+s.zPlus p (centers p) ≤ (121/1000:ℝ)) ∧
      (∀ p ∉ s.primeSupport,centers p = 0) := by
  classical
  let centers : ℕ → ℕ := fun p => if h : Nat.Prime p ∧ 142 < p then
    Classical.choose (hc p h.1 h.2) else 0
  have hchosen (p : ℕ) (hp : Nat.Prime p) (h142 : 142 < p) :
      centers p ∈ s.valuationSupport p ∧
        1-(s.alpha p (centers p)+s.beta p (centers p))/2 ≤ (121/1000:ℝ) := by
    simpa only [centers,dif_pos (And.intro hp h142)] using
      Classical.choose_spec (hc p hp h142)
  refine ⟨centers,?_,?_⟩
  · intro p hp h142
    have h := hchosen p hp h142
    exact ⟨h.1,(s.zMinus_add_zPlus p (centers p) h.1).trans_le h.2⟩
  · intro p hoff
    by_cases h : Nat.Prime p ∧ 142 < p
    · exact s.center_zero_off_primeSupport h.1 hoff (hchosen p h.1 h.2).1
    · simp only [centers,dif_neg h]

/-- Concrete ordinary-score centers and their retained original edge set.
The last bound is exact finite-union accounting; it does NOT assert 27/50. -/
theorem stable_directional_retention (s : TaggedState Label n)
    (hs : ∀ t,Step s t → t.quality ≤ s.quality) (hM : 0 < s.edgeMass) :
    ∃ centers : ℕ → ℕ,
      (∀ p ∉ s.primeSupport,centers p = 0) ∧
      (∀ p,Nat.Prime p → 142 < p →
        centers p ∈ s.valuationSupport p ∧
        s.zMinus p (centers p)+s.zPlus p (centers p) ≤ (121/1000:ℝ) ∧
        LCDirection.directionalInequality ((p:ℝ)^(-1/q))
          (s.zMinus p (centers p)) (s.zPlus p (centers p)) ∧
        s.primeException p (centers p) ≤
          (s.zMinus p (centers p))^(3/2:ℝ)+(s.zPlus p (centers p))^(3/2:ℝ)) ∧
      (s.retainedLargeEdges centers ⊆ s.edges) ∧
      (∀ e ∈ s.retainedLargeEdges centers,∀ p,Nat.Prime p → 142 < p →
        s.centerBrackets p (centers p) e) ∧
      (1-∑ p ∈ s.largePrimeSupport,s.primeException p (centers p) ≤
        ∑ e ∈ s.retainedLargeEdges centers,s.edgeProbability e) := by
  obtain ⟨centers,hc,hoff⟩ := s.select_large_centers (s.stable_prime_center hs hM)
  refine ⟨centers,hoff,?_,s.retainedLargeEdges_subset centers,?_,s.retainedLargeEdges_mass hM centers⟩
  · intro p hp h142
    have h := hc p hp h142
    exact ⟨h.1,h.2,s.actual_directional_iteration hs hM p hp _ h.1,
      s.actual_same_direction hs hM p _⟩
  · intro e he p hp h142
    exact s.retainedLargeEdges_all_large_primes centers hoff he p hp h142

/-- Universal score uses its own L04 and L05, not ordinary-score stability. -/
theorem universal_directional_retention (s : TaggedState Label n)
    (hs : ∀ t,Step s t → t.universalQuality ≤ s.universalQuality) (hM : 0 < s.edgeMass) :
    ∃ centers : ℕ → ℕ,
      (∀ p ∉ s.primeSupport,centers p = 0) ∧
      (∀ p,Nat.Prime p → 142 < p →
        centers p ∈ s.valuationSupport p ∧
        s.zMinus p (centers p)+s.zPlus p (centers p) ≤ (121/1000:ℝ) ∧
        LCDirection.directionalInequality ((p:ℝ)^(-1/q))
          (s.zMinus p (centers p)) (s.zPlus p (centers p)) ∧
        s.primeException p (centers p) ≤
          (s.zMinus p (centers p))^(3/2:ℝ)+(s.zPlus p (centers p))^(3/2:ℝ)) ∧
      (s.retainedLargeEdges centers ⊆ s.edges) ∧
      (∀ e ∈ s.retainedLargeEdges centers,∀ p,Nat.Prime p → 142 < p →
        s.centerBrackets p (centers p) e) ∧
      (1-∑ p ∈ s.largePrimeSupport,s.primeException p (centers p) ≤
        ∑ e ∈ s.retainedLargeEdges centers,s.edgeProbability e) := by
  obtain ⟨centers,hc,hoff⟩ := s.select_large_centers (s.universal_prime_center hs hM)
  refine ⟨centers,hoff,?_,s.retainedLargeEdges_subset centers,?_,s.retainedLargeEdges_mass hM centers⟩
  · intro p hp h142
    have h := hc p hp h142
    exact ⟨h.1,h.2,s.actual_universal_directional_iteration hs hM p hp _ h.1,
      s.actual_universal_same_direction hs hM p _⟩
  · intro e he p hp h142
    exact s.retainedLargeEdges_all_large_primes centers hoff he p hp h142

end LonelyRunnerNew.TaggedState

namespace LonelyRunnerNew

/-- Extraction from the original speed set still precedes all prime choices.
This result closes the finite-support/retained-set construction, but leaves
the directional interval certificate and 23/50 budget unproved. -/
theorem original_universal_retained_large_edges (V : Finset ℕ) (hV : valid V) :
    ∃ (s : TaggedState ℕ V.card) (centers : ℕ → ℕ),
      Relation.ReflTransGen TaggedState.Step (initialTaggedState V hV) s ∧
      (initialTaggedState V hV).universalQuality ≤ s.universalQuality ∧
      (∀ t,TaggedState.Step s t → t.universalQuality ≤ s.universalQuality) ∧
      0 < s.edgeMass ∧
      (∀ p ∉ s.primeSupport,centers p = 0) ∧
      (∀ p,Nat.Prime p → 142 < p →
        s.zMinus p (centers p)+s.zPlus p (centers p) ≤ (121/1000:ℝ) ∧
        LCDirection.directionalInequality ((p:ℝ)^(-1/q))
          (s.zMinus p (centers p)) (s.zPlus p (centers p)) ∧
        s.primeException p (centers p) ≤
          (s.zMinus p (centers p))^(3/2:ℝ)+(s.zPlus p (centers p))^(3/2:ℝ)) ∧
      (s.retainedLargeEdges centers ⊆ s.edges) ∧
      (∀ e ∈ s.retainedLargeEdges centers,∀ p,Nat.Prime p → 142 < p →
        s.centerBrackets p (centers p) e) ∧
      (1-∑ p ∈ s.largePrimeSupport,s.primeException p (centers p) ≤
        ∑ e ∈ s.retainedLargeEdges centers,s.edgeProbability e) := by
  obtain ⟨s,hr,hq,hs,hM⟩ := original_universal_stable_state_exists V hV
  obtain ⟨centers,hoff,hc,hsub,hbr,hmass⟩ := s.universal_directional_retention hs hM
  exact ⟨s,centers,hr,hq,hs,hM,hoff,fun p hp h142 =>
    ⟨(hc p hp h142).2.1,(hc p hp h142).2.2⟩,hsub,hbr,hmass⟩

end LonelyRunnerNew
