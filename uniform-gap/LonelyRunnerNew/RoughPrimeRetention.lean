import LonelyRunnerNew.LCQuantitativeRetention

noncomputable section
open scoped BigOperators
namespace LonelyRunnerNew.TaggedState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

theorem rough_left_valuation_zero (s : TaggedState Label n) {Y p : ℕ}
    (hL : ∀ x∈s.left,rough Y (s.leftValue x)) (hp : Nat.Prime p) (hY : p≤Y)
    {x : Label} (hx : x∈s.left) : padicValNat p (s.leftValue x)=0 :=
  padicValNat.eq_zero_of_not_dvd ((hL x hx).2 p hp hY)

theorem rough_right_valuation_zero (s : TaggedState Label n) {Y p : ℕ}
    (hR : ∀ y∈s.right,rough Y (s.rightValue y)) (hp : Nat.Prime p) (hY : p≤Y)
    {y : Label} (hy : y∈s.right) : padicValNat p (s.rightValue y)=0 :=
  padicValNat.eq_zero_of_not_dvd ((hR y hy).2 p hp hY)

theorem rough_prime_not_mem_support (s : TaggedState Label n) {Y p : ℕ}
    (hL : ∀ x∈s.left,rough Y (s.leftValue x))
    (hR : ∀ y∈s.right,rough Y (s.rightValue y)) (hp : Nat.Prime p) (hY : p≤Y) :
    p∉s.primeSupport := by
  intro hm
  rcases Finset.mem_union.mp hm with hm | hm
  · obtain ⟨x,hx,hd⟩ := Finset.mem_biUnion.mp hm
    exact (hL x hx).2 p hp hY (Nat.dvd_of_mem_primeFactors hd)
  · obtain ⟨y,hy,hd⟩ := Finset.mem_biUnion.mp hm
    exact (hR y hy).2 p hp hY (Nat.dvd_of_mem_primeFactors hd)

theorem rough_retained_all_primes (s : TaggedState Label n)
    (hL : ∀ x∈s.left,rough 142 (s.leftValue x))
    (hR : ∀ y∈s.right,rough 142 (s.rightValue y)) (centers : ℕ → ℕ)
    (hoff : ∀ p∉s.primeSupport,centers p=0) {e : Label × Label}
    (he : e∈s.retainedLargeEdges centers) {p : ℕ} (hp : Nat.Prime p) :
    s.centerBrackets p (centers p) e := by
  by_cases hY : p≤142
  · have hnot := s.rough_prime_not_mem_support hL hR hp hY
    rw [hoff p hnot]
    exact s.brackets_zero_off_primeSupport hp hnot (s.retainedLargeEdges_subset centers he)
  · exact s.retainedLargeEdges_all_large_primes centers hoff he p hp (by omega)

/-- The SAME retained set, now bracketing every prime. Roughness is a property
of this actual stable state's positive values, not of arbitrary original speeds. -/
theorem stable_rough_all_prime_retention (s : TaggedState Label n)
    (hs : ∀ t,Step s t → t.quality≤s.quality) (hM : 0<s.edgeMass)
    (hL : ∀ x∈s.left,rough 142 (s.leftValue x))
    (hR : ∀ y∈s.right,rough 142 (s.rightValue y)) :
    ∃ centers : ℕ → ℕ,
      (∀ p∉s.primeSupport,centers p=0) ∧
      s.retainedLargeEdges centers ⊆ s.edges ∧
      (27/50:ℝ) ≤ ∑ e∈s.retainedLargeEdges centers,s.edgeProbability e ∧
      (∀ e∈s.retainedLargeEdges centers,∀ p,Nat.Prime p → s.centerBrackets p (centers p) e) := by
  obtain ⟨centers,hoff,_,_,hsub,hmass,_⟩ := s.stable_large_prime_retention hs hM
  exact ⟨centers,hoff,hsub,hmass,fun _ he _ hp => s.rough_retained_all_primes hL hR centers hoff he hp⟩

theorem universal_rough_all_prime_retention (s : TaggedState Label n)
    (hs : ∀ t,Step s t → t.universalQuality≤s.universalQuality) (hM : 0<s.edgeMass)
    (hL : ∀ x∈s.left,rough 142 (s.leftValue x))
    (hR : ∀ y∈s.right,rough 142 (s.rightValue y)) :
    ∃ centers : ℕ → ℕ,
      (∀ p∉s.primeSupport,centers p=0) ∧
      s.retainedLargeEdges centers ⊆ s.edges ∧
      (27/50:ℝ) ≤ ∑ e∈s.retainedLargeEdges centers,s.edgeProbability e ∧
      (∀ e∈s.retainedLargeEdges centers,∀ p,Nat.Prime p → s.centerBrackets p (centers p) e) := by
  obtain ⟨centers,hoff,_,_,hsub,hmass,_⟩ := s.universal_large_prime_retention hs hM
  exact ⟨centers,hoff,hsub,hmass,fun _ he _ hp => s.rough_retained_all_primes hL hR centers hoff he hp⟩

end LonelyRunnerNew.TaggedState
