import LonelyRunnerNew.FixedScaleCenter
import Mathlib.Data.Nat.PrimeFin

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace LonelyRunnerNew.TaggedState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

/-- Prime factors of the actual positive vertex values of this one state. -/
def primeSupport (s : TaggedState Label n) : Finset ℕ :=
  s.left.biUnion (fun x => (s.leftValue x).primeFactors) ∪
    s.right.biUnion (fun y => (s.rightValue y).primeFactors)

theorem prime_of_mem_primeSupport (s : TaggedState Label n) {p : ℕ}
    (hp : p ∈ s.primeSupport) : Nat.Prime p := by
  rcases Finset.mem_union.mp hp with h | h
  · obtain ⟨x,hx,hp⟩ := Finset.mem_biUnion.mp h
    exact Nat.prime_of_mem_primeFactors hp
  · obtain ⟨y,hy,hp⟩ := Finset.mem_biUnion.mp h
    exact Nat.prime_of_mem_primeFactors hp

theorem left_valuation_zero_off_primeSupport (s : TaggedState Label n) {p : ℕ}
    (hp : Nat.Prime p) (hnot : p ∉ s.primeSupport) {x : Label} (hx : x ∈ s.left) :
    padicValNat p (s.leftValue x) = 0 := by
  apply padicValNat.eq_zero_of_not_dvd
  intro hd
  apply hnot
  apply Finset.mem_union_left
  exact Finset.mem_biUnion.mpr ⟨x,hx,
    Nat.mem_primeFactors_iff_mem_primeFactorsList.mpr
      ((Nat.mem_primeFactorsList (s.left_positive x hx).ne').mpr ⟨hp,hd⟩)⟩

theorem right_valuation_zero_off_primeSupport (s : TaggedState Label n) {p : ℕ}
    (hp : Nat.Prime p) (hnot : p ∉ s.primeSupport) {y : Label} (hy : y ∈ s.right) :
    padicValNat p (s.rightValue y) = 0 := by
  apply padicValNat.eq_zero_of_not_dvd
  intro hd
  apply hnot
  apply Finset.mem_union_right
  exact Finset.mem_biUnion.mpr ⟨y,hy,
    Nat.mem_primeFactors_iff_mem_primeFactorsList.mpr
      ((Nat.mem_primeFactorsList (s.right_positive y hy).ne').mpr ⟨hp,hd⟩)⟩

def centerBrackets (s : TaggedState Label n) (p k : ℕ) (e : Label × Label) : Prop :=
  min (s.valuationPair p e).1 (s.valuationPair p e).2 ≤ k ∧
    k ≤ max (s.valuationPair p e).1 (s.valuationPair p e).2

theorem brackets_zero_off_primeSupport (s : TaggedState Label n) {p : ℕ}
    (hp : Nat.Prime p) (hnot : p ∉ s.primeSupport) {e : Label × Label}
    (he : e ∈ s.edges) : s.centerBrackets p 0 e := by
  have hm := Finset.mem_product.mp (s.edges_subset he)
  simp [centerBrackets,valuationPair,s.left_valuation_zero_off_primeSupport hp hnot hm.1,
    s.right_valuation_zero_off_primeSupport hp hnot hm.2]

/-- Actual labelled-edge probability, not the cardinality of an image. -/
def primeException (s : TaggedState Label n) (p k : ℕ) : ℝ :=
  ∑ e ∈ s.edges.filter (fun e => ¬ s.centerBrackets p k e), s.edgeProbability e

theorem primeException_eq_valuation_exception (s : TaggedState Label n) (p k : ℕ) :
    s.primeException p k =
      LargePrime.exceptionMass ((s.leftValuationSupport p).product
        (s.rightValuationSupport p)) (s.mu p) k := by
  unfold primeException LargePrime.exceptionMass
  simp_rw [mu_eq_fiber_sum]
  rw [Finset.sum_fiberwise_eq_sum_filter]
  congr 1
  apply Finset.filter_congr
  intro e he
  have hm := Finset.mem_product.mp (s.edges_subset he)
  have hL : (s.valuationPair p e).1 ∈ s.leftValuationSupport p :=
    Finset.mem_image_of_mem _ hm.1
  have hR : (s.valuationPair p e).2 ∈ s.rightValuationSupport p :=
    Finset.mem_image_of_mem _ hm.2
  simp only [Finset.mem_filter,Finset.product_eq_sprod,Finset.mem_product,hL,hR,
    true_and,centerBrackets]

theorem primeException_nonneg (s : TaggedState Label n) (hM : 0 < s.edgeMass) (p k : ℕ) :
    0 ≤ s.primeException p k :=
  Finset.sum_nonneg (fun e _ => s.edgeProbability_nonneg hM e)

theorem primeException_zero_off_primeSupport (s : TaggedState Label n) {p : ℕ}
    (hp : Nat.Prime p) (hnot : p ∉ s.primeSupport) : s.primeException p 0 = 0 := by
  unfold primeException
  have he : s.edges.filter (fun e => ¬ s.centerBrackets p 0 e) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    have h := Finset.mem_filter.mp he
    exact h.2 (s.brackets_zero_off_primeSupport hp hnot h.1)
  rw [he,Finset.sum_empty]

def largePrimeSupport (s : TaggedState Label n) : Finset ℕ := s.primeSupport.filter (142 < ·)

/-- Only large-prime conditions. No small-prime or roughness claim is made. -/
def retainedLargeEdges (s : TaggedState Label n) (centers : ℕ → ℕ) : Finset (Label × Label) :=
  s.edges.filter (fun e => ∀ p ∈ s.largePrimeSupport, s.centerBrackets p (centers p) e)

theorem retainedLargeEdges_subset (s : TaggedState Label n) (centers : ℕ → ℕ) :
    s.retainedLargeEdges centers ⊆ s.edges := Finset.filter_subset _ _

theorem retainedLargeEdges_all_large_primes (s : TaggedState Label n) (centers : ℕ → ℕ)
    (hoff : ∀ p ∉ s.primeSupport, centers p = 0) {e : Label × Label}
    (he : e ∈ s.retainedLargeEdges centers) (p : ℕ) (hp : Nat.Prime p) (hp142 : 142 < p) :
    s.centerBrackets p (centers p) e := by
  have h := Finset.mem_filter.mp he
  by_cases hs : p ∈ s.primeSupport
  · exact h.2 p (Finset.mem_filter.mpr ⟨hs,hp142⟩)
  · rw [hoff p hs]
    exact s.brackets_zero_off_primeSupport hp hs h.1

/-- A union bound proved on the original labelled edge set. The numerical
`23/50` budget is NOT a premise or a conclusion of this accounting identity. -/
theorem retainedLargeEdges_mass (s : TaggedState Label n) (hM : 0 < s.edgeMass)
    (centers : ℕ → ℕ) :
    1 - ∑ p ∈ s.largePrimeSupport, s.primeException p (centers p) ≤
      ∑ e ∈ s.retainedLargeEdges centers, s.edgeProbability e := by
  let P := s.largePrimeSupport
  let G := s.retainedLargeEdges centers
  have hpoint (e : Label × Label) (he : e ∈ s.edges) :
      s.edgeProbability e ≤
        (if e ∈ G then s.edgeProbability e else 0) +
        ∑ p ∈ P, if ¬ s.centerBrackets p (centers p) e then s.edgeProbability e else 0 := by
    have hw := s.edgeProbability_nonneg hM e
    by_cases hG : e ∈ G
    · simp only [hG,ite_true]
      exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity))
    · have hbad : ∃ p ∈ P, ¬ s.centerBrackets p (centers p) e := by
        simpa only [G,retainedLargeEdges,Finset.mem_filter,he,true_and,not_forall,exists_prop] using hG
      obtain ⟨p,hp,hbad⟩ := hbad
      simp only [hG,ite_false,zero_add]
      calc
        s.edgeProbability e = if ¬ s.centerBrackets p (centers p) e then
            s.edgeProbability e else 0 := by simp [hbad]
        _ ≤ _ := Finset.single_le_sum (s := P)
          (f := fun r => if ¬ s.centerBrackets r (centers r) e then s.edgeProbability e else 0)
          (fun _ _ => by split_ifs <;> positivity) hp
  have hsum := Finset.sum_le_sum hpoint
  rw [s.edgeProbability_sum hM,Finset.sum_add_distrib] at hsum
  have hGsum : (∑ e ∈ s.edges, if e ∈ G then s.edgeProbability e else 0) =
      ∑ e ∈ G, s.edgeProbability e := by
    rw [← Finset.sum_filter]
    congr 1
    ext e
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2,fun h => ⟨s.retainedLargeEdges_subset centers h,h⟩⟩
  rw [hGsum,Finset.sum_comm] at hsum
  have hPsum : (∑ p ∈ P, ∑ e ∈ s.edges,
      if ¬ s.centerBrackets p (centers p) e then s.edgeProbability e else 0) =
      ∑ p ∈ P, s.primeException p (centers p) := by
    apply Finset.sum_congr rfl
    intro p hp
    exact (Finset.sum_filter _ _).symm
  rw [hPsum] at hsum
  linarith

/-- Every finite collection of large primes is bounded by the SAME actual
finite-support budget. This is the reduction needed before an infinite-prime
estimate; no numerical budget is postulated. -/
theorem large_prime_sum_le_support (s : TaggedState Label n) (hM : 0 < s.edgeMass)
    (centers : ℕ → ℕ) (hoff : ∀ p ∉ s.primeSupport,centers p=0)
    (P : Finset ℕ) (hP : ∀ p ∈ P,Nat.Prime p ∧ 142 < p) :
    (∑ p ∈ P,s.primeException p (centers p)) ≤
      ∑ p ∈ s.largePrimeSupport,s.primeException p (centers p) := by
  have he : (∑ p ∈ P,s.primeException p (centers p)) =
      ∑ p ∈ P.filter (· ∈ s.largePrimeSupport),s.primeException p (centers p) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hs : p ∈ s.largePrimeSupport
    · simp only [hs,ite_true]
    · have hn : p ∉ s.primeSupport := by
        intro hin
        exact hs (Finset.mem_filter.mpr ⟨hin,(hP p hp).2⟩)
      rw [hoff p hn,s.primeException_zero_off_primeSupport (hP p hp).1 hn]
      simp only [ite_self]
  rw [he]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    exact (Finset.mem_filter.mp hp).2
  · intro p hp hnot
    exact s.primeException_nonneg hM p (centers p)

end LonelyRunnerNew.TaggedState

