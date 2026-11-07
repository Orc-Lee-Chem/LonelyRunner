import LonelyRunnerNew.SmallPrimeActual

noncomputable section
open scoped BigOperators
namespace LonelyRunnerNew.TaggedState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

/-- Every original labelled edge contributes, including collisions in valuation
fibres. No image-set de-duplication occurs in this identity. -/
theorem primeMeanLogDistance_eq_edge_sum (s : TaggedState Label n) (p : ℕ) :
    s.primeMeanLogDistance p =
      ∑ e∈s.edges,s.edgeProbability e*primeLogDistance p (s.valuationPair p e) := by
  have hf (ij : ℕ × ℕ) : s.mu p ij*primeLogDistance p ij =
      ∑ e∈s.edges.filter (s.valuationPair p ·=ij),s.edgeProbability e*primeLogDistance p (s.valuationPair p e) := by
    rw [s.mu_eq_fiber_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e he
    rw [(Finset.mem_filter.mp he).2]
  unfold primeMeanLogDistance
  simp_rw [hf]
  apply Finset.sum_fiberwise_of_maps_to
  intro e he
  have hm := Finset.mem_product.mp (s.edges_subset he)
  exact Finset.mem_product.mpr
    ⟨Finset.mem_union_left _ (Finset.mem_image_of_mem _ hm.1),
      Finset.mem_union_right _ (Finset.mem_image_of_mem _ hm.2)⟩

def smallPrimeEdgeDistance (s : TaggedState Label n) (e : Label × Label) : ℝ :=
  ∑ p∈Certificate.smallPrimes,primeLogDistance p (s.valuationPair p e)

theorem small_prime_edge_mean_identity (s : TaggedState Label n) :
    (∑ e∈s.edges,s.edgeProbability e*s.smallPrimeEdgeDistance e) =
      ∑ p∈Certificate.smallPrimes,s.primeMeanLogDistance p := by
  unfold smallPrimeEdgeDistance
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [primeMeanLogDistance_eq_edge_sum]

theorem stable_small_prime_edge_mean (s : TaggedState Label n)
    (hs : ∀ t,Step s t → t.quality≤s.quality) (hM : 0<s.edgeMass) :
    (∑ e∈s.edges,s.edgeProbability e*s.smallPrimeEdgeDistance e)<(Certificate.edgebar:ℝ) := by
  rw [s.small_prime_edge_mean_identity]
  exact s.stable_small_prime_mean_distance hs hM

theorem universal_small_prime_edge_mean (s : TaggedState Label n)
    (hs : ∀ t,Step s t → t.universalQuality≤s.universalQuality) (hM : 0<s.edgeMass) :
    (∑ e∈s.edges,s.edgeProbability e*s.smallPrimeEdgeDistance e)<(Certificate.edgebar:ℝ) := by
  rw [s.small_prime_edge_mean_identity]
  exact s.universal_small_prime_mean_distance hs hM

end LonelyRunnerNew.TaggedState
