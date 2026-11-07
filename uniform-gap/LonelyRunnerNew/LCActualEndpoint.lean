import LonelyRunnerNew.LCDirectionInterval

noncomputable section
open scoped BigOperators
namespace LonelyRunnerNew.TaggedState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

/-- A proved pointwise-in-direction bound. This is NOT a numerical certificate
for the supremum of B, and it contains no numerical exceptional budget. -/
def directionalEndpoint (s : TaggedState Label n) (p k : ℕ) : Prop :=
  let z := s.zMinus p k+s.zPlus p k
  let u := LCDirection.directionRatio (s.zMinus p k) (s.zPlus p k)
  let lam := (p:ℝ)^(-1/q)
  (z=0 ∧ s.primeException p k=0) ∨
    (0 < z ∧ 0 ≤ u ∧ u ≤ 1/2 ∧
      z ≤ (p:ℝ)^(-4/q)*(LCDirection.B (121/1000) lam u)^4 ∧
      s.primeException p k ≤ (p:ℝ)^(-6/q)*(LCDirection.B (121/1000) lam u)^6*LCDirection.h0 u)

theorem prime_lambda_power (p : ℕ) (hp : Nat.Prime p) (r : ℕ) :
    ((p:ℝ)^(-1/q))^r=(p:ℝ)^(-(r:ℝ)/q) := by
  rw [← Real.rpow_natCast,← Real.rpow_mul (by exact_mod_cast hp.pos.le : (0:ℝ) ≤ p)]
  congr 1
  ring

/-- Mathematical inputs are supplied by each score's own proved L04/L05
wrappers below; the scalar interval argument does not postulate them. -/
theorem directional_endpoint_of_actual_bounds (s : TaggedState Label n) (hM : 0 < s.edgeMass)
    (p : ℕ) (hp : Nat.Prime p) (hp142 : 142 < p) (k : ℕ)
    (hseed : s.zMinus p k+s.zPlus p k ≤ (121/1000:ℝ))
    (hit : LCDirection.directionalInequality ((p:ℝ)^(-1/q)) (s.zMinus p k) (s.zPlus p k))
    (hE : s.primeException p k ≤ (s.zMinus p k)^(3/2:ℝ)+(s.zPlus p k)^(3/2:ℝ)) :
    s.directionalEndpoint p k := by
  let z := s.zMinus p k+s.zPlus p k
  let u := LCDirection.directionRatio (s.zMinus p k) (s.zPlus p k)
  let lam := (p:ℝ)^(-1/q)
  have hz0 : 0 ≤ z := add_nonneg (s.zMinus_nonneg p k) (s.zPlus_nonneg p k)
  by_cases hz : z=0
  · exact Or.inl ⟨hz,s.primeException_zero_of_zero_deficit hM p k hz hE⟩
  · have hzp : 0 < z := lt_of_le_of_ne hz0 (Ne.symm hz)
    have hu := LCDirection.directionRatio_spec (s.zMinus_nonneg p k) (s.zPlus_nonneg p k) hzp
    have hln : 0 ≤ lam := Real.rpow_nonneg (by exact_mod_cast hp.pos.le) _
    have hlu : lam ≤ 1/3 := (BootstrapEndpoint.actual_lambda_upper hp hp142).trans
      (by norm_num [BootstrapEndpoint.lambdaUpper])
    have hnorm : LCDirection.normalizedInequality lam z u :=
      LCDirection.normalize_iteration (s.zMinus_nonneg p k) (s.zPlus_nonneg p k) hzp hit
    have he : s.primeException p k ≤ z^(3/2:ℝ)*LCDirection.h0 u := by
      rw [LCDirection.h0,← LCDirection.normalized_power_sum (s.zMinus_nonneg p k) (s.zPlus_nonneg p k) hzp]
      exact hE
    have hzBound := LCDirection.endpoint_bound hln hlu hu.1 (by linarith [hu.2.1]) hzp hseed
      (by norm_num : (121/1000:ℝ) ≤ 1/8) hnorm
    have hEBound := LCDirection.endpoint_exception_bound hln hlu hu.1 (by linarith [hu.2.1]) hzp hseed
      (by norm_num : (121/1000:ℝ) ≤ 1/8) hnorm he
    dsimp only [lam] at hzBound hEBound
    rw [prime_lambda_power p hp 4] at hzBound
    rw [prime_lambda_power p hp 6] at hEBound
    exact Or.inr ⟨hzp,hu.1,hu.2.1,hzBound,hEBound⟩

theorem actual_directional_endpoint (s : TaggedState Label n)
    (hs : ∀ t,Step s t → t.quality ≤ s.quality) (hM : 0 < s.edgeMass)
    (p : ℕ) (hp : Nat.Prime p) (hp142 : 142 < p) (k : ℕ)
    (hk : k ∈ s.valuationSupport p) (hseed : s.zMinus p k+s.zPlus p k ≤ (121/1000:ℝ)) :
    s.directionalEndpoint p k :=
  s.directional_endpoint_of_actual_bounds hM p hp hp142 k hseed
    (s.actual_directional_iteration hs hM p hp k hk) (s.actual_same_direction hs hM p k)

theorem actual_universal_directional_endpoint (s : TaggedState Label n)
    (hs : ∀ t,Step s t → t.universalQuality ≤ s.universalQuality) (hM : 0 < s.edgeMass)
    (p : ℕ) (hp : Nat.Prime p) (hp142 : 142 < p) (k : ℕ)
    (hk : k ∈ s.valuationSupport p) (hseed : s.zMinus p k+s.zPlus p k ≤ (121/1000:ℝ)) :
    s.directionalEndpoint p k :=
  s.directional_endpoint_of_actual_bounds hM p hp hp142 k hseed
    (s.actual_universal_directional_iteration hs hM p hp k hk) (s.actual_universal_same_direction hs hM p k)

theorem stable_endpoint_centers (s : TaggedState Label n)
    (hs : ∀ t,Step s t → t.quality ≤ s.quality) (hM : 0 < s.edgeMass) :
    ∃ centers : ℕ → ℕ,
      (∀ p ∉ s.primeSupport,centers p=0) ∧
      (∀ p,Nat.Prime p → 142 < p → s.directionalEndpoint p (centers p)) ∧
      (s.retainedLargeEdges centers ⊆ s.edges) ∧
      (∀ e ∈ s.retainedLargeEdges centers,∀ p,Nat.Prime p → 142 < p →
        s.centerBrackets p (centers p) e) ∧
      (1-∑ p ∈ s.largePrimeSupport,s.primeException p (centers p) ≤
        ∑ e ∈ s.retainedLargeEdges centers,s.edgeProbability e) := by
  obtain ⟨centers,hoff,hc,hsub,hbr,hmass⟩ := s.stable_directional_retention hs hM
  refine ⟨centers,hoff,?_,hsub,hbr,hmass⟩
  intro p hp hp142
  have h := hc p hp hp142
  exact s.actual_directional_endpoint hs hM p hp hp142 _ h.1 h.2.1

theorem universal_endpoint_centers (s : TaggedState Label n)
    (hs : ∀ t,Step s t → t.universalQuality ≤ s.universalQuality) (hM : 0 < s.edgeMass) :
    ∃ centers : ℕ → ℕ,
      (∀ p ∉ s.primeSupport,centers p=0) ∧
      (∀ p,Nat.Prime p → 142 < p → s.directionalEndpoint p (centers p)) ∧
      (s.retainedLargeEdges centers ⊆ s.edges) ∧
      (∀ e ∈ s.retainedLargeEdges centers,∀ p,Nat.Prime p → 142 < p →
        s.centerBrackets p (centers p) e) ∧
      (1-∑ p ∈ s.largePrimeSupport,s.primeException p (centers p) ≤
        ∑ e ∈ s.retainedLargeEdges centers,s.edgeProbability e) := by
  obtain ⟨centers,hoff,hc,hsub,hbr,hmass⟩ := s.universal_directional_retention hs hM
  refine ⟨centers,hoff,?_,hsub,hbr,hmass⟩
  intro p hp hp142
  have h := hc p hp hp142
  exact s.actual_universal_directional_endpoint hs hM p hp hp142 _ h.1 h.2.1

end LonelyRunnerNew.TaggedState

namespace LonelyRunnerNew

/-- All primes share the extracted stable state, and the endpoint estimate
and retained-edge set use exactly the same selected centers. -/
theorem original_universal_directional_endpoints (V : Finset ℕ) (hV : valid V) :
    ∃ (s : TaggedState ℕ V.card) (centers : ℕ → ℕ),
      Relation.ReflTransGen TaggedState.Step (initialTaggedState V hV) s ∧
      (initialTaggedState V hV).universalQuality ≤ s.universalQuality ∧
      (∀ t,TaggedState.Step s t → t.universalQuality ≤ s.universalQuality) ∧
      0 < s.edgeMass ∧
      (∀ p ∉ s.primeSupport,centers p=0) ∧
      (∀ p,Nat.Prime p → 142 < p → s.directionalEndpoint p (centers p)) ∧
      (s.retainedLargeEdges centers ⊆ s.edges) ∧
      (∀ e ∈ s.retainedLargeEdges centers,∀ p,Nat.Prime p → 142 < p →
        s.centerBrackets p (centers p) e) ∧
      (1-∑ p ∈ s.largePrimeSupport,s.primeException p (centers p) ≤
        ∑ e ∈ s.retainedLargeEdges centers,s.edgeProbability e) := by
  obtain ⟨s,hr,hq,hs,hM⟩ := original_universal_stable_state_exists V hV
  obtain ⟨centers,hoff,hc,hsub,hbr,hmass⟩ := s.universal_endpoint_centers hs hM
  exact ⟨s,centers,hr,hq,hs,hM,hoff,hc,hsub,hbr,hmass⟩

end LonelyRunnerNew
