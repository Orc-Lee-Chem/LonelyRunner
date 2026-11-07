import LonelyRunnerNew.WeightedRetention
import LonelyRunnerNew.PhysicalReachability
import LonelyRunnerNew.CenterRationalAdapter

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew.PhysicalState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

/-- Generic finite-measure LC is instantiated with the actual physical
weights. Its 27/50 denominator is this physical state's mass. -/
theorem all_prime_retention_of_concentration (s : PhysicalState Label n) (hM : 0<s.edgeMass)
    (h04 : s.weighted.RectangleConcentration) (h05 : s.weighted.LayerConcentration)
    (hL : ∀ x∈s.geometry.left,rough 142 (s.geometry.leftValue x))
    (hR : ∀ y∈s.geometry.right,rough 142 (s.geometry.rightValue y)) :
    ∃ (centers : ℕ → ℕ) (G : Finset (Label × Label)),
      (∀ p∉s.geometry.primeSupport,centers p=0) ∧ G⊆s.geometry.edges ∧
      (27/50:ℝ)*s.edgeMass≤∑ e∈G,s.edgeWeight e ∧
      (∀ e∈G,∀ p,Nat.Prime p → s.geometry.centerBrackets p (centers p) e) := by
  obtain ⟨centers,hoff,hsub,hmass,hlarge⟩ := s.weighted.large_prime_retention hM h04 h05
  refine ⟨centers,s.weighted.retainedLargeEdges centers,hoff,hsub,?_,?_⟩
  · simp only [WeightedState.edgeProbability] at hmass
    rw [←Finset.sum_div] at hmass
    exact (le_div_iff₀ hM).mp hmass
  · intro e he p hp
    by_cases hY : p≤142
    · have hnot := s.geometry.rough_prime_not_mem_support hL hR hp hY
      rw [hoff p hnot]
      exact s.geometry.brackets_zero_off_primeSupport hp hnot (hsub he)
    · exact hlarge e he p hp (by omega)

theorem ordinary_all_prime_retention (s : PhysicalState Label n)
    (hs : ∀ t,Step s t → t.quality q sigma≤s.quality q sigma) (hM : 0<s.edgeMass)
    (hL : ∀ x∈s.geometry.left,rough 142 (s.geometry.leftValue x))
    (hR : ∀ y∈s.geometry.right,rough 142 (s.geometry.rightValue y)) :
    ∃ (centers : ℕ → ℕ) (G : Finset (Label × Label)),
      (∀ p∉s.geometry.primeSupport,centers p=0) ∧ G⊆s.geometry.edges ∧
      (27/50:ℝ)*s.edgeMass≤∑ e∈G,s.edgeWeight e ∧
      (∀ e∈G,∀ p,Nat.Prime p → s.geometry.centerBrackets p (centers p) e) :=
  s.all_prime_retention_of_concentration hM
    (s.weighted_rectangle (by norm_num [q]) (by norm_num [q,sigma]) hs hM)
    (s.ordinary_weighted_layer hs hM) hL hR

theorem universal_all_prime_retention (s : PhysicalState Label n)
    (hs : ∀ t,Step s t → t.quality 4 0≤s.quality 4 0) (hM : 0<s.edgeMass)
    (hL : ∀ x∈s.geometry.left,rough 142 (s.geometry.leftValue x))
    (hR : ∀ y∈s.geometry.right,rough 142 (s.geometry.rightValue y)) :
    ∃ (centers : ℕ → ℕ) (G : Finset (Label × Label)),
      (∀ p∉s.geometry.primeSupport,centers p=0) ∧ G⊆s.geometry.edges ∧
      (27/50:ℝ)*s.edgeMass≤∑ e∈G,s.edgeWeight e ∧
      (∀ e∈G,∀ p,Nat.Prime p → s.geometry.centerBrackets p (centers p) e) :=
  s.all_prime_retention_of_concentration hM
    (s.weighted_rectangle (by norm_num : (0:ℝ)<4) (by norm_num) hs hM)
    (s.universal_weighted_layer hs hM) hL hR

/-- The same single N supplies the exact reduced-product identity on every
retained physical edge; no edge-dependent center is introduced. -/
theorem retained_product_identity (s : PhysicalState Label n) (centers : ℕ → ℕ)
    (hoff : ∀ p∉s.geometry.primeSupport,centers p=0) {e : Label × Label}
    (he : e∈s.geometry.edges)
    (hall : ∀ p,Nat.Prime p → s.geometry.centerBrackets p (centers p) e) :
    (RoughRational.product (CenterNormalization.ratio (s.geometry.commonCenter centers) (s.geometry.leftValue e.1))*
      RoughRational.product (CenterNormalization.ratio (s.geometry.commonCenter centers) (s.geometry.rightValue e.2)))*
      (Nat.gcd (s.geometry.leftValue e.1) (s.geometry.rightValue e.2))^2=
        s.geometry.leftValue e.1*s.geometry.rightValue e.2 :=
  CenterNormalization.rational_product_identity (s.geometry.commonCenter_pos centers)
    (s.geometry.commonCenter_gcd_identity centers hoff he hall)

end LonelyRunnerNew.PhysicalState
