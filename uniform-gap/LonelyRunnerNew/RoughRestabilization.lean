import LonelyRunnerNew.RoughStepInvariants
import LonelyRunnerNew.RoughPrimeRetention

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew.TaggedState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

theorem ordinary_rough_stable_exists (s : TaggedState Label n) {P : ℝ}
    (hM : 0<s.edgeMass) (hL : ∀ x∈s.left,rough 142 (s.leftValue x))
    (hR : ∀ y∈s.right,rough 142 (s.rightValue y)) (hsep : separated P s) :
    ∃ t : TaggedState Label n,Relation.ReflTransGen Step s t ∧ s.quality≤t.quality ∧
      (∀ u,Step t u → u.quality≤t.quality) ∧ 0<t.edgeMass ∧
      (∀ x∈t.left,rough 142 (t.leftValue x)) ∧
      (∀ y∈t.right,rough 142 (t.rightValue y)) ∧ separated P t := by
  obtain ⟨t,hpath,hq,hs⟩ := s.stable_state_exists
  have htM := (t.quality_pos_iff_mass_pos).mp ((s.quality_pos_iff_mass_pos.mpr hM).trans_le hq)
  have hr := reachable_preserves_rough hpath hL hR
  exact ⟨t,hpath,hq,hs,htM,hr.1,hr.2,reachable_preserves_separation hpath hsep⟩

theorem universal_rough_stable_exists (s : TaggedState Label n) {P : ℝ}
    (hM : 0<s.edgeMass) (hL : ∀ x∈s.left,rough 142 (s.leftValue x))
    (hR : ∀ y∈s.right,rough 142 (s.rightValue y)) (hsep : separated P s) :
    ∃ t : TaggedState Label n,Relation.ReflTransGen Step s t ∧ s.universalQuality≤t.universalQuality ∧
      (∀ u,Step t u → u.universalQuality≤t.universalQuality) ∧ 0<t.edgeMass ∧
      (∀ x∈t.left,rough 142 (t.leftValue x)) ∧
      (∀ y∈t.right,rough 142 (t.rightValue y)) ∧ separated P t := by
  obtain ⟨t,hpath,hq,hs⟩ := s.universal_stable_state_exists
  have htM := (t.universalQuality_pos_iff_mass).mp
    ((s.universalQuality_pos_iff_mass.mpr hM).trans_le hq)
  have hr := reachable_preserves_rough hpath hL hR
  exact ⟨t,hpath,hq,hs,htM,hr.1,hr.2,reachable_preserves_separation hpath hsep⟩

/-- The retained probability is explicitly normalized by the NEW stable state's
edge mass. This does not assert a retained probability in the starting graph. -/
theorem ordinary_rough_stable_retention (s : TaggedState Label n) {P : ℝ}
    (hM : 0<s.edgeMass) (hL : ∀ x∈s.left,rough 142 (s.leftValue x))
    (hR : ∀ y∈s.right,rough 142 (s.rightValue y)) (hsep : separated P s) :
    ∃ (t : TaggedState Label n) (centers : ℕ → ℕ),
      Relation.ReflTransGen Step s t ∧ s.quality≤t.quality ∧
      (∀ u,Step t u → u.quality≤t.quality) ∧ 0<t.edgeMass ∧
      (∀ x∈t.left,rough 142 (t.leftValue x)) ∧
      (∀ y∈t.right,rough 142 (t.rightValue y)) ∧ separated P t ∧
      (∀ p∉t.primeSupport,centers p=0) ∧ t.retainedLargeEdges centers⊆t.edges ∧
      (27/50:ℝ)≤∑ e∈t.retainedLargeEdges centers,t.edgeProbability e ∧
      (27/50:ℝ)*t.edgeMass≤∑ e∈t.retainedLargeEdges centers,
        weight t.a t.b (t.leftValue e.1) (t.rightValue e.2) ∧
      (∀ e∈t.retainedLargeEdges centers,∀ p,Nat.Prime p → t.centerBrackets p (centers p) e) := by
  obtain ⟨t,hpath,hq,hs,htM,htL,htR,htsep⟩ := s.ordinary_rough_stable_exists hM hL hR hsep
  obtain ⟨centers,hoff,hsub,hmass,hall⟩ := t.stable_rough_all_prime_retention hs htM htL htR
  have hraw : (27/50:ℝ)*t.edgeMass≤∑ e∈t.retainedLargeEdges centers,
      weight t.a t.b (t.leftValue e.1) (t.rightValue e.2) := by
    simp only [edgeProbability,← Finset.sum_div] at hmass
    exact (le_div_iff₀ htM).mp hmass
  exact ⟨t,centers,hpath,hq,hs,htM,htL,htR,htsep,hoff,hsub,hmass,hraw,hall⟩

theorem universal_rough_stable_retention (s : TaggedState Label n) {P : ℝ}
    (hM : 0<s.edgeMass) (hL : ∀ x∈s.left,rough 142 (s.leftValue x))
    (hR : ∀ y∈s.right,rough 142 (s.rightValue y)) (hsep : separated P s) :
    ∃ (t : TaggedState Label n) (centers : ℕ → ℕ),
      Relation.ReflTransGen Step s t ∧ s.universalQuality≤t.universalQuality ∧
      (∀ u,Step t u → u.universalQuality≤t.universalQuality) ∧ 0<t.edgeMass ∧
      (∀ x∈t.left,rough 142 (t.leftValue x)) ∧
      (∀ y∈t.right,rough 142 (t.rightValue y)) ∧ separated P t ∧
      (∀ p∉t.primeSupport,centers p=0) ∧ t.retainedLargeEdges centers⊆t.edges ∧
      (27/50:ℝ)≤∑ e∈t.retainedLargeEdges centers,t.edgeProbability e ∧
      (27/50:ℝ)*t.edgeMass≤∑ e∈t.retainedLargeEdges centers,
        weight t.a t.b (t.leftValue e.1) (t.rightValue e.2) ∧
      (∀ e∈t.retainedLargeEdges centers,∀ p,Nat.Prime p → t.centerBrackets p (centers p) e) := by
  obtain ⟨t,hpath,hq,hs,htM,htL,htR,htsep⟩ := s.universal_rough_stable_exists hM hL hR hsep
  obtain ⟨centers,hoff,hsub,hmass,hall⟩ := t.universal_rough_all_prime_retention hs htM htL htR
  have hraw : (27/50:ℝ)*t.edgeMass≤∑ e∈t.retainedLargeEdges centers,
      weight t.a t.b (t.leftValue e.1) (t.rightValue e.2) := by
    simp only [edgeProbability,← Finset.sum_div] at hmass
    exact (le_div_iff₀ htM).mp hmass
  exact ⟨t,centers,hpath,hq,hs,htM,htL,htR,htsep,hoff,hsub,hmass,hraw,hall⟩

end LonelyRunnerNew.TaggedState
