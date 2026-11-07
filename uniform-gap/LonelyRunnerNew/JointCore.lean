import LonelyRunnerNew.CoreSmallPrimeCenters
import LonelyRunnerNew.CoreMarkov
import LonelyRunnerNew.CoreMarginals

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew.TaggedState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

/-- Only actual ordinary stability and positive mass. All cut, median, coarea,
mean-cost and deletion estimates are proved dependencies, not inputs. -/
theorem stable_joint_core (s : TaggedState Label n)
    (hs : ∀ t,Step s t → t.quality≤s.quality) (hM : 0<s.edgeMass) :
    (∑ v∈s.coreVertices,s.corePi v*s.coreSmallCost (s.coreSmallCenters hM) v)<(Certificate.Dbar:ℝ) ∧
    (s.jointLeft (s.coreSmallCost (s.coreSmallCenters hM))).Nonempty ∧
    (s.jointRight (s.coreSmallCost (s.coreSmallCenters hM))).Nonempty ∧
    (Certificate.tbar:ℝ)≤∑ e∈s.jointEdges (s.coreSmallCost (s.coreSmallCenters hM)),s.edgeProbability e := by
  have hcost := s.stable_core_cost_mean hs hM
  have hmass := s.jointCore_of_cost hM _ (fun v _ => s.coreSmallCost_nonneg _ v) hcost
  have hne := s.joint_sides_nonempty _ hmass
  exact ⟨hcost,hne.1,hne.2,hmass⟩

theorem universal_joint_core (s : TaggedState Label n)
    (hs : ∀ t,Step s t → t.universalQuality≤s.universalQuality) (hM : 0<s.edgeMass) :
    (∑ v∈s.coreVertices,s.corePi v*s.coreSmallCost (s.coreSmallCenters hM) v)<(Certificate.Dbar:ℝ) ∧
    (s.jointLeft (s.coreSmallCost (s.coreSmallCenters hM))).Nonempty ∧
    (s.jointRight (s.coreSmallCost (s.coreSmallCenters hM))).Nonempty ∧
    (Certificate.tbar:ℝ)≤∑ e∈s.jointEdges (s.coreSmallCost (s.coreSmallCenters hM)),s.edgeProbability e := by
  have hcost := s.universal_core_cost_mean hs hM
  have hmass := s.jointCore_of_cost hM _ (fun v _ => s.coreSmallCost_nonneg _ v) hcost
  have hne := s.joint_sides_nonempty _ hmass
  exact ⟨hcost,hne.1,hne.2,hmass⟩

/-- An actual restriction state with the proved mass comparison. No assertion
that this restriction is stable is part of this result. -/
theorem joint_core_state_of_mass (s : TaggedState Label n) (hM : 0<s.edgeMass)
    (B : (Label ⊕ Label) → ℝ)
    (hmass : (Certificate.tbar:ℝ)≤∑ e∈s.jointEdges B,s.edgeProbability e) :
    ∃ t : TaggedState Label n,Step s t ∧ t.left=s.jointLeft B ∧ t.right=s.jointRight B ∧
      t.edges=s.jointEdges B ∧ t.leftValue=s.leftValue ∧ t.rightValue=s.rightValue ∧
      t.a=s.a ∧ t.b=s.b ∧ (Certificate.tbar:ℝ)*s.edgeMass≤t.edgeMass ∧
      (∀ x∈t.left,B (Sum.inl x)≤1375) ∧ (∀ y∈t.right,B (Sum.inr y)≤1375) := by
  obtain ⟨hL,hR⟩ := s.joint_sides_nonempty B hmass
  let t := s.restrict (s.jointLeft B) (s.jointRight B) (Finset.filter_subset _ _) (Finset.filter_subset _ _) hL hR
  have he : t.edges=s.jointEdges B := (s.jointEdges_eq_inter B).symm
  have hr := s.joint_restriction_probability B hL hR
  have hm : (Certificate.tbar:ℝ)*s.edgeMass≤t.edgeMass := by
    rw [hr] at hmass
    exact (le_div_iff₀ hM).mp hmass
  exact ⟨t,Step.restrict s _ _ _ _ _ _,rfl,rfl,he,rfl,rfl,rfl,rfl,hm,
    fun x hx => (Finset.mem_filter.mp hx).2,fun y hy => (Finset.mem_filter.mp hy).2⟩

theorem stable_joint_core_state (s : TaggedState Label n)
    (hs : ∀ t,Step s t → t.quality≤s.quality) (hM : 0<s.edgeMass) :
    ∃ t : TaggedState Label n,Step s t ∧ t.left=s.jointLeft (s.coreSmallCost (s.coreSmallCenters hM)) ∧
      t.right=s.jointRight (s.coreSmallCost (s.coreSmallCenters hM)) ∧
      t.edges=s.jointEdges (s.coreSmallCost (s.coreSmallCenters hM)) ∧
      t.leftValue=s.leftValue ∧ t.rightValue=s.rightValue ∧ t.a=s.a ∧ t.b=s.b ∧
      (Certificate.tbar:ℝ)*s.edgeMass≤t.edgeMass ∧
      (∀ x∈t.left,s.coreSmallCost (s.coreSmallCenters hM) (Sum.inl x)≤1375) ∧
      (∀ y∈t.right,s.coreSmallCost (s.coreSmallCenters hM) (Sum.inr y)≤1375) :=
  s.joint_core_state_of_mass hM _ (s.stable_joint_core hs hM).2.2.2

theorem universal_joint_core_state (s : TaggedState Label n)
    (hs : ∀ t,Step s t → t.universalQuality≤s.universalQuality) (hM : 0<s.edgeMass) :
    ∃ t : TaggedState Label n,Step s t ∧ t.left=s.jointLeft (s.coreSmallCost (s.coreSmallCenters hM)) ∧
      t.right=s.jointRight (s.coreSmallCost (s.coreSmallCenters hM)) ∧
      t.edges=s.jointEdges (s.coreSmallCost (s.coreSmallCenters hM)) ∧
      t.leftValue=s.leftValue ∧ t.rightValue=s.rightValue ∧ t.a=s.a ∧ t.b=s.b ∧
      (Certificate.tbar:ℝ)*s.edgeMass≤t.edgeMass ∧
      (∀ x∈t.left,s.coreSmallCost (s.coreSmallCenters hM) (Sum.inl x)≤1375) ∧
      (∀ y∈t.right,s.coreSmallCost (s.coreSmallCenters hM) (Sum.inr y)≤1375) :=
  s.joint_core_state_of_mass hM _ (s.universal_joint_core hs hM).2.2.2

end LonelyRunnerNew.TaggedState
