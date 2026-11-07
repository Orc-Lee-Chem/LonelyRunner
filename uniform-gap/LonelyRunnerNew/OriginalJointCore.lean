import LonelyRunnerNew.CoreScore
import LonelyRunnerNew.CorePeelingBounds

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew

/-- Original speeds -> one ordinary stable parent -> its concrete joint core.
The child is not claimed stable. -/
theorem original_ordinary_joint_core (V : Finset ℕ) (hV : valid V) :
    ∃ s t : TaggedState ℕ V.card,
      Relation.ReflTransGen TaggedState.Step (initialTaggedState V hV) s ∧
      TaggedState.Step s t ∧ (initialTaggedState V hV).quality≤s.quality ∧
      (∀ u,TaggedState.Step s u → u.quality≤s.quality) ∧
      ∃ hM : 0<s.edgeMass,
        t.left=s.jointLeft (s.coreSmallCost (s.coreSmallCenters hM)) ∧
        t.right=s.jointRight (s.coreSmallCost (s.coreSmallCenters hM)) ∧
        t.edges=s.jointEdges (s.coreSmallCost (s.coreSmallCenters hM)) ∧
        t.leftValue=s.leftValue ∧ t.rightValue=s.rightValue ∧ t.a=s.a ∧ t.b=s.b ∧
        (Certificate.tbar:ℝ)*s.edgeMass≤t.edgeMass ∧ 0<t.edgeMass ∧
        (∀ x∈t.left,s.coreSmallCost (s.coreSmallCenters hM) (Sum.inl x)≤1375) ∧
        (∀ y∈t.right,s.coreSmallCost (s.coreSmallCenters hM) (Sum.inr y)≤1375) := by
  obtain ⟨s,hr,hq,hs⟩ := TaggedState.stable_state_exists (initialTaggedState V hV)
  have hp : 0<(initialTaggedState V hV).quality :=
    (TaggedState.quality_pos_iff_mass_pos _).mpr (initialTaggedState_mass_pos V hV)
  have hM : 0<s.edgeMass := (s.quality_pos_iff_mass_pos).mp (hp.trans_le hq)
  obtain ⟨t,hstep,hL,hR,hE,hvL,hvR,ha,hb,hm,hcostL,hcostR⟩ := s.stable_joint_core_state hs hM
  have htM : 0<t.edgeMass := (mul_pos TaggedState.tbar_exact_positive.2 hM).trans_le hm
  exact ⟨s,t,hr,hstep,hq,hs,hM,hL,hR,hE,hvL,hvR,ha,hb,hm,htM,hcostL,hcostR⟩

theorem original_universal_joint_core (V : Finset ℕ) (hV : valid V) :
    ∃ s t : TaggedState ℕ V.card,
      Relation.ReflTransGen TaggedState.Step (initialTaggedState V hV) s ∧
      TaggedState.Step s t ∧ (initialTaggedState V hV).universalQuality≤s.universalQuality ∧
      (∀ u,TaggedState.Step s u → u.universalQuality≤s.universalQuality) ∧
      ∃ hM : 0<s.edgeMass,
        t.left=s.jointLeft (s.coreSmallCost (s.coreSmallCenters hM)) ∧
        t.right=s.jointRight (s.coreSmallCost (s.coreSmallCenters hM)) ∧
        t.edges=s.jointEdges (s.coreSmallCost (s.coreSmallCenters hM)) ∧
        t.leftValue=s.leftValue ∧ t.rightValue=s.rightValue ∧ t.a=s.a ∧ t.b=s.b ∧
        (Certificate.tbar:ℝ)*s.edgeMass≤t.edgeMass ∧ 0<t.edgeMass ∧
        (∀ x∈t.left,s.coreSmallCost (s.coreSmallCenters hM) (Sum.inl x)≤1375) ∧
        (∀ y∈t.right,s.coreSmallCost (s.coreSmallCenters hM) (Sum.inr y)≤1375) := by
  obtain ⟨s,hr,hq,hs,hM⟩ := original_universal_stable_state_exists V hV
  obtain ⟨t,hstep,hL,hR,hE,hvL,hvR,ha,hb,hm,hcostL,hcostR⟩ := s.universal_joint_core_state hs hM
  have htM : 0<t.edgeMass := (mul_pos TaggedState.tbar_exact_positive.2 hM).trans_le hm
  exact ⟨s,t,hr,hstep,hq,hs,hM,hL,hR,hE,hvL,hvR,ha,hb,hm,htM,hcostL,hcostR⟩

end LonelyRunnerNew
