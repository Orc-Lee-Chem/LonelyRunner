import LonelyRunnerNew.SeparatedCorePeeling
import LonelyRunnerNew.OriginalJointCore

noncomputable section
set_option autoImplicit false
namespace LonelyRunnerNew

/-- Original separated speeds, ordinary descent, the same parent's joint core,
and its actual rough image. The value replacement is not asserted to be a Step;
only the path from the original state to the stable parent is a Step path. -/
theorem original_ordinary_rough_core (V : Finset ℕ) (hV : valid V)
    (hsep : separated (Real.exp 6880) V) :
    ∃ s r : TaggedState ℕ V.card,
      Relation.ReflTransGen TaggedState.Step (initialTaggedState V hV) s ∧
      (initialTaggedState V hV).quality≤s.quality ∧
      (∀ u,TaggedState.Step s u → u.quality≤s.quality) ∧
      TaggedState.separated (Real.exp 6880) s ∧
      ∃ hM : 0<s.edgeMass,
        r.left=s.jointLeft (s.coreSmallCost (s.coreSmallCenters hM)) ∧
        r.right=s.jointRight (s.coreSmallCost (s.coreSmallCenters hM)) ∧
        r.edges=s.jointEdges (s.coreSmallCost (s.coreSmallCenters hM)) ∧
        r.leftValue=(fun x => SmallPrimePeeling.roughPart (s.leftValue x)) ∧
        r.rightValue=(fun y => SmallPrimePeeling.roughPart (s.rightValue y)) ∧
        r.a=s.a ∧ r.b=s.b ∧ r.left⊆V ∧ r.right⊆V ∧ r.edges⊆initialEdges V ∧
        r.left.Nonempty ∧ r.right.Nonempty ∧
        (∀ x∈r.left,rough 142 (r.leftValue x)) ∧
        (∀ y∈r.right,rough 142 (r.rightValue y)) ∧
        TaggedState.separated (Real.exp 4130) r ∧
        (Certificate.tbar:ℝ)*s.edgeMass≤r.edgeMass ∧ 0<r.edgeMass ∧
        (Certificate.tbar:ℝ)^q*(initialTaggedState V hV).quality≤r.quality := by
  obtain ⟨s,t,hpath,hstep,hscore,hs,hM,hL,hR,hE,hvL,hvR,ha,hb,hm,_,hcostL,hcostR⟩ :=
    original_ordinary_joint_core V hV
  have hparentsep := TaggedState.reachable_preserves_separation hpath
    (initialTaggedState_separated V hV _ hsep)
  obtain ⟨r,hrL,hrR,hrE,hrvL,hrvR,hra,hrb,hrLN,hrRN,hrroughL,hrroughR,
    hrsep,hrM,hrpos,hrQ,_⟩ := s.peel_core_restriction t hM hparentsep hstep
      hL hR hE hvL hvR ha hb hm hcostL hcostR
  have hinit := mul_le_mul_of_nonneg_left hscore
    (Real.rpow_nonneg TaggedState.tbar_exact_positive.2.le q)
  have hsupp := TaggedState.reachable_label_support hpath
  have hrleft : r.left⊆V := by rw [hrL]; exact (Finset.filter_subset _ _).trans hsupp.1
  have hrright : r.right⊆V := by rw [hrR]; exact (Finset.filter_subset _ _).trans hsupp.2.1
  have hredges : r.edges⊆initialEdges V := by
    rw [hrE]
    exact (Finset.filter_subset _ _).trans hsupp.2.2
  exact ⟨s,r,hpath,hscore,hs,hparentsep,hM,hrL,hrR,hrE,hrvL,hrvR,hra,hrb,
    hrleft,hrright,hredges,hrLN,hrRN,hrroughL,hrroughR,hrsep,hrM,hrpos,hinit.trans hrQ⟩

/-- The universal scoring branch uses its own stable parent and core estimates.
No ordinary stability is used as a substitute for universal stability. -/
theorem original_universal_rough_core (V : Finset ℕ) (hV : valid V)
    (hsep : separated (Real.exp 6880) V) :
    ∃ s r : TaggedState ℕ V.card,
      Relation.ReflTransGen TaggedState.Step (initialTaggedState V hV) s ∧
      (initialTaggedState V hV).universalQuality≤s.universalQuality ∧
      (∀ u,TaggedState.Step s u → u.universalQuality≤s.universalQuality) ∧
      TaggedState.separated (Real.exp 6880) s ∧
      ∃ hM : 0<s.edgeMass,
        r.left=s.jointLeft (s.coreSmallCost (s.coreSmallCenters hM)) ∧
        r.right=s.jointRight (s.coreSmallCost (s.coreSmallCenters hM)) ∧
        r.edges=s.jointEdges (s.coreSmallCost (s.coreSmallCenters hM)) ∧
        r.leftValue=(fun x => SmallPrimePeeling.roughPart (s.leftValue x)) ∧
        r.rightValue=(fun y => SmallPrimePeeling.roughPart (s.rightValue y)) ∧
        r.a=s.a ∧ r.b=s.b ∧ r.left⊆V ∧ r.right⊆V ∧ r.edges⊆initialEdges V ∧
        r.left.Nonempty ∧ r.right.Nonempty ∧
        (∀ x∈r.left,rough 142 (r.leftValue x)) ∧
        (∀ y∈r.right,rough 142 (r.rightValue y)) ∧
        TaggedState.separated (Real.exp 4130) r ∧
        (Certificate.tbar:ℝ)*s.edgeMass≤r.edgeMass ∧ 0<r.edgeMass ∧
        (Certificate.tbar:ℝ)^4*(initialTaggedState V hV).universalQuality≤r.universalQuality := by
  obtain ⟨s,t,hpath,hstep,hscore,hs,hM,hL,hR,hE,hvL,hvR,ha,hb,hm,_,hcostL,hcostR⟩ :=
    original_universal_joint_core V hV
  have hparentsep := TaggedState.reachable_preserves_separation hpath
    (initialTaggedState_separated V hV _ hsep)
  obtain ⟨r,hrL,hrR,hrE,hrvL,hrvR,hra,hrb,hrLN,hrRN,hrroughL,hrroughR,
    hrsep,hrM,hrpos,_,hrQ⟩ := s.peel_core_restriction t hM hparentsep hstep
      hL hR hE hvL hvR ha hb hm hcostL hcostR
  have hinit := mul_le_mul_of_nonneg_left hscore (pow_nonneg TaggedState.tbar_exact_positive.2.le 4)
  have hsupp := TaggedState.reachable_label_support hpath
  have hrleft : r.left⊆V := by rw [hrL]; exact (Finset.filter_subset _ _).trans hsupp.1
  have hrright : r.right⊆V := by rw [hrR]; exact (Finset.filter_subset _ _).trans hsupp.2.1
  have hredges : r.edges⊆initialEdges V := by
    rw [hrE]
    exact (Finset.filter_subset _ _).trans hsupp.2.2
  exact ⟨s,r,hpath,hscore,hs,hparentsep,hM,hrL,hrR,hrE,hrvL,hrvR,hra,hrb,
    hrleft,hrright,hredges,hrLN,hrRN,hrroughL,hrroughR,hrsep,hrM,hrpos,hinit.trans hrQ⟩

end LonelyRunnerNew
