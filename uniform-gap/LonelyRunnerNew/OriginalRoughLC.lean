import LonelyRunnerNew.OriginalSeparatedPeeling
import LonelyRunnerNew.CenterRationalAdapter

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew

/-- Original separated speeds -> concrete peeled state -> a new stable rough
state -> one all-prime retained set. Its probability uses the NEW state's mass. -/
theorem original_ordinary_stable_rough_LC (V : Finset ℕ) (hV : valid V)
    (hsep : separated (Real.exp 6880) V) :
    ∃ (s r t : TaggedState ℕ V.card) (centers : ℕ → ℕ),
      Relation.ReflTransGen TaggedState.Step (initialTaggedState V hV) s ∧
      (∀ u,TaggedState.Step s u → u.quality≤s.quality) ∧
      TaggedState.separated (Real.exp 6880) s ∧
      ∃ hM : 0<s.edgeMass,
        r.left=s.jointLeft (s.coreSmallCost (s.coreSmallCenters hM)) ∧
        r.right=s.jointRight (s.coreSmallCost (s.coreSmallCenters hM)) ∧
        r.edges=s.jointEdges (s.coreSmallCost (s.coreSmallCenters hM)) ∧
        r.leftValue=(fun x => SmallPrimePeeling.roughPart (s.leftValue x)) ∧
        r.rightValue=(fun y => SmallPrimePeeling.roughPart (s.rightValue y)) ∧
        r.a=s.a ∧ r.b=s.b ∧ 0<r.edgeMass ∧
        Relation.ReflTransGen TaggedState.Step r t ∧ r.quality≤t.quality ∧
        (∀ u,TaggedState.Step t u → u.quality≤t.quality) ∧ 0<t.edgeMass ∧
        (∀ x∈t.left,rough 142 (t.leftValue x)) ∧
        (∀ y∈t.right,rough 142 (t.rightValue y)) ∧
        TaggedState.separated (Real.exp 4130) t ∧
        t.left⊆V ∧ t.right⊆V ∧ t.edges⊆initialEdges V ∧
        (Certificate.tbar:ℝ)^q*s.quality≤t.quality ∧
        (Certificate.tbar:ℝ)^q*(initialTaggedState V hV).quality≤t.quality ∧
        (∀ p∉t.primeSupport,centers p=0) ∧ t.retainedLargeEdges centers⊆t.edges ∧
        (27/50:ℝ)≤∑ e∈t.retainedLargeEdges centers,t.edgeProbability e ∧
        (27/50:ℝ)*t.edgeMass≤∑ e∈t.retainedLargeEdges centers,
          weight t.a t.b (t.leftValue e.1) (t.rightValue e.2) ∧
        (∀ e∈t.retainedLargeEdges centers,∀ p,Nat.Prime p → t.centerBrackets p (centers p) e) ∧
        rough 142 (t.commonCenter centers) ∧
        (∀ e∈t.retainedLargeEdges centers,
          ((CenterNormalization.ratio (t.commonCenter centers) (t.leftValue e.1)).den*
            (CenterNormalization.ratio (t.commonCenter centers) (t.rightValue e.2)).den)*
            Nat.gcd (t.leftValue e.1) (t.rightValue e.2)=t.commonCenter centers) := by
  obtain ⟨s,r,hpath,hinit,hs,hparentsep,hM,hrL,hrR,hrE,hrvL,hrvR,hra,hrb,
    hrleft,hrright,hredges,_,_,hrroughL,hrroughR,hrsep,hrMass,hrpos,hrQ⟩ :=
      original_ordinary_rough_core V hV hsep
  have hleft : r.left⊆s.left := by rw [hrL];exact Finset.filter_subset _ _
  have hright : r.right⊆s.right := by rw [hrR];exact Finset.filter_subset _ _
  have hparentQ := s.quality_restriction_mass_bound r hleft hright hra hrb
    TaggedState.tbar_exact_positive.2.le hrMass
  obtain ⟨t,centers,htpath,htQ,htstable,htM,htL,htR,htsep,hoff,hG,hprob,hraw,hall⟩ :=
    r.ordinary_rough_stable_retention hrpos hrroughL hrroughR hrsep
  have hsupp := TaggedState.reachable_label_support htpath
  refine ⟨s,r,t,centers,hpath,hs,hparentsep,hM,hrL,hrR,hrE,hrvL,hrvR,hra,hrb,hrpos,
    htpath,htQ,htstable,htM,htL,htR,htsep,hsupp.1.trans hrleft,
    hsupp.2.1.trans hrright,hsupp.2.2.trans hredges,hparentQ.trans htQ,
    hrQ.trans htQ,hoff,hG,hprob,hraw,hall,t.commonCenter_rough centers htL htR,?_⟩
  intro e he
  exact CenterNormalization.denominator_product (t.commonCenter_pos centers)
    (t.commonCenter_gcd_identity centers hoff (hG he) (hall e he))

/-- Original separated speeds -> concrete peeled state -> a new stable rough
state -> one all-prime retained set. Its probability uses the NEW state's mass. -/
theorem original_universal_stable_rough_LC (V : Finset ℕ) (hV : valid V)
    (hsep : separated (Real.exp 6880) V) :
    ∃ (s r t : TaggedState ℕ V.card) (centers : ℕ → ℕ),
      Relation.ReflTransGen TaggedState.Step (initialTaggedState V hV) s ∧
      (∀ u,TaggedState.Step s u → u.universalQuality≤s.universalQuality) ∧
      TaggedState.separated (Real.exp 6880) s ∧
      ∃ hM : 0<s.edgeMass,
        r.left=s.jointLeft (s.coreSmallCost (s.coreSmallCenters hM)) ∧
        r.right=s.jointRight (s.coreSmallCost (s.coreSmallCenters hM)) ∧
        r.edges=s.jointEdges (s.coreSmallCost (s.coreSmallCenters hM)) ∧
        r.leftValue=(fun x => SmallPrimePeeling.roughPart (s.leftValue x)) ∧
        r.rightValue=(fun y => SmallPrimePeeling.roughPart (s.rightValue y)) ∧
        r.a=s.a ∧ r.b=s.b ∧ 0<r.edgeMass ∧
        Relation.ReflTransGen TaggedState.Step r t ∧ r.universalQuality≤t.universalQuality ∧
        (∀ u,TaggedState.Step t u → u.universalQuality≤t.universalQuality) ∧ 0<t.edgeMass ∧
        (∀ x∈t.left,rough 142 (t.leftValue x)) ∧
        (∀ y∈t.right,rough 142 (t.rightValue y)) ∧
        TaggedState.separated (Real.exp 4130) t ∧
        t.left⊆V ∧ t.right⊆V ∧ t.edges⊆initialEdges V ∧
        (Certificate.tbar:ℝ)^4*s.universalQuality≤t.universalQuality ∧
        (Certificate.tbar:ℝ)^4*(initialTaggedState V hV).universalQuality≤t.universalQuality ∧
        (∀ p∉t.primeSupport,centers p=0) ∧ t.retainedLargeEdges centers⊆t.edges ∧
        (27/50:ℝ)≤∑ e∈t.retainedLargeEdges centers,t.edgeProbability e ∧
        (27/50:ℝ)*t.edgeMass≤∑ e∈t.retainedLargeEdges centers,
          weight t.a t.b (t.leftValue e.1) (t.rightValue e.2) ∧
        (∀ e∈t.retainedLargeEdges centers,∀ p,Nat.Prime p → t.centerBrackets p (centers p) e) ∧
        rough 142 (t.commonCenter centers) ∧
        (∀ e∈t.retainedLargeEdges centers,
          ((CenterNormalization.ratio (t.commonCenter centers) (t.leftValue e.1)).den*
            (CenterNormalization.ratio (t.commonCenter centers) (t.rightValue e.2)).den)*
            Nat.gcd (t.leftValue e.1) (t.rightValue e.2)=t.commonCenter centers) := by
  obtain ⟨s,r,hpath,hinit,hs,hparentsep,hM,hrL,hrR,hrE,hrvL,hrvR,hra,hrb,
    hrleft,hrright,hredges,_,_,hrroughL,hrroughR,hrsep,hrMass,hrpos,hrQ⟩ :=
      original_universal_rough_core V hV hsep
  have hleft : r.left⊆s.left := by rw [hrL];exact Finset.filter_subset _ _
  have hright : r.right⊆s.right := by rw [hrR];exact Finset.filter_subset _ _
  have hparentQ := s.universal_quality_restriction_mass_bound r hleft hright hra hrb
    TaggedState.tbar_exact_positive.2.le hrMass
  obtain ⟨t,centers,htpath,htQ,htstable,htM,htL,htR,htsep,hoff,hG,hprob,hraw,hall⟩ :=
    r.universal_rough_stable_retention hrpos hrroughL hrroughR hrsep
  have hsupp := TaggedState.reachable_label_support htpath
  refine ⟨s,r,t,centers,hpath,hs,hparentsep,hM,hrL,hrR,hrE,hrvL,hrvR,hra,hrb,hrpos,
    htpath,htQ,htstable,htM,htL,htR,htsep,hsupp.1.trans hrleft,
    hsupp.2.1.trans hrright,hsupp.2.2.trans hredges,hparentQ.trans htQ,
    hrQ.trans htQ,hoff,hG,hprob,hraw,hall,t.commonCenter_rough centers htL htR,?_⟩
  intro e he
  exact CenterNormalization.denominator_product (t.commonCenter_pos centers)
    (t.commonCenter_gcd_identity centers hoff (hG he) (hall e he))

end LonelyRunnerNew
