import LonelyRunnerNew.RoughImageState

noncomputable section
set_option autoImplicit false
namespace LonelyRunnerNew.TaggedState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

/-- A concrete core restriction supplies all the inputs to value replacement.
The conclusion compares both scores, without asserting stability of the image. -/
theorem peel_core_restriction (s t : TaggedState Label n) (hM : 0<s.edgeMass)
    (hsep : separated (Real.exp 6880) s) (hstep : Step s t)
    (hL : t.left=s.jointLeft (s.coreSmallCost (s.coreSmallCenters hM)))
    (hR : t.right=s.jointRight (s.coreSmallCost (s.coreSmallCenters hM)))
    (hE : t.edges=s.jointEdges (s.coreSmallCost (s.coreSmallCenters hM)))
    (hvL : t.leftValue=s.leftValue) (hvR : t.rightValue=s.rightValue)
    (ha : t.a=s.a) (hb : t.b=s.b)
    (hm : (Certificate.tbar:ℝ)*s.edgeMass≤t.edgeMass)
    (hcostL : ∀ x∈t.left,s.coreSmallCost (s.coreSmallCenters hM) (Sum.inl x)≤1375)
    (hcostR : ∀ y∈t.right,s.coreSmallCost (s.coreSmallCenters hM) (Sum.inr y)≤1375) :
    ∃ r : TaggedState Label n,
      r.left=s.jointLeft (s.coreSmallCost (s.coreSmallCenters hM)) ∧
      r.right=s.jointRight (s.coreSmallCost (s.coreSmallCenters hM)) ∧
      r.edges=s.jointEdges (s.coreSmallCost (s.coreSmallCenters hM)) ∧
      r.leftValue=(fun x => SmallPrimePeeling.roughPart (s.leftValue x)) ∧
      r.rightValue=(fun y => SmallPrimePeeling.roughPart (s.rightValue y)) ∧
      r.a=s.a ∧ r.b=s.b ∧ r.left.Nonempty ∧ r.right.Nonempty ∧
      (∀ x∈r.left,rough 142 (r.leftValue x)) ∧
      (∀ y∈r.right,rough 142 (r.rightValue y)) ∧
      separated (Real.exp 4130) r ∧
      (Certificate.tbar:ℝ)*s.edgeMass≤r.edgeMass ∧ 0<r.edgeMass ∧
      (Certificate.tbar:ℝ)^q*s.quality≤r.quality ∧
      (Certificate.tbar:ℝ)^4*s.universalQuality≤r.universalQuality := by
  let centers := s.coreSmallCenters hM
  have htL : ∀ x∈t.left,t.coreSmallCost centers (Sum.inl x)≤1375 := by
    intro x hx
    rw [s.coreSmallCost_congr_values t hvL hvR]
    exact hcostL x hx
  have htR : ∀ y∈t.right,t.coreSmallCost centers (Sum.inr y)≤1375 := by
    intro y hy
    rw [s.coreSmallCost_congr_values t hvL hvR]
    exact hcostR y hy
  have htsep := step_preserves_separation hstep hsep
  let r := t.roughImage centers htL htR htsep
  have hrM : t.edgeMass≤r.edgeMass := t.roughImage_mass_ge centers htL htR htsep
  have hrQ : t.quality≤r.quality := t.roughImage_quality_ge centers htL htR htsep
  have hrU : t.universalQuality≤r.universalQuality := t.roughImage_universal_quality_ge centers htL htR htsep
  have htleft : t.left⊆s.left := by rw [hL]; exact Finset.filter_subset _ _
  have htright : t.right⊆s.right := by rw [hR]; exact Finset.filter_subset _ _
  have hQ := s.quality_restriction_mass_bound t htleft htright ha hb tbar_exact_positive.2.le hm
  have hU := s.universal_quality_restriction_mass_bound t htleft htright ha hb tbar_exact_positive.2.le hm
  have hrrough := t.roughImage_rough centers htL htR htsep
  refine ⟨r,hL,hR,hE,?_,?_,ha,hb,r.left_nonempty,r.right_nonempty,
    hrrough.1,hrrough.2,t.roughImage_separated centers htL htR htsep,
    hm.trans hrM,(mul_pos tbar_exact_positive.2 hM).trans_le (hm.trans hrM),
    hQ.trans hrQ,hU.trans hrU⟩
  · change (fun x => SmallPrimePeeling.roughPart (t.leftValue x))=_
    rw [hvL]
  · change (fun y => SmallPrimePeeling.roughPart (t.rightValue y))=_
    rw [hvR]

end LonelyRunnerNew.TaggedState
