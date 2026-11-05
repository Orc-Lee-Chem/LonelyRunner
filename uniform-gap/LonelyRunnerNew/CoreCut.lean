import LonelyRunnerNew.CoreProbability
import LonelyRunnerNew.CoreCutScalar

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew.TaggedState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

def corePiMass (s : TaggedState Label n) (S : Finset (Label ⊕ Label)) : ℝ :=
  ∑ v∈s.coreVertices.filter (·∈S),s.corePi v
def coreCross (s : TaggedState Label n) (S : Finset (Label ⊕ Label)) : ℝ :=
  ∑ v∈s.coreVertices,∑ u∈s.coreVertices,if v∈S ∧ u∉S then s.coreOmega v u else 0
def coreLeftPart (s : TaggedState Label n) (S : Finset (Label ⊕ Label)) : Finset Label :=
  s.left.filter (fun x => Sum.inl x∈S)
def coreRightPart (s : TaggedState Label n) (S : Finset (Label ⊕ Label)) : Finset Label :=
  s.right.filter (fun y => Sum.inr y∈S)
def coreRectangle (s : TaggedState Label n) (A B : Finset Label) : ℝ :=
  ∑ e∈s.edges.filter (fun e => e.1∈A ∧ e.2∈B),s.edgeProbability e
def coreUniformMass (s : TaggedState Label n) (S : Finset (Label ⊕ Label)) : ℝ :=
  (((s.coreLeftPart S).card:ℝ)/s.left.card+((s.coreRightPart S).card:ℝ)/s.right.card)/2
def coreCrossingEdges (s : TaggedState Label n) (S : Finset (Label ⊕ Label)) : ℝ :=
  s.coreRectangle (s.coreLeftPart S) (s.right\s.coreRightPart S)+
    s.coreRectangle (s.left\s.coreLeftPart S) (s.coreRightPart S)

theorem corePiMass_average (s : TaggedState Label n) (S : Finset (Label ⊕ Label)) :
    s.corePiMass S=∑ e∈s.edges,(s.edgeProbability e/2)*
      ((if coreSource e∈S then 1 else 0)+(if coreTarget e∈S then 1 else 0)) := by
  simpa only [corePiMass,Finset.sum_filter,mul_ite,mul_one,mul_zero] using
    s.corePi_average (fun v => if v∈S then 1 else 0)

theorem coreCross_average (s : TaggedState Label n) (S : Finset (Label ⊕ Label)) :
    s.coreCross S=∑ e∈s.edges,(s.edgeProbability e/2)*
      ((if coreSource e∈S ∧ coreTarget e∉S then 1 else 0)+
       (if coreTarget e∈S ∧ coreSource e∉S then 1 else 0)) := by
  simpa only [coreCross,mul_ite,mul_one,mul_zero] using
    s.coreOmega_average (fun v u => if v∈S ∧ u∉S then 1 else 0)

theorem core_cut_bookkeeping (s : TaggedState Label n) (hM : 0<s.edgeMass)
    (S : Finset (Label ⊕ Label)) :
    s.coreCross S=s.coreCrossingEdges S/2 ∧
    s.corePiMass S=s.coreRectangle (s.coreLeftPart S) (s.coreRightPart S)+s.coreCrossingEdges S/2 ∧
    s.corePiMass (s.coreVertices\S)=s.coreRectangle (s.left\s.coreLeftPart S) (s.right\s.coreRightPart S)+s.coreCrossingEdges S/2 ∧
    s.coreRectangle (s.coreLeftPart S) (s.coreRightPart S)+
      s.coreRectangle (s.left\s.coreLeftPart S) (s.right\s.coreRightPart S)+s.coreCrossingEdges S=1 := by
  have hprob := s.edgeProbability_sum hM
  refine ⟨?_,?_,?_,?_⟩
  · rw [s.coreCross_average]
    unfold coreCrossingEdges coreRectangle
    simp only [Finset.sum_filter,Finset.sum_div,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e he
    have hm := Finset.mem_product.mp (s.edges_subset he)
    by_cases hl : Sum.inl e.1∈S <;> by_cases hr : Sum.inr e.2∈S <;>
      simp [coreSource,coreTarget,coreLeftPart,coreRightPart,hm.1,hm.2,hl,hr] <;> ring
  · rw [s.corePiMass_average]
    unfold coreCrossingEdges coreRectangle
    simp only [Finset.sum_filter,Finset.sum_div,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e he
    have hm := Finset.mem_product.mp (s.edges_subset he)
    by_cases hl : Sum.inl e.1∈S <;> by_cases hr : Sum.inr e.2∈S <;>
      simp [coreSource,coreTarget,coreLeftPart,coreRightPart,hm.1,hm.2,hl,hr] <;> ring
  · rw [s.corePiMass_average]
    unfold coreCrossingEdges coreRectangle
    simp only [Finset.sum_filter,Finset.sum_div,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e he
    have hm := Finset.mem_product.mp (s.edges_subset he)
    have hsrc := s.coreSource_mem he
    have hdst := s.coreTarget_mem he
    by_cases hl : Sum.inl e.1∈S <;> by_cases hr : Sum.inr e.2∈S <;>
      simp [coreSource,coreTarget,coreLeftPart,coreRightPart,coreVertices,hm.1,hm.2,hl,hr] <;> ring
  · rw [← hprob]
    unfold coreCrossingEdges coreRectangle
    simp only [Finset.sum_filter,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e he
    have hm := Finset.mem_product.mp (s.edges_subset he)
    by_cases hl : Sum.inl e.1∈S <;> by_cases hr : Sum.inr e.2∈S <;>
      simp [coreLeftPart,coreRightPart,hm.1,hm.2,hl,hr]

theorem coreRectangle_eq (s : TaggedState Label n) (A B : Finset Label) :
    s.coreRectangle A B=s.rectangleMass A B/s.edgeMass := by
  unfold coreRectangle rectangleMass edgeProbability
  rw [Finset.sum_div]

theorem uniform_card_bounds (F A : Finset Label) (hF : F.Nonempty) (hA : A⊆F) :
    0≤(A.card:ℝ)/F.card ∧ (A.card:ℝ)/F.card≤1 := by
  have hFp : (0:ℝ)<F.card := by exact_mod_cast hF.card_pos
  exact ⟨div_nonneg (Nat.cast_nonneg _) hFp.le,(div_le_one hFp).mpr (by exact_mod_cast Finset.card_le_card hA)⟩

theorem uniform_card_complement (F A : Finset Label) (hF : F.Nonempty) (hA : A⊆F) :
    ((F\A).card:ℝ)/F.card=1-(A.card:ℝ)/F.card := by
  have hc : ((F\A).card:ℝ)=(F.card:ℝ)-(A.card:ℝ) := by
    rw [Finset.card_sdiff_of_subset hA]
    exact Nat.cast_sub (Finset.card_le_card hA)
  rw [hc,sub_div,div_self (by exact_mod_cast hF.card_pos.ne')]

/-- L04 is an intermediate input here; both actual score specializations below
supply their own already proved rectangle concentration. -/
theorem core_cut_of_rectangles (s : TaggedState Label n) (hM : 0<s.edgeMass)
    (hrect : ∀ A⊆s.left,∀ B⊆s.right,s.rectangleMass A B/s.edgeMass≤
      (((A.card:ℝ)/s.left.card)*((B.card:ℝ)/s.right.card))^(3/4:ℝ))
    (S : Finset (Label ⊕ Label)) :
    FiniteCore.cutConstant*min (s.corePiMass S) (s.corePiMass (s.coreVertices\S))≤s.coreCross S := by
  let A := s.coreLeftPart S
  let B := s.coreRightPart S
  have hA : A⊆s.left := Finset.filter_subset _ _
  have hB : B⊆s.right := Finset.filter_subset _ _
  have ha := uniform_card_bounds s.left A s.left_nonempty hA
  have hb := uniform_card_bounds s.right B s.right_nonempty hB
  have hi : s.coreRectangle A B≤(s.coreUniformMass S)^(3/2:ℝ) := by
    rw [s.coreRectangle_eq]
    exact (hrect A hA B hB).trans (LargePrime.product_rpow_le_mean ha.1 hb.1)
  have ho : s.coreRectangle (s.left\A) (s.right\B)≤(1-s.coreUniformMass S)^(3/2:ℝ) := by
    rw [s.coreRectangle_eq]
    have hl := hrect (s.left\A) (Finset.sdiff_subset) (s.right\B) (Finset.sdiff_subset)
    have hm := LargePrime.product_rpow_le_mean
      (uniform_card_bounds s.left (s.left\A) s.left_nonempty Finset.sdiff_subset).1
      (uniform_card_bounds s.right (s.right\B) s.right_nonempty Finset.sdiff_subset).1
    have hh := hl.trans hm
    rw [uniform_card_complement s.left A s.left_nonempty hA,uniform_card_complement s.right B s.right_nonempty hB] at hh
    have he : ((1-(A.card:ℝ)/s.left.card)+(1-(B.card:ℝ)/s.right.card))/2=1-s.coreUniformMass S := by
      dsimp [coreUniformMass,A,B];ring
    rwa [he] at hh
  obtain ⟨hcross,hpi,hpic,hpart⟩ := s.core_cut_bookkeeping hM S
  have hz : 0≤s.coreUniformMass S ∧ s.coreUniformMass S≤1 := by
    change 0≤((A.card:ℝ)/s.left.card+(B.card:ℝ)/s.right.card)/2 ∧
      ((A.card:ℝ)/s.left.card+(B.card:ℝ)/s.right.card)/2≤1
    constructor <;> linarith [ha.1,ha.2,hb.1,hb.2]
  have hh := FiniteCore.cut_to_cheeger hz.1 hz.2 hi ho hpart
  rw [hpi,hpic,hcross]
  exact hh

theorem stable_core_cut (s : TaggedState Label n)
    (hs : ∀ t,Step s t → t.quality≤s.quality) (hM : 0<s.edgeMass)
    (S : Finset (Label ⊕ Label)) :
    FiniteCore.cutConstant*min (s.corePiMass S) (s.corePiMass (s.coreVertices\S))≤s.coreCross S :=
  s.core_cut_of_rectangles hM (fun A hA B hB => s.stable_rectangle_concentration hs hM A B hA hB) S

theorem universal_core_cut (s : TaggedState Label n)
    (hs : ∀ t,Step s t → t.universalQuality≤s.universalQuality) (hM : 0<s.edgeMass)
    (S : Finset (Label ⊕ Label)) :
    FiniteCore.cutConstant*min (s.corePiMass S) (s.corePiMass (s.coreVertices\S))≤s.coreCross S :=
  s.core_cut_of_rectangles hM (fun A hA B hB => s.universal_rectangle_concentration hs hM A B hA hB) S

end LonelyRunnerNew.TaggedState
