import LonelyRunnerNew.CoreCut
import LonelyRunnerNew.Certificates

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew.TaggedState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

def jointLeft (s : TaggedState Label n) (B : (Label ⊕ Label) → ℝ) : Finset Label :=
  s.left.filter (fun x => B (Sum.inl x)≤1375)
def jointRight (s : TaggedState Label n) (B : (Label ⊕ Label) → ℝ) : Finset Label :=
  s.right.filter (fun y => B (Sum.inr y)≤1375)
def jointEdges (s : TaggedState Label n) (B : (Label ⊕ Label) → ℝ) : Finset (Label × Label) :=
  s.edges.filter (fun e => B (coreSource e)≤1375 ∧ B (coreTarget e)≤1375)

theorem jointEdges_eq_inter (s : TaggedState Label n) (B : (Label ⊕ Label) → ℝ) :
    s.jointEdges B=s.edges∩(s.jointLeft B).product (s.jointRight B) := by
  apply Finset.ext
  intro e
  constructor
  · intro he
    have hh := Finset.mem_filter.mp he
    have hm := Finset.mem_product.mp (s.edges_subset hh.1)
    exact Finset.mem_inter.mpr ⟨hh.1,Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨hm.1,hh.2.1⟩,Finset.mem_filter.mpr ⟨hm.2,hh.2.2⟩⟩⟩
  · intro he
    have hh := Finset.mem_inter.mp he
    have hm := Finset.mem_product.mp hh.2
    exact Finset.mem_filter.mpr ⟨hh.1,(Finset.mem_filter.mp hm.1).2,(Finset.mem_filter.mp hm.2).2⟩

theorem marginal_markov (s : TaggedState Label n) (hM : 0<s.edgeMass)
    (B : (Label ⊕ Label) → ℝ) (hB : ∀ v∈s.coreVertices,0≤B v) :
    1375*s.corePiMass (s.coreVertices.filter (fun v => 1375<B v))≤
      ∑ v∈s.coreVertices,s.corePi v*B v := by
  unfold corePiMass
  rw [Finset.mul_sum]
  simp only [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro v hv
  have hp := s.corePi_nonneg hM v
  by_cases hb : 1375<B v
  · simp only [Finset.mem_filter,hv,hb,and_self,ite_true]
    nlinarith
  · simp only [Finset.mem_filter,hv,hb,and_false,ite_false,mul_zero]
    exact mul_nonneg hp (hB v hv)

/-- The factor 2 is exact incidence accounting from the edge-induced marginal. -/
theorem deleted_edges_le_twice_marginal (s : TaggedState Label n) (hM : 0<s.edgeMass)
    (B : (Label ⊕ Label) → ℝ) :
    (∑ e∈s.edges.filter (fun e => ¬(B (coreSource e)≤1375 ∧ B (coreTarget e)≤1375)),s.edgeProbability e)≤
      2*s.corePiMass (s.coreVertices.filter (fun v => 1375<B v)) := by
  have hp := s.corePiMass_average (s.coreVertices.filter (fun v => 1375<B v))
  have he : (∑ e∈s.edges,s.edgeProbability e*
      ((if 1375<B (coreSource e) then (1:ℝ) else 0)+(if 1375<B (coreTarget e) then (1:ℝ) else 0)))=
      2*s.corePiMass (s.coreVertices.filter (fun v => 1375<B v)) := by
    rw [hp,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    simp only [Finset.mem_filter,s.coreSource_mem he,s.coreTarget_mem he,true_and]
    ring
  rw [← he,Finset.sum_filter]
  apply Finset.sum_le_sum
  intro e he
  have hprob := s.edgeProbability_nonneg hM e
  by_cases hl : B (coreSource e)≤1375 <;> by_cases hr : B (coreTarget e)≤1375 <;>
    simp [hl,hr,← not_le] <;> linarith

theorem tbar_exact_positive : (Certificate.tbar:ℝ)=(103363/137500:ℝ) ∧ (0:ℝ)<Certificate.tbar := by
  norm_num [Certificate.tbar,Certificate.Dbar]

/-- Intermediate Markov assembly. The actual score theorems supply hcost. -/
theorem jointCore_of_cost (s : TaggedState Label n) (hM : 0<s.edgeMass)
    (B : (Label ⊕ Label) → ℝ) (hB : ∀ v∈s.coreVertices,0≤B v)
    (hcost : (∑ v∈s.coreVertices,s.corePi v*B v)<(Certificate.Dbar:ℝ)) :
    (Certificate.tbar:ℝ)≤∑ e∈s.jointEdges B,s.edgeProbability e := by
  have hm := s.marginal_markov hM B hB
  have hloss := s.deleted_edges_le_twice_marginal hM B
  have hprob := s.edgeProbability_sum hM
  have hpart : (∑ e∈s.jointEdges B,s.edgeProbability e)+
      (∑ e∈s.edges.filter (fun e => ¬(B (coreSource e)≤1375 ∧ B (coreTarget e)≤1375)),s.edgeProbability e)=1 := by
    unfold jointEdges
    rw [← hprob]
    simp only [Finset.sum_filter,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e he
    by_cases h : B (coreSource e)≤1375 ∧ B (coreTarget e)≤1375 <;> simp [h]
  have ht : (Certificate.tbar:ℝ)=1-2*(Certificate.Dbar:ℝ)/1375 := by norm_num [Certificate.tbar,Certificate.Dbar]
  rw [ht]
  linarith

theorem joint_sides_nonempty (s : TaggedState Label n) (B : (Label ⊕ Label) → ℝ)
    (hmass : (Certificate.tbar:ℝ)≤∑ e∈s.jointEdges B,s.edgeProbability e) :
    (s.jointLeft B).Nonempty ∧ (s.jointRight B).Nonempty := by
  have hE : (s.jointEdges B).Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    rw [he,Finset.sum_empty] at hmass
    linarith [tbar_exact_positive.2]
  obtain ⟨e,he⟩ := hE
  rw [s.jointEdges_eq_inter] at he
  have hm := Finset.mem_product.mp (Finset.mem_inter.mp he).2
  exact ⟨⟨e.1,hm.1⟩,⟨e.2,hm.2⟩⟩

theorem joint_restriction_probability (s : TaggedState Label n) (B : (Label ⊕ Label) → ℝ)
    (hL : (s.jointLeft B).Nonempty) (hR : (s.jointRight B).Nonempty) :
    (∑ e∈s.jointEdges B,s.edgeProbability e)=
      (s.restrict (s.jointLeft B) (s.jointRight B) (Finset.filter_subset _ _) (Finset.filter_subset _ _) hL hR).edgeMass/s.edgeMass := by
  rw [s.jointEdges_eq_inter]
  unfold edgeProbability
  rw [← Finset.sum_div]
  rfl

end LonelyRunnerNew.TaggedState
