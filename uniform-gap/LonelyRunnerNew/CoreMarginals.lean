import LonelyRunnerNew.CoreProbability

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew.FiniteCore
variable {V E : Type*} [DecidableEq V] [DecidableEq E]

theorem pushKernel_row_sum (F : Finset V) (I : Finset E) (src dst : E → V) (w : E → ℝ)
    (ht : ∀ e∈I,dst e∈F) (v : V) :
    (∑ u∈F,pushKernel I src dst w v u)=∑ e∈I,if src e=v then w e else 0 := by
  unfold pushKernel
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  simp [ite_and,ht e he,eq_comm]

end LonelyRunnerNew.FiniteCore

namespace LonelyRunnerNew.TaggedState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

theorem corePi_eq_incident (s : TaggedState Label n) (v : Label ⊕ Label) :
    s.corePi v=∑ e∈s.edges,
      ((if coreSource e=v then s.edgeProbability e/2 else 0)+
      (if coreTarget e=v then s.edgeProbability e/2 else 0)) := by
  unfold corePi coreOmega
  rw [Finset.sum_add_distrib,
    FiniteCore.pushKernel_row_sum _ _ _ _ _ (fun _ he => s.coreTarget_mem he),
    FiniteCore.pushKernel_row_sum _ _ _ _ _ (fun _ he => s.coreSource_mem he),← Finset.sum_add_distrib]

theorem corePi_inl (s : TaggedState Label n) (x : Label) :
    s.corePi (Sum.inl x)=(∑ e∈s.edges.filter (fun e => e.1=x),s.edgeProbability e)/2 := by
  rw [s.corePi_eq_incident,Finset.sum_div,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hx : e.1=x <;> simp [coreSource,coreTarget,hx]

theorem corePi_inr (s : TaggedState Label n) (y : Label) :
    s.corePi (Sum.inr y)=(∑ e∈s.edges.filter (fun e => e.2=y),s.edgeProbability e)/2 := by
  rw [s.corePi_eq_incident,Finset.sum_div,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hy : e.2=y <;> simp [coreSource,coreTarget,hy]

theorem corePi_zero_of_isolated (s : TaggedState Label n) (v : Label ⊕ Label)
    (hno : ∀ e∈s.edges,coreSource e≠v ∧ coreTarget e≠v) : s.corePi v=0 := by
  rw [s.corePi_eq_incident]
  exact Finset.sum_eq_zero (fun e he => by simp [(hno e he).1,(hno e he).2])

theorem corePi_zero_off_vertices (s : TaggedState Label n) {v : Label ⊕ Label}
    (hv : v∉s.coreVertices) : s.corePi v=0 := by
  apply s.corePi_zero_of_isolated
  intro e he
  exact ⟨fun h => hv (h ▸ s.coreSource_mem he),fun h => hv (h ▸ s.coreTarget_mem he)⟩

end LonelyRunnerNew.TaggedState
