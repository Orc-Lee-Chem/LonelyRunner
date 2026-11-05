import LonelyRunnerNew.SmallPrimeEdgeMean
import Mathlib.Data.Finset.Sum

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew.FiniteCore
variable {V E : Type*} [DecidableEq V] [DecidableEq E]

def pushKernel (I : Finset E) (src dst : E → V) (w : E → ℝ) (v u : V) : ℝ :=
  ∑ e∈I,if src e=v ∧ dst e=u then w e else 0

theorem pushKernel_average (F : Finset V) (I : Finset E) (src dst : E → V) (w : E → ℝ)
    (hs : ∀ e∈I,src e∈F) (ht : ∀ e∈I,dst e∈F) (H : V → V → ℝ) :
    (∑ v∈F,∑ u∈F,pushKernel I src dst w v u*H v u)=∑ e∈I,w e*H (src e) (dst e) := by
  unfold pushKernel
  simp_rw [Finset.sum_mul]
  calc
    _ = ∑ v∈F,∑ e∈I,∑ u∈F,(if src e=v ∧ dst e=u then w e else 0)*H v u :=
      Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = ∑ e∈I,∑ v∈F,∑ u∈F,(if src e=v ∧ dst e=u then w e else 0)*H v u := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e he
      simp [ite_and,ite_mul,hs e he,ht e he,eq_comm]

end LonelyRunnerNew.FiniteCore

namespace LonelyRunnerNew.TaggedState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

def coreVertices (s : TaggedState Label n) : Finset (Label ⊕ Label) := s.left.disjSum s.right
def coreSource (e : Label × Label) : Label ⊕ Label := Sum.inl e.1
def coreTarget (e : Label × Label) : Label ⊕ Label := Sum.inr e.2

/-- Half of each actual edge probability in each orientation. -/
def coreOmega (s : TaggedState Label n) (v u : Label ⊕ Label) : ℝ :=
  FiniteCore.pushKernel s.edges coreSource coreTarget (fun e => s.edgeProbability e/2) v u+
  FiniteCore.pushKernel s.edges coreTarget coreSource (fun e => s.edgeProbability e/2) v u

/-- Edge-induced marginal, not the uniform alpha/beta probabilities of L04. -/
def corePi (s : TaggedState Label n) (v : Label ⊕ Label) : ℝ :=
  ∑ u∈s.coreVertices,s.coreOmega v u

theorem coreSource_mem (s : TaggedState Label n) {e : Label × Label} (he : e∈s.edges) :
    coreSource e∈s.coreVertices := by
  exact Finset.inl_mem_disjSum.mpr (Finset.mem_product.mp (s.edges_subset he)).1
theorem coreTarget_mem (s : TaggedState Label n) {e : Label × Label} (he : e∈s.edges) :
    coreTarget e∈s.coreVertices := by
  exact Finset.inr_mem_disjSum.mpr (Finset.mem_product.mp (s.edges_subset he)).2

theorem coreOmega_nonneg (s : TaggedState Label n) (hM : 0<s.edgeMass) (v u : Label ⊕ Label) :
    0≤s.coreOmega v u := by
  apply add_nonneg <;> apply Finset.sum_nonneg <;> intro e he <;>
    split_ifs <;> first | exact div_nonneg (s.edgeProbability_nonneg hM e) (by norm_num) | rfl

theorem coreOmega_symm (s : TaggedState Label n) (v u : Label ⊕ Label) :
    s.coreOmega v u=s.coreOmega u v := by
  unfold coreOmega FiniteCore.pushKernel
  rw [add_comm]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro e he <;> simp only [and_comm]

theorem coreOmega_average (s : TaggedState Label n) (H : (Label ⊕ Label) → (Label ⊕ Label) → ℝ) :
    (∑ v∈s.coreVertices,∑ u∈s.coreVertices,s.coreOmega v u*H v u)=
      ∑ e∈s.edges,(s.edgeProbability e/2)*(H (coreSource e) (coreTarget e)+H (coreTarget e) (coreSource e)) := by
  unfold coreOmega
  simp_rw [add_mul,Finset.sum_add_distrib]
  rw [FiniteCore.pushKernel_average _ _ _ _ _ (fun _ he => s.coreSource_mem he) (fun _ he => s.coreTarget_mem he),
    FiniteCore.pushKernel_average _ _ _ _ _ (fun _ he => s.coreTarget_mem he) (fun _ he => s.coreSource_mem he)]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  ring

theorem corePi_average (s : TaggedState Label n) (f : (Label ⊕ Label) → ℝ) :
    (∑ v∈s.coreVertices,s.corePi v*f v)=
      ∑ e∈s.edges,(s.edgeProbability e/2)*(f (coreSource e)+f (coreTarget e)) := by
  have h := s.coreOmega_average (fun v _ => f v)
  simpa only [corePi,Finset.sum_mul] using h

theorem corePi_nonneg (s : TaggedState Label n) (hM : 0<s.edgeMass) (v : Label ⊕ Label) :
    0≤s.corePi v := Finset.sum_nonneg (fun u _ => s.coreOmega_nonneg hM v u)

theorem corePi_sum (s : TaggedState Label n) (hM : 0<s.edgeMass) :
    (∑ v∈s.coreVertices,s.corePi v)=1 := by
  have h := s.corePi_average (fun _ => 1)
  norm_num only [mul_one,show (1:ℝ)+1=2 by norm_num,div_mul_cancel₀ _ (by norm_num : (2:ℝ)≠0)] at h
  exact h.trans (s.edgeProbability_sum hM)

theorem coreOmega_sum (s : TaggedState Label n) (hM : 0<s.edgeMass) :
    (∑ v∈s.coreVertices,∑ u∈s.coreVertices,s.coreOmega v u)=1 := s.corePi_sum hM

theorem coreOmega_abs_difference (s : TaggedState Label n) (f : (Label ⊕ Label) → ℝ) :
    (∑ v∈s.coreVertices,∑ u∈s.coreVertices,s.coreOmega v u*|f v-f u|)=
      ∑ e∈s.edges,s.edgeProbability e*|f (coreSource e)-f (coreTarget e)| := by
  rw [s.coreOmega_average]
  apply Finset.sum_congr rfl
  intro e he
  rw [abs_sub_comm (f (coreTarget e)) (f (coreSource e))]
  ring

end LonelyRunnerNew.TaggedState
