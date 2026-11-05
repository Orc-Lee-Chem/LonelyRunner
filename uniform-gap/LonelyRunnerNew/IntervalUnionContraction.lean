import LonelyRunnerNew.IntervalComponentCover
import Mathlib.Tactic.Linarith

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped BigOperators
namespace LonelyRunnerNew.IntervalCoverage
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [DecidableEq ι]

theorem finite_union_envelope (G : Finset ι) (hG : G.Nonempty) (L R : ι → ℝ) :
    ∃ a∈G,∃ b∈G,volume (intervalUnion G L R)≤ENNReal.ofReal (R b-L a) := by
  obtain ⟨a,ha,hmin⟩ := Finset.exists_min_image G L hG
  obtain ⟨b,hb,hmax⟩ := Finset.exists_max_image G R hG
  refine ⟨a,ha,b,hb,?_⟩
  calc
    _ ≤ volume (Icc (L a) (R b)) := measure_mono (by
      intro t ht
      obtain ⟨i,hi,hit⟩ := Set.mem_iUnion₂.mp ht
      exact ⟨(hmin i hi).trans hit.1,hit.2.trans (hmax i hi)⟩)
    _ = _ := Real.volume_Icc

theorem endpoint_span_contraction (c r : ι → ℝ) {u v a b : ℝ} (hu : 0≤u) (huv : u≤v)
    {i j : ι} (hiL : a≤v*c i-r i) (hiR : v*c i+r i≤b)
    (hjL : a≤v*c j-r j) (hjR : v*c j+r j≤b) :
    (u*c i+r i)-(u*c j-r j)≤b-a := by
  by_cases hc : c j≤c i
  · have hm := mul_nonneg (sub_nonneg.mpr huv) (sub_nonneg.mpr hc)
    nlinarith only [hiR,hjL,hm]
  · have hc' : c i≤c j := le_of_not_ge hc
    have hm1 := mul_nonneg hu (sub_nonneg.mpr hc')
    have hm2 := mul_nonneg (hu.trans huv) (sub_nonneg.mpr hc')
    nlinarith only [hjR,hiL,hm1,hm2]

theorem block_union_contraction (F : Finset ι) (c r : ι → ℝ) {u v : ℝ}
    (hu : 0≤u) (huv : u≤v) (hr : ∀ i∈F,0≤r i) {C : Set ℝ}
    (hC : C∈components F (fun i => v*c i-r i) (fun i => v*c i+r i) (fun i => v*c i)) :
    volume (intervalUnion (componentGroup F (fun i => v*c i) C)
      (fun i => u*c i-r i) (fun i => u*c i+r i))≤volume C := by
  let L := fun i => v*c i-r i
  let R := fun i => v*c i+r i
  let p := fun i => v*c i
  let G := componentGroup F p C
  have hp : ∀ i∈F,p i∈Icc (L i) (R i) := by
    intro i hi
    dsimp [p,L,R]
    exact ⟨by linarith [hr i hi],by linarith [hr i hi]⟩
  have hG := componentGroup_nonempty F L R p hp hC
  obtain ⟨l,b,hlb,hshape⟩ := component_shape F L R p hp hC
  have hcover : intervalUnion G L R=C := componentGroup_cover F L R p hp hC
  have hbound (i : ι) (hi : i∈G) : l≤L i ∧ R i≤b := by
    have hm := Finset.mem_filter.mp hi
    have hlr : L i≤R i := by dsimp [L,R];linarith [hr i hm.1]
    have hleft : L i∈intervalUnion G L R := interval_subset_union G L R hi ⟨le_rfl,hlr⟩
    have hright : R i∈intervalUnion G L R := interval_subset_union G L R hi ⟨hlr,le_rfl⟩
    rw [hcover,hshape] at hleft hright
    exact ⟨hleft.1,hright.2⟩
  obtain ⟨a,ha,z,hz,henv⟩ := finite_union_envelope G hG (fun i => u*c i-r i) (fun i => u*c i+r i)
  have hspan := endpoint_span_contraction c r hu huv (hbound z hz).1 (hbound z hz).2
    (hbound a ha).1 (hbound a ha).2
  exact henv.trans ((ENNReal.ofReal_le_ofReal hspan).trans_eq (by rw [hshape,Real.volume_Icc]))

/-- Finite interval unions contract in measure when all centers are multiplied
by 0≤u≤v and the individual radii stay fixed. Old components supply disjoint
interval envelopes; no endpoint-crossing differentiation is used. -/
theorem union_center_contraction (F : Finset ι) (c r : ι → ℝ) {u v : ℝ}
    (hu : 0≤u) (huv : u≤v) (hr : ∀ i∈F,0≤r i) :
    volume (intervalUnion F (fun i => u*c i-r i) (fun i => u*c i+r i))≤
      volume (intervalUnion F (fun i => v*c i-r i) (fun i => v*c i+r i)) := by
  classical
  let L := fun i => v*c i-r i
  let R := fun i => v*c i+r i
  let p := fun i => v*c i
  let C := components F L R p
  have hp : ∀ i∈F,p i∈Icc (L i) (R i) := by
    intro i hi
    dsimp [p,L,R]
    exact ⟨by linarith [hr i hi],by linarith [hr i hi]⟩
  have hsub : intervalUnion F (fun i => u*c i-r i) (fun i => u*c i+r i)⊆
      ⋃ D∈C,intervalUnion (componentGroup F p D) (fun i => u*c i-r i) (fun i => u*c i+r i) := by
    intro t ht
    obtain ⟨i,hi,hit⟩ := Set.mem_iUnion₂.mp ht
    let D := connectedComponentIn (intervalUnion F L R) (p i)
    have hD : D∈C := Finset.mem_image_of_mem _ hi
    have hpi : p i∈D := mem_connectedComponentIn (interval_subset_union F L R hi (hp i hi))
    exact Set.mem_iUnion₂.mpr ⟨D,hD,Set.mem_iUnion₂.mpr ⟨i,Finset.mem_filter.mpr ⟨hi,hpi⟩,hit⟩⟩
  calc
    _ ≤ volume (⋃ D∈C,intervalUnion (componentGroup F p D) (fun i => u*c i-r i) (fun i => u*c i+r i)) :=
      measure_mono hsub
    _ ≤ ∑ D∈C,volume (intervalUnion (componentGroup F p D) (fun i => u*c i-r i) (fun i => u*c i+r i)) :=
      measure_biUnion_finset_le C _
    _ ≤ ∑ D∈C,volume D := Finset.sum_le_sum (fun D hD => block_union_contraction F c r hu huv hr hD)
    _ = _ := (components_measure F L R p hp).symm

end LonelyRunnerNew.IntervalCoverage
