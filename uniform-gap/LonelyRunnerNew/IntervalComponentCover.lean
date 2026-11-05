import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Connected.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped BigOperators
namespace LonelyRunnerNew.IntervalCoverage
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [DecidableEq ι]

def intervalUnion (F : Finset ι) (L R : ι → ℝ) : Set ℝ := ⋃ i∈F,Icc (L i) (R i)
def components (F : Finset ι) (L R p : ι → ℝ) : Finset (Set ℝ) :=
  F.image (fun i => connectedComponentIn (intervalUnion F L R) (p i))
def componentGroup (F : Finset ι) (p : ι → ℝ) (C : Set ℝ) : Finset ι :=
  F.filter (fun i => p i∈C)

theorem interval_subset_union (F : Finset ι) (L R : ι → ℝ) {i : ι} (hi : i∈F) :
    Icc (L i) (R i)⊆intervalUnion F L R := by
  intro t ht
  exact Set.mem_iUnion₂.mpr ⟨i,hi,ht⟩

theorem interval_subset_component (F : Finset ι) (L R p : ι → ℝ)
    (hp : ∀ i∈F,p i∈Icc (L i) (R i)) {i : ι} (hi : i∈F) :
    Icc (L i) (R i)⊆connectedComponentIn (intervalUnion F L R) (p i) :=
  isPreconnected_Icc.subset_connectedComponentIn (hp i hi) (interval_subset_union F L R hi)

theorem components_cover (F : Finset ι) (L R p : ι → ℝ)
    (hp : ∀ i∈F,p i∈Icc (L i) (R i)) :
    intervalUnion F L R=⋃ C∈components F L R p,C := by
  ext t
  constructor
  · intro ht
    obtain ⟨i,hi,hit⟩ := Set.mem_iUnion₂.mp ht
    exact Set.mem_iUnion₂.mpr ⟨_,Finset.mem_image_of_mem _ hi,
      interval_subset_component F L R p hp hi hit⟩
  · intro ht
    obtain ⟨C,hC,htC⟩ := Set.mem_iUnion₂.mp ht
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hC
    exact connectedComponentIn_subset _ _ htC

theorem components_disjoint (F : Finset ι) (L R p : ι → ℝ) :
    Set.PairwiseDisjoint (components F L R p:Set (Set ℝ)) id := by
  intro C hC D hD hne
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hC
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hD
  apply Set.disjoint_left.mpr
  intro t hti htj
  exact hne ((connectedComponentIn_eq hti).trans (connectedComponentIn_eq htj).symm)

theorem component_shape (F : Finset ι) (L R p : ι → ℝ)
    (hp : ∀ i∈F,p i∈Icc (L i) (R i)) {C : Set ℝ} (hC : C∈components F L R p) :
    ∃ l r : ℝ,l≤r ∧ C=Icc l r := by
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hC
  let U := intervalUnion F L R
  have hU : IsCompact U := F.isCompact_biUnion (fun _ _ => isCompact_Icc)
  have hpi : p i∈U := interval_subset_union F L R hi (hp i hi)
  have hcomp : IsCompact (connectedComponentIn U (p i)) := by
    letI : CompactSpace U := isCompact_iff_compactSpace.mp hU
    rw [connectedComponentIn_eq_image hpi]
    exact (isClosed_connectedComponent (x:=(⟨p i,hpi⟩:U))).isCompact.image continuous_subtype_val
  have hconn : IsConnected (connectedComponentIn U (p i)) := isConnected_connectedComponentIn_iff.mpr hpi
  have he := eq_Icc_of_connected_compact hconn hcomp
  obtain ⟨t,ht⟩ := hconn.nonempty
  have htle := ht
  rw [he] at htle
  exact ⟨_,_,htle.1.trans htle.2,he⟩

theorem componentGroup_nonempty (F : Finset ι) (L R p : ι → ℝ)
    (hp : ∀ i∈F,p i∈Icc (L i) (R i)) {C : Set ℝ} (hC : C∈components F L R p) :
    (componentGroup F p C).Nonempty := by
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hC
  refine ⟨i,Finset.mem_filter.mpr ⟨hi,?_⟩⟩
  exact mem_connectedComponentIn (interval_subset_union F L R hi (hp i hi))

theorem componentGroup_cover (F : Finset ι) (L R p : ι → ℝ)
    (hp : ∀ i∈F,p i∈Icc (L i) (R i)) {C : Set ℝ} (hC : C∈components F L R p) :
    intervalUnion (componentGroup F p C) L R=C := by
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hC
  let U := intervalUnion F L R
  ext t
  constructor
  · intro ht
    obtain ⟨i,hi,hit⟩ := Set.mem_iUnion₂.mp ht
    have hm := Finset.mem_filter.mp hi
    have he := connectedComponentIn_eq hm.2
    rw [he]
    exact interval_subset_component F L R p hp hm.1 hit
  · intro ht
    have htU := connectedComponentIn_subset U (p a) ht
    obtain ⟨i,hi,hit⟩ := Set.mem_iUnion₂.mp htU
    have hiC := interval_subset_component F L R p hp hi hit
    have he : connectedComponentIn U (p i)=connectedComponentIn U (p a) :=
      (connectedComponentIn_eq hiC).trans (connectedComponentIn_eq ht).symm
    refine Set.mem_iUnion₂.mpr ⟨i,Finset.mem_filter.mpr ⟨hi,?_⟩,hit⟩
    rw [←he]
    exact mem_connectedComponentIn (interval_subset_union F L R hi (hp i hi))

theorem components_measure (F : Finset ι) (L R p : ι → ℝ)
    (hp : ∀ i∈F,p i∈Icc (L i) (R i)) :
    volume (intervalUnion F L R)=∑ C∈components F L R p,volume C := by
  rw [components_cover F L R p hp]
  apply measure_biUnion_finset (components_disjoint F L R p)
  intro C hC
  obtain ⟨l,r,hle,rfl⟩ := component_shape F L R p hp hC
  exact measurableSet_Icc

end LonelyRunnerNew.IntervalCoverage
