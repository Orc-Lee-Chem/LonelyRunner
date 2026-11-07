import LonelyRunnerNew.PeriodicArcGeometry
import Mathlib.Tactic.Linarith

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped BigOperators
namespace LonelyRunnerNew.PeriodicArc
variable {ι : Type*} [DecidableEq ι]
attribute [local instance] Classical.propDecidable

def turns (m : ℕ) : Finset ℤ := Finset.Icc (-((m:ℤ)+1)) ((m:ℤ)+1)
def turnCount (J : Finset ℤ) (c r x : ℝ) : ℝ := (J.filter (fun j : ℤ => |x-c-(j:ℝ)|≤r)).card
def copySet (F : Finset ι) (m : ℕ) : Finset (ι × ℤ) := F.product (turns m)
def lineMultiplicity (F : Finset ι) (c r : ι → ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  IntervalCoverage.multiplicity (copySet F m)
    (fun ij => c ij.1+(ij.2:ℝ)-r ij.1) (fun ij => c ij.1+(ij.2:ℝ)+r ij.1) x

theorem mem_copy_interval {c r x : ℝ} {j : ℤ} :
    x∈Icc (c+(j:ℝ)-r) (c+(j:ℝ)+r) ↔ |x-c-(j:ℝ)|≤r := by
  rw [abs_le]
  constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]

theorem turnCount_le_arc (J : Finset ℤ) (c r x : ℝ) (hr : r<1/2) :
    turnCount J c r x≤(arc c r).indicator (fun _ => (1:ℝ)) x := by
  by_cases h : x∈arc c r
  · rw [Set.indicator_of_mem h]
    have hc : (J.filter (fun j : ℤ => |x-c-(j:ℝ)|≤r)).card≤1 := Finset.card_le_one.mpr (by
      intro j hj l hl
      exact turn_unique hr (Finset.mem_filter.mp hj).2 (Finset.mem_filter.mp hl).2)
    unfold turnCount
    exact_mod_cast hc
  · rw [Set.indicator_of_notMem h]
    have he : J.filter (fun j : ℤ => |x-c-(j:ℝ)|≤r)=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      exact h ⟨j,(Finset.mem_filter.mp hj).2⟩
    simp [turnCount,he]

theorem turnCount_eq_arc (J : Finset ℤ) (c r x : ℝ) (hr : r<1/2)
    (hJ : ∀ j : ℤ,|x-c-(j:ℝ)|≤r → j∈J) :
    turnCount J c r x=(arc c r).indicator (fun _ => (1:ℝ)) x := by
  apply le_antisymm (turnCount_le_arc J c r x hr)
  by_cases h : x∈arc c r
  · rw [Set.indicator_of_mem h]
    obtain ⟨j,hj⟩ := h
    have hne : (J.filter (fun j : ℤ => |x-c-(j:ℝ)|≤r)).Nonempty := ⟨j,Finset.mem_filter.mpr ⟨hJ j hj,hj⟩⟩
    unfold turnCount
    exact_mod_cast (Nat.succ_le_iff.mpr hne.card_pos)
  · rw [Set.indicator_of_notMem h]
    exact Nat.cast_nonneg _

theorem line_eq_turn_sum (F : Finset ι) (c r : ι → ℝ) (m : ℕ) (x : ℝ) :
    lineMultiplicity F c r m x=∑ i∈F,turnCount (turns m) (c i) (r i) x := by
  rw [lineMultiplicity,IntervalCoverage.multiplicity_eq_indicators]
  simp only [copySet,Finset.product_eq_sprod,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Set.indicator_apply,mem_copy_interval]
  rw [←Finset.sum_filter]
  simp [turnCount]

theorem lineMultiplicity_le (F : Finset ι) (c r : ι → ℝ) (m : ℕ)
    (hr : ∀ i∈F,r i<1/2) (x : ℝ) : lineMultiplicity F c r m x≤multiplicity F c r x := by
  rw [line_eq_turn_sum]
  exact Finset.sum_le_sum (fun i hi => turnCount_le_arc _ _ _ _ (hr i hi))

theorem turns_capture (m : ℕ) {c r x : ℝ} (hc0 : 0≤c) (hc1 : c<1) (hr : r<1/2)
    (hx : x∈Icc (-(m:ℝ)) ((m:ℝ)+1)) (j : ℤ) (hj : |x-c-(j:ℝ)|≤r) : j∈turns m := by
  have ha := abs_le.mp hj
  apply Finset.mem_Icc.mpr
  constructor
  · by_contra h
    have hh : j≤-(m:ℤ)-2 := by omega
    have hhR : (j:ℝ)≤-(m:ℝ)-2 := by exact_mod_cast hh
    linarith [hx.1]
  · by_contra h
    have hh : (m:ℤ)+2≤j := by omega
    have hhR : (m:ℝ)+2≤(j:ℝ) := by exact_mod_cast hh
    linarith [hx.2]

theorem lineMultiplicity_eq_inner (F : Finset ι) (c r : ι → ℝ) (m : ℕ)
    (hc : ∀ i∈F,0≤c i ∧ c i<1) (hr : ∀ i∈F,r i<1/2)
    {x : ℝ} (hx : x∈Icc (-(m:ℝ)) ((m:ℝ)+1)) :
    lineMultiplicity F c r m x=multiplicity F c r x := by
  rw [line_eq_turn_sum]
  exact Finset.sum_congr rfl (fun i hi => turnCount_eq_arc _ _ _ _ (hr i hi)
    (turns_capture m (hc i hi).1 (hc i hi).2 (hr i hi) hx))

theorem copy_interval_subset_outer (F : Finset ι) (c r : ι → ℝ) (m : ℕ)
    (hc : ∀ i∈F,0≤c i ∧ c i<1) (hr : ∀ i∈F,r i<1/2)
    {ij : ι × ℤ} (hij : ij∈copySet F m) :
    Icc (c ij.1+(ij.2:ℝ)-r ij.1) (c ij.1+(ij.2:ℝ)+r ij.1)⊆
      Icc (-(m:ℝ)-2) ((m:ℝ)+3) := by
  have hm := Finset.mem_product.mp hij
  have hj := Finset.mem_Icc.mp hm.2
  have hj0 : -(m:ℝ)-1≤(ij.2:ℝ) := by
    have hh : ((-((m:ℤ)+1):ℤ):ℝ)≤(ij.2:ℝ) := by exact_mod_cast hj.1
    norm_num only [Int.cast_neg,Int.cast_add,Int.cast_natCast,Int.cast_one] at hh
    linarith
  have hj1 : (ij.2:ℝ)≤(m:ℝ)+1 := by exact_mod_cast hj.2
  intro x hx
  exact ⟨by linarith [(hc ij.1 hm.1).1,hr ij.1 hm.1,hx.1],
    by linarith [(hc ij.1 hm.1).2,hr ij.1 hm.1,hx.2]⟩

theorem lineMultiplicity_zero_off_outer (F : Finset ι) (c r : ι → ℝ) (m : ℕ)
    (hc : ∀ i∈F,0≤c i ∧ c i<1) (hr : ∀ i∈F,r i<1/2)
    {x : ℝ} (hx : x∉Icc (-(m:ℝ)-2) ((m:ℝ)+3)) : lineMultiplicity F c r m x=0 := by
  have he : IntervalCoverage.active (copySet F m)
      (fun ij => c ij.1+(ij.2:ℝ)-r ij.1) (fun ij => c ij.1+(ij.2:ℝ)+r ij.1) x=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro ij hij
    have hm := Finset.mem_filter.mp hij
    exact hx (copy_interval_subset_outer F c r m hc hr hm.1 hm.2)
  simp only [lineMultiplicity,IntervalCoverage.multiplicity,he,Finset.card_empty,Nat.cast_zero]

end LonelyRunnerNew.PeriodicArc
