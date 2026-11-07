import LonelyRunnerNew.ForbiddenCommonCenter
import LonelyRunnerNew.IntervalMultiplicity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators
namespace LonelyRunnerNew.PeriodicArc
variable {ι : Type*} [DecidableEq ι]
attribute [local instance] Classical.propDecidable

def arc (c r : ℝ) : Set ℝ := {x | ∃ j : ℤ,|x-c-(j:ℝ)|≤r}
def multiplicity (F : Finset ι) (c r : ι → ℝ) (x : ℝ) : ℝ :=
  ∑ i∈F,(arc (c i) (r i)).indicator (fun _ => (1:ℝ)) x
def level (F : Finset ι) (c r : ι → ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  IntervalCoverage.tail (multiplicity F c r x) k

theorem arc_measurable (c r : ℝ) : MeasurableSet (arc c r) := by
  have he : arc c r=(fun x : ℝ => x-c) ⁻¹' forbidden 1 r := by ext x;simp [arc,forbidden]
  rw [he]
  exact (forbidden_measurable 1 (by norm_num) r).preimage (measurable_id.sub measurable_const)

theorem arc_add_int (c r x : ℝ) (m : ℤ) : x+(m:ℝ)∈arc c r ↔ x∈arc c r := by
  constructor
  · rintro ⟨j,hj⟩
    refine ⟨j-m,?_⟩
    have he : x-c-((j-m:ℤ):ℝ)=(x+(m:ℝ))-c-(j:ℝ) := by push_cast;ring
    rwa [he]
  · rintro ⟨j,hj⟩
    refine ⟨j+m,?_⟩
    have he : (x+(m:ℝ))-c-((j+m:ℤ):ℝ)=x-c-(j:ℝ) := by push_cast;ring
    rwa [he]

theorem turn_unique {c r x : ℝ} (hr : r<1/2) {j l : ℤ}
    (hj : |x-c-(j:ℝ)|≤r) (hl : |x-c-(l:ℝ)|≤r) : j=l := by
  have hja := abs_le.mp hj
  have hla := abs_le.mp hl
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have hstep : (j:ℝ)+1≤(l:ℝ) := by exact_mod_cast (Int.add_one_le_iff.mpr h)
    linarith
  · have hstep : (l:ℝ)+1≤(j:ℝ) := by exact_mod_cast (Int.add_one_le_iff.mpr h)
    linarith

theorem multiplicity_nonneg (F : Finset ι) (c r : ι → ℝ) (x : ℝ) :
    0≤multiplicity F c r x := Finset.sum_nonneg (fun _ _ => by simp only [Set.indicator_apply];split_ifs <;> norm_num)

theorem multiplicity_le_card (F : Finset ι) (c r : ι → ℝ) (x : ℝ) :
    multiplicity F c r x≤F.card := by
  calc
    _ ≤ ∑ _i∈F,(1:ℝ) := Finset.sum_le_sum (fun _ _ => by simp only [Set.indicator_apply];split_ifs <;> norm_num)
    _ = _ := by simp

theorem multiplicity_measurable (F : Finset ι) (c r : ι → ℝ) : Measurable (multiplicity F c r) := by
  apply Finset.measurable_sum
  intro i hi
  exact measurable_const.indicator (arc_measurable _ _)

theorem multiplicity_periodic (F : Finset ι) (c r : ι → ℝ) : Function.Periodic (multiplicity F c r) 1 := by
  intro x
  unfold multiplicity
  apply Finset.sum_congr rfl
  intro i hi
  have he := arc_add_int (c i) (r i) x 1
  norm_num only [Int.cast_one] at he
  simp only [Set.indicator_apply,he]

theorem level_nonneg (F : Finset ι) (c r : ι → ℝ) (k : ℕ) (x : ℝ) :
    0≤level F c r k x := IntervalCoverage.tail_nonneg _ _

theorem level_le_card (F : Finset ι) (c r : ι → ℝ) (k : ℕ) (x : ℝ) :
    level F c r k x≤F.card := (IntervalCoverage.tail_le (multiplicity_nonneg F c r x) k).trans
      (multiplicity_le_card F c r x)

theorem level_measurable (F : Finset ι) (c r : ι → ℝ) (k : ℕ) : Measurable (level F c r k) :=
  measurable_const.max ((multiplicity_measurable F c r).sub measurable_const)

theorem level_periodic (F : Finset ι) (c r : ι → ℝ) (k : ℕ) : Function.Periodic (level F c r k) 1 := by
  intro x
  unfold level
  rw [multiplicity_periodic F c r x]

theorem level_intervalIntegrable (F : Finset ι) (c r : ι → ℝ) (k : ℕ) (a b : ℝ) :
    IntervalIntegrable (level F c r k) volume a b := by
  have main (a b : ℝ) (hab : a≤b) : IntervalIntegrable (level F c r k) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    apply (integrableOn_const (C:=(F.card:ℝ)) isCompact_Icc.measure_ne_top).mono'
      (level_measurable F c r k).aestronglyMeasurable
    filter_upwards with x
    rw [Real.norm_eq_abs,abs_of_nonneg (level_nonneg F c r k x)]
    exact level_le_card F c r k x
  by_cases hab : a≤b
  · exact main a b hab
  · exact (main b a (le_of_not_ge hab)).symm

theorem integral_int_endpoints {f : ℝ → ℝ} (hf : Function.Periodic f 1)
    (hi : ∀ a b,IntervalIntegrable f volume a b) (a b : ℤ) :
    (∫ x in (a:ℝ)..(b:ℝ),f x)=((b-a:ℤ):ℝ)*(∫ x in (0:ℝ)..1,f x) := by
  have he : (b:ℝ)=(a:ℝ)+(b-a:ℤ) • (1:ℝ) := by simp only [zsmul_eq_mul];push_cast;ring
  rw [he,hf.intervalIntegral_add_zsmul_eq (b-a) (a:ℝ) hi,hf.intervalIntegral_add_eq (a:ℝ) 0]
  simp only [zero_add,zsmul_eq_mul]

end LonelyRunnerNew.PeriodicArc
