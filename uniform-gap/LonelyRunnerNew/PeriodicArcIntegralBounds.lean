import LonelyRunnerNew.PeriodicArcCopies
import LonelyRunnerNew.IntervalLevelDilation

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators
namespace LonelyRunnerNew.PeriodicArc
variable {ι : Type*} [DecidableEq ι]
attribute [local instance] Classical.propDecidable

theorem level_indicator_integrable (F : Finset ι) (c r : ι → ℝ) (k : ℕ)
    {a b : ℝ} (hab : a≤b) :
    Integrable ((Icc a b).indicator (level F c r k)) volume :=
  ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp (level_intervalIntegrable F c r k a b)).integrable_indicator
    measurableSet_Icc

theorem level_indicator_integral (F : Finset ι) (c r : ι → ℝ) (k : ℕ)
    {a b : ℝ} (hab : a≤b) :
    (∫ x,(Icc a b).indicator (level F c r k) x)=∫ x in a..b,level F c r k x := by
  rw [integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le hab]

/-- Integer-window comparison uses a width-four endpoint allowance. This
allowance disappears in the subsequent unbounded-window argument and does
not change any final constant. -/
theorem line_level_integral_bounds (F : Finset ι) (c r : ι → ℝ) (k m : ℕ)
    (hc : ∀ i∈F,0≤c i ∧ c i<1) (hr : ∀ i∈F,r i<1/2) :
    ((2:ℝ)*(m:ℝ)+1)*(∫x in (0:ℝ)..1,level F c r k x)≤
      (∫x,IntervalCoverage.tail (lineMultiplicity F c r m x) k) ∧
    (∫x,IntervalCoverage.tail (lineMultiplicity F c r m x) k)≤
      ((2:ℝ)*(m:ℝ)+5)*(∫x in (0:ℝ)..1,level F c r k x) := by
  let A := Icc (-(m:ℝ)) ((m:ℝ)+1)
  let B := Icc (-(m:ℝ)-2) ((m:ℝ)+3)
  let f := fun x => IntervalCoverage.tail (lineMultiplicity F c r m x) k
  let g := level F c r k
  have ha : -(m:ℝ)≤(m:ℝ)+1 := by nlinarith [Nat.cast_nonneg (α:=ℝ) m]
  have hb : -(m:ℝ)-2≤(m:ℝ)+3 := by nlinarith [Nat.cast_nonneg (α:=ℝ) m]
  have hfi : Integrable f volume := IntervalCoverage.tail_integrable _ _ _ _
  have hlower : ∀ x,A.indicator g x≤f x := by
    intro x
    by_cases hx : x∈A
    · rw [Set.indicator_of_mem hx]
      exact le_of_eq (congrArg (fun z => IntervalCoverage.tail z k) (lineMultiplicity_eq_inner F c r m hc hr hx).symm)
    · rw [Set.indicator_of_notMem hx]
      exact IntervalCoverage.tail_nonneg _ _
  have hupper : ∀ x,f x≤B.indicator g x := by
    intro x
    by_cases hx : x∈B
    · rw [Set.indicator_of_mem hx]
      exact max_le_max le_rfl (sub_le_sub_right (lineMultiplicity_le F c r m hr x) _)
    · rw [Set.indicator_of_notMem hx]
      have hz := lineMultiplicity_zero_off_outer F c r m hc hr hx
      change IntervalCoverage.tail (lineMultiplicity F c r m x) k≤0
      rw [hz]
      simp [IntervalCoverage.tail,max_eq_left (neg_nonpos.mpr (Nat.cast_nonneg k : (0:ℝ)≤k))]
  have hlow := integral_mono (level_indicator_integrable F c r k ha) hfi hlower
  have hupp := integral_mono hfi (level_indicator_integrable F c r k hb) hupper
  have hI : (∫x,A.indicator g x)=((2:ℝ)*(m:ℝ)+1)*(∫x in (0:ℝ)..1,level F c r k x) := by
    rw [level_indicator_integral F c r k ha]
    have hh := integral_int_endpoints (level_periodic F c r k) (level_intervalIntegrable F c r k)
      (-(m:ℤ)) ((m:ℤ)+1)
    convert hh using 1 <;> push_cast <;> ring
  have hO : (∫x,B.indicator g x)=((2:ℝ)*(m:ℝ)+5)*(∫x in (0:ℝ)..1,level F c r k x) := by
    rw [level_indicator_integral F c r k hb]
    have hh := integral_int_endpoints (level_periodic F c r k) (level_intervalIntegrable F c r k)
      (-(m:ℤ)-2) ((m:ℤ)+3)
    convert hh using 1 <;> push_cast <;> ring
  rw [hI] at hlow
  rw [hO] at hupp
  exact ⟨hlow,hupp⟩

theorem slope_le_of_windows {A B : ℝ}
    (h : ∀ m : ℕ,((2:ℝ)*(m:ℝ)+1)*A≤((2:ℝ)*(m:ℝ)+5)*B) : A≤B := by
  by_contra hbad
  have hd : 0<2*(A-B) := by linarith
  obtain ⟨m,hm⟩ := exists_nat_gt ((5*B-A)/(2*(A-B)))
  have hh := (div_lt_iff₀ hd).mp hm
  nlinarith only [hh,h m]

end LonelyRunnerNew.PeriodicArc
