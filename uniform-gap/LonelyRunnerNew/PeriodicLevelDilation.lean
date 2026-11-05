import LonelyRunnerNew.PeriodicArcIntegralBounds

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators
namespace LonelyRunnerNew.PeriodicArc
variable {ι : Type*} [DecidableEq ι]
attribute [local instance] Classical.propDecidable

/-- Every truncated periodic coverage integral has the normalized dilation
property. Finite-copy endpoint losses are removed by arbitrary integer windows. -/
theorem level_dilation (F : Finset ι) (c r : ι → ℝ) (k : ℕ) {s t : ℝ}
    (hs : 0<s) (hst : s≤t) (hc : ∀ i∈F,0≤c i ∧ c i<1)
    (hr : ∀ i∈F,0≤r i) (htsmall : ∀ i∈F,t*r i<1/2) :
    (∫ x in (0:ℝ)..1,level F c (fun i => s*r i) k x)/s ≤
      (∫ x in (0:ℝ)..1,level F c (fun i => t*r i) k x)/t := by
  have ht : 0<t := hs.trans_le hst
  have hssmall : ∀ i∈F,s*r i<1/2 := fun i hi =>
    (mul_le_mul_of_nonneg_right hst (hr i hi)).trans_lt (htsmall i hi)
  apply slope_le_of_windows
  intro m
  have hlo := (line_level_integral_bounds F c (fun i => s*r i) k m hc hssmall).1
  have hup := (line_level_integral_bounds F c (fun i => t*r i) k m hc htsmall).2
  have hd := IntervalCoverage.tail_dilation (copySet F m)
    (fun ij => c ij.1+(ij.2:ℝ)) (fun ij => r ij.1) k hs hst
    (fun ij hij => hr ij.1 (Finset.mem_product.mp hij).1)
  have hchain := (div_le_div_of_nonneg_right hlo hs.le).trans
    (hd.trans (div_le_div_of_nonneg_right hup ht.le))
  simpa only [mul_div_assoc] using hchain

end LonelyRunnerNew.PeriodicArc
