import LonelyRunnerNew.CoprimeGridCount
import LonelyRunnerNew.PairMeasureReduction
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators
namespace LonelyRunnerNew
attribute [local instance] Classical.propDecidable

def pairIndicator (a b : ℕ) (r : ℝ) : ℝ → ℝ :=
  (forbidden a r∩forbidden b r).indicator (fun _ => 1)

theorem bounded_intervalIntegrable (f : ℝ → ℝ) (hf : Measurable f)
    (hbound : ∀ x,|f x|≤1) (a b : ℝ) : IntervalIntegrable f volume a b := by
  have main (a b : ℝ) (hab : a≤b) : IntervalIntegrable f volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    apply (integrableOn_const (C:=(1:ℝ)) isCompact_Icc.measure_ne_top).mono' hf.aestronglyMeasurable
    filter_upwards with x
    simpa only [Real.norm_eq_abs] using hbound x
  by_cases hab : a≤b
  · exact main a b hab
  · exact (main b a (le_of_not_ge hab)).symm

theorem pairIndicator_measurable (a b : ℕ) (ha : 0<a) (hb : 0<b) (r : ℝ) :
    Measurable (pairIndicator a b r) :=
  measurable_const.indicator ((forbidden_measurable a ha r).inter (forbidden_measurable b hb r))

theorem pairIndicator_abs_le (a b : ℕ) (r x : ℝ) : |pairIndicator a b r x|≤1 := by
  simp only [pairIndicator,Set.indicator_apply]
  split_ifs <;> norm_num

theorem indicator_interval_measure (S : Set ℝ) (hS : MeasurableSet S) :
    (∫ x in (0:ℝ)..1,S.indicator (fun _ => (1:ℝ)) x)=(volume (Ico 0 1∩S)).toReal := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),←integral_Ico_eq_integral_Ioc]
  have hh := integral_indicator_const (μ:=volume.restrict (Ico (0:ℝ) 1)) (1:ℝ) hS
  simpa only [Measure.real,Measure.restrict_apply hS,smul_eq_mul,mul_one,Set.inter_comm] using hh

theorem pairIndicator_integral (a b : ℕ) (ha : 0<a) (hb : 0<b) (r : ℝ) :
    (∫ x in (0:ℝ)..1,pairIndicator a b r x)=
      (volume (forbiddenInUnit a r∩forbiddenInUnit b r)).toReal := by
  rw [pairIndicator,indicator_interval_measure _ ((forbidden_measurable a ha r).inter (forbidden_measurable b hb r))]
  congr 2
  ext x
  simp [forbiddenInUnit,and_assoc,and_left_comm,and_comm]

/-- Exact finite-cell change of variables, including all half-open endpoints
through interval integrals (which agree with Ico integrals). -/
theorem grid_integral (b : ℕ) (hb : 0<b) (f : ℝ → ℝ) (hf : Measurable f)
    (hbound : ∀ x,|f x|≤1) :
    (∫ z in (0:ℝ)..1,∑ j∈Finset.range b,f (((j:ℝ)+z)/(b:ℝ)))=
      (b:ℝ)*(∫ x in (0:ℝ)..1,f x) := by
  have hbR : (0:ℝ)<b := by exact_mod_cast hb
  have hint (j : ℕ) : IntervalIntegrable (fun z => f (((j:ℝ)+z)/(b:ℝ))) volume 0 1 :=
    bounded_intervalIntegrable _ (hf.comp ((measurable_const.add measurable_id).div_const _))
      (fun z => hbound _) _ _
  rw [intervalIntegral.integral_finsetSum (fun j _ => hint j)]
  have he (j : ℕ) : (∫ z in (0:ℝ)..1,f (((j:ℝ)+z)/(b:ℝ)))=
      (b:ℝ)*(∫ x in ((j:ℝ)/(b:ℝ))..((j+1:ℕ):ℝ)/(b:ℝ),f x) := by
    have hh := intervalIntegral.integral_comp_div_add (a:=(0:ℝ)) (b:=(1:ℝ)) f hbR.ne' ((j:ℝ)/(b:ℝ))
    have hefun : (fun z : ℝ => f (((j:ℝ)+z)/(b:ℝ)))=
        (fun z : ℝ => f (z/(b:ℝ)+(j:ℝ)/(b:ℝ))) := by
      funext z
      congr 1
      ring
    have heright : 1/(b:ℝ)+(j:ℝ)/(b:ℝ)=((j+1:ℕ):ℝ)/(b:ℝ) := by push_cast;ring
    rw [hefun]
    simpa only [smul_eq_mul,zero_div,zero_add,heright] using hh
  simp_rw [he]
  rw [←Finset.mul_sum]
  have hs := intervalIntegral.sum_integral_adjacent_intervals
    (a:=fun j : ℕ => (j:ℝ)/(b:ℝ)) (n:=b) (fun j _ => bounded_intervalIntegrable f hf hbound _ _)
  simpa only [Nat.cast_zero,zero_div,div_self hbR.ne'] using congrArg (fun v : ℝ => (b:ℝ)*v) hs

theorem forbidden_grid_second (b j : ℕ) (hb : 0<b) (r z : ℝ) :
    ((j:ℝ)+z)/(b:ℝ)∈forbidden b r ↔ z∈forbidden 1 r := by
  have hbR : (0:ℝ)<b := by exact_mod_cast hb
  have he : (b:ℝ)*(((j:ℝ)+z)/(b:ℝ))=z+(j:ℝ) := by field_simp;ring
  simp only [forbidden,Set.mem_setOf_eq,Nat.cast_one]
  rw [he]
  constructor
  · rintro ⟨k,hk⟩
    refine ⟨k-(j:ℤ),?_⟩
    have hh : 1*z-((k-(j:ℤ):ℤ):ℝ)=z+(j:ℝ)-(k:ℝ) := by push_cast;ring
    rwa [hh]
  · rintro ⟨k,hk⟩
    refine ⟨k+(j:ℤ),?_⟩
    have hh : z+(j:ℝ)-((k+(j:ℤ):ℤ):ℝ)=1*z-(k:ℝ) := by push_cast;ring
    rwa [hh]

theorem pair_grid_count (a b : ℕ) (hb : 0<b) (r z : ℝ) :
    (∑ j∈Finset.range b,pairIndicator a b r (((j:ℝ)+z)/(b:ℝ)))=
      (forbidden 1 r).indicator (fun z => ((eligibleGrid a b r z).card:ℝ)) z := by
  by_cases hz : z∈forbidden 1 r
  · rw [Set.indicator_of_mem hz]
    have hterm (j : ℕ) : pairIndicator a b r (((j:ℝ)+z)/(b:ℝ))=
        if (((j:ℝ)+z)/(b:ℝ))∈forbidden a r then (1:ℝ) else 0 := by
      have hj := (forbidden_grid_second b j hb r z).mpr hz
      simp [pairIndicator,Set.indicator_apply,hj]
    simp_rw [hterm]
    rw [←Finset.sum_filter]
    simp [eligibleGrid]
  · rw [Set.indicator_of_notMem hz]
    apply Finset.sum_eq_zero
    intro j _
    have hj := mt (forbidden_grid_second b j hb r z).mp hz
    simp [pairIndicator,Set.indicator_apply,hj]

end LonelyRunnerNew
