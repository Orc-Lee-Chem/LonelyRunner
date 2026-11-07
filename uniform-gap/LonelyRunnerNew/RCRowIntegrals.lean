import LonelyRunnerNew.RCRowKernels
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace LonelyRunnerNew.RoughRational.RowKernels

theorem integrable {R T B : ℝ} (hR : 0<R) (hB : 0<B) (hBT : R*B^2=T) :
    IntervalIntegrable (cap R T) volume 0 B ∧ IntervalIntegrable (gap R T) volume 0 B := by
  have hc := switch_geometry hR hB hBT
  have hlin : IntervalIntegrable (fun x : ℝ => 2*R*x) volume 0 (switch B) :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  have hleft : IntervalIntegrable (cap R T) volume 0 (switch B) := hlin.congr (by
    intro x hx
    rw [Set.uIoc_of_le hc.1.le] at hx
    exact (cap_small hR hB hBT hx.1.le hx.2).symm)
  have hright : IntervalIntegrable (cap R T) volume (switch B) B := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hc.2.1]
    exact (cap_continuous hc.1).integrableOn_Icc
  have hcap := hleft.trans hright
  have hline : IntervalIntegrable (fun x : ℝ => R*x) volume 0 B :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  exact ⟨hcap,hcap.sub hline⟩

theorem cap_integral {R T B : ℝ} (hR : 0<R) (hB : 0<B) (hBT : R*B^2=T) :
    (∫x in (0:ℝ)..B,cap R T x)=(T/2)*(1+Real.log 2) := by
  have hc := switch_geometry hR hB hBT
  have hwhole := (integrable hR hB hBT).1
  have hl : IntervalIntegrable (cap R T) volume 0 (switch B) := by
    have hfi := (intervalIntegrable_iff_integrableOn_Icc_of_le hB.le).mp hwhole
    exact (hfi.mono_set (by
      rw [Set.uIcc_of_le hc.1.le]
      intro x hx;exact ⟨hx.1,hx.2.trans hc.2.1⟩)).intervalIntegrable
  have hr : IntervalIntegrable (cap R T) volume (switch B) B := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hc.2.1]
    exact (cap_continuous hc.1).integrableOn_Icc
  have he := intervalIntegral.integral_add_adjacent_intervals hl hr
  have hfirst : (∫x in (0:ℝ)..switch B,cap R T x)=R*(switch B)^2 := by
    have hcng : (∫x in (0:ℝ)..switch B,cap R T x)=∫x in (0:ℝ)..switch B,2*R*x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hc.1.le] at hx
      exact cap_small hR hB hBT hx.1 hx.2
    rw [hcng,intervalIntegral.integral_const_mul,integral_id]
    ring
  have hsecond : (∫x in switch B..B,cap R T x)=T*(Real.log 2/2) := by
    have hcng : (∫x in switch B..B,cap R T x)=∫x in switch B..B,T/x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hc.2.1] at hx
      exact cap_large hR hB hBT hx.1
    have hf : (fun x : ℝ => T/x)=(fun x => T*(1/x)) := by funext x;ring
    rw [hcng,hf,intervalIntegral.integral_const_mul,integral_one_div_of_pos hc.1 hB]
    have hs : 0<Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hsq := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
    have hratio : B/switch B=Real.sqrt 2 := by unfold switch;field_simp
    have hlog : Real.log (Real.sqrt 2)=Real.log 2/2 := by
      have hh := Real.log_pow (Real.sqrt 2) 2
      rw [hsq] at hh
      norm_num at hh
      linarith
    rw [hratio,hlog]
  rw [hfirst,hsecond] at he
  nlinarith [hc.2.2]

theorem gap_integral {R T B : ℝ} (hR : 0<R) (hB : 0<B) (hBT : R*B^2=T) :
    (∫x in (0:ℝ)..B,gap R T x)=(T/2)*Real.log 2 := by
  have hcap := (integrable hR hB hBT).1
  have hline : IntervalIntegrable (fun x : ℝ => R*x) volume 0 B :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  unfold gap
  rw [intervalIntegral.integral_sub hcap hline,cap_integral hR hB hBT,
    intervalIntegral.integral_const_mul,integral_id]
  norm_num only [zero_pow,sub_zero,mul_zero] at *
  nlinarith [hBT]

theorem maximum_values {R T B : ℝ} (hR : 0<R) (hB : 0<B) (hBT : R*B^2=T) :
    2*R*switch B=Real.sqrt 2*T/B ∧ R*switch B=T/(Real.sqrt 2*B) := by
  have hs : 0<Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hprod : 2*R*B^2=(Real.sqrt 2)^2*T := by rw [hsq,←hBT];ring
  unfold switch
  constructor <;> field_simp <;> nlinarith [hprod,hBT]

end LonelyRunnerNew.RoughRational.RowKernels
