import LonelyRunnerNew.SaturatedTerminal
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons

noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace LonelyRunnerNew.Saturated

/-- Continuous extension of min(1,t/sqrt(x)) at zero. For positive t the
denominator is everywhere positive; zero coordinates have value exactly 1. -/
def cap (t x : ℝ) : ℝ := t/Real.sqrt (max (t^2) x)
def inner (t v : ℝ) : ℝ := ∫ u in (0:ℝ)..1,cap t (u*v)

theorem cap_continuous {t : ℝ} (ht : 0<t) : Continuous (cap t) := by
  apply continuous_const.div ((continuous_const.max continuous_id).sqrt)
  intro x
  exact (Real.sqrt_pos.mpr ((sq_pos_of_pos ht).trans_le (le_max_left _ _))).ne'

theorem cap_antitone {t : ℝ} (ht : 0<t) : Antitone (cap t) := by
  intro x y hxy
  exact div_le_div_of_nonneg_left ht.le
    (Real.sqrt_pos.mpr ((sq_pos_of_pos ht).trans_le (le_max_left _ _)))
    (Real.sqrt_le_sqrt (max_le_max_left _ hxy))

theorem cap_nonneg {t x : ℝ} (ht : 0<t) : 0≤cap t x := by
  exact div_nonneg ht.le (Real.sqrt_nonneg _)
theorem cap_le_one {t x : ℝ} (ht : 0<t) : cap t x≤1 := by
  apply (div_le_one (Real.sqrt_pos.mpr ((sq_pos_of_pos ht).trans_le (le_max_left _ _)))).mpr
  exact (Real.le_sqrt ht.le ((sq_pos_of_pos ht).le.trans (le_max_left _ _))).mpr (le_max_left _ _)
theorem cap_low {t x : ℝ} (ht : 0<t) (hx : x≤t^2) : cap t x=1 := by
  simp [cap,max_eq_left hx,Real.sqrt_sq_eq_abs,abs_of_pos ht,ht.ne']
theorem cap_high {t x : ℝ} (hx : t^2≤x) : cap t x=t*x^(-(1/2):ℝ) := by
  rw [cap,max_eq_right hx,Real.sqrt_eq_rpow,Real.rpow_neg (by nlinarith [sq_nonneg t] : 0≤x)]
  ring

theorem cap_eq_min {t x : ℝ} (ht : 0<t) (hx : 0<x) :
    cap t x=min 1 (t/Real.sqrt x) := by
  by_cases h : x≤t^2
  · rw [cap_low ht h,min_eq_left]
    exact (one_le_div (Real.sqrt_pos.mpr hx)).mpr ((Real.sqrt_le_left ht.le).mpr h)
  · have h' : t^2≤x := (le_of_not_ge h)
    rw [cap,max_eq_right h',min_eq_right]
    exact (div_le_one (Real.sqrt_pos.mpr hx)).mpr ((Real.le_sqrt ht.le hx.le).mpr h')

theorem inner_nonneg {t v : ℝ} (ht : 0<t) : 0 ≤ inner t v :=
  intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => cap_nonneg ht)

theorem inner_antitone {t : ℝ} (ht : 0<t) : AntitoneOn (inner t) (Set.Ici 0) := by
  intro v hv w hw hvw
  apply intervalIntegral.integral_mono_on (by norm_num)
    (((cap_continuous ht).comp (continuous_id.mul continuous_const)).intervalIntegrable _ _)
    (((cap_continuous ht).comp (continuous_id.mul continuous_const)).intervalIntegrable _ _)
  intro u hu
  exact cap_antitone ht (mul_le_mul_of_nonneg_left hvw hu.1)

theorem inner_low {t v : ℝ} (ht : 0<t) (hv : 0≤v) (hvt : v≤t^2) : inner t v=1 := by
  have he : inner t v=∫ _ in (0:ℝ)..1,(1:ℝ) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ)≤1)] at hu
    exact cap_low ht ((mul_le_of_le_one_left hv hu.2).trans hvt)
  simpa using he

theorem inner_high {t v : ℝ} (ht : 0<t) (hv : t^2≤v) :
    inner t v=2*t/Real.sqrt v-t^2/v := by
  have hv0 : 0<v := (sq_pos_of_pos ht).trans_le hv
  let c := t^2/v
  have hc0 : 0<c := div_pos (sq_pos_of_pos ht) hv0
  have hc1 : c≤1 := (div_le_one hv0).mpr hv
  have hi (a b : ℝ) : IntervalIntegrable (fun u => cap t (u*v)) volume a b :=
    ((cap_continuous ht).comp (continuous_id.mul continuous_const)).intervalIntegrable _ _
  have hleft : (∫ u in (0:ℝ)..c,cap t (u*v))=c := by
    calc
      _ = ∫ _ in (0:ℝ)..c,(1:ℝ) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [Set.uIcc_of_le hc0.le] at hu
        apply cap_low ht
        exact (le_div_iff₀ hv0).mp hu.2
      _ = c := by simp
  have hright : (∫ u in c..(1:ℝ),cap t (u*v))=
      (t/Real.sqrt v)*(2*(1-c^(1/2:ℝ))) := by
    have heq : (∫ u in c..(1:ℝ),cap t (u*v))=
        ∫ u in c..(1:ℝ),(t/Real.sqrt v)*u^(-(1/2):ℝ) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_le hc1] at hu
      have hu0 : 0≤u := hc0.le.trans hu.1
      have huv : t^2≤u*v := (div_le_iff₀ hv0).mp hu.1
      change cap t (u*v)=(t/Real.sqrt v)*u^(-(1/2):ℝ)
      rw [cap_high huv,Real.mul_rpow hu0 hv0.le,Real.rpow_neg hv0.le,
        ←Real.sqrt_eq_rpow]
      ring
    rw [heq,intervalIntegral.integral_const_mul,integral_rpow (Or.inl (by norm_num))]
    norm_num only [show (-(1/2):ℝ)+1=1/2 by norm_num,Real.one_rpow]
    ring
  have hroot : c^(1/2:ℝ)=t/Real.sqrt v := by
    rw [←Real.sqrt_eq_rpow,Real.sqrt_div (sq_nonneg t),Real.sqrt_sq_eq_abs,abs_of_pos ht]
  have he := intervalIntegral.integral_add_adjacent_intervals (hi 0 c) (hi c 1)
  change (∫u in (0:ℝ)..c,cap t (u*v))+(∫u in c..(1:ℝ),cap t (u*v))=inner t v at he
  rw [hleft,hright,hroot] at he
  rw [←he]
  dsimp only [c]
  have hs := Real.sq_sqrt hv0.le
  have hs0 := (Real.sqrt_pos.mpr hv0).ne'
  field_simp
  nlinarith only [congrArg (fun x : ℝ => t*x) hs]

theorem inner_integrable {t : ℝ} (ht : 0<t) : IntervalIntegrable (inner t) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0:ℝ)≤1)]
  exact ((inner_antitone ht).mono (fun _ hx => hx.1)).integrableOn_isCompact isCompact_Icc

end LonelyRunnerNew.Saturated
