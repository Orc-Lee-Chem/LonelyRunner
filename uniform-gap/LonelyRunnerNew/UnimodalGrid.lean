import LonelyRunnerNew.RCSelbergRows
import Mathlib.Analysis.SumIntegralComparisons

noncomputable section
set_option autoImplicit false
open scoped BigOperators
open MeasureTheory
namespace LonelyRunnerNew.UnimodalGrid

def BetweenLower (g : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀x∈Set.Icc a b,∀z∈Set.Icc a b,∀y,x≤y → y≤z → min (g x) (g z)≤g y

/-- Finite adjacent-cell argument. The maximum is over the actual samples,
and no monotonicity on either side of that sample is assumed. -/
theorem unit_grid (n : ℕ) (g : ℝ → ℝ) (M : ℝ)
    (hc : ContinuousOn g (Set.Icc 0 (n:ℝ))) (hb : BetweenLower g 0 (n:ℝ))
    (hM : ∀i∈Finset.range (n+1),g (i:ℝ)≤M) :
    (∑i∈Finset.range (n+1),g (i:ℝ))≤(∫t in (0:ℝ)..(n:ℝ),g t)+M := by
  obtain ⟨k,hk,hmax⟩ := Finset.exists_max_image (Finset.range (n+1)) (fun i : ℕ => g (i:ℝ))
    ⟨0,Finset.mem_range.mpr (by omega)⟩
  have hkn : k≤n := by have hh := Finset.mem_range.mp hk;omega
  have hknR : (k:ℝ)≤n := by exact_mod_cast hkn
  have hg : IntegrableOn g (Set.Icc 0 (n:ℝ)) volume := hc.integrableOn_Icc
  have hleftInt : IntegrableOn g (Set.Ico (0:ℝ) (k:ℝ)) := hg.mono_set (by
    intro t ht;exact ⟨ht.1,ht.2.le.trans hknR⟩)
  have hrightInt : IntegrableOn g (Set.Ico (k:ℝ) (n:ℝ)) := hg.mono_set (by
    intro t ht;exact ⟨(Nat.cast_nonneg k).trans ht.1,ht.2.le⟩)
  have hl := sum_Ico_le_integral_of_le (a:=0) (b:=k) (f:=g) (g:=g) (by omega)
    (by
      intro i hi t ht
      have hi' := hi
      have hiK : i<k := hi'.2
      have hiN : i∈Finset.range (n+1) := Finset.mem_range.mpr (by omega)
      have hiR : (i:ℝ)≤n := by exact_mod_cast (by omega : i≤n)
      have htK : t≤(k:ℝ) := by
        have hh : (i+1:ℝ)≤k := by exact_mod_cast (by omega : i+1≤k)
        have ht' : t<(i+1:ℝ) := by simpa only [Nat.cast_add,Nat.cast_one] using ht.2
        linarith
      have hbetween := hb (i:ℝ) ⟨Nat.cast_nonneg _,hiR⟩ (k:ℝ) ⟨Nat.cast_nonneg _,hknR⟩ t ht.1 htK
      rw [min_eq_left (hmax i hiN)] at hbetween
      exact hbetween) (by simpa only [Nat.cast_zero] using hleftInt)
  have hr := sum_Ico_le_integral_of_le (a:=k) (b:=n) (f:=fun t => g (t+1)) (g:=g) hkn
    (by
      intro i hi t ht
      have hi' := hi
      have hil : i<n := hi.2
      have hiN : i+1∈Finset.range (n+1) := Finset.mem_range.mpr (by omega)
      have hiR : (i+1:ℝ)≤n := by exact_mod_cast (by omega : i+1≤n)
      have htK : (k:ℝ)≤t := (show (k:ℝ)≤(i:ℝ) from by exact_mod_cast hi'.1).trans ht.1
      have ht' : t≤(i+1:ℝ) := by exact_mod_cast ht.2.le
      have hbetween := hb (k:ℝ) ⟨Nat.cast_nonneg _,hknR⟩ (i+1:ℝ) ⟨by positivity,hiR⟩ t htK ht'
      have hm : g (i+1:ℝ)≤g (k:ℝ) := by simpa only [Nat.cast_add,Nat.cast_one] using hmax (i+1) hiN
      rw [min_eq_right hm] at hbetween
      exact hbetween) hrightInt
  have hsum : (∑i∈Finset.range (n+1),g (i:ℝ))=
      (∑i∈Finset.Ico 0 k,g (i:ℝ))+g (k:ℝ)+(∑i∈Finset.Ico k n,g (i+1:ℝ)) := by
    have hright := Finset.sum_Ico_eq_sub (fun i : ℕ => g (i+1:ℝ)) hkn
    have hn := Finset.sum_range_succ' (fun i : ℕ => g (i:ℝ)) n
    have hk' := Finset.sum_range_succ' (fun i : ℕ => g (i:ℝ)) k
    have hk'' := Finset.sum_range_succ (fun i : ℕ => g (i:ℝ)) k
    simp only [Nat.cast_add,Nat.cast_one,Nat.cast_zero] at hn hk' hk''
    rw [←Finset.range_eq_Ico]
    linarith
  have h0k : IntervalIntegrable g volume (0:ℝ) (k:ℝ) := (hg.mono_set (by
    rw [Set.uIcc_of_le (Nat.cast_nonneg k)]
    intro t ht;exact ⟨ht.1,ht.2.trans hknR⟩)).intervalIntegrable
  have hknI : IntervalIntegrable g volume (k:ℝ) (n:ℝ) := (hg.mono_set (by
    rw [Set.uIcc_of_le hknR]
    intro t ht;exact ⟨(Nat.cast_nonneg k).trans ht.1,ht.2⟩)).intervalIntegrable
  have he := intervalIntegral.integral_add_adjacent_intervals h0k hknI
  norm_num only [Nat.cast_zero] at hl
  have hm := hM k hk
  rw [hsum]
  linarith

end LonelyRunnerNew.UnimodalGrid
