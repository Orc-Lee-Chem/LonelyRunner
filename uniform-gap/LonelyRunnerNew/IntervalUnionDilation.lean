import LonelyRunnerNew.IntervalUnionContraction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
namespace LonelyRunnerNew.IntervalCoverage
variable {ι : Type*} [DecidableEq ι]

theorem normalize_interval {s c r t : ℝ} (hs : 0<s) :
    s*t∈Icc (c-s*r) (c+s*r) ↔ t∈Icc ((1/s)*c-r) ((1/s)*c+r) := by
  have hl : (c-s*r)/s=(1/s)*c-r := by field_simp
  have hr : (c+s*r)/s=(1/s)*c+r := by field_simp
  simp only [Set.mem_Icc]
  rw [←hl,←hr,div_le_iff₀ hs,le_div_iff₀ hs]
  simp only [mul_comm t s]

theorem normalized_union_preimage (F : Finset ι) (c r : ι → ℝ) {s : ℝ} (hs : 0<s) :
    intervalUnion F (fun i => (1/s)*c i-r i) (fun i => (1/s)*c i+r i)=
      (fun t : ℝ => s*t) ⁻¹' intervalUnion F (fun i => c i-s*r i) (fun i => c i+s*r i) := by
  ext t
  simp only [intervalUnion,Set.mem_iUnion,Set.mem_preimage,exists_prop]
  exact exists_congr (fun i => and_congr_right (fun _ => (normalize_interval hs).symm))

theorem normalized_union_volume (F : Finset ι) (c r : ι → ℝ) {s : ℝ} (hs : 0<s) :
    (volume (intervalUnion F (fun i => (1/s)*c i-r i) (fun i => (1/s)*c i+r i))).toReal=
      (volume (intervalUnion F (fun i => c i-s*r i) (fun i => c i+s*r i))).toReal/s := by
  rw [normalized_union_preimage F c r hs,Real.volume_preimage_mul_left hs.ne',ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _),abs_of_pos (inv_pos.mpr hs)]
  ring

/-- The actual finite-union dilation inequality, normalized by its own
positive radius scale. No connected-component or scalar estimate is input. -/
theorem union_dilation (F : Finset ι) (c r : ι → ℝ) {s t : ℝ}
    (hs : 0<s) (hst : s≤t) (hr : ∀ i∈F,0≤r i) :
    (volume (intervalUnion F (fun i => c i-t*r i) (fun i => c i+t*r i))).toReal/t≤
      (volume (intervalUnion F (fun i => c i-s*r i) (fun i => c i+s*r i))).toReal/s := by
  have ht : 0<t := hs.trans_le hst
  have hcmp := union_center_contraction F c r (u:=1/t) (v:=1/s)
    (one_div_pos.mpr ht).le (one_div_le_one_div_of_le hs hst) hr
  have hf : volume (intervalUnion F (fun i => (1/s)*c i-r i) (fun i => (1/s)*c i+r i))≠⊤ :=
    (F.isCompact_biUnion (fun _ _ => isCompact_Icc)).measure_ne_top
  have hh := ENNReal.toReal_mono hf hcmp
  rwa [normalized_union_volume F c r ht,normalized_union_volume F c r hs] at hh

end LonelyRunnerNew.IntervalCoverage
