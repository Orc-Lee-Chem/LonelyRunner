import LonelyRunnerNew.RadiusExpansion
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
namespace LonelyRunnerNew

theorem height_ge_one {u v : ℕ} (hu : 0<u) : (1:ℝ)≤height u v := by
  have hd : (0:ℝ)<Nat.gcd u v := by exact_mod_cast Nat.gcd_pos_of_pos_left v hu
  apply (one_le_div hd).mpr
  exact_mod_cast (Nat.gcd_le_left v hu).trans (le_max_left u v)

/-- Multiplying the same nearest-integer witness gives an actual forbidden
set inclusion. It does not require choosing a continuous nearest-integer map. -/
theorem forbidden_mul_subset (d a : ℕ) {r e : ℝ} (h : (a:ℝ)*e≤r) :
    forbidden d e⊆forbidden (d*a) r := by
  rintro t ⟨k,hk⟩
  refine ⟨(a:ℤ)*k,?_⟩
  push_cast
  rw [show (d:ℝ)*(a:ℝ)*t-(a:ℝ)*(k:ℝ)=(a:ℝ)*((d:ℝ)*t-(k:ℝ)) by ring,
    abs_mul,abs_of_nonneg (Nat.cast_nonneg a)]
  exact (mul_le_mul_of_nonneg_left hk (Nat.cast_nonneg a)).trans h

def commonForbidden (u v : ℕ) (r : ℝ) : Set ℝ :=
  forbiddenInUnit (Nat.gcd u v) (r/height u v)

theorem commonForbidden_subset {u v : ℕ} (hu : 0<u) (hv : 0<v) {r : ℝ} (hr : 0≤r) :
    commonForbidden u v r⊆forbiddenInUnit u r∩forbiddenInUnit v r := by
  let d := Nat.gcd u v
  have hd : (0:ℝ)<d := by exact_mod_cast Nat.gcd_pos_of_pos_left v hu
  have hH := height_pos (y:=v) hu
  have hleft : ((u/d:ℕ):ℝ)≤height u v := by
    apply (le_div_iff₀ hd).mpr
    have he : ((u/d:ℕ):ℝ)*(d:ℝ)=(u:ℝ) := by exact_mod_cast Nat.div_mul_cancel (Nat.gcd_dvd_left u v)
    rw [he]
    exact_mod_cast le_max_left u v
  have hright : ((v/d:ℕ):ℝ)≤height u v := by
    apply (le_div_iff₀ hd).mpr
    have he : ((v/d:ℕ):ℝ)*(d:ℝ)=(v:ℝ) := by exact_mod_cast Nat.div_mul_cancel (Nat.gcd_dvd_right u v)
    rw [he]
    exact_mod_cast le_max_right u v
  have hb {a : ℕ} (ha : (a:ℝ)≤height u v) : (a:ℝ)*(r/height u v)≤r := by
    have hh := mul_le_mul_of_nonneg_right ha (div_nonneg hr hH.le)
    rwa [mul_div_cancel₀ _ hH.ne'] at hh
  rintro t ⟨ht,hc⟩
  have hlu := forbidden_mul_subset d (u/d) (hb hleft) hc
  have hlv := forbidden_mul_subset d (v/d) (hb hright) hc
  have hluv : d*(u/d)=u := Nat.mul_div_cancel' (Nat.gcd_dvd_left u v)
  have hlvv : d*(v/d)=v := Nat.mul_div_cancel' (Nat.gcd_dvd_right u v)
  rw [hluv] at hlu
  rw [hlvv] at hlv
  exact ⟨⟨ht,hlu⟩,⟨ht,hlv⟩⟩

theorem volume_ne_top_in_unit {S : Set ℝ} (hS : S⊆Ico (0:ℝ) 1) : volume S≠⊤ := by
  apply ne_of_lt
  exact (measure_mono hS).trans_lt (by norm_num)

theorem commonForbidden_measure {u v : ℕ} (hu : 0<u) {r : ℝ}
    (hr : 0≤r) (hrh : r≤1/2) :
    volume (commonForbidden u v r)=ENNReal.ofReal (2*r/height u v) := by
  have hH := height_ge_one (v:=v) hu
  have hd := Nat.gcd_pos_of_pos_left v hu
  have he : r/height u v≤r := div_le_self hr hH
  have hh := forbiddenInUnit_measure (Nat.gcd u v) hd (r/height u v)
    (div_nonneg hr (height_pos (y:=v) hu).le) (he.trans hrh)
  convert hh using 1 <;> congr 1 <;> ring

/-- The exact common-center mass is a certified lower bound on the full
intersection, including the common center at the half-open unit boundary. -/
theorem forbidden_pair_intersection_lower {u v : ℕ} (hu : 0<u) (hv : 0<v) {r : ℝ}
    (hr : 0≤r) (hrh : r≤1/2) :
    2*r/height u v≤(volume (forbiddenInUnit u r∩forbiddenInUnit v r)).toReal := by
  have hm := measure_mono (μ:=volume) (commonForbidden_subset hu hv hr)
  rw [commonForbidden_measure hu hr hrh] at hm
  have hf : volume (forbiddenInUnit u r∩forbiddenInUnit v r)≠⊤ :=
    volume_ne_top_in_unit (fun _ hx => hx.1.1)
  have hh := ENNReal.toReal_mono hf hm
  rw [ENNReal.toReal_ofReal (div_nonneg (mul_nonneg (by norm_num) hr) (height_pos (y:=v) hu).le)] at hh
  exact hh

end LonelyRunnerNew
