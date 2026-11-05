import LonelyRunnerNew.Definitions
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open scoped BigOperators

namespace LonelyRunnerNew
namespace RationalAnalysis

def logSeriesLower (y : ℝ) (m : ℕ) : ℝ :=
  2 * ∑ k ∈ Finset.range m,
    ((y - 1) / (y + 1)) ^ (2 * k + 1) / (2 * k + 1)

/-- A slightly wider remainder than the handoff's proposed bound. This version
uses a theorem already proved in the locked mathlib and suffices as a candidate
for replaying the frozen certificates. The row checks are separate obligations. -/
def logSeriesUpper (y : ℝ) (m : ℕ) : ℝ :=
  logSeriesLower y m +
    2 * ((y - 1) / (y + 1)) ^ (2 * m + 1) / (1 - ((y - 1) / (y + 1)) ^ 2)

theorem log_series_enclosure {y : ℝ} (hy : 1 ≤ y) (m : ℕ) :
    logSeriesLower y m ≤ Real.log y ∧ Real.log y ≤ logSeriesUpper y m := by
  let z := (y - 1) / (y + 1)
  have hy1 : 0 < y + 1 := by linarith
  have hz0 : 0 ≤ z := div_nonneg (sub_nonneg.mpr hy) hy1.le
  have hz1 : z < 1 := (div_lt_one hy1).2 (by linarith)
  have hratio : (1 + z) / (1 - z) = y := by
    dsimp [z]
    field_simp
    ring
  have hlo := Real.sum_range_le_log_div hz0 hz1 m
  have hhi := Real.log_div_le_sum_range_add hz0 hz1 m
  rw [hratio] at hlo hhi
  constructor
  · change 2 * (∑ k ∈ Finset.range m, z ^ (2 * k + 1) / (2 * k + 1)) ≤ _
    linarith
  · change Real.log y ≤ 2 * (∑ k ∈ Finset.range m, z ^ (2 * k + 1) / (2 * k + 1)) +
      2 * z ^ (2 * m + 1) / (1 - z ^ 2)
    rw [mul_div_assoc]
    linarith

theorem log_two_pow_mul {y : ℝ} (hy : 0 < y) (s : ℕ) :
    Real.log ((2 : ℝ) ^ s * y) = (s : ℝ) * Real.log 2 + Real.log y := by
  rw [Real.log_mul (pow_ne_zero s (by norm_num)) hy.ne', Real.log_pow]

/-- Integer power certificates imply the corresponding real root bound. -/
theorem root_bound {p lam : ℝ} (hp : 0 < p) (hlam : 0 < lam)
    (a b : ℕ) (hb : 0 < b) (hcert : 1 ≤ lam ^ b * p ^ a) :
    p ^ (-(a : ℝ) / (b : ℝ)) ≤ lam := by
  apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hp _) hlam).mp
  rw [Real.log_rpow hp]
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 1) hcert
  rw [Real.log_one, Real.log_mul (pow_ne_zero b hlam.ne') (pow_ne_zero a hp.ne'),
    Real.log_pow, Real.log_pow] at hlog
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have heq : (-(a : ℝ) / (b : ℝ)) * Real.log p =
      (-(a : ℝ) * Real.log p) / (b : ℝ) := by ring
  rw [heq]
  apply (div_le_iff₀ hbR).2
  nlinarith

end RationalAnalysis
end LonelyRunnerNew
