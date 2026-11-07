import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases

noncomputable section
open scoped BigOperators

namespace LonelyRunnerNew.RoughRow

/-- The row-sum expression carrying the constants from the two-sided sieve input. -/
def rowSum (m : ℕ) (R T : ℝ) : ℝ :=
  ∑ i ∈ Finset.range m, (
    (569 / 1000 : ℝ) * min (2 * R * (i + 1 : ℕ)) (T / (i + 1 : ℕ)) -
      (499 / 1000 : ℝ) * R * (i + 1 : ℕ))

set_option maxHeartbeats 1600000 in
/-- Exact finite breakpoint part of round33 (16). No RC or sieve assumption.
The number of rows here is <=6; RC itself remains unbounded. -/
theorem rowSum_le_six (m : ℕ) (hm : m ≤ 6) (R T : ℝ) (hT : 0 ≤ T) :
    rowSum m R T ≤ (639 / 2000 : ℝ) * T := by
  interval_cases m <;>
    norm_num [rowSum, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one] <;>
    (try simp only [min_def]) <;>
    (try split_ifs) <;> linarith

theorem one_row_sharp (T : ℝ) : rowSum 1 (T / 2) T = (639 / 2000 : ℝ) * T := by
  norm_num [rowSum]
  ring_nf
  rw [min_self]
  ring

end LonelyRunnerNew.RoughRow
