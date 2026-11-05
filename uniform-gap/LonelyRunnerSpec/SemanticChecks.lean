import LonelyRunnerSpec.V1
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Round

namespace LonelyRunnerSpec

/-- The domain has valid speed sets of every permitted cardinality. -/
theorem admissible_of_any_card (n : ℕ) (_hn : 2 ≤ n) :
    ∃ V : Finset ℕ, (∀ v ∈ V, 0 < v) ∧ V.card = n := by
  refine ⟨Finset.Icc 1 n, ?_, ?_⟩
  · intro v hv
    exact (Finset.mem_Icc.mp hv).1
  · simp

theorem exists_nearest_integer (x : ℝ) :
    ∃ k : ℤ, ∀ l : ℤ, |x - (k : ℝ)| ≤ |x - (l : ℝ)| :=
  ⟨round x, round_le x⟩

/-- A proved strict comparison with the attained nearest-integer distance. -/
theorem strict_all_integers_iff_nearest (x r : ℝ) :
    (∀ k : ℤ, r < |x - (k : ℝ)|) ↔ r < |x - (round x : ℝ)| := by
  constructor
  · intro h
    exact h (round x)
  · intro h k
    exact h.trans_le (round_le x k)

end LonelyRunnerSpec
