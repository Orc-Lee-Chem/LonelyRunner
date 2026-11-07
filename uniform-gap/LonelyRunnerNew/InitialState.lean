import LonelyRunnerNew.Foundation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section
open scoped BigOperators

namespace LonelyRunnerNew

/-- The original ordered edge support, with only the original diagonal removed. -/
def initialEdges (V : Finset ℕ) : Finset (ℕ × ℕ) :=
  (V.product V).filter (fun e => e.1 ≠ e.2)

theorem initial_weight (n x y : ℕ) (hn : 0 < n) (hx : 0 < x) :
    weight (1 / (2 * (n : ℝ))) (1 / (2 * (n : ℝ))) x y =
      min 1 (2 * (n : ℝ) / height x y) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hmax0 : ((max x y : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le hx (le_max_left x y)))
  have hgcd0 : (Nat.gcd x y : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.gcd_pos_of_pos_left y hx))
  have hscale : (0 : ℝ) ≤ 1 / (2 * (n : ℝ)) := by positivity
  unfold weight height
  rw [← mul_max_of_nonneg (x : ℝ) (y : ℝ) hscale, ← Nat.cast_max]
  congr 1
  field_simp

theorem initial_density_eq_W (V : Finset ℕ) (hpos : positive V)
    (hn : 0 < V.card) :
    density V V (initialEdges V) (1 / (2 * (V.card : ℝ)))
      (1 / (2 * (V.card : ℝ))) = W V := by
  unfold density initialEdges W
  rw [Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product]
  simp only [pow_two]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hxy : x = y
  · simp [hxy]
  · simpa [hxy] using initial_weight V.card x y hn (hpos x hx)

theorem initial_quality_eq (V : Finset ℕ) (hpos : positive V)
    (hn : 0 < V.card) :
    quality V.card V V (initialEdges V) (1 / (2 * (V.card : ℝ)))
      (1 / (2 * (V.card : ℝ))) = Real.rpow (W V) q / 4 := by
  unfold quality
  rw [initial_density_eq_W V hpos hn]
  have hn0 : (V.card : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hratio : (V.card : ℝ) * (V.card : ℝ) / (V.card : ℝ) ^ 2 = 1 := by
    field_simp
  rw [hratio]
  simp only [Real.rpow_eq_pow, Real.one_rpow, mul_one]
  field_simp
  ring

end LonelyRunnerNew
