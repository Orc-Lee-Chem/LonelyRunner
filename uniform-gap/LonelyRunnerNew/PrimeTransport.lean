import LonelyRunnerNew.Foundation
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Int.NatAbs
import Mathlib.Tactic.Ring

namespace LonelyRunnerNew

theorem gcd_prime_layers_of_le {p u : ℕ} (hp : Nat.Prime p)
    (hu : ¬ p ∣ u) (v i j : ℕ) (hij : i ≤ j) :
    Nat.gcd (p ^ i * u) (p ^ j * v) = p ^ i * Nat.gcd u v := by
  have hpow : p ^ j = p ^ i * p ^ (j - i) := by
    rw [← pow_add, Nat.add_sub_of_le hij]
  rw [hpow, Nat.mul_assoc, Nat.gcd_mul_left,
    (hp.coprime_pow_of_not_dvd hu).symm.gcd_mul_left_cancel_right v]

theorem gcd_prime_layers {p u v : ℕ} (hp : Nat.Prime p)
    (hu : ¬ p ∣ u) (hv : ¬ p ∣ v) (i j : ℕ) :
    Nat.gcd (p ^ i * u) (p ^ j * v) = p ^ min i j * Nat.gcd u v := by
  rcases le_total i j with hij | hji
  · simpa only [min_eq_left hij] using gcd_prime_layers_of_le hp hu v i j hij
  · simpa only [min_eq_right hji, Nat.gcd_comm] using
      gcd_prime_layers_of_le hp hv u j i hji

/-- Exact transport occurs inside the cap, so saturated edges are retained. -/
theorem prime_layer_transport {p u v : ℕ} (hp : Nat.Prime p)
    (hu : ¬ p ∣ u) (hv : ¬ p ∣ v) (a b : ℝ) (i j : ℕ) :
    weight a b (p ^ i * u) (p ^ j * v) =
      weight (a * (p : ℝ) ^ (i - j)) (b * (p : ℝ) ^ (j - i)) u v := by
  have hi : p ^ i = p ^ min i j * p ^ (i - j) := by
    rw [← pow_add, Nat.add_comm, Nat.sub_add_min_cancel]
  have hj : p ^ j = p ^ min i j * p ^ (j - i) := by
    rw [min_comm, ← pow_add, Nat.add_comm, Nat.sub_add_min_cancel]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hd : (0 : ℝ) < (p : ℝ) ^ min i j := pow_pos hp0 _
  have hl : a * ((p ^ i * u : ℕ) : ℝ) =
      (p : ℝ) ^ min i j * ((a * (p : ℝ) ^ (i - j)) * (u : ℝ)) := by
    rw [hi]
    push_cast
    ring
  have hr : b * ((p ^ j * v : ℕ) : ℝ) =
      (p : ℝ) ^ min i j * ((b * (p : ℝ) ^ (j - i)) * (v : ℝ)) := by
    rw [hj]
    push_cast
    ring
  unfold weight
  rw [gcd_prime_layers hp hu hv, Nat.cast_mul, Nat.cast_pow, hl, hr,
    ← mul_max_of_nonneg _ _ hd.le, mul_div_mul_left _ _ hd.ne']

theorem prime_layer_scale_product (a b : ℝ) (p i j : ℕ) :
    (a * (p : ℝ) ^ (i - j)) * (b * (p : ℝ) ^ (j - i)) =
      (a * b) * (p : ℝ) ^ ((i : ℤ) - (j : ℤ)).natAbs := by
  have habs : ((i : ℤ) - (j : ℤ)).natAbs = (i - j) + (j - i) := by
    rcases le_total i j with hij | hji
    · rw [Int.natAbs_natCast_sub_natCast_of_le hij, Nat.sub_eq_zero_of_le hij,
        zero_add]
    · rw [Int.natAbs_natCast_sub_natCast_of_ge hji, Nat.sub_eq_zero_of_le hji,
        add_zero]
  rw [habs, pow_add]
  ring

end LonelyRunnerNew
