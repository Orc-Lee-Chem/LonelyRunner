import LonelyRunnerNew.Definitions

namespace LonelyRunnerNew

theorem height_pos {x y : ℕ} (hx : 0 < x) : 0 < height x y := by
  have hmax : 0 < max x y := lt_of_lt_of_le hx (le_max_left x y)
  have hgcd : 0 < Nat.gcd x y := Nat.gcd_pos_of_pos_left y hx
  exact div_pos (by exact_mod_cast hmax) (by exact_mod_cast hgcd)

/-- A common positive factor on both speeds does not change their height. -/
theorem height_mul_left (c x y : ℕ) (hc : 0 < c) :
    height (c * x) (c * y) = height x y := by
  have hc0 : (c : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hc)
  simpa only [height, Nat.mul_max_mul_left, Nat.gcd_mul_left, Nat.cast_mul,
    Nat.cast_max] using
    (mul_div_mul_left (max x y : ℝ) (Nat.gcd x y : ℝ) hc0)

/-- Restricting to a subset preserves the separation property. -/
theorem separated_mono {P : ℝ} {U V : Finset ℕ} (hUV : U ⊆ V)
    (hV : separated P V) : separated P U := by
  intro x hx y hy hxy
  exact hV x (hUV hx) y (hUV hy) hxy

/-- Common multiplication preserves separation in both directions. -/
theorem separated_image_mul {P : ℝ} (V : Finset ℕ) (c : ℕ) (hc : 0 < c) :
    separated P (V.image (fun x => c * x)) ↔ separated P V := by
  constructor
  · intro h x hx y hy hxy
    have hne : c * x ≠ c * y := by
      intro heq
      exact hxy (Nat.eq_of_mul_eq_mul_left hc heq)
    have h' := h (c * x) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
      (c * y) (Finset.mem_image.mpr ⟨y, hy, rfl⟩) hne
    simpa only [height_mul_left c x y hc] using h'
  · intro h u hu v hv huv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
    have hxy : x ≠ y := by
      intro heq
      exact huv (congrArg (fun z => c * z) heq)
    simpa only [height_mul_left c x y hc] using h x hx y hy hxy

theorem valid_card_pos {V : Finset ℕ} (hV : valid V) : 0 < V.card := by
  exact lt_of_lt_of_le (by decide : 0 < 2) hV.2

end LonelyRunnerNew
