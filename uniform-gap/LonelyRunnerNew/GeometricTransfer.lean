import LonelyRunnerNew.Inputs
import LonelyRunnerNew.NumericEndgame

namespace LonelyRunnerNew

/-- Algebraic part of L18; the geometric input theorems remain separate obligations. -/
theorem geometric_transfer_lower_bound (hS : spilloverInput) (hF : forestInput)
    (hSep : separatedControl (Real.exp 6880) (17 / 100))
    (V : Finset ℕ) (hV : valid V) :
    1 / 1400 ≤ (Real.exp 6880 + 1) * gap V := by
  have hP : 1 ≤ Real.exp 6880 := Real.one_le_exp_iff.mpr (by norm_num)
  have hs := hS V hV
  have hf := hF (Real.exp 6880) (17 / 100) hP (by norm_num) hSep V hV
  nlinarith

theorem gap_gt_c_of_separated_control (hS : spilloverInput) (hF : forestInput)
    (hSep : separatedControl (Real.exp 6880) (17 / 100))
    (V : Finset ℕ) (hV : valid V) : c < gap V := by
  have hP : 1 ≤ Real.exp 6880 := Real.one_le_exp_iff.mpr (by norm_num)
  have hcP : c * Real.exp 6880 = 1 / Real.exp 8 := by
    unfold c
    rw [← Real.exp_add]
    norm_num
    rw [Real.exp_neg]
  have hsmall : c * (Real.exp 6880 + 1) < 1 / 1400 := by
    calc
      c * (Real.exp 6880 + 1) ≤ c * (2 * Real.exp 6880) :=
        mul_le_mul_of_nonneg_left (by linarith) c_pos.le
      _ = 2 * (c * Real.exp 6880) := by ring
      _ = 2 / Real.exp 8 := by rw [hcP]; ring
      _ < 1 / 1400 := by
        apply (div_lt_iff₀ (Real.exp_pos 8)).2
        have he := Endgame.exp_eight_gt
        linarith
  have hlower := geometric_transfer_lower_bound hS hF hSep V hV
  apply (mul_lt_mul_iff_right₀ (show 0 < Real.exp 6880 + 1 by positivity)).mp
  nlinarith

end LonelyRunnerNew
