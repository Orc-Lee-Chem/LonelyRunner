import LonelyRunnerNew.Definitions
import LonelyRunnerNew.CertificateData
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

noncomputable section
open scoped BigOperators

namespace LonelyRunnerNew
namespace Endgame

def expPoly (x : ℝ) (degree : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (degree + 1), x ^ j / (Nat.factorial j : ℝ)

theorem expPoly_le_exp {x : ℝ} (hx : 0 ≤ x) (degree : ℕ) :
    expPoly x degree ≤ Real.exp x :=
  Real.sum_le_exp_of_nonneg hx (degree + 1)

def entropyRatio : ℝ := 4 / ((27 / 50 : ℝ) * (1 / 1000) * (1 / 20))

theorem taylor_four_eighty : entropyRatio < expPoly 80 4 := by
  norm_num [entropyRatio, expPoly, Finset.sum_range_succ, Nat.factorial]

set_option maxRecDepth 4096 in
theorem taylor_sixty_thirtyfour : (10 : ℝ) ^ 14 < expPoly 34 60 := by
  norm_num [expPoly, Finset.sum_range_succ, Nat.factorial]

theorem taylor_twenty_eight : (2800 : ℝ) < expPoly 8 20 := by
  norm_num [expPoly, Finset.sum_range_succ, Nat.factorial]

theorem exp_eight_gt : (2800 : ℝ) < Real.exp 8 :=
  lt_of_lt_of_le taylor_twenty_eight (expPoly_le_exp (by norm_num) 20)

theorem exp_thirtyfour_gt : (10 : ℝ) ^ 14 < Real.exp 34 :=
  lt_of_lt_of_le taylor_sixty_thirtyfour (expPoly_le_exp (by norm_num) 60)

theorem log_entropyRatio_lt : Real.log entropyRatio < 80 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num [entropyRatio])).2
  exact lt_of_lt_of_le taylor_four_eighty (expPoly_le_exp (by norm_num) 4)

theorem rational_error_bound :
    4 / (19 / 100 : ℝ) ^ 2 * ((17 / 25 : ℝ) / 4130) ^ 2 +
      8 / (19 / 100 : ℝ) ^ 2 / (10 : ℝ) ^ 14 < (Certificate.Cbar : ℝ) := by
  norm_num [Certificate.Cbar]

def largeNConstant : ℝ :=
  4 / (19 / 100 : ℝ) ^ 2 * ((17 / 25 : ℝ) / 4130) ^ 2 +
    8 / (19 / 100 : ℝ) ^ 2 * Real.exp (sigma * (Real.log entropyRatio - 6880))

/-- The Taylor certificates are connected to the actual real exponential. -/
theorem largeNConstant_lt_Cbar : largeNConstant < (Certificate.Cbar : ℝ) := by
  have hexponent : sigma * (Real.log entropyRatio - 6880) < -34 := by
    have hlog := log_entropyRatio_lt
    unfold sigma
    linarith
  have hexp := Real.exp_lt_exp.mpr hexponent
  have hinv : Real.exp (-34) < 1 / (10 : ℝ) ^ 14 := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_lt_one_div_of_lt (by norm_num) exp_thirtyfour_gt
  have herror := lt_trans hexp hinv
  have hrat := rational_error_bound
  unfold largeNConstant
  norm_num only [div_pow, one_pow] at *
  nlinarith

end Endgame

theorem c_pos : 0 < c := Real.exp_pos _

theorem c_lt_one : c < 1 := by
  unfold c
  exact Real.exp_lt_one_iff.mpr (by norm_num)

end LonelyRunnerNew
