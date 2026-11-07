import LonelyRunnerNew.Targets
import Mathlib.Tactic.NormNum

namespace LonelyRunnerNew
namespace Certificate

theorem tbar_pos : 0 < tbar := by
  norm_num [tbar, Dbar]

theorem wbar_lt_delta : (wbar : ℝ) < 17 / 100 := by
  norm_num [wbar]

theorem sqrtHalfUpper_sq : (1 / 2 : ℚ) < sqrtHalfUpper ^ 2 := by
  norm_num [sqrtHalfUpper]

end Certificate

theorem rational_endgame : rationalEndgameTarget := by
  norm_num [rationalEndgameTarget, Certificate.Cbar, Certificate.Bbar,
    Certificate.wbar, Certificate.tbar, Certificate.Dbar]

end LonelyRunnerNew
