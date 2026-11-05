import LonelyRunnerNew.GeometricTransfer
import LonelyRunnerNew.RadiusExpansion

namespace LonelyRunnerNew

/-- A proved outer assembly, with every remaining mathematical input explicit.
This is an intermediate theorem and does not discharge the final task. -/
theorem main_of_separated_control (hS : spilloverInput) (hF : forestInput)
    (hSep : separatedControl (Real.exp 6880) (17 / 100)) : mainStatement := by
  intro V hV
  exact radius_expansion V hV c_pos c_lt_one
    (gap_gt_c_of_separated_control hS hF hSep V hV)

end LonelyRunnerNew
