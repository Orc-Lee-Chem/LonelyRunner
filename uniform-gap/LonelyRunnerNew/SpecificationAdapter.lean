import LonelyRunnerSpec.V1
import LonelyRunnerNew.TargetSemantics

namespace LonelyRunnerNew

theorem internalStatement_iff_frozen : mainStatement ↔ LonelyRunnerSpec.V1.Statement :=
  mainStatement_iff_explicit

/-- This implication is an adapter; it is not a proof of its premise. -/
theorem frozen_uniform_of_explicit (h : LonelyRunnerSpec.V1.Statement) :
    LonelyRunnerSpec.V1.UniformStatement := by
  exact ⟨Real.exp (-6888 : ℝ), Real.exp_pos _, h⟩

end LonelyRunnerNew
