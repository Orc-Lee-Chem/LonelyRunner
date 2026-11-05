import LonelyRunnerNew.LCNumericIntegerCheck
import LonelyRunnerNew.LCNumericFirstBand

namespace LonelyRunnerNew.LCNumeric.Data
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
theorem steps_0_fast : ∀ d ∈ steps_0,∀ b ∈ boxes,d.FastAccepts b := by decide +kernel
end LonelyRunnerNew.LCNumeric.Data
