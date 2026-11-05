import LonelyRunnerNew.LCNumericRawCheck
import LonelyRunnerNew.LCNumericFirstBand
namespace LonelyRunnerNew.LCNumeric.Data
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
theorem steps_0_integer : ∀ d ∈ steps_0,∀ b ∈ boxes,d.IntegerAccepts b := by decide +kernel
end LonelyRunnerNew.LCNumeric.Data
