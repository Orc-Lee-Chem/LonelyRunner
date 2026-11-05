import LonelyRunnerNew.SmallPrimeAnalytic

namespace LonelyRunnerNew.Certificate
set_option maxRecDepth 32768
set_option maxHeartbeats 0
set_option exponentiation.threshold 4096

def analyticWitness_25 : AnalyticWitness :=
  ⟨(334079619502688183820663/500000000000000000000000:ℚ),(668159239005376367641329/1000000000000000000000000:ℚ),(817410080073261861192097/1000000000000000000000000:ℚ),0⟩
theorem analyticRow_25_checked : (analyticWitness_25).Valid (rows[25]'(by decide)) := by decide +kernel

def analyticWitness_26 : AnalyticWitness :=
  ⟨(336651956358968567551531/500000000000000000000000:ℚ),(134660782543587427020613/200000000000000000000000:ℚ),(410275490590754499405723/500000000000000000000000:ℚ),0⟩
theorem analyticRow_26_checked : (analyticWitness_26).Valid (rows[26]'(by decide)) := by decide +kernel

def analyticWitness_27 : AnalyticWitness :=
  ⟨(681163606217581346286989/1000000000000000000000000:ℚ),(136232721243516269257399/200000000000000000000000:ℚ),(20633159086431441107951/25000000000000000000000:ℚ),0⟩
theorem analyticRow_27_checked : (analyticWitness_27).Valid (rows[27]'(by decide)) := by decide +kernel

def analyticWitness_28 : AnalyticWitness :=
  ⟨(683863149001561743011413/1000000000000000000000000:ℚ),(683863149001561743011419/1000000000000000000000000:ℚ),(206740046465597973025101/250000000000000000000000:ℚ),0⟩
theorem analyticRow_28_checked : (analyticWitness_28).Valid (rows[28]'(by decide)) := by decide +kernel

def analyticWitness_29 : AnalyticWitness :=
  ⟨(691468666020611007579861/1000000000000000000000000:ℚ),(691468666020611007579871/1000000000000000000000000:ℚ),(10394324367928897279067/12500000000000000000000:ℚ),0⟩
theorem analyticRow_29_checked : (analyticWitness_29).Valid (rows[29]'(by decide)) := by decide +kernel

end LonelyRunnerNew.Certificate
