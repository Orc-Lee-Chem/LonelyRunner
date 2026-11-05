import LonelyRunnerNew.SmallPrimeAnalytic

namespace LonelyRunnerNew.Certificate
set_option maxRecDepth 32768
set_option maxHeartbeats 0
set_option exponentiation.threshold 4096

def analyticWitness_5 : AnalyticWitness :=
  ⟨(14228450415769221196379/50000000000000000000000:ℚ),(284569008315384423927581/1000000000000000000000000:ℚ),(21338003967208720112923/40000000000000000000000:ℚ),0⟩
theorem analyticRow_5_checked : (analyticWitness_5).Valid (rows[5]'(by decide)) := by decide +kernel

def analyticWitness_6 : AnalyticWitness :=
  ⟨(5153699646370915426689/15625000000000000000000:ℚ),(329836777367738587308097/1000000000000000000000000:ℚ),(287157090008125425053859/500000000000000000000000:ℚ),0⟩
theorem analyticRow_6_checked : (analyticWitness_6).Valid (rows[6]'(by decide)) := by decide +kernel

def analyticWitness_7 : AnalyticWitness :=
  ⟨(348645013453538719758983/1000000000000000000000000:ℚ),(43580626681692339969873/125000000000000000000000:ℚ),(295230847580981415201181/500000000000000000000000:ℚ),0⟩
theorem analyticRow_7_checked : (analyticWitness_7).Valid (rows[7]'(by decide)) := by decide +kernel

def analyticWitness_8 : AnalyticWitness :=
  ⟨(95546776480428068581793/250000000000000000000000:ℚ),(382187105921712274327173/1000000000000000000000000:ℚ),(309106416110096408625941/500000000000000000000000:ℚ),0⟩
theorem analyticRow_8_checked : (analyticWitness_8).Valid (rows[8]'(by decide)) := by decide +kernel

def analyticWitness_9 : AnalyticWitness :=
  ⟨(106379743882657263822757/250000000000000000000000:ℚ),(425518975530629055291029/1000000000000000000000000:ℚ),(326159077572060323949691/500000000000000000000000:ℚ),0⟩
theorem analyticRow_9_checked : (analyticWitness_9).Valid (rows[9]'(by decide)) := by decide +kernel

end LonelyRunnerNew.Certificate
