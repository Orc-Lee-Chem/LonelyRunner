import LonelyRunnerNew.SmallPrimeAnalytic

namespace LonelyRunnerNew.Certificate
set_option maxRecDepth 32768
set_option maxHeartbeats 0
set_option exponentiation.threshold 4096

def analyticWitness_10 : AnalyticWitness :=
  ⟨(218681772225919760356447/500000000000000000000000:ℚ),(87472708890367904142579/200000000000000000000000:ℚ),(661334669023059398774967/1000000000000000000000000:ℚ),0⟩
theorem analyticRow_10_checked : (analyticWitness_10).Valid (rows[10]'(by decide)) := by decide +kernel

def analyticWitness_11 : AnalyticWitness :=
  ⟨(14708651945161486350317/31250000000000000000000:ℚ),(94135372449033512642029/200000000000000000000000:ℚ),(42878683435306007466441/62500000000000000000000:ℚ),0⟩
theorem analyticRow_11_checked : (analyticWitness_11).Valid (rows[11]'(by decide)) := by decide +kernel

def analyticWitness_12 : AnalyticWitness :=
  ⟨(122861961410863914685997/250000000000000000000000:ℚ),(491447845643455658743989/1000000000000000000000000:ℚ),(70103341264411617111989/100000000000000000000000:ℚ),0⟩
theorem analyticRow_12_checked : (analyticWitness_12).Valid (rows[12]'(by decide)) := by decide +kernel

def analyticWitness_13 : AnalyticWitness :=
  ⟨(499622104920488141492407/1000000000000000000000000:ℚ),(62452763115061017686551/125000000000000000000000:ℚ),(28273580740203053141613/40000000000000000000000:ℚ),0⟩
theorem analyticRow_13_checked : (analyticWitness_13).Valid (rows[13]'(by decide)) := by decide +kernel

def analyticWitness_14 : AnalyticWitness :=
  ⟨(103436801239971722971043/200000000000000000000000:ℚ),(32324000387491163428451/62500000000000000000000:ℚ),(89894383010690889646567/125000000000000000000000:ℚ),0⟩
theorem analyticRow_14_checked : (analyticWitness_14).Valid (rows[14]'(by decide)) := by decide +kernel

end LonelyRunnerNew.Certificate
