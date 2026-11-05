import LonelyRunnerNew.SmallPrimeAnalytic

namespace LonelyRunnerNew.Certificate
set_option maxRecDepth 32768
set_option maxHeartbeats 0
set_option exponentiation.threshold 4096

def analyticWitness_15 : AnalyticWitness :=
  ⟨(21648954911707092149453/40000000000000000000000:ℚ),(270611936396338651868163/500000000000000000000000:ℚ),(73567919149088164469733/100000000000000000000000:ℚ),0⟩
theorem analyticRow_15_checked : (analyticWitness_15).Valid (rows[15]'(by decide)) := by decide +kernel

def analyticWitness_16 : AnalyticWitness :=
  ⟨(70241161191659470502529/125000000000000000000000:ℚ),(561929289533275764020233/1000000000000000000000000:ℚ),(93702428724966536017827/125000000000000000000000:ℚ),0⟩
theorem analyticRow_16_checked : (analyticWitness_16).Valid (rows[16]'(by decide)) := by decide +kernel

def analyticWitness_17 : AnalyticWitness :=
  ⟨(568568624000089813986853/1000000000000000000000000:ℚ),(284284312000044906993427/500000000000000000000000:ℚ),(94254361968035215932621/125000000000000000000000:ℚ),0⟩
theorem analyticRow_17_checked : (analyticWitness_17).Valid (rows[17]'(by decide)) := by decide +kernel

def analyticWitness_18 : AnalyticWitness :=
  ⟨(585728325089288803960811/1000000000000000000000000:ℚ),(146432081272322200990203/250000000000000000000000:ℚ),(765328899943866489268641/1000000000000000000000000:ℚ),0⟩
theorem analyticRow_18_checked : (analyticWitness_18).Valid (rows[18]'(by decide)) := by decide +kernel

def analyticWitness_19 : AnalyticWitness :=
  ⟨(23921904981604994001969/40000000000000000000000:ℚ),(299023812270062425024613/500000000000000000000000:ℚ),(24166730919592034756599/31250000000000000000000:ℚ),0⟩
theorem analyticRow_19_checked : (analyticWitness_19).Valid (rows[19]'(by decide)) := by decide +kernel

end LonelyRunnerNew.Certificate
