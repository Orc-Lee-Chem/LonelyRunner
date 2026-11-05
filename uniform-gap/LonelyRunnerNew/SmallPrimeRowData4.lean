import LonelyRunnerNew.SmallPrimeAnalytic

namespace LonelyRunnerNew.Certificate
set_option maxRecDepth 32768
set_option maxHeartbeats 0
set_option exponentiation.threshold 4096

def analyticWitness_20 : AnalyticWitness :=
  ⟨(302039806429103155791413/500000000000000000000000:ℚ),(604079612858206311582827/1000000000000000000000000:ℚ),(31089023474099827353241/40000000000000000000000:ℚ),0⟩
theorem analyticRow_20_checked : (analyticWitness_20).Valid (rows[20]'(by decide)) := by decide +kernel

def analyticWitness_21 : AnalyticWitness :=
  ⟨(61954857609607021006087/100000000000000000000000:ℚ),(619548576096070210060871/1000000000000000000000000:ℚ),(157422816147605517298863/200000000000000000000000:ℚ),0⟩
theorem analyticRow_21_checked : (analyticWitness_21).Valid (rows[21]'(by decide)) := by decide +kernel

def analyticWitness_22 : AnalyticWitness :=
  ⟨(314375227320852488917019/500000000000000000000000:ℚ),(15718761366042624445851/25000000000000000000000:ℚ),(792937863039535385909853/1000000000000000000000000:ℚ),0⟩
theorem analyticRow_22_checked : (analyticWitness_22).Valid (rows[22]'(by decide)) := by decide +kernel

def analyticWitness_23 : AnalyticWitness :=
  ⟨(128629579550532962397677/200000000000000000000000:ℚ),(321573948876332405994193/500000000000000000000000:ℚ),(400982511386925954792309/500000000000000000000000:ℚ),0⟩
theorem analyticRow_23_checked : (analyticWitness_23).Valid (rows[23]'(by decide)) := by decide +kernel

def analyticWitness_24 : AnalyticWitness :=
  ⟨(330016463623378362394177/500000000000000000000000:ℚ),(165008231811689181197089/250000000000000000000000:ℚ),(406212052765164984090147/500000000000000000000000:ℚ),0⟩
theorem analyticRow_24_checked : (analyticWitness_24).Valid (rows[24]'(by decide)) := by decide +kernel

end LonelyRunnerNew.Certificate
