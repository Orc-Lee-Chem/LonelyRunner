import LonelyRunnerNew.SmallPrimeAnalytic

namespace LonelyRunnerNew.Certificate
set_option maxRecDepth 32768
set_option maxHeartbeats 0
set_option exponentiation.threshold 4096

def analyticWitness_30 : AnalyticWitness :=
  ⟨(715782867999105275754993/1000000000000000000000000:ℚ),(357891433999552637877517/500000000000000000000000:ℚ),(105754939896375620481343/125000000000000000000000:ℚ),0⟩
theorem analyticRow_30_checked : (analyticWitness_30).Valid (rows[30]'(by decide)) := by decide +kernel

def analyticWitness_31 : AnalyticWitness :=
  ⟨(722790448912409531749243/1000000000000000000000000:ℚ),(722790448912409531749307/1000000000000000000000000:ℚ),(850170835133980311575471/1000000000000000000000000:ℚ),0⟩
theorem analyticRow_31_checked : (analyticWitness_31).Valid (rows[31]'(by decide)) := by decide +kernel

def analyticWitness_32 : AnalyticWitness :=
  ⟨(73187775961323848239337/100000000000000000000000:ℚ),(365938879806619241196741/500000000000000000000000:ℚ),(85549854448341318168263/100000000000000000000000:ℚ),0⟩
theorem analyticRow_32_checked : (analyticWitness_32).Valid (rows[32]'(by decide)) := by decide +kernel

def analyticWitness_33 : AnalyticWitness :=
  ⟨(734033684580137727904781/1000000000000000000000000:ℚ),(183508421145034431976227/250000000000000000000000:ℚ),(53547353626404012979377/62500000000000000000000:ℚ),0⟩
theorem analyticRow_33_checked : (analyticWitness_33).Valid (rows[33]'(by decide)) := by decide +kernel

end LonelyRunnerNew.Certificate
