import LonelyRunnerNew.SmallPrimeAnalytic

namespace LonelyRunnerNew.Certificate
set_option maxRecDepth 32768
set_option maxHeartbeats 0
set_option exponentiation.threshold 4096

def analyticWitness_0 : AnalyticWitness :=
  ⟨(22415207331540519833139/500000000000000000000000:ℚ),(44830414663081039666279/1000000000000000000000000:ℚ),(105865970291544864849259/500000000000000000000000:ℚ),2⟩
theorem analyticRow_0_checked : (analyticWitness_0).Valid (rows[0]'(by decide)) := by decide +kernel

def analyticWitness_1 : AnalyticWitness :=
  ⟨(20906427881370744076293/250000000000000000000000:ℚ),(83625711525482976305173/1000000000000000000000000:ℚ),(72295276265760863465301/250000000000000000000000:ℚ),1⟩
theorem analyticRow_1_checked : (analyticWitness_1).Valid (rows[1]'(by decide)) := by decide +kernel

def analyticWitness_2 : AnalyticWitness :=
  ⟨(143328052898360182369283/1000000000000000000000000:ℚ),(35832013224590045592321/250000000000000000000000:ℚ),(378586915910151578457101/1000000000000000000000000:ℚ),1⟩
theorem analyticRow_2_checked : (analyticWitness_2).Valid (rows[2]'(by decide)) := by decide +kernel

def analyticWitness_3 : AnalyticWitness :=
  ⟨(188782327893425917395971/1000000000000000000000000:ℚ),(47195581973356479348993/250000000000000000000000:ℚ),(108622720889043834691533/250000000000000000000000:ℚ),1⟩
theorem analyticRow_3_checked : (analyticWitness_3).Valid (rows[3]'(by decide)) := by decide +kernel

def analyticWitness_4 : AnalyticWitness :=
  ⟨(128842134060807969327093/500000000000000000000000:ℚ),(257684268121615938654187/1000000000000000000000000:ℚ),(253813055279676235695063/500000000000000000000000:ℚ),0⟩
theorem analyticRow_4_checked : (analyticWitness_4).Valid (rows[4]'(by decide)) := by decide +kernel

end LonelyRunnerNew.Certificate
