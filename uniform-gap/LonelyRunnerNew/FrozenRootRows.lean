import LonelyRunnerNew.CertificateData
import LonelyRunnerNew.RationalAnalysis
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime

namespace LonelyRunnerNew.Certificate

def RootRowChecked (r : PrimeRow) : Prop :=
  Nat.Prime r.prime ∧ 0 < r.exponentDenominator ∧ 0 < r.lambdaUpper ∧ r.lambdaUpper < 1 ∧
    1 ≤ r.lambdaUpper ^ r.exponentDenominator * (r.prime:ℚ) ^ r.exponentNumerator ∧
    (r.exponentNumerator:ℚ)/r.exponentDenominator = (50/201:ℚ)-r.tau

set_option maxRecDepth 16384 in
set_option maxHeartbeats 16000000 in
set_option exponentiation.threshold 4096 in
theorem frozen_root_rows_checked : ∀ r ∈ rows, RootRowChecked r := by
  intro r hr
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [RootRowChecked]

theorem frozen_moment_lambda_bound (r : PrimeRow) (hr : r ∈ rows) :
    (r.prime:ℝ)^(-1/q+(r.tau:ℝ)) ≤ (r.lambdaUpper:ℝ) := by
  obtain ⟨hp,hb,hl,hlt,hcert,he⟩ := frozen_root_rows_checked r hr
  have hbR := RationalAnalysis.root_bound (p := (r.prime:ℝ)) (lam := (r.lambdaUpper:ℝ)) (by exact_mod_cast hp.pos)
    (by exact_mod_cast hl) r.exponentNumerator r.exponentDenominator hb (by exact_mod_cast hcert)
  have hreal : (r.exponentNumerator:ℝ)/r.exponentDenominator = (50/201:ℝ)-(r.tau:ℝ) := by
    have he' := congrArg (fun z : ℚ => (z:ℝ)) he
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_sub, Rat.cast_ofNat] using he'
  have hneg : -(r.exponentNumerator:ℝ)/r.exponentDenominator = -1/q+(r.tau:ℝ) := by
    rw [neg_div,hreal]
    norm_num [q]
    <;> ring
  rw [hneg] at hbR
  exact hbR

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem real_scale_root_checked : (1:ℚ) ≤ realLambdaUpper^201*(2:ℚ)^50 := by
  norm_num [realLambdaUpper]

theorem real_scale_lambda_bound : (2:ℝ)^(-(50:ℝ)/201) ≤ (realLambdaUpper:ℝ) := by
  exact RationalAnalysis.root_bound (by norm_num) (by norm_num [realLambdaUpper]) 50 201
    (by decide) (by exact_mod_cast real_scale_root_checked)

end LonelyRunnerNew.Certificate
