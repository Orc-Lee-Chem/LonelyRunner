import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.IntervalCases
import LonelyRunnerNew.RationalAnalysis

namespace LonelyRunnerNew.BootstrapEndpoint
def lambdaUpper : ℚ := 144004613283/500000000000
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem lambda_root_certificate : 1 ≤ lambdaUpper^201*(149:ℚ)^50 := by norm_num [lambdaUpper]

-- Exact endpoint data for step 0; no analytic bootstrap implication is asserted.
theorem step_0 : (0:ℚ)<(357/1000:ℚ) ∧ (357/1000:ℚ)≤1/2 ∧
    0≤(5974947699/10000000000:ℚ) ∧ (357/1000:ℚ)≤(5974947699/10000000000:ℚ)^2 ∧
    0≤(1031208431/2000000000:ℚ) ∧ (1-(357/1000:ℚ))^3≤(1031208431/2000000000:ℚ)^2 ∧
    0<((1-(1031208431/2000000000:ℚ))/(357/1000:ℚ)-(5974947699/10000000000:ℚ)) ∧
    16*lambdaUpper^4*(1+(1-2*(357/1000:ℚ))^3) ≤
      (171/500:ℚ)*(1-lambdaUpper^4)*((1-(1031208431/2000000000:ℚ))/(357/1000:ℚ)-(5974947699/10000000000:ℚ))^4 := by
  norm_num [lambdaUpper]

-- Exact endpoint data for step 1; no analytic bootstrap implication is asserted.
theorem step_1 : (0:ℚ)<(171/500:ℚ) ∧ (171/500:ℚ)≤1/2 ∧
    0≤(5848076607/10000000000:ℚ) ∧ (171/500:ℚ)≤(5848076607/10000000000:ℚ)^2 ∧
    0≤(1067502341/2000000000:ℚ) ∧ (1-(171/500:ℚ))^3≤(1067502341/2000000000:ℚ)^2 ∧
    0<((1-(1067502341/2000000000:ℚ))/(171/500:ℚ)-(5848076607/10000000000:ℚ)) ∧
    16*lambdaUpper^4*(1+(1-2*(171/500:ℚ))^3) ≤
      (39/125:ℚ)*(1-lambdaUpper^4)*((1-(1067502341/2000000000:ℚ))/(171/500:ℚ)-(5848076607/10000000000:ℚ))^4 := by
  norm_num [lambdaUpper]

-- Exact endpoint data for step 2; no analytic bootstrap implication is asserted.
theorem step_2 : (0:ℚ)<(39/125:ℚ) ∧ (39/125:ℚ)≤1/2 ∧
    0≤(2792848009/5000000000:ℚ) ∧ (39/125:ℚ)≤(2792848009/5000000000:ℚ)^2 ∧
    0≤(5706668661/10000000000:ℚ) ∧ (1-(39/125:ℚ))^3≤(5706668661/10000000000:ℚ)^2 ∧
    0<((1-(5706668661/10000000000:ℚ))/(39/125:ℚ)-(2792848009/5000000000:ℚ)) ∧
    16*lambdaUpper^4*(1+(1-2*(39/125:ℚ))^3) ≤
      (131/500:ℚ)*(1-lambdaUpper^4)*((1-(5706668661/10000000000:ℚ))/(39/125:ℚ)-(2792848009/5000000000:ℚ))^4 := by
  norm_num [lambdaUpper]

-- Exact endpoint data for step 3; no analytic bootstrap implication is asserted.
theorem step_3 : (0:ℚ)<(131/500:ℚ) ∧ (131/500:ℚ)≤1/2 ∧
    0≤(5118593557/10000000000:ℚ) ∧ (131/500:ℚ)≤(5118593557/10000000000:ℚ)^2 ∧
    0≤(6339931167/10000000000:ℚ) ∧ (1-(131/500:ℚ))^3≤(6339931167/10000000000:ℚ)^2 ∧
    0<((1-(6339931167/10000000000:ℚ))/(131/500:ℚ)-(5118593557/10000000000:ℚ)) ∧
    16*lambdaUpper^4*(1+(1-2*(131/500:ℚ))^3) ≤
      (201/1000:ℚ)*(1-lambdaUpper^4)*((1-(6339931167/10000000000:ℚ))/(131/500:ℚ)-(5118593557/10000000000:ℚ))^4 := by
  norm_num [lambdaUpper]

-- Exact endpoint data for step 4; no analytic bootstrap implication is asserted.
theorem step_4 : (0:ℚ)<(201/1000:ℚ) ∧ (201/1000:ℚ)≤1/2 ∧
    0≤(896660471/2000000000:ℚ) ∧ (201/1000:ℚ)≤(896660471/2000000000:ℚ)^2 ∧
    0≤(3571002657/5000000000:ℚ) ∧ (1-(201/1000:ℚ))^3≤(3571002657/5000000000:ℚ)^2 ∧
    0<((1-(3571002657/5000000000:ℚ))/(201/1000:ℚ)-(896660471/2000000000:ℚ)) ∧
    16*lambdaUpper^4*(1+(1-2*(201/1000:ℚ))^3) ≤
      (3/20:ℚ)*(1-lambdaUpper^4)*((1-(3571002657/5000000000:ℚ))/(201/1000:ℚ)-(896660471/2000000000:ℚ))^4 := by
  norm_num [lambdaUpper]

-- Exact endpoint data for step 5; no analytic bootstrap implication is asserted.
theorem step_5 : (0:ℚ)<(3/20:ℚ) ∧ (3/20:ℚ)≤1/2 ∧
    0≤(3872983347/10000000000:ℚ) ∧ (3/20:ℚ)≤(3872983347/10000000000:ℚ)^2 ∧
    0≤(7836612789/10000000000:ℚ) ∧ (1-(3/20:ℚ))^3≤(7836612789/10000000000:ℚ)^2 ∧
    0<((1-(7836612789/10000000000:ℚ))/(3/20:ℚ)-(3872983347/10000000000:ℚ)) ∧
    16*lambdaUpper^4*(1+(1-2*(3/20:ℚ))^3) ≤
      (121/1000:ℚ)*(1-lambdaUpper^4)*((1-(7836612789/10000000000:ℚ))/(3/20:ℚ)-(3872983347/10000000000:ℚ))^4 := by
  norm_num [lambdaUpper]

theorem last_below_one_eighth : (121/1000:ℚ)<1/8 := by norm_num

theorem prime_ge_149 {p : ℕ} (hp : Nat.Prime p) (h : 142 < p) : 149 ≤ p := by
  by_contra hn
  have hh : 143 ≤ p ∧ p ≤ 148 := by omega
  interval_cases p <;> norm_num at hp

theorem actual_lambda_upper {p : ℕ} (hp : Nat.Prime p) (h : 142 < p) :
    (p:ℝ)^(-1/q) ≤ (lambdaUpper:ℝ) := by
  have hgap : (149:ℚ) ≤ p := by exact_mod_cast prime_ge_149 hp h
  have hpow := pow_le_pow_left₀ (by norm_num : (0:ℚ)≤149) hgap 50
  have hcert : (1:ℚ)≤lambdaUpper^201*(p:ℚ)^50 :=
    lambda_root_certificate.trans (mul_le_mul_of_nonneg_left hpow
      (pow_nonneg (by norm_num [lambdaUpper] : (0:ℚ)≤lambdaUpper) _))
  have hr := RationalAnalysis.root_bound (p := (p:ℝ)) (lam := (lambdaUpper:ℝ))
    (by exact_mod_cast hp.pos) (by norm_num [lambdaUpper]) 50 201
    (by decide) (by exact_mod_cast hcert)
  convert hr using 1 <;> norm_num [q]

end LonelyRunnerNew.BootstrapEndpoint
