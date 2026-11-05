import LonelyRunnerNew.BootstrapInterval

noncomputable section
namespace LonelyRunnerNew.BootstrapInterval

private theorem real_certificate (S T u v : ℚ)
    (h : 0<S ∧ S≤1/2 ∧ 0≤u ∧ S≤u^2 ∧ 0≤v ∧ (1-S)^3≤v^2 ∧
      0<(1-v)/S-u ∧
      16*BootstrapEndpoint.lambdaUpper^4*(1+(1-2*S)^3) ≤
        T*(1-BootstrapEndpoint.lambdaUpper^4)*((1-v)/S-u)^4) :
    (0:ℝ)<S ∧ (S:ℝ)≤1/2 ∧ (0:ℝ)≤u ∧ (S:ℝ)≤(u:ℝ)^2 ∧ (0:ℝ)≤v ∧
      (1-(S:ℝ))^3≤(v:ℝ)^2 ∧ 0<(1-(v:ℝ))/(S:ℝ)-(u:ℝ) ∧
      16*(BootstrapEndpoint.lambdaUpper:ℝ)^4*(1+(1-2*(S:ℝ))^3) ≤
        (T:ℝ)*(1-(BootstrapEndpoint.lambdaUpper:ℝ)^4)*((1-(v:ℝ))/(S:ℝ)-(u:ℝ))^4 := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact_mod_cast h.1
  · have hh : (S:ℝ) ≤ ((1/2:ℚ):ℝ) := by exact_mod_cast h.2.1
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hh
  · exact_mod_cast h.2.2.1
  · exact_mod_cast h.2.2.2.1
  · exact_mod_cast h.2.2.2.2.1
  · exact_mod_cast h.2.2.2.2.2.1
  · exact_mod_cast h.2.2.2.2.2.2.1
  · exact_mod_cast h.2.2.2.2.2.2.2

theorem rational_step_0 {lam z : ℝ}
    (hl0 : 0 ≤ lam) (hlU : lam ≤ (BootstrapEndpoint.lambdaUpper:ℝ))
    (hz : 0 ≤ z) (hzS : z ≤ (357/1000:ℝ)) (hiter : iterationInequality lam z) :
    z ≤ (171/500:ℝ) := by
  have hc := real_certificate (357/1000) (171/500) (5974947699/10000000000) (1031208431/2000000000) BootstrapEndpoint.step_0
  push_cast at hc
  apply certified_step (u := (5974947699/10000000000:ℝ)) (v := (1031208431/2000000000:ℝ)) hl0 hlU hz hzS
  · exact_mod_cast hc.1
  · exact_mod_cast hc.2.1
  · norm_num
  · exact_mod_cast hc.2.2.1
  · exact_mod_cast hc.2.2.2.1
  · exact_mod_cast hc.2.2.2.2.1
  · exact_mod_cast hc.2.2.2.2.2.1
  · exact_mod_cast hc.2.2.2.2.2.2.1
  · exact_mod_cast hc.2.2.2.2.2.2.2
  · exact hiter

theorem rational_step_1 {lam z : ℝ}
    (hl0 : 0 ≤ lam) (hlU : lam ≤ (BootstrapEndpoint.lambdaUpper:ℝ))
    (hz : 0 ≤ z) (hzS : z ≤ (171/500:ℝ)) (hiter : iterationInequality lam z) :
    z ≤ (39/125:ℝ) := by
  have hc := real_certificate (171/500) (39/125) (5848076607/10000000000) (1067502341/2000000000) BootstrapEndpoint.step_1
  push_cast at hc
  apply certified_step (u := (5848076607/10000000000:ℝ)) (v := (1067502341/2000000000:ℝ)) hl0 hlU hz hzS
  · exact_mod_cast hc.1
  · exact_mod_cast hc.2.1
  · norm_num
  · exact_mod_cast hc.2.2.1
  · exact_mod_cast hc.2.2.2.1
  · exact_mod_cast hc.2.2.2.2.1
  · exact_mod_cast hc.2.2.2.2.2.1
  · exact_mod_cast hc.2.2.2.2.2.2.1
  · exact_mod_cast hc.2.2.2.2.2.2.2
  · exact hiter

theorem rational_step_2 {lam z : ℝ}
    (hl0 : 0 ≤ lam) (hlU : lam ≤ (BootstrapEndpoint.lambdaUpper:ℝ))
    (hz : 0 ≤ z) (hzS : z ≤ (39/125:ℝ)) (hiter : iterationInequality lam z) :
    z ≤ (131/500:ℝ) := by
  have hc := real_certificate (39/125) (131/500) (2792848009/5000000000) (5706668661/10000000000) BootstrapEndpoint.step_2
  push_cast at hc
  apply certified_step (u := (2792848009/5000000000:ℝ)) (v := (5706668661/10000000000:ℝ)) hl0 hlU hz hzS
  · exact_mod_cast hc.1
  · exact_mod_cast hc.2.1
  · norm_num
  · exact_mod_cast hc.2.2.1
  · exact_mod_cast hc.2.2.2.1
  · exact_mod_cast hc.2.2.2.2.1
  · exact_mod_cast hc.2.2.2.2.2.1
  · exact_mod_cast hc.2.2.2.2.2.2.1
  · exact_mod_cast hc.2.2.2.2.2.2.2
  · exact hiter

theorem rational_step_3 {lam z : ℝ}
    (hl0 : 0 ≤ lam) (hlU : lam ≤ (BootstrapEndpoint.lambdaUpper:ℝ))
    (hz : 0 ≤ z) (hzS : z ≤ (131/500:ℝ)) (hiter : iterationInequality lam z) :
    z ≤ (201/1000:ℝ) := by
  have hc := real_certificate (131/500) (201/1000) (5118593557/10000000000) (6339931167/10000000000) BootstrapEndpoint.step_3
  push_cast at hc
  apply certified_step (u := (5118593557/10000000000:ℝ)) (v := (6339931167/10000000000:ℝ)) hl0 hlU hz hzS
  · exact_mod_cast hc.1
  · exact_mod_cast hc.2.1
  · norm_num
  · exact_mod_cast hc.2.2.1
  · exact_mod_cast hc.2.2.2.1
  · exact_mod_cast hc.2.2.2.2.1
  · exact_mod_cast hc.2.2.2.2.2.1
  · exact_mod_cast hc.2.2.2.2.2.2.1
  · exact_mod_cast hc.2.2.2.2.2.2.2
  · exact hiter

theorem rational_step_4 {lam z : ℝ}
    (hl0 : 0 ≤ lam) (hlU : lam ≤ (BootstrapEndpoint.lambdaUpper:ℝ))
    (hz : 0 ≤ z) (hzS : z ≤ (201/1000:ℝ)) (hiter : iterationInequality lam z) :
    z ≤ (3/20:ℝ) := by
  have hc := real_certificate (201/1000) (3/20) (896660471/2000000000) (3571002657/5000000000) BootstrapEndpoint.step_4
  push_cast at hc
  apply certified_step (u := (896660471/2000000000:ℝ)) (v := (3571002657/5000000000:ℝ)) hl0 hlU hz hzS
  · exact_mod_cast hc.1
  · exact_mod_cast hc.2.1
  · norm_num
  · exact_mod_cast hc.2.2.1
  · exact_mod_cast hc.2.2.2.1
  · exact_mod_cast hc.2.2.2.2.1
  · exact_mod_cast hc.2.2.2.2.2.1
  · exact_mod_cast hc.2.2.2.2.2.2.1
  · exact_mod_cast hc.2.2.2.2.2.2.2
  · exact hiter

theorem rational_step_5 {lam z : ℝ}
    (hl0 : 0 ≤ lam) (hlU : lam ≤ (BootstrapEndpoint.lambdaUpper:ℝ))
    (hz : 0 ≤ z) (hzS : z ≤ (3/20:ℝ)) (hiter : iterationInequality lam z) :
    z ≤ (121/1000:ℝ) := by
  have hc := real_certificate (3/20) (121/1000) (3872983347/10000000000) (7836612789/10000000000) BootstrapEndpoint.step_5
  push_cast at hc
  apply certified_step (u := (3872983347/10000000000:ℝ)) (v := (7836612789/10000000000:ℝ)) hl0 hlU hz hzS
  · exact_mod_cast hc.1
  · exact_mod_cast hc.2.1
  · norm_num
  · exact_mod_cast hc.2.2.1
  · exact_mod_cast hc.2.2.2.1
  · exact_mod_cast hc.2.2.2.2.1
  · exact_mod_cast hc.2.2.2.2.2.1
  · exact_mod_cast hc.2.2.2.2.2.2.1
  · exact_mod_cast hc.2.2.2.2.2.2.2
  · exact hiter

theorem six_steps {lam z : ℝ}
    (hl0 : 0 ≤ lam) (hlU : lam ≤ (BootstrapEndpoint.lambdaUpper:ℝ))
    (hz : 0 ≤ z) (hzS : z ≤ (357/1000:ℝ)) (hiter : iterationInequality lam z) :
    z ≤ (121/1000:ℝ) := by
  have h0 := rational_step_0 hl0 hlU hz hzS hiter
  have h1 := rational_step_1 hl0 hlU hz h0 hiter
  have h2 := rational_step_2 hl0 hlU hz h1 hiter
  have h3 := rational_step_3 hl0 hlU hz h2 hiter
  have h4 := rational_step_4 hl0 hlU hz h3 hiter
  exact rational_step_5 hl0 hlU hz h4 hiter

end LonelyRunnerNew.BootstrapInterval

