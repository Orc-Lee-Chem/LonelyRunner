import LonelyRunnerNew.BootstrapEndpoint
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

noncomputable section

namespace LonelyRunnerNew.BootstrapInterval

def b (z : ℝ) : ℝ := (1-(1-z)^(3/2:ℝ)-z^(3/2:ℝ))/z
def s (z : ℝ) : ℝ := Real.sqrt z + Real.sqrt (1-z)
def H (z : ℝ) : ℝ := b z / (1+(1-2*z)^3)^(1/4:ℝ)

theorem three_halves (x : ℝ) (hx : 0 ≤ x) :
    x^(3/2:ℝ) = (Real.sqrt x)^3 := by
  rw [← Real.rpow_natCast, Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  norm_num

theorem b_identity {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1/2) :
    b z = 2*(1-z)*(s z+2)/(s z+1)^2 := by
  have hy : 0 ≤ 1-z := by linarith
  have hx2 := Real.sq_sqrt hz.le
  have hy2 := Real.sq_sqrt hy
  have hs : 0 < s z+1 := by unfold s; positivity
  have hsum : (Real.sqrt z)^2+(Real.sqrt (1-z))^2=1 := by linarith
  have hf : 1-(Real.sqrt (1-z))^3-(Real.sqrt z)^3 = (s z-1)^2*(s z+2)/2 := by
    unfold s
    nlinarith only [congrArg (fun t : ℝ => t*(Real.sqrt z+Real.sqrt (1-z))) hsum]
  have hlin : (s z-1)*(s z+1) = 2*Real.sqrt z*Real.sqrt (1-z) := by
    unfold s
    nlinarith
  have hsq : (s z-1)^2*(s z+1)^2 = 4*z*(1-z) := by
    calc
      _ = ((s z-1)*(s z+1))^2 := by ring
      _ = (2*Real.sqrt z*Real.sqrt (1-z))^2 := by rw [hlin]
      _ = 4*z*(1-z) := by rw [mul_pow, mul_pow, hx2, hy2]; ring
  unfold b
  rw [three_halves _ hy, three_halves _ hz.le, hf]
  field_simp [hz.ne', hs.ne']
  nlinarith only [congrArg (fun t : ℝ => t*(s z+2)) hsq]

theorem b_pos {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1/2) : 0 < b z := by
  rw [b_identity hz hz1]
  have : 0 < 1-z := by linarith
  unfold s
  positivity

theorem s_monotone : MonotoneOn s (Set.Icc (0:ℝ) (1/2)) := by
  intro x hx y hy hxy
  have hprod : x*(1-x) ≤ y*(1-y) := by nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (show 0 ≤ 1-x-y by linarith [hx.2, hy.2])]
  have hroot := Real.sqrt_le_sqrt hprod
  rw [Real.sqrt_mul hx.1, Real.sqrt_mul hy.1] at hroot
  have hxs := Real.sq_sqrt hx.1
  have hxc := Real.sq_sqrt (show 0 ≤ 1-x by linarith [hx.2])
  have hys := Real.sq_sqrt hy.1
  have hyc := Real.sq_sqrt (show 0 ≤ 1-y by linarith [hy.2])
  have h0 : 0 ≤ s x := by unfold s; positivity
  have h1 : 0 ≤ s y := by unfold s; positivity
  dsimp [s] at *
  nlinarith

theorem first_factor_antitone : AntitoneOn (fun t : ℝ => (t+2)/(t+1)^2) (Set.Ici 0) := by
  intro x hx y hy hxy
  change 0 ≤ x at hx
  change 0 ≤ y at hy
  have hx1 : 0 < x+1 := by linarith [hx]
  have hy1 : 0 < y+1 := by linarith [hy]
  apply (div_le_div_iff₀ (sq_pos_of_pos hy1) (sq_pos_of_pos hx1)).2
  have hf : (x+2)*(y+1)^2-(y+2)*(x+1)^2 = (y-x)*(x*y+2*x+2*y+3) := by ring
  have hn : 0 ≤ (y-x)*(x*y+2*x+2*y+3) := by positivity
  linarith

private theorem rational_factor_monotone :
    MonotoneOn (fun t : ℝ => (1+t)^4/(1+t^3)) (Set.Icc 0 1) := by
  let d : ℝ → ℝ := fun t => (1+t)^3*(4-3*t^2+t^3)/(1+t^3)^2
  apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := d) (convex_Icc 0 1)
  · apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    positivity
  · intro t ht
    have ht0 : 0 ≤ t := (interior_subset ht).1
    have hd : 1+t^3 ≠ 0 := by positivity
    have hh := (((hasDerivAt_id t).const_add 1).pow 4).div
      ((hasDerivAt_id t).pow 3 |>.const_add 1) hd
    simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, mul_one] at hh
    change HasDerivAt (fun u : ℝ => (1+u)^4/(1+u^3))
      ((4*(1+t)^3*(1+t^3)-(1+t)^4*(3*t^2))/(1+t^3)^2) t at hh
    have heq : (4*(1+t)^3*(1+t^3)-(1+t)^4*(3*t^2))/(1+t^3)^2 = d t := by
      dsimp [d]
      field_simp [hd]
      ring
    rw [heq] at hh
    exact hh.hasDerivWithinAt
  · intro t ht
    have ht0 : 0 ≤ t := (interior_subset ht).1
    have ht1 : t ≤ 1 := (interior_subset ht).2
    have hsq : t^2 ≤ 1 := by nlinarith
    have hp : 0 ≤ 4-3*t^2+t^3 := by nlinarith [pow_nonneg ht0 3]
    dsimp [d]
    positivity

theorem second_factor_antitone :
    AntitoneOn (fun z : ℝ => (1-z)/(1+(1-2*z)^3)^(1/4:ℝ)) (Set.Icc 0 (1/2)) := by
  intro x hx y hy hxy
  have htx : 0 ≤ 1-2*x := by linarith [hx.2]
  have hty : 0 ≤ 1-2*y := by linarith [hy.2]
  have hd (z : ℝ) (hz : z ≤ 1/2) : 0 < 1+(1-2*z)^3 := by
    have : 0 ≤ 1-2*z := by linarith
    positivity
  have he (z : ℝ) (hz : z ≤ 1/2) :
      ((1-z)/(1+(1-2*z)^3)^(1/4:ℝ))^4 =
        (1+(1-2*z))^4/(16*(1+(1-2*z)^3)) := by
    have hr : ((1+(1-2*z)^3)^(1/4:ℝ))^4 = 1+(1-2*z)^3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (hd z hz).le]
      norm_num
    rw [div_pow, hr]
    field_simp
    ring
  have hrat := rational_factor_monotone
    (show 1-2*y ∈ Set.Icc (0:ℝ) 1 by constructor <;> linarith [hy.1])
    (show 1-2*x ∈ Set.Icc (0:ℝ) 1 by constructor <;> linarith [hx.1]) (by linarith)
  have hp : ((1-y)/(1+(1-2*y)^3)^(1/4:ℝ))^4 ≤
      ((1-x)/(1+(1-2*x)^3)^(1/4:ℝ))^4 := by
    rw [he y hy.2, he x hx.2]
    simpa only [div_div, mul_comm] using div_le_div_of_nonneg_right hrat (by norm_num : (0:ℝ)≤16)
  apply (pow_le_pow_iff_left₀ _ _ (by decide : (4:ℕ) ≠ 0)).mp hp
  · exact div_nonneg (by linarith [hy.2]) (Real.rpow_nonneg (hd y hy.2).le _)
  · exact div_nonneg (by linarith [hx.2]) (Real.rpow_nonneg (hd x hx.2).le _)

theorem H_antitone : AntitoneOn H (Set.Ioc (0:ℝ) (1/2)) := by
  intro x hx y hy hxy
  have hs := s_monotone ⟨hx.1.le,hx.2⟩ ⟨hy.1.le,hy.2⟩ hxy
  have hf := first_factor_antitone (show 0 ≤ s x by unfold s; positivity)
    (show 0 ≤ s y by unfold s; positivity) hs
  have hg := second_factor_antitone ⟨hx.1.le,hx.2⟩ ⟨hy.1.le,hy.2⟩ hxy
  unfold H
  rw [b_identity hx.1 hx.2, b_identity hy.1 hy.2]
  have hh := mul_le_mul hf hg
    (by
      dsimp only
      exact div_nonneg (by linarith [hy.2]) (Real.rpow_nonneg (by
        have : 0 ≤ 1-2*y := by linarith [hy.2]
        positivity) _))
    (by unfold s; positivity)
  convert mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ)≤2) using 1 <;> ring

theorem quarter_fourth (x : ℝ) (hx : 0 ≤ x) : (x^(1/4:ℝ))^4=x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

theorem three_quarters_fourth (x : ℝ) (hx : 0 ≤ x) : (x^(3/4:ℝ))^4=x^3 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

/-- This is the explicit inequality to be proved from the actual four rectangles.
It is not asserted by definition, and is not an additional state field. -/
def iterationInequality (lam z : ℝ) : Prop :=
  1 ≤ (1-z)^(3/2:ℝ)+z^(3/2:ℝ)+
    (2/(1-lam^4))^(1/4:ℝ)*lam*(2*z)^(3/4:ℝ)*(1+(1-2*z)^3)^(1/4:ℝ)

theorem interval_moment {lam z S : ℝ} (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (hz : 0 < z) (hzS : z ≤ S) (hS : S ≤ 1/2)
    (hiter : iterationInequality lam z) :
    z*(b S)^4*(1-lam^4) ≤ 16*lam^4*(1+(1-2*S)^3) := by
  have hz1 : z ≤ 1/2 := hzS.trans hS
  have hS0 : 0 < S := hz.trans_le hzS
  have hl4 : lam^4 < 1 := by nlinarith [pow_lt_pow_left₀ hl1 hl0 (by decide : (4:ℕ)≠0)]
  have hden : 0 < 1-lam^4 := by linarith
  have hD (u : ℝ) (hu : u ≤ 1/2) : 0 < 1+(1-2*u)^3 := by
    have : 0 ≤ 1-2*u := by linarith
    positivity
  let W := (2/(1-lam^4))^(1/4:ℝ)*lam*(2*z)^(3/4:ℝ)*(1+(1-2*z)^3)^(1/4:ℝ)
  have hzb : z*b z ≤ W := by
    have he : z*b z = 1-(1-z)^(3/2:ℝ)-z^(3/2:ℝ) := by
      unfold b
      field_simp
    unfold iterationInequality at hiter
    dsimp [W]
    linarith
  have hW : W^4 = 16*lam^4*z^3*(1+(1-2*z)^3)/(1-lam^4) := by
    dsimp [W]
    rw [mul_pow, mul_pow, mul_pow, quarter_fourth _ (by positivity),
      three_quarters_fourth _ (by positivity), quarter_fourth _ (hD z hz1).le]
    ring
  have hp := pow_le_pow_left₀ (mul_nonneg hz.le (b_pos hz hz1).le) hzb 4
  rw [mul_pow, hW] at hp
  have hp' := (le_div_iff₀ hden).mp hp
  have hcore : z*(b z)^4*(1-lam^4) ≤ 16*lam^4*(1+(1-2*z)^3) := by
    apply (mul_le_mul_iff_left₀ (pow_pos hz 3)).mp
    convert hp' using 1 <;> ring
  have hH := H_antitone ⟨hz,hz1⟩ ⟨hS0,hS⟩ hzS
  have hH0 : 0 ≤ H S := div_nonneg (b_pos hS0 hS).le (Real.rpow_nonneg (hD S hS).le _)
  have hH4 := pow_le_pow_left₀ hH0 hH 4
  unfold H at hH4
  rw [div_pow, div_pow, quarter_fourth _ (hD S hS).le,
    quarter_fourth _ (hD z hz1).le] at hH4
  have hc := (div_le_div_iff₀ (hD S hS) (hD z hz1)).mp hH4
  have hmul := mul_le_mul_of_nonneg_left hc (mul_nonneg hz.le hden.le)
  have hcore' := mul_le_mul_of_nonneg_right hcore (hD S hS).le
  apply (mul_le_mul_iff_right₀ (hD z hz1)).mp
  nlinarith only [hmul, hcore']

theorem interval_bound {lam z S : ℝ} (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (hz : 0 < z) (hzS : z ≤ S) (hS : S ≤ 1/2)
    (hiter : iterationInequality lam z) :
    z ≤ 16*lam^4*(1+(1-2*S)^3)/((1-lam^4)*(b S)^4) := by
  have hden : 0 < (1-lam^4)*(b S)^4 := by
    have : lam^4 < 1 := by simpa using pow_lt_pow_left₀ hl1 hl0 (by decide : (4:ℕ)≠0)
    exact mul_pos (by linarith) (pow_pos (b_pos (hz.trans_le hzS) hS) _)
  apply (le_div_iff₀ hden).mpr
  simpa only [mul_assoc, mul_left_comm, mul_comm] using interval_moment hl0 hl1 hz hzS hS hiter

theorem b_lower {S u v : ℝ} (hS : 0 < S) (hS1 : S ≤ 1/2)
    (hu : 0 ≤ u) (hu2 : S ≤ u^2) (hv : 0 ≤ v) (hv2 : (1-S)^3 ≤ v^2) :
    (1-v)/S-u ≤ b S := by
  have hsqrt : Real.sqrt S ≤ u := (Real.sqrt_le_iff).mpr ⟨hu,hu2⟩
  have h1S : 0 ≤ 1-S := by linarith
  have he : ((1-S)^(3/2:ℝ))^2 = (1-S)^3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h1S]
    norm_num
  have hpow : (1-S)^(3/2:ℝ) ≤ v :=
    (pow_le_pow_iff_left₀ (Real.rpow_nonneg h1S _) hv (by decide : (2:ℕ)≠0)).mp (he ▸ hv2)
  have hs : S^(3/2:ℝ) = S*Real.sqrt S := by
    rw [three_halves _ hS.le, pow_succ, Real.sq_sqrt hS.le]
  unfold b
  rw [hs]
  have he' : (1-(1-S)^(3/2:ℝ)-S*Real.sqrt S)/S = (1-(1-S)^(3/2:ℝ))/S-Real.sqrt S := by field_simp
  rw [he']
  exact sub_le_sub (div_le_div_of_nonneg_right (by linarith : 1-v ≤ 1-(1-S)^(3/2:ℝ)) hS.le) hsqrt

theorem certified_step {lam z S T u v : ℝ}
    (hl0 : 0 ≤ lam) (hlU : lam ≤ (BootstrapEndpoint.lambdaUpper:ℝ))
    (hz : 0 ≤ z) (hzS : z ≤ S)
    (hS : 0 < S) (hS1 : S ≤ 1/2) (hT : 0 ≤ T)
    (hu : 0 ≤ u) (hu2 : S ≤ u^2) (hv : 0 ≤ v) (hv2 : (1-S)^3 ≤ v^2)
    (hbLow : 0 < (1-v)/S-u)
    (hcert : 16*(BootstrapEndpoint.lambdaUpper:ℝ)^4*(1+(1-2*S)^3) ≤
      T*(1-(BootstrapEndpoint.lambdaUpper:ℝ)^4)*((1-v)/S-u)^4)
    (hiter : iterationInequality lam z) : z ≤ T := by
  by_cases hz0 : z=0
  · simpa [hz0] using hT
  have hzp : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
  have hU1 : (BootstrapEndpoint.lambdaUpper:ℝ) < 1 := by norm_num [BootstrapEndpoint.lambdaUpper]
  have hU0 : 0 ≤ (BootstrapEndpoint.lambdaUpper:ℝ) := hl0.trans hlU
  have hU4 : (BootstrapEndpoint.lambdaUpper:ℝ)^4 < 1 := by
    simpa using pow_lt_pow_left₀ hU1 hU0 (by decide : (4:ℕ)≠0)
  have hl4 := pow_le_pow_left₀ hl0 hlU 4
  have hm := interval_moment hl0 (hlU.trans_lt hU1) hzp hzS hS1 hiter
  have hb := b_lower hS hS1 hu hu2 hv hv2
  have hb4 := pow_le_pow_left₀ hbLow.le hb 4
  have hD : 0 ≤ 1+(1-2*S)^3 := by
    have : 0 ≤ 1-2*S := by linarith
    positivity
  have hc : z*((1-v)/S-u)^4*(1-(BootstrapEndpoint.lambdaUpper:ℝ)^4) ≤
      T*((1-v)/S-u)^4*(1-(BootstrapEndpoint.lambdaUpper:ℝ)^4) := by
    calc
      _ ≤ z*(b S)^4*(1-(BootstrapEndpoint.lambdaUpper:ℝ)^4) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb4 hz) (by linarith)
      _ ≤ z*(b S)^4*(1-lam^4) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ 16*lam^4*(1+(1-2*S)^3) := hm
      _ ≤ 16*(BootstrapEndpoint.lambdaUpper:ℝ)^4*(1+(1-2*S)^3) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hl4 (by norm_num)) hD
      _ ≤ _ := by convert hcert using 1 <;> ring
  have hpos : 0 < ((1-v)/S-u)^4*(1-(BootstrapEndpoint.lambdaUpper:ℝ)^4) :=
    mul_pos (pow_pos hbLow 4) (by linarith)
  apply (mul_le_mul_iff_right₀ hpos).mp
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hc

end LonelyRunnerNew.BootstrapInterval
