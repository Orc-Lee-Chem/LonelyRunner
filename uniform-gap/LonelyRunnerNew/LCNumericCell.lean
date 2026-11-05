import LonelyRunnerNew.LCNumericIntervals

noncomputable section
namespace LonelyRunnerNew.LCNumeric

structure Scale where
  lambdaUpper : ℚ
  a1 : ℚ
  two : ℚ
  four : ℚ
  deriving Inhabited,DecidableEq

def Scale.Valid (c : Scale) : Prop :=
  0 ≤ c.lambdaUpper ∧ c.lambdaUpper ≤ 1/3 ∧ 0 ≤ c.a1 ∧
  1 ≤ c.a1^4*(1-c.lambdaUpper^4) ∧ 0 ≤ c.two ∧ 2^3 ≤ c.two^4 ∧
  0 ≤ c.four ∧ 4^3 ≤ c.four^4
instance (c : Scale) : Decidable c.Valid := by unfold Scale.Valid; infer_instance

theorem Scale.bounds (c : Scale) (hc : c.Valid) {lam : ℝ}
    (hl0 : 0 ≤ lam) (hlU : lam ≤ (c.lambdaUpper:ℝ)) :
    (1/(1-lam^4))^(1/4:ℝ) ≤ (c.a1:ℝ) ∧ (2:ℝ)^(3/4:ℝ) ≤ (c.two:ℝ) ∧
      (4:ℝ)^(3/4:ℝ) ≤ (c.four:ℝ) := by
  rcases hc with ⟨hL0,hL1,ha1,hroot,ht,h2,hf,h4⟩
  have hL1R : (c.lambdaUpper:ℝ) ≤ 1/3 := by
    have h : (3:ℚ)*c.lambdaUpper ≤ 1 := by linarith
    have hR : (3:ℝ)*(c.lambdaUpper:ℝ) ≤ 1 := by exact_mod_cast h
    linarith
  have hL0R : (0:ℝ) ≤ c.lambdaUpper := by exact_mod_cast hL0
  have hL4 : (c.lambdaUpper:ℝ)^4 < 1 := by
    have hh := pow_le_pow_left₀ hL0R hL1R 4
    norm_num at hh
    linarith
  have hl4 := pow_le_pow_left₀ hl0 hlU 4
  have hd : 0 < 1-lam^4 := by linarith
  have hrootR : (1:ℝ) ≤ (c.a1:ℝ)^4*(1-(c.lambdaUpper:ℝ)^4) := by exact_mod_cast hroot
  have hb : (1:ℝ)/(1-lam^4) ≤ (c.a1:ℝ)^4 := by
    apply (div_le_iff₀ hd).mpr
    have hh := mul_le_mul_of_nonneg_left (show 1-(c.lambdaUpper:ℝ)^4 ≤ 1-lam^4 by linarith)
      (pow_nonneg (by exact_mod_cast ha1 : (0:ℝ) ≤ c.a1) 4)
    linarith
  refine ⟨?_,?_,?_⟩
  · have hh := rational_power_upper (show (0:ℝ) ≤ 1/(1-lam^4) by positivity)
      (by exact_mod_cast ha1 : (0:ℝ) ≤ c.a1) 1 4 (by decide) (by simpa only [pow_one] using hb)
    simpa only [Nat.cast_one,Nat.cast_ofNat] using hh
  · exact rational_power_upper (by norm_num : (0:ℝ) ≤ 2) (by exact_mod_cast ht)
      3 4 (by decide) (by exact_mod_cast h2)
  · exact rational_power_upper (by norm_num : (0:ℝ) ≤ 4) (by exact_mod_cast hf)
      3 4 (by decide) (by exact_mod_cast h4)

structure CellStep where
  S : ℚ
  aLower : ℚ
  sqrtUpper : ℚ
  cRoot : ℚ
  pre : ℚ
  cross : ℚ
  bUpper : ℚ
  eUpper : ℚ
  nextS : ℚ
  deriving Inhabited,DecidableEq

def CellStep.Valid (c : Scale) (d : CellStep) : Prop :=
  0 < d.S ∧ d.S ≤ 1/8 ∧ 0 ≤ 1-d.aLower*d.S ∧
  (1-d.S)^3 ≤ (1-d.aLower*d.S)^2 ∧
  0 ≤ d.sqrtUpper ∧ d.S ≤ d.sqrtUpper^2 ∧
  0 ≤ d.cRoot ∧ 1+(1-2*d.S)^3 ≤ d.cRoot^4 ∧
  0 ≤ d.pre ∧ c.two*c.a1*d.cRoot ≤ d.pre ∧
  0 ≤ d.cross ∧ c.four*c.a1^2*c.lambdaUpper^2 ≤ d.cross ∧
  0 ≤ d.bUpper ∧ 0 ≤ d.eUpper ∧ 0 < d.nextS ∧ d.nextS ≤ 1/8 ∧
  c.lambdaUpper^4*d.bUpper^4 ≤ d.nextS
instance (c : Scale) (d : CellStep) : Decidable (d.Valid c) := by
  unfold CellStep.Valid; infer_instance

def CellStep.lowerDen (d : CellStep) (b : Box) : ℚ :=
  d.aLower-((b.h1+b.h2)+d.cross*b.jj)*d.sqrtUpper

def CellStep.Accepts (d : CellStep) (b : Box) : Prop :=
  0 < d.lowerDen b ∧ d.pre*(b.f1+b.f2) ≤ d.bUpper*d.lowerDen b ∧
    (d.pre*(b.f1+b.f2))^6*(b.h1+b.h2) ≤ d.eUpper*(d.lowerDen b)^6
instance (d : CellStep) (b : Box) : Decidable (d.Accepts b) := by
  unfold CellStep.Accepts; infer_instance

theorem CellStep.scalar_bounds (c : Scale) (d : CellStep) (hc : c.Valid) (hd : d.Valid c)
    {lam : ℝ} (hl0 : 0 ≤ lam) (hlU : lam ≤ (c.lambdaUpper:ℝ)) :
    (d.aLower:ℝ) ≤ LCDirection.A d.S ∧ Real.sqrt (d.S:ℝ) ≤ (d.sqrtUpper:ℝ) ∧
      (2:ℝ)^(3/4:ℝ)*(1/(1-lam^4))^(1/4:ℝ)*LCDirection.C d.S ≤ (d.pre:ℝ) ∧
      (4:ℝ)^(3/4:ℝ)*((1/(1-lam^4))^(1/4:ℝ))^2*lam^2 ≤ (d.cross:ℝ) := by
  rcases hd with ⟨hS,hS1,ha,haP,hs,hsP,hc0,hcP,hpre,hpreP,hcross,hcrossP,hb,he,hn,hn1,hnP⟩
  have hS0 : (0:ℝ) < d.S := by exact_mod_cast hS
  have hS1R : (d.S:ℝ) ≤ 1/8 := by
    have h : (8:ℚ)*d.S ≤ 1 := by linarith
    have hR : (8:ℝ)*(d.S:ℝ) ≤ 1 := by exact_mod_cast h
    linarith
  have hsqrt := (Real.sqrt_le_iff).mpr (show (0:ℝ) ≤ d.sqrtUpper ∧ (d.S:ℝ) ≤ (d.sqrtUpper:ℝ)^2 by
    exact_mod_cast And.intro hs hsP)
  have hAroot := rational_power_upper (show (0:ℝ) ≤ 1-d.S by linarith)
    (show (0:ℝ) ≤ 1-(d.aLower:ℝ)*d.S by exact_mod_cast ha) 3 2 (by decide)
    (by exact_mod_cast haP)
  have hA : (d.aLower:ℝ) ≤ LCDirection.A d.S := by
    unfold LCDirection.A
    apply (le_div_iff₀ hS0).mpr
    norm_num only [Nat.cast_ofNat] at hAroot
    linarith
  have hCt : LCDirection.C d.S ≤ (d.cRoot:ℝ) := by
    have hh := rational_power_upper (X := (d.cRoot:ℝ)) (show (0:ℝ) ≤ 1+(1-2*(d.S:ℝ))^3 by
      have : 0 ≤ 1-2*(d.S:ℝ) := by linarith
      positivity) (by exact_mod_cast hc0) 1 4 (by decide)
      (by simpa only [pow_one] using (show (1:ℝ)+(1-2*(d.S:ℝ))^3 ≤ (d.cRoot:ℝ)^4 by exact_mod_cast hcP))
    simpa only [LCDirection.C,Nat.cast_one,Nat.cast_ofNat] using hh
  have hscl := c.bounds hc hl0 hlU
  have ha10 : (0:ℝ) ≤ c.a1 := by exact_mod_cast hc.2.2.1
  have ht0 : (0:ℝ) ≤ c.two := by exact_mod_cast hc.2.2.2.2.1
  have hf0 : (0:ℝ) ≤ c.four := by exact_mod_cast hc.2.2.2.2.2.2.1
  have hL0 : (0:ℝ) ≤ c.lambdaUpper := by exact_mod_cast hc.1
  have hL1R : (c.lambdaUpper:ℝ) ≤ 1/3 := by
    have h : (3:ℚ)*c.lambdaUpper ≤ 1 := by linarith [hc.2.1]
    have hR : (3:ℝ)*(c.lambdaUpper:ℝ) ≤ 1 := by exact_mod_cast h
    linarith
  have hl1 : lam < 1 := by linarith
  have hl4 : lam^4 < 1 := by simpa using pow_lt_pow_left₀ hl1 hl0 (by decide : (4:ℕ)≠0)
  have hactualA1 : (0:ℝ) ≤ (1/(1-lam^4))^(1/4:ℝ) := Real.rpow_nonneg (by positivity) _
  have hprod := mul_le_mul hscl.2.1 hscl.1 hactualA1 ht0
  have hprodC := mul_le_mul hprod hCt (LCDirection.C_pos (by linarith)).le (mul_nonneg ht0 ha10)
  have hcross0 := mul_le_mul hscl.2.2 (pow_le_pow_left₀ hactualA1 hscl.1 2)
    (sq_nonneg _) hf0
  have hcross1 := mul_le_mul hcross0 (pow_le_pow_left₀ hl0 hlU 2) (sq_nonneg _) (mul_nonneg hf0 (sq_nonneg _))
  refine ⟨hA,hsqrt,hprodC.trans ?_,hcross1.trans ?_⟩
  · exact_mod_cast hpreP
  · exact_mod_cast hcrossP

theorem CellStep.box_sound (c : Scale) (d : CellStep) (b : Box)
    (hc : c.Valid) (hd : d.Valid c) (hb : b.Valid) (hacc : d.Accepts b)
    {lam u : ℝ} (hl0 : 0 ≤ lam) (hlU : lam ≤ (c.lambdaUpper:ℝ))
    (hu : (b.lo:ℝ) ≤ u) (hu1 : u ≤ (b.hi:ℝ)) :
    LCDirection.B d.S lam u ≤ (d.bUpper:ℝ) ∧
      (LCDirection.B d.S lam u)^6*LCDirection.h0 u ≤ (d.eUpper:ℝ) := by
  have hbb := b.bounds hb hu hu1
  have hscalar := d.scalar_bounds c hc hd hl0 hlU
  have hu0 : 0 ≤ u := (show (0:ℝ) ≤ b.lo by exact_mod_cast hb.1).trans hu
  have hhi : (b.hi:ℝ) ≤ 1/2 := by
    have hh : (2:ℚ)*b.hi ≤ 1 := by linarith [hb.2.2.1]
    have hhR : (2:ℝ)*(b.hi:ℝ) ≤ 1 := by exact_mod_cast hh
    linarith
  have huHalf := hu1.trans hhi
  have huf : 0 ≤ LCDirection.f u := add_nonneg (Real.rpow_nonneg hu0 _)
    (Real.rpow_nonneg (by linarith) _)
  have huh : 0 ≤ LCDirection.h0 u := add_nonneg (Real.rpow_nonneg hu0 _)
    (Real.rpow_nonneg (by linarith) _)
  have huj : 0 ≤ j u := Real.rpow_nonneg (mul_nonneg hu0 (by linarith)) _
  have hpre0 : (0:ℝ) ≤ d.pre := by exact_mod_cast hd.2.2.2.2.2.2.2.2.1
  have hcross0 : (0:ℝ) ≤ d.cross := by exact_mod_cast hd.2.2.2.2.2.2.2.2.2.2.1
  have hsq0 : (0:ℝ) ≤ d.sqrtUpper := by exact_mod_cast hd.2.2.2.2.1
  have hBU0 : (0:ℝ) ≤ d.bUpper := by exact_mod_cast hd.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hEU0 : (0:ℝ) ≤ d.eUpper := by exact_mod_cast hd.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hden0 : (0:ℝ) < (d.lowerDen b:ℝ) := by exact_mod_cast hacc.1
  have hH : LCDirection.h lam u ≤ ((b.h1+b.h2:ℚ):ℝ)+(d.cross:ℝ)*(b.jj:ℝ) := by
    have hh := mul_le_mul hscalar.2.2.2 hbb.2.2 huj hcross0
    exact add_le_add hbb.2.1 hh
  have hH0 := LCDirection.h_nonneg (lam := lam) hu0 (by linarith : u ≤ 1)
  have hHupper0 : 0 ≤ ((b.h1+b.h2:ℚ):ℝ)+(d.cross:ℝ)*(b.jj:ℝ) := hH0.trans hH
  have hD : (d.lowerDen b:ℝ) ≤ LCDirection.denominator (LCDirection.h lam u) d.S := by
    have hh := mul_le_mul hH hscalar.2.1 (Real.sqrt_nonneg _) hHupper0
    unfold CellStep.lowerDen LCDirection.denominator
    push_cast
    push_cast at hh
    linarith [hscalar.1]
  have hDpos := hden0.trans_le hD
  let num := (2:ℝ)^(3/4:ℝ)*(1/(1-lam^4))^(1/4:ℝ)*LCDirection.f u*LCDirection.C d.S
  have hNum : num ≤ (d.pre:ℝ)*(b.f1+b.f2:ℚ) := by
    have hh := mul_le_mul hscalar.2.2.1 hbb.1 huf hpre0
    convert hh using 1 <;> dsimp [num] <;> ring
  have hNum0 : 0 ≤ num := by
    have hS : (d.S:ℝ) ≤ 1/2 := by
      have h : (8:ℚ)*d.S ≤ 1 := by linarith [hd.2.1]
      have hR : (8:ℝ)*(d.S:ℝ) ≤ 1 := by exact_mod_cast h
      linarith
    have hL : (c.lambdaUpper:ℝ) ≤ 1/3 := by
      have h : (3:ℚ)*c.lambdaUpper ≤ 1 := by linarith [hc.2.1]
      have hR : (3:ℝ)*(c.lambdaUpper:ℝ) ≤ 1 := by exact_mod_cast h
      linarith
    have hl1 : lam < 1 := by linarith
    have hl4 : lam^4 < 1 := by simpa using pow_lt_pow_left₀ hl1 hl0 (by decide : (4:ℕ)≠0)
    dsimp [num]
    exact mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_nonneg (by positivity) _)) huf) (LCDirection.C_pos hS).le
  have heB : LCDirection.B d.S lam u = num/LCDirection.denominator (LCDirection.h lam u) d.S := by
    dsimp [LCDirection.B,LCDirection.denominator,LCDirection.A,LCDirection.C,num]
  have hBbound : LCDirection.B d.S lam u ≤ (d.bUpper:ℝ) := by
    rw [heB]
    apply (div_le_iff₀ hDpos).mpr
    calc
      num ≤ (d.pre:ℝ)*(b.f1+b.f2:ℚ) := hNum
      _ ≤ (d.bUpper:ℝ)*(d.lowerDen b:ℝ) := by exact_mod_cast hacc.2.1
      _ ≤ _ := mul_le_mul_of_nonneg_left hD hBU0
  refine ⟨hBbound,?_⟩
  rw [heB,div_pow,div_mul_eq_mul_div]
  apply (div_le_iff₀ (pow_pos hDpos 6)).mpr
  calc
    num^6*LCDirection.h0 u ≤ ((d.pre:ℝ)*(b.f1+b.f2:ℚ))^6*(b.h1+b.h2:ℚ) :=
      mul_le_mul (pow_le_pow_left₀ hNum0 hNum 6) hbb.2.1 huh (by positivity)
    _ ≤ (d.eUpper:ℝ)*(d.lowerDen b:ℝ)^6 := by exact_mod_cast hacc.2.2
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hden0.le hD 6) hEU0

end LonelyRunnerNew.LCNumeric
