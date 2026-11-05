import LonelyRunnerNew.LCSelectedCenters

noncomputable section
open scoped BigOperators
namespace LonelyRunnerNew.LCDirection

def directionRatio (zm zp : ℝ) : ℝ := min zm zp/(zm+zp)
def f (u : ℝ) : ℝ := u^(3/4:ℝ)+(1-u)^(3/4:ℝ)
def h0 (u : ℝ) : ℝ := u^(3/2:ℝ)+(1-u)^(3/2:ℝ)
def h (lam u : ℝ) : ℝ := h0 u+
  4^(3/4:ℝ)*((1/(1-lam^4))^(1/4:ℝ))^2*lam^2*(u*(1-u))^(3/4:ℝ)
def B (S lam u : ℝ) : ℝ :=
  (2^(3/4:ℝ)*(1/(1-lam^4))^(1/4:ℝ)*f u*(1+(1-2*S)^3)^(1/4:ℝ))/
    ((1-(1-S)^(3/2:ℝ))/S-h lam u*Real.sqrt S)

/-- The smaller direction is selected only in this scalar formula. The
underlying distribution and its center are never reflected or changed. -/
theorem directionRatio_spec {zm zp : ℝ} (hm : 0 ≤ zm) (hp : 0 ≤ zp)
    (hz : 0 < zm+zp) :
    0 ≤ directionRatio zm zp ∧ directionRatio zm zp ≤ 1/2 ∧
      ((zm=(zm+zp)*directionRatio zm zp ∧ zp=(zm+zp)*(1-directionRatio zm zp)) ∨
       (zp=(zm+zp)*directionRatio zm zp ∧ zm=(zm+zp)*(1-directionRatio zm zp))) := by
  have hu0 : 0 ≤ directionRatio zm zp := div_nonneg (le_min hm hp) hz.le
  have hu1 : directionRatio zm zp ≤ 1/2 := by
    apply (div_le_iff₀ hz).mpr
    have h1 := min_le_left zm zp
    have h2 := min_le_right zm zp
    linarith
  refine ⟨hu0,hu1,?_⟩
  rcases le_total zm zp with hmp | hpm
  · left
    simp only [directionRatio,min_eq_left hmp]
    constructor <;> field_simp [hz.ne'] <;> ring
  · right
    simp only [directionRatio,min_eq_right hpm]
    constructor <;> field_simp [hz.ne'] <;> ring

theorem normalized_power_sum {zm zp : ℝ} (hm : 0 ≤ zm) (hp : 0 ≤ zp)
    (hz : 0 < zm+zp) (r : ℝ) :
    zm^r+zp^r = (zm+zp)^r*((directionRatio zm zp)^r+(1-directionRatio zm zp)^r) := by
  obtain ⟨hu0,hu1,he⟩ := directionRatio_spec hm hp hz
  have hu2 : 0 ≤ 1-directionRatio zm zp := by linarith
  rcases he with ⟨he1,he2⟩ | ⟨he2,he1⟩
  · calc
      _ = ((zm+zp)*directionRatio zm zp)^r+((zm+zp)*(1-directionRatio zm zp))^r :=
        congrArg₂ (fun x y : ℝ => x^r+y^r) he1 he2
      _ = _ := by rw [Real.mul_rpow hz.le hu0,Real.mul_rpow hz.le hu2]; ring
  · calc
      _ = ((zm+zp)*(1-directionRatio zm zp))^r+((zm+zp)*directionRatio zm zp)^r :=
        congrArg₂ (fun x y : ℝ => x^r+y^r) he1 he2
      _ = _ := by rw [Real.mul_rpow hz.le hu0,Real.mul_rpow hz.le hu2]; ring

theorem normalized_product {zm zp : ℝ} (hm : 0 ≤ zm) (hp : 0 ≤ zp)
    (hz : 0 < zm+zp) :
    (zm*zp)^(3/4:ℝ) = (zm+zp)^(3/2:ℝ)*
      (directionRatio zm zp*(1-directionRatio zm zp))^(3/4:ℝ) := by
  obtain ⟨hu0,hu1,he⟩ := directionRatio_spec hm hp hz
  have hu2 : 0 ≤ 1-directionRatio zm zp := by linarith
  have hmul : zm*zp = (zm+zp)^2*(directionRatio zm zp*(1-directionRatio zm zp)) := by
    rcases he with ⟨he1,he2⟩ | ⟨he2,he1⟩
    · calc
        _ = ((zm+zp)*directionRatio zm zp)*((zm+zp)*(1-directionRatio zm zp)) :=
          congrArg₂ (· * ·) he1 he2
        _ = _ := by ring
    · calc
        _ = ((zm+zp)*(1-directionRatio zm zp))*((zm+zp)*directionRatio zm zp) :=
          congrArg₂ (· * ·) he1 he2
        _ = _ := by ring
  rw [hmul,Real.mul_rpow (sq_nonneg _) (mul_nonneg hu0 hu2)]
  congr 1
  rw [← Real.rpow_natCast,← Real.rpow_mul hz.le]
  norm_num

theorem normalize_iteration {lam zm zp : ℝ} (hm : 0 ≤ zm) (hp : 0 ≤ zp)
    (hz : 0 < zm+zp) (hit : directionalInequality lam zm zp) :
    1 ≤ (1-(zm+zp))^(3/2:ℝ)+(zm+zp)^(3/2:ℝ)*h lam (directionRatio zm zp)+
      2^(3/4:ℝ)*(1/(1-lam^4))^(1/4:ℝ)*lam*(zm+zp)^(3/4:ℝ)*f (directionRatio zm zp)*
        (1+(1-2*(zm+zp))^3)^(1/4:ℝ) := by
  have hs := normalized_power_sum hm hp hz (3/2:ℝ)
  have hs' := normalized_power_sum hm hp hz (3/4:ℝ)
  have ht := normalized_product hm hp hz
  unfold directionalInequality at hit
  rw [show (1-(zm+zp))^(3/2:ℝ)+zm^(3/2:ℝ)+zp^(3/2:ℝ) =
    (1-(zm+zp))^(3/2:ℝ)+(zm^(3/2:ℝ)+zp^(3/2:ℝ)) by ring,hs,hs',ht] at hit
  convert hit using 1 <;> dsimp [h,h0,f] <;> ring

/-- Uniform in the WHOLE interval of directions, including both endpoints. -/
theorem h0_sq_lower {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) : (1/2:ℝ) ≤ (h0 u)^2 := by
  let x := Real.sqrt u
  let y := Real.sqrt (1-u)
  have hx : 0 ≤ x := Real.sqrt_nonneg _
  have hy : 0 ≤ y := Real.sqrt_nonneg _
  have hxs : x^2=u := Real.sq_sqrt hu
  have hys : y^2=1-u := Real.sq_sqrt (by linarith)
  have hnorm : x^2+y^2=1 := by linarith
  have hid : 2*(x^3+y^3)^2-(x^2+y^2)^3 =
      (x-y)^2*(x^4+2*x^3*y+2*x*y^3+y^4) := by ring
  have hn : 0 ≤ (x-y)^2*(x^4+2*x^3*y+2*x*y^3+y^4) := by positivity
  rw [hnorm] at hid
  unfold h0
  rw [BootstrapInterval.three_halves _ hu,
    BootstrapInterval.three_halves _ (by linarith : 0 ≤ 1-u)]
  change (1/2:ℝ) ≤ (x^3+y^3)^2
  nlinarith only [hid,hn]

theorem h_nonneg {lam u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) : 0 ≤ h lam u := by
  unfold h h0
  have h4 : 0 ≤ ((1/(1-lam^4))^(1/4:ℝ))^2 := sq_nonneg _
  exact add_nonneg (add_nonneg (Real.rpow_nonneg hu _) (Real.rpow_nonneg (by linarith) _))
    (mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _) h4) (sq_nonneg _))
      (Real.rpow_nonneg (mul_nonneg hu (by linarith)) _))

theorem h_sq_lower {lam u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) : (1/2:ℝ) ≤ (h lam u)^2 := by
  have hh0 : 0 ≤ h0 u := add_nonneg (Real.rpow_nonneg hu _) (Real.rpow_nonneg (by linarith) _)
  have hh : h0 u ≤ h lam u := by
    unfold h
    apply le_add_of_nonneg_right
    exact mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (sq_nonneg _))
      (sq_nonneg _)) (Real.rpow_nonneg (mul_nonneg hu (by linarith)) _)
  exact (h0_sq_lower hu hu1).trans (pow_le_pow_left₀ hh0 hh 2)

end LonelyRunnerNew.LCDirection

namespace LonelyRunnerNew.TaggedState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

theorem primeException_zero_of_zero_deficit (s : TaggedState Label n)
    (hM : 0 < s.edgeMass) (p k : ℕ) (hz : s.zMinus p k+s.zPlus p k=0)
    (hE : s.primeException p k ≤ (s.zMinus p k)^(3/2:ℝ)+(s.zPlus p k)^(3/2:ℝ)) :
    s.primeException p k=0 := by
  have hm := s.zMinus_nonneg p k
  have hp := s.zPlus_nonneg p k
  have hm0 : s.zMinus p k=0 := by linarith
  have hp0 : s.zPlus p k=0 := by linarith
  norm_num only [hm0,hp0,Real.zero_rpow (by norm_num : (3/2:ℝ)≠0),zero_add] at hE
  exact le_antisymm hE (s.primeException_nonneg hM p k)

theorem actual_normalized_exception (s : TaggedState Label n)
    (hs : ∀ t,Step s t → t.quality ≤ s.quality) (hM : 0 < s.edgeMass)
    (p k : ℕ) (hz : 0 < s.zMinus p k+s.zPlus p k) :
    s.primeException p k ≤ (s.zMinus p k+s.zPlus p k)^(3/2:ℝ)*
      LCDirection.h0 (LCDirection.directionRatio (s.zMinus p k) (s.zPlus p k)) := by
  rw [LCDirection.h0,← LCDirection.normalized_power_sum (s.zMinus_nonneg p k) (s.zPlus_nonneg p k) hz]
  exact s.actual_same_direction hs hM p k

theorem actual_universal_normalized_exception (s : TaggedState Label n)
    (hs : ∀ t,Step s t → t.universalQuality ≤ s.universalQuality) (hM : 0 < s.edgeMass)
    (p k : ℕ) (hz : 0 < s.zMinus p k+s.zPlus p k) :
    s.primeException p k ≤ (s.zMinus p k+s.zPlus p k)^(3/2:ℝ)*
      LCDirection.h0 (LCDirection.directionRatio (s.zMinus p k) (s.zPlus p k)) := by
  rw [LCDirection.h0,← LCDirection.normalized_power_sum (s.zMinus_nonneg p k) (s.zPlus_nonneg p k) hz]
  exact s.actual_universal_same_direction hs hM p k

theorem actual_normalized_direction (s : TaggedState Label n)
    (hs : ∀ t,Step s t → t.quality ≤ s.quality) (hM : 0 < s.edgeMass)
    (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (hk : k ∈ s.valuationSupport p)
    (hz : 0 < s.zMinus p k+s.zPlus p k) :
    1 ≤ (1-(s.zMinus p k+s.zPlus p k))^(3/2:ℝ)+
      (s.zMinus p k+s.zPlus p k)^(3/2:ℝ)*LCDirection.h ((p:ℝ)^(-1/q))
        (LCDirection.directionRatio (s.zMinus p k) (s.zPlus p k))+
      2^(3/4:ℝ)*(1/(1-((p:ℝ)^(-1/q))^4))^(1/4:ℝ)*((p:ℝ)^(-1/q))*
        (s.zMinus p k+s.zPlus p k)^(3/4:ℝ)*
        LCDirection.f (LCDirection.directionRatio (s.zMinus p k) (s.zPlus p k))*
        (1+(1-2*(s.zMinus p k+s.zPlus p k))^3)^(1/4:ℝ) :=
  LCDirection.normalize_iteration (s.zMinus_nonneg p k) (s.zPlus_nonneg p k) hz
    (s.actual_directional_iteration hs hM p hp k hk)

theorem actual_universal_normalized_direction (s : TaggedState Label n)
    (hs : ∀ t,Step s t → t.universalQuality ≤ s.universalQuality) (hM : 0 < s.edgeMass)
    (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (hk : k ∈ s.valuationSupport p)
    (hz : 0 < s.zMinus p k+s.zPlus p k) :
    1 ≤ (1-(s.zMinus p k+s.zPlus p k))^(3/2:ℝ)+
      (s.zMinus p k+s.zPlus p k)^(3/2:ℝ)*LCDirection.h ((p:ℝ)^(-1/q))
        (LCDirection.directionRatio (s.zMinus p k) (s.zPlus p k))+
      2^(3/4:ℝ)*(1/(1-((p:ℝ)^(-1/q))^4))^(1/4:ℝ)*((p:ℝ)^(-1/q))*
        (s.zMinus p k+s.zPlus p k)^(3/4:ℝ)*
        LCDirection.f (LCDirection.directionRatio (s.zMinus p k) (s.zPlus p k))*
        (1+(1-2*(s.zMinus p k+s.zPlus p k))^3)^(1/4:ℝ) :=
  LCDirection.normalize_iteration (s.zMinus_nonneg p k) (s.zPlus_nonneg p k) hz
    (s.actual_universal_directional_iteration hs hM p hp k hk)

end LonelyRunnerNew.TaggedState
