import LonelyRunnerNew.LCNumericTailData
import LonelyRunnerNew.LCWheelNumerics

noncomputable section
open scoped BigOperators
namespace LonelyRunnerNew.LCNumeric

theorem actual_grid_valid : GridValid Data.boxes :=
  ⟨Data.boxes_length,Data.boxes_valid,Data.boxes_grid⟩

theorem tail_coefficient_eq : lastCoefficient Data.band_141.steps=tailCoefficient := by
  norm_num [lastCoefficient,Data.band_141,Data.steps_141,tailCoefficient]

end LonelyRunnerNew.LCNumeric

namespace LonelyRunnerNew.TaggedState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

theorem numeric_tail_of_actual_bounds (s : TaggedState Label n) (hM : 0<s.edgeMass)
    (p : ℕ) (hp : Nat.Prime p) (hpB : 10000 ≤ p) (k : ℕ)
    (hseed : s.zMinus p k+s.zPlus p k ≤ (121/1000:ℝ))
    (hit : LCDirection.directionalInequality ((p:ℝ)^(-1/q)) (s.zMinus p k) (s.zPlus p k))
    (hE : s.primeException p k ≤ (s.zMinus p k)^(3/2:ℝ)+(s.zPlus p k)^(3/2:ℝ)) :
    s.primeException p k ≤ (LCNumeric.tailCoefficient:ℝ)*(p:ℝ)^(-(100:ℝ)/67) := by
  let z := s.zMinus p k+s.zPlus p k
  have hz0 : 0 ≤ z := add_nonneg (s.zMinus_nonneg p k) (s.zPlus_nonneg p k)
  by_cases hz : z=0
  · rw [s.primeException_zero_of_zero_deficit hM p k hz hE]
    have hc : (0:ℝ) ≤ LCNumeric.tailCoefficient := by norm_num [LCNumeric.tailCoefficient]
    exact mul_nonneg hc (Real.rpow_nonneg (by positivity) _)
  · have hzP : 0<z := lt_of_le_of_ne hz0 (Ne.symm hz)
    have hu := LCDirection.directionRatio_spec (s.zMinus_nonneg p k) (s.zPlus_nonneg p k) hzP
    have hn := LCDirection.normalize_iteration (s.zMinus_nonneg p k) (s.zPlus_nonneg p k) hzP hit
    have he : s.primeException p k ≤ z^(3/2:ℝ)*
        LCDirection.h0 (LCDirection.directionRatio (s.zMinus p k) (s.zPlus p k)) := by
      rw [LCDirection.h0,← LCDirection.normalized_power_sum (s.zMinus_nonneg p k) (s.zPlus_nonneg p k) hzP]
      exact hE
    have hh := LCNumeric.Data.band_141.sound LCNumeric.Data.boxes LCNumeric.actual_grid_valid
      LCNumeric.Data.band_141_valid hp (by simpa only [LCNumeric.Data.band_141] using hpB)
      hu.1 hu.2.1 hzP hseed hn he
    rw [LCNumeric.tail_coefficient_eq] at hh
    simpa only [mul_comm] using hh

theorem actual_numeric_tail (s : TaggedState Label n)
    (hs : ∀ t,Step s t → t.quality≤s.quality) (hM : 0<s.edgeMass)
    (p : ℕ) (hp : Nat.Prime p) (hpB : 10000≤p) (k : ℕ) (hk : k∈s.valuationSupport p)
    (hseed : s.zMinus p k+s.zPlus p k ≤ (121/1000:ℝ)) :
    s.primeException p k ≤ (LCNumeric.tailCoefficient:ℝ)*(p:ℝ)^(-(100:ℝ)/67) :=
  s.numeric_tail_of_actual_bounds hM p hp hpB k hseed
    (s.actual_directional_iteration hs hM p hp k hk) (s.actual_same_direction hs hM p k)

theorem actual_universal_numeric_tail (s : TaggedState Label n)
    (hs : ∀ t,Step s t → t.universalQuality≤s.universalQuality) (hM : 0<s.edgeMass)
    (p : ℕ) (hp : Nat.Prime p) (hpB : 10000≤p) (k : ℕ) (hk : k∈s.valuationSupport p)
    (hseed : s.zMinus p k+s.zPlus p k ≤ (121/1000:ℝ)) :
    s.primeException p k ≤ (LCNumeric.tailCoefficient:ℝ)*(p:ℝ)^(-(100:ℝ)/67) :=
  s.numeric_tail_of_actual_bounds hM p hp hpB k hseed
    (s.actual_universal_directional_iteration hs hM p hp k hk) (s.actual_universal_same_direction hs hM p k)

/-- Unconditional numerical tail budget for one actual ordinary stable state.
The centers are supplied by the proved center chain, not as a numerical input. -/
theorem stable_infinite_prime_tail (s : TaggedState Label n)
    (hs : ∀ t,Step s t → t.quality≤s.quality) (hM : 0<s.edgeMass) :
    ∃ centers : ℕ → ℕ,
      (∀ p ∉ s.primeSupport,centers p=0) ∧
      (∀ p,Nat.Prime p → 142<p → centers p∈s.valuationSupport p ∧
        s.zMinus p (centers p)+s.zPlus p (centers p) ≤ (121/1000:ℝ)) ∧
      (∀ P : Finset ℕ,(∀ p∈P,Nat.Prime p ∧ 1000000<p) →
        (∑ p∈P,s.primeException p (centers p)) < (1/125:ℝ)) := by
  obtain ⟨centers,hc,hoff⟩ := s.select_large_centers (s.stable_prime_center hs hM)
  refine ⟨centers,hoff,hc,?_⟩
  intro P hP
  have hbound : (∑ p∈P,s.primeException p (centers p)) ≤
      (LCNumeric.tailCoefficient:ℝ)*(∑ p∈P,(p:ℝ)^(-(100:ℝ)/67)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    have h := hc p (hP p hp).1 (by have := (hP p hp).2; omega)
    exact s.actual_numeric_tail hs hM p (hP p hp).1 (by have := (hP p hp).2; omega) _ h.1 h.2
  exact hbound.trans_lt (LCNumeric.prime_tail_numeric_budget P hP)

theorem universal_infinite_prime_tail (s : TaggedState Label n)
    (hs : ∀ t,Step s t → t.universalQuality≤s.universalQuality) (hM : 0<s.edgeMass) :
    ∃ centers : ℕ → ℕ,
      (∀ p ∉ s.primeSupport,centers p=0) ∧
      (∀ p,Nat.Prime p → 142<p → centers p∈s.valuationSupport p ∧
        s.zMinus p (centers p)+s.zPlus p (centers p) ≤ (121/1000:ℝ)) ∧
      (∀ P : Finset ℕ,(∀ p∈P,Nat.Prime p ∧ 1000000<p) →
        (∑ p∈P,s.primeException p (centers p)) < (1/125:ℝ)) := by
  obtain ⟨centers,hc,hoff⟩ := s.select_large_centers (s.universal_prime_center hs hM)
  refine ⟨centers,hoff,hc,?_⟩
  intro P hP
  have hbound : (∑ p∈P,s.primeException p (centers p)) ≤
      (LCNumeric.tailCoefficient:ℝ)*(∑ p∈P,(p:ℝ)^(-(100:ℝ)/67)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    have h := hc p (hP p hp).1 (by have := (hP p hp).2; omega)
    exact s.actual_universal_numeric_tail hs hM p (hP p hp).1 (by have := (hP p hp).2; omega) _ h.1 h.2
  exact hbound.trans_lt (LCNumeric.prime_tail_numeric_budget P hP)

end LonelyRunnerNew.TaggedState
