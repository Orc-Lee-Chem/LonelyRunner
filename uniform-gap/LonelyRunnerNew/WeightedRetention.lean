import LonelyRunnerNew.WeightedDirections

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew.WeightedState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

theorem band_numeric_of_actual (s : WeightedState Label n) (hM : 0<s.edgeMass)
    (b : LCNumeric.Band) (hb : b.Valid LCNumeric.Data.boxes)
    (p : ℕ) (hp : Nat.Prime p) (hpB : b.lower≤p) (k : ℕ)
    (hseed : s.zMinus p k+s.zPlus p k ≤ (121/1000:ℝ))
    (hit : LCDirection.directionalInequality ((p:ℝ)^(-1/q)) (s.zMinus p k) (s.zPlus p k))
    (hE : s.primeException p k ≤ (s.zMinus p k)^(3/2:ℝ)+(s.zPlus p k)^(3/2:ℝ)) :
    s.primeException p k ≤ (LCNumeric.lastCoefficient b.steps:ℝ)*(p:ℝ)^(-(100:ℝ)/67) := by
  let z := s.zMinus p k+s.zPlus p k
  have hz0 := add_nonneg (s.zMinus_nonneg p k) (s.zPlus_nonneg p k)
  by_cases hz : z=0
  · rw [s.primeException_zero_of_zero_deficit hM p k hz hE]
    have hc : (0:ℝ) ≤ LCNumeric.lastCoefficient b.steps := by
      exact_mod_cast LCNumeric.lastCoefficient_nonneg b.steps b.scale hb.2.2.2.2.2.1
    exact mul_nonneg hc (Real.rpow_nonneg (by positivity) _)
  · have hzP : 0<z := lt_of_le_of_ne hz0 (Ne.symm hz)
    have hu := LCDirection.directionRatio_spec (s.zMinus_nonneg p k) (s.zPlus_nonneg p k) hzP
    have hn := LCDirection.normalize_iteration (s.zMinus_nonneg p k) (s.zPlus_nonneg p k) hzP hit
    have he : s.primeException p k ≤ z^(3/2:ℝ)*
        LCDirection.h0 (LCDirection.directionRatio (s.zMinus p k) (s.zPlus p k)) := by
      rw [LCDirection.h0,← LCDirection.normalized_power_sum (s.zMinus_nonneg p k) (s.zPlus_nonneg p k) hzP]
      exact hE
    have hh := b.sound LCNumeric.Data.boxes LCNumeric.actual_grid_valid hb hp hpB hu.1 hu.2.1 hzP hseed hn he
    simpa only [mul_comm] using hh

theorem numeric_tail_of_actual_bounds (s : WeightedState Label n) (hM : 0<s.edgeMass)
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

theorem numerical_budget_of_pointwise (s : WeightedState Label n) (hM : 0<s.edgeMass)
    (centers : ℕ → ℕ)
    (hsmall : ∀ i : Fin 141,∀ p,Nat.Prime p → 142<p →
      LCNumeric.Index.smallLo i≤p → p<LCNumeric.Index.smallHi i →
      s.primeException p (centers p) ≤
        (LCNumeric.Index.smallCoefficient i:ℝ)*(p:ℝ)^(-(100:ℝ)/67))
    (htail : ∀ p,Nat.Prime p → 10000≤p → s.primeException p (centers p) ≤
      (LCNumeric.tailCoefficient:ℝ)*(p:ℝ)^(-(100:ℝ)/67))
    (P : Finset ℕ) (hP : ∀ p∈P,Nat.Prime p ∧ 142<p) :
    (∑ p∈P,s.primeException p (centers p)) < (451/1000:ℝ) := by
  let w := fun p => s.primeException p (centers p)
  let Ps := P.filter (·≤10000)
  let Pm := P.filter (fun p => 10000<p ∧ p≤1000000)
  let Pt := P.filter (1000000<·)
  have hs : (∑ p∈Ps,w p) < (21/50:ℝ) := by
    apply LCNumeric.small_prime_budget Ps w (fun p _ => s.primeException_nonneg hM p _)
    · intro p hp
      have hm := Finset.mem_filter.mp hp
      exact ⟨(hP p hm.1).1,(hP p hm.1).2,hm.2⟩
    · intro i p hp hlo hhi
      have hm := (Finset.mem_filter.mp hp).1
      exact hsmall i p (hP p hm).1 (hP p hm).2 hlo hhi
  have hm : (∑ p∈Pm,w p) < (23/1000:ℝ) := by
    apply LCNumeric.middle_prime_budget Pm w (fun p _ => s.primeException_nonneg hM p _)
    · intro p hp
      have hr := Finset.mem_filter.mp hp
      exact ⟨(hP p hr.1).1,hr.2⟩
    · intro p hp
      have hr := Finset.mem_filter.mp hp
      exact htail p (hP p hr.1).1 hr.2.1.le
  have hPt : ∀ p∈Pt,Nat.Prime p ∧ 1000000<p := by
    intro p hp
    have hr := Finset.mem_filter.mp hp
    exact ⟨(hP p hr.1).1,hr.2⟩
  have ht : (∑ p∈Pt,w p) < (1/125:ℝ) := by
    have hbound : (∑ p∈Pt,w p) ≤ (LCNumeric.tailCoefficient:ℝ)*(∑ p∈Pt,(p:ℝ)^(-(100:ℝ)/67)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro p hp
      exact htail p (hPt p hp).1 (by have := (hPt p hp).2; omega)
    exact hbound.trans_lt (LCNumeric.prime_tail_numeric_budget Pt hPt)
  have heq : (∑ p∈P,w p)=(∑ p∈Ps,w p)+(∑ p∈Pm,w p)+(∑ p∈Pt,w p) := by
    dsimp [Ps,Pm,Pt]
    simp only [Finset.sum_filter]
    rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases h1 : p≤10000
    · have h2 : p≤1000000 := by omega
      simp [h1,h2,show ¬10000<p by omega,show ¬1000000<p by omega]
    · by_cases h2 : p≤1000000
      · simp [h1,h2,show 10000<p by omega,show ¬1000000<p by omega]
      · simp [h1,h2,show 10000<p by omega,show 1000000<p by omega]
  change (∑ p∈P,w p) < (451/1000:ℝ)
  rw [heq]
  linarith

theorem large_prime_retention (s : WeightedState Label n) (hM : 0<s.edgeMass)
    (h04 : s.RectangleConcentration) (h05 : s.LayerConcentration) :
    ∃ centers : ℕ → ℕ,
      (∀ p∉s.primeSupport,centers p=0) ∧
      s.retainedLargeEdges centers⊆s.edges ∧
      (27/50:ℝ)≤∑ e∈s.retainedLargeEdges centers,s.edgeProbability e ∧
      (∀ e∈s.retainedLargeEdges centers,∀ p,Nat.Prime p → 142<p →
        s.centerBrackets p (centers p) e) := by
  obtain ⟨centers,hc,hoff⟩ := s.select_large_centers (s.prime_center hM h04 h05)
  have hsmall (i : Fin 141) (p : ℕ) (hp : Nat.Prime p) (h142 : 142<p)
      (hlo : LCNumeric.Index.smallLo i≤p) (hhi : p<LCNumeric.Index.smallHi i) :
      s.primeException p (centers p)≤
        (LCNumeric.Index.smallCoefficient i:ℝ)*(p:ℝ)^(-(100:ℝ)/67) := by
    have h := hc p hp h142
    have hB := LCNumeric.Index.small_band_lower i
    have hh := s.band_numeric_of_actual hM (LCNumeric.Index.smallBand i)
      (LCNumeric.Index.small_band_valid i) p hp (by omega) _ h.2
      (s.directional_iteration hM h04 h05 p hp _ h.1) (s.same_direction h04 p _)
    rwa [LCNumeric.Index.small_coefficient_eq] at hh
  have htail (p : ℕ) (hp : Nat.Prime p) (hB : 10000≤p) :
      s.primeException p (centers p)≤(LCNumeric.tailCoefficient:ℝ)*(p:ℝ)^(-(100:ℝ)/67) := by
    have h := hc p hp (by omega)
    exact s.numeric_tail_of_actual_bounds hM p hp hB _ h.2
      (s.directional_iteration hM h04 h05 p hp _ h.1) (s.same_direction h04 p _)
  have hP : ∀ p∈s.largePrimeSupport,Nat.Prime p ∧ 142<p := by
    intro p hp
    have h := Finset.mem_filter.mp hp
    exact ⟨s.prime_of_mem_primeSupport h.1,h.2⟩
  have hb := s.numerical_budget_of_pointwise hM centers hsmall htail s.largePrimeSupport hP
  have hm := s.retainedLargeEdges_mass hM centers
  exact ⟨centers,hoff,s.retainedLargeEdges_subset centers,by linarith,
    fun _ he p hp h142 => s.retainedLargeEdges_all_large_primes centers hoff he p hp h142⟩

end LonelyRunnerNew.WeightedState
