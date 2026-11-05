import LonelyRunnerNew.CoreCut
import LonelyRunnerNew.FiniteCoarea
import LonelyRunnerNew.Certificates

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew.TaggedState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

def coreValuation (s : TaggedState Label n) (p : ℕ) : (Label ⊕ Label) → ℕ :=
  Sum.elim (fun x => padicValNat p (s.leftValue x)) (fun y => padicValNat p (s.rightValue y))

theorem small_medians_exist (s : TaggedState Label n) (hM : 0<s.edgeMass) :
    ∃ centers : ℕ → ℕ,∀ p,
      centers p∈s.coreVertices.image (s.coreValuation p) ∧
      (∑ v∈s.coreVertices.filter (fun v => s.coreValuation p v<centers p),s.corePi v)≤1/2 ∧
      (∑ v∈s.coreVertices.filter (fun v => centers p<s.coreValuation p v),s.corePi v)≤1/2 := by
  have hp (p : ℕ) := FiniteCore.nat_median_exists s.coreVertices s.corePi (s.coreValuation p)
    (fun v _ => s.corePi_nonneg hM v) (s.corePi_sum hM)
  choose centers hmem hlow hhigh using hp
  exact ⟨centers,fun p => ⟨hmem p,hlow p,hhigh p⟩⟩

/-- These are edge-marginal medians, distinct from large-prime modal centers. -/
def coreSmallCenters (s : TaggedState Label n) (hM : 0<s.edgeMass) : ℕ → ℕ :=
  Classical.choose (s.small_medians_exist hM)

theorem coreSmallCenters_spec (s : TaggedState Label n) (hM : 0<s.edgeMass) (p : ℕ) :
    s.coreSmallCenters hM p∈s.coreVertices.image (s.coreValuation p) ∧
      (∑ v∈s.coreVertices.filter (fun v => s.coreValuation p v<s.coreSmallCenters hM p),s.corePi v)≤1/2 ∧
      (∑ v∈s.coreVertices.filter (fun v => s.coreSmallCenters hM p<s.coreValuation p v),s.corePi v)≤1/2 :=
  Classical.choose_spec (s.small_medians_exist hM) p

theorem coarea_of_core_cut (s : TaggedState Label n) (hM : 0<s.edgeMass)
    (hcut : ∀ S,FiniteCore.cutConstant*min (s.corePiMass S) (s.corePiMass (s.coreVertices\S))≤s.coreCross S)
    (p : ℕ) :
    (∑ v∈s.coreVertices,s.corePi v*|(s.coreValuation p v:ℝ)-(s.coreSmallCenters hM p:ℝ)|)≤
      FiniteCore.coareaConstant*(∑ e∈s.edges,s.edgeProbability e*
        |(s.coreValuation p (coreSource e):ℝ)-(s.coreValuation p (coreTarget e):ℝ)|) := by
  have hm := s.coreSmallCenters_spec hM p
  have h := FiniteCore.nat_median_coarea s.coreVertices s.corePi s.coreOmega
    (fun v _ => s.corePi_nonneg hM v) (s.corePi_sum hM) (s.coreOmega_symm)
    hcut (s.coreValuation p) (s.coreSmallCenters hM p) hm.2.1 hm.2.2
  rw [s.coreOmega_abs_difference] at h
  exact h

def coreSmallCost (s : TaggedState Label n) (centers : ℕ → ℕ) (v : Label ⊕ Label) : ℝ :=
  ∑ p∈Certificate.smallPrimes,|(s.coreValuation p v:ℝ)-(centers p:ℝ)| *Real.log (p:ℝ)

theorem coreSmallCost_nonneg (s : TaggedState Label n) (centers : ℕ → ℕ) (v : Label ⊕ Label) :
    0≤s.coreSmallCost centers v := by
  apply Finset.sum_nonneg
  intro p hp
  have hprime := (Certificate.smallPrimes_mem.mp hp).1
  exact mul_nonneg (abs_nonneg _) (Real.log_nonneg (by exact_mod_cast hprime.one_lt.le))

theorem core_valuation_edge_distance (s : TaggedState Label n) (p : ℕ) (e : Label × Label) :
    |(s.coreValuation p (coreSource e):ℝ)-(s.coreValuation p (coreTarget e):ℝ)| *Real.log (p:ℝ)=
      primeLogDistance p (s.valuationPair p e) := by
  unfold primeLogDistance valuationPair coreValuation coreSource coreTarget
  dsimp only [Sum.elim_inl,Sum.elim_inr]
  rw [Nat.cast_natAbs,Int.cast_abs,Int.cast_sub]
  simp only [Int.cast_natCast]

theorem core_cost_mean_of_cut (s : TaggedState Label n) (hM : 0<s.edgeMass)
    (hcut : ∀ S,FiniteCore.cutConstant*min (s.corePiMass S) (s.corePiMass (s.coreVertices\S))≤s.coreCross S) :
    (∑ v∈s.coreVertices,s.corePi v*s.coreSmallCost (s.coreSmallCenters hM) v)≤
      FiniteCore.coareaConstant*(∑ p∈Certificate.smallPrimes,s.primeMeanLogDistance p) := by
  have hper (p : ℕ) (hp : p∈Certificate.smallPrimes) :
      (∑ v∈s.coreVertices,s.corePi v*(|(s.coreValuation p v:ℝ)-(s.coreSmallCenters hM p:ℝ)| *Real.log (p:ℝ)))≤
        FiniteCore.coareaConstant*s.primeMeanLogDistance p := by
    have hl : 0≤Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast (Certificate.smallPrimes_mem.mp hp).1.one_lt.le)
    have h := mul_le_mul_of_nonneg_right (s.coarea_of_core_cut hM hcut p) hl
    rw [s.primeMeanLogDistance_eq_edge_sum]
    rw [mul_assoc] at h
    simp_rw [Finset.sum_mul,mul_assoc,s.core_valuation_edge_distance] at h
    exact h
  unfold coreSmallCost
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum hper

end LonelyRunnerNew.TaggedState

namespace LonelyRunnerNew.FiniteCore

theorem coarea_edgebar_lt_Dbar : coareaConstant*(Certificate.edgebar:ℝ)<(Certificate.Dbar:ℝ) := by
  have hroot : 1/Real.sqrt 2≤(Certificate.sqrtHalfUpper:ℝ) := by
    have hs : Real.sqrt (1/2:ℝ)=1/Real.sqrt 2 := by rw [Real.sqrt_div,Real.sqrt_one] <;> norm_num
    rw [← hs]
    apply Real.sqrt_le_iff.mpr
    norm_num [Certificate.sqrtHalfUpper]
  have hrat : (1+(Certificate.sqrtHalfUpper:ℝ))*(Certificate.edgebar:ℝ)<(Certificate.Dbar:ℝ) := by
    norm_num [Certificate.sqrtHalfUpper,Certificate.edgebar,Certificate.Dbar]
  exact (mul_le_mul_of_nonneg_right (show coareaConstant≤1+(Certificate.sqrtHalfUpper:ℝ) by unfold coareaConstant;linarith)
    (by norm_num [Certificate.edgebar])).trans_lt hrat

end LonelyRunnerNew.FiniteCore

namespace LonelyRunnerNew.TaggedState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

theorem stable_core_cost_mean (s : TaggedState Label n)
    (hs : ∀ t,Step s t → t.quality≤s.quality) (hM : 0<s.edgeMass) :
    (∑ v∈s.coreVertices,s.corePi v*s.coreSmallCost (s.coreSmallCenters hM) v)<(Certificate.Dbar:ℝ) := by
  have h := s.core_cost_mean_of_cut hM (s.stable_core_cut hs hM)
  have hb := mul_lt_mul_of_pos_left (s.stable_small_prime_mean_distance hs hM)
    (show 0<FiniteCore.coareaConstant by unfold FiniteCore.coareaConstant;positivity)
  exact h.trans_lt (hb.trans FiniteCore.coarea_edgebar_lt_Dbar)

theorem universal_core_cost_mean (s : TaggedState Label n)
    (hs : ∀ t,Step s t → t.universalQuality≤s.universalQuality) (hM : 0<s.edgeMass) :
    (∑ v∈s.coreVertices,s.corePi v*s.coreSmallCost (s.coreSmallCenters hM) v)<(Certificate.Dbar:ℝ) := by
  have h := s.core_cost_mean_of_cut hM (s.universal_core_cut hs hM)
  have hb := mul_lt_mul_of_pos_left (s.universal_small_prime_mean_distance hs hM)
    (show 0<FiniteCore.coareaConstant by unfold FiniteCore.coareaConstant;positivity)
  exact h.trans_lt (hb.trans FiniteCore.coarea_edgebar_lt_Dbar)

end LonelyRunnerNew.TaggedState
