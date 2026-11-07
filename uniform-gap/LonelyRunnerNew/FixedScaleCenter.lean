import LonelyRunnerNew.FixedScaleNumerics
import LonelyRunnerNew.KernelScaleAdapter
import LonelyRunnerNew.BootstrapDistribution

noncomputable section
open scoped BigOperators
namespace LonelyRunnerNew.TaggedState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

def fixedKernel (s : TaggedState Label n) (p : ℕ) : ℝ :=
  ∑ i ∈ s.valuationSupport p,∑ j ∈ s.valuationSupport p,
    FixedScale.lambda0^((i:ℤ)-(j:ℤ)).natAbs*(s.alpha p i*s.beta p j)^(3/4:ℝ)

theorem scaleKernel_fixed (s : TaggedState Label n) (p : ℕ) :
    s.scaleKernel p FixedScale.a0=s.fixedKernel p := rfl

/-- The sharp Green bound supplies the old hcell, without an analytic premise. -/
theorem actual_fixed_enhanced (s : TaggedState Label n) (p : ℕ) :
    s.fixedKernel p ≤ FixedScale.C0+FixedScale.d0*
      (∑ i ∈ s.valuationSupport p,(s.alpha p i*s.beta p i)^(3/4:ℝ)) := by
  simpa only [s.scaleKernel_fixed p,FixedScale.C0,FixedScale.d0,FixedScale.lambda0] using
    s.actual_enhanced_scale p FixedScale.a0 FixedScale.a0_pos

theorem fixed_lower_of_L05 (s : TaggedState Label n) (hM : 0<s.edgeMass)
    (p : ℕ) (hp : Nat.Prime p) (hp142 : 142<p)
    (hL05 : ∀ i j,s.mu p (i,j) ≤ (p:ℝ)^(-(((i:ℤ)-(j:ℤ)).natAbs:ℝ)/q)*
      (s.alpha p i*s.beta p j)^(3/4:ℝ)) : 1≤s.fixedKernel p := by
  have hl := FixedScale.prime_lambda_le hp hp142
  calc
    1 = ∑ ij ∈ (s.valuationSupport p).product (s.valuationSupport p),s.mu p ij :=
      (s.mu_sum_common_support hM p).symm
    _ ≤ ∑ ij ∈ (s.valuationSupport p).product (s.valuationSupport p),
        FixedScale.lambda0^((ij.1:ℤ)-(ij.2:ℤ)).natAbs*(s.alpha p ij.1*s.beta p ij.2)^(3/4:ℝ) := by
      apply Finset.sum_le_sum
      intro ij hij
      have hh := hL05 ij.1 ij.2
      rw [layer_lambda s p ij.1 ij.2 hp] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Real.rpow_nonneg (by exact_mod_cast hp.pos.le) _) hl _)
        (Real.rpow_nonneg (mul_nonneg (s.alpha_nonneg p _) (s.beta_nonneg p _)) _))
    _ = _ := by rw [Finset.product_eq_sprod,Finset.sum_product]; rfl

theorem stable_fixed_lower (s : TaggedState Label n)
    (hstable : ∀ t,Step s t → t.quality≤s.quality) (hM : 0<s.edgeMass)
    (p : ℕ) (hp : Nat.Prime p) (hp142 : 142<p) : 1≤s.fixedKernel p :=
  s.fixed_lower_of_L05 hM p hp hp142 (s.stable_layer_concentration hstable hM p hp)

theorem universal_fixed_lower (s : TaggedState Label n)
    (hstable : ∀ t,Step s t → t.universalQuality≤s.universalQuality) (hM : 0<s.edgeMass)
    (p : ℕ) (hp : Nat.Prime p) (hp142 : 142<p) : 1≤s.fixedKernel p :=
  s.fixed_lower_of_L05 hM p hp hp142 (s.universal_layer_target_kernel hstable hM p hp)

theorem initial_center_of_fixed_lower (s : TaggedState Label n) (p : ℕ) (hl : 1≤s.fixedKernel p) :
    ∃ k ∈ s.valuationSupport p,1-(s.alpha p k+s.beta p k)/2≤(89199/250000:ℝ) := by
  have hD := FixedScale.diagonal_lower (hl.trans (s.actual_fixed_enhanced p))
  obtain ⟨k,hk,hm⟩ := LargePrime.center_of_diagonal_lower_bound (s.valuationSupport p) (s.alpha p) (s.beta p)
    (fun i _ => s.alpha_nonneg p i) (fun j _ => s.beta_nonneg p j)
    (s.alpha_sum_common_support p) (s.beta_sum_common_support p) (401/500:ℝ) (by norm_num) hD
  refine ⟨k,hk,?_⟩
  nlinarith

/-- From an actual positive-mass stable state, with no initial center, cell,
continuous estimate or diagonal lower bound supplied as a premise. -/
theorem stable_prime_center (s : TaggedState Label n)
    (hstable : ∀ t,Step s t → t.quality≤s.quality) (hM : 0<s.edgeMass)
    (p : ℕ) (hp : Nat.Prime p) (hp142 : 142<p) :
    ∃ k ∈ s.valuationSupport p,1-(s.alpha p k+s.beta p k)/2≤(121/1000:ℝ) := by
  obtain ⟨k,hk,hinit⟩ := s.initial_center_of_fixed_lower p (s.stable_fixed_lower hstable hM p hp hp142)
  exact ⟨k,hk,s.actual_six_steps hstable hM p hp hp142 k hk (by linarith)⟩

theorem universal_prime_center (s : TaggedState Label n)
    (hstable : ∀ t,Step s t → t.universalQuality≤s.universalQuality) (hM : 0<s.edgeMass)
    (p : ℕ) (hp : Nat.Prime p) (hp142 : 142<p) :
    ∃ k ∈ s.valuationSupport p,1-(s.alpha p k+s.beta p k)/2≤(121/1000:ℝ) := by
  obtain ⟨k,hk,hinit⟩ := s.initial_center_of_fixed_lower p (s.universal_fixed_lower hstable hM p hp hp142)
  exact ⟨k,hk,s.actual_universal_six_steps hstable hM p hp hp142 k hk (by linarith)⟩

end LonelyRunnerNew.TaggedState

namespace LonelyRunnerNew

/-- One state is extracted from V, and that same state supplies a center for
every large prime. This is an LC intermediate result, not the final gap theorem. -/
theorem original_universal_stable_centers (V : Finset ℕ) (hV : valid V) :
    ∃ s : TaggedState ℕ V.card,
      Relation.ReflTransGen TaggedState.Step (initialTaggedState V hV) s ∧
      (initialTaggedState V hV).universalQuality≤s.universalQuality ∧
      (∀ t,TaggedState.Step s t → t.universalQuality≤s.universalQuality) ∧
      0<s.edgeMass ∧
      (∀ p : ℕ,Nat.Prime p → 142<p →
        ∃ k ∈ s.valuationSupport p,1-(s.alpha p k+s.beta p k)/2≤(121/1000:ℝ)) := by
  obtain ⟨s,hr,hq,hs,hM⟩ := original_universal_stable_state_exists V hV
  exact ⟨s,hr,hq,hs,hM,fun p hp hp142 => s.universal_prime_center hs hM p hp hp142⟩

end LonelyRunnerNew
