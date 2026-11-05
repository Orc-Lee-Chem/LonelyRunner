import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Finset.Card

set_option autoImplicit false

namespace LonelyRunnerSpec.V1

/-- Frozen direct specification, version 1. No implementation imports. -/
def Statement : Prop :=
  ∀ V : Finset ℕ, (∀ v ∈ V, 0 < v) → 2 ≤ V.card →
    ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧
      ∀ v ∈ V, ∀ k : ℤ,
        |(v : ℝ) * t - (k : ℝ)| >
          (1 + Real.exp (-6888 : ℝ)) / (2 * (V.card : ℝ))

/-- The required absolute-constant corollary, also without implementation imports. -/
def UniformStatement : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ V : Finset ℕ, (∀ v ∈ V, 0 < v) → 2 ≤ V.card →
      ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧
        ∀ v ∈ V, ∀ k : ℤ,
          |(v : ℝ) * t - (k : ℝ)| > (1 + c) / (2 * (V.card : ℝ))

end LonelyRunnerSpec.V1
