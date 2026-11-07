import LonelyRunnerNew

set_option autoImplicit false
namespace LonelyRunnerAcceptance

-- Final acceptance adapter template. Not buildable until lonely_runner_gap is proved.
theorem explicit_gap (V : Finset ℕ)
    (hpos : ∀ v ∈ V, 0 < v) (hn : 2 ≤ V.card) :
    ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧
      ∀ v ∈ V, ∀ k : ℤ,
        |(v : ℝ) * t - (k : ℝ)| >
          (1 + Real.exp (-6888 : ℝ)) / (2 * (V.card : ℝ)) := by
  exact LonelyRunnerNew.lonely_runner_gap V hpos hn

theorem uniform_gap :
    ∃ c : ℝ, 0 < c ∧
      ∀ V : Finset ℕ, (∀ v ∈ V, 0 < v) → 2 ≤ V.card →
        ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧
          ∀ v ∈ V, ∀ k : ℤ,
            |(v : ℝ) * t - (k : ℝ)| > (1 + c) / (2 * (V.card : ℝ)) := by
  exact ⟨Real.exp (-6888 : ℝ), Real.exp_pos _, explicit_gap⟩

end LonelyRunnerAcceptance
