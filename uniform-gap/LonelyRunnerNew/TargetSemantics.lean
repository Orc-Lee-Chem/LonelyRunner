import LonelyRunnerNew.Definitions

namespace LonelyRunnerNew

/-- Independent expanded target, with only the original speed assumptions. -/
theorem mainStatement_iff_explicit : mainStatement ↔
    ∀ V : Finset ℕ, (∀ v ∈ V, 0 < v) → 2 ≤ V.card →
      ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧
        ∀ v ∈ V, ∀ k : ℤ,
          (1 + Real.exp (-6888)) / (2 * (V.card : ℝ)) <
            |(v : ℝ) * t - (k : ℝ)| := by
  constructor
  · intro h V hpos hn
    obtain ⟨t, ht, hdist⟩ := h V ⟨hpos, hn⟩
    exact ⟨t, ht.1, ht.2, hdist⟩
  · intro h V hV
    obtain ⟨t, ht0, ht1, hdist⟩ := h V hV.1 hV.2
    exact ⟨t, ⟨ht0, ht1⟩, hdist⟩

end LonelyRunnerNew
