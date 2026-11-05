import LonelyRunnerNew.RoughReciprocal
import LonelyRunnerNew.RoughModerateRow

noncomputable section
set_option autoImplicit false
namespace LonelyRunnerNew.RoughRational

/-- Exact equivalence with the two residual analytic ranges, not a proof of
LargeRangeCountBound. All R endpoints and the medium single row are closed. -/
theorem largeRange_iff_two_ranges : LargeRangeCountBound ↔
    (∀(ell R T : ℝ),4096≤ell → 0<R → 1/Real.sqrt 2≤R → 0<T →
      Real.exp ell<Real.sqrt 2*T → ∀S : Finset ℚ,
      (∀r∈S,roughPoint 142 r) → (∀r∈S,R≤(r:ℝ) ∧ (r:ℝ)<2*R) →
      separated (Real.exp ell) S →
      (128≤Real.sqrt (T/R) ∨ Real.exp ((17/10:ℝ)*ell)<min (2*R) T) →
      (count S T:ℝ)≤1+(17/25:ℝ)*T/ell) := by
  constructor
  · intro h ell R T hell hR _ hT hlarge S hr hs hsep _
    exact h ell R T hell hR hT hlarge S hr hs hsep
  · intro h
    apply largeRange_iff_normalized.mpr
    intro ell R T hell hR hRn hT hlarge S hr hs hsep
    by_cases hB : Real.sqrt (T/R)<128
    · by_cases hA : min (2*R) T≤Real.exp ((17/10:ℝ)*ell)
      · exact rc_small_B_moderate S hR hT hell hB hA hr hs hsep
      · exact h ell R T hell hR hRn hT hlarge S hr hs hsep (Or.inr (lt_of_not_ge hA))
    · exact h ell R T hell hR hRn hT hlarge S hr hs hsep (Or.inl (le_of_not_gt hB))

end LonelyRunnerNew.RoughRational
