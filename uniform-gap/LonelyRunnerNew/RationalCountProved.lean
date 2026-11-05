import LonelyRunnerNew.RCLargeRows
import LonelyRunnerNew.RCLargeSingleRow
import LonelyRunnerNew.RCRangeReduction

noncomputable section
set_option autoImplicit false
namespace LonelyRunnerNew.RoughRational

/-- Original, unchanged, fully quantified large-range RC proposition.
No analytic sieve/packing/prime-counting inputs remain. -/
theorem largeRangeCountBound_proved : LargeRangeCountBound := by
  apply largeRange_iff_two_ranges.mpr
  intro ell R T hell hR hRn hT hlarge S hrough hsector hsep hcase
  by_cases hB : 128≤Real.sqrt (T/R)
  · exact rc_large_B S hR hT hell hRn hlarge hB hrough hsector hsep
  · rcases hcase with h | hA
    · exact False.elim (hB h)
    · exact rc_small_B_large_A S hR hT hell (lt_of_not_ge hB) hA hrough hsector hsep

theorem countBound_proved : CountBound := countBound_iff_largeRange.mpr largeRangeCountBound_proved

end LonelyRunnerNew.RoughRational
