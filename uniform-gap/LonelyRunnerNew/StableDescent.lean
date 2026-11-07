import Mathlib.Logic.Relation
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Push

namespace LonelyRunnerNew

/-- Structural descent lemma for L03. Concrete state moves still need a proof
that every strict improvement decreases their integer potential. -/
theorem exists_stable_of_descent {State : Type*} (step : State → State → Prop)
    (potential : State → ℕ) (value : State → ℝ)
    (hdesc : ∀ s t, step s t → value s < value t → potential t < potential s)
    (s : State) :
    ∃ t, Relation.ReflTransGen step s t ∧ value s ≤ value t ∧
      ∀ u, step t u → value u ≤ value t := by
  classical
  induction s using (measure potential).wf.induction with
  | h s ih =>
    by_cases hstable : ∀ u, step s u → value u ≤ value s
    · exact ⟨s, .refl, le_rfl, hstable⟩
    · push Not at hstable
      obtain ⟨u, hsu, himprove⟩ := hstable
      obtain ⟨t, hut, hvalue, hst⟩ := ih u (hdesc s u hsu himprove)
      exact ⟨t, hut.head hsu, le_trans himprove.le hvalue, hst⟩

end LonelyRunnerNew
