import LonelyRunnerNew.TaggedStates
import LonelyRunnerNew.InitialState

noncomputable section

namespace LonelyRunnerNew

/-- Original speed values are used as permanent labels. They are not replaced
when the current integer values are divided during later moves. -/
def initialTaggedState (V : Finset ℕ) (hV : valid V) : TaggedState ℕ V.card where
  left := V
  right := V
  left_nonempty := Finset.card_pos.mp (valid_card_pos hV)
  right_nonempty := Finset.card_pos.mp (valid_card_pos hV)
  leftValue := id
  rightValue := id
  left_positive := hV.1
  right_positive := hV.1
  left_injective := fun _ _ _ _ h => h
  right_injective := fun _ _ _ _ h => h
  left_budget := le_rfl
  right_budget := le_rfl
  edges := initialEdges V
  edges_subset := Finset.filter_subset _ _
  a := 1 / (2 * (V.card : ℝ))
  b := 1 / (2 * (V.card : ℝ))
  a_positive := by have hn : (0 : ℝ) < V.card := by exact_mod_cast valid_card_pos hV
                   positivity
  b_positive := by have hn : (0 : ℝ) < V.card := by exact_mod_cast valid_card_pos hV
                   positivity

theorem initialTaggedState_quality (V : Finset ℕ) (hV : valid V) :
    (initialTaggedState V hV).quality = Real.rpow (W V) q / 4 := by
  change quality V.card V V (initialEdges V) (1 / (2 * (V.card : ℝ)))
    (1 / (2 * (V.card : ℝ))) = _
  exact initial_quality_eq V hV.1 (valid_card_pos hV)

theorem initialTaggedState_separated (V : Finset ℕ) (hV : valid V) (P : ℝ)
    (hsep : separated P V) : TaggedState.separated P (initialTaggedState V hV) :=
  ⟨hsep, hsep⟩

/-- The stable-state extraction starts at the actual original speed set. -/
theorem separated_stable_state_exists (V : Finset ℕ) (hV : valid V) (P : ℝ)
    (hsep : separated P V) :
    ∃ t : TaggedState ℕ V.card,
      Relation.ReflTransGen TaggedState.Step (initialTaggedState V hV) t ∧
      Real.rpow (W V) q / 4 ≤ t.quality ∧
      (∀ u, TaggedState.Step t u → u.quality ≤ t.quality) ∧
      TaggedState.separated P t := by
  obtain ⟨t, hpath, hquality, hstable, hseparated⟩ :=
    TaggedState.stable_state_exists_separated (initialTaggedState V hV) P
      (initialTaggedState_separated V hV P hsep)
  rw [initialTaggedState_quality] at hquality
  exact ⟨t, hpath, hquality, hstable, hseparated⟩

end LonelyRunnerNew
