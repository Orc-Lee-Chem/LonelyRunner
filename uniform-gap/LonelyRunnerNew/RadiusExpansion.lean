import LonelyRunnerNew.SingleSpeedMeasure
import LonelyRunnerNew.Foundation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace LonelyRunnerNew

theorem forbiddenInUnit_mono (v : ℕ) {r r' : ℝ} (h : r ≤ r') :
    forbiddenInUnit v r ⊆ forbiddenInUnit v r' := by
  rintro t ⟨ht, k, hk⟩
  exact ⟨ht, k, hk.trans h⟩

theorem forbidden_shell_measure (v : ℕ) (hv : 0 < v) {r r' : ℝ}
    (hr : 0 ≤ r) (hrr' : r ≤ r') (hr' : r' ≤ 1 / 2) :
    volume (forbiddenInUnit v r' \ forbiddenInUnit v r) =
      ENNReal.ofReal (2 * (r' - r)) := by
  have hrhalf : r ≤ 1 / 2 := hrr'.trans hr'
  have hfinite : volume (forbiddenInUnit v r) ≠ ⊤ := by
    rw [forbiddenInUnit_measure v hv r hr hrhalf]
    exact ENNReal.ofReal_ne_top
  rw [measure_sdiff (forbiddenInUnit_mono v hrr')
    (forbiddenInUnit_measurable v hv r).nullMeasurableSet hfinite,
    forbiddenInUnit_measure v hv r' (hr.trans hrr') hr',
    forbiddenInUnit_measure v hv r hr hrhalf,
    ← ENNReal.ofReal_sub _ (by linarith : 0 ≤ 2 * r)]
  congr 1
  ring

/-- L19. The only gap assumption is the quantitative premise that this outer
measure step consumes; it will be supplied by the arithmetic and geometric proof. -/
theorem radius_expansion (V : Finset ℕ) (hV : valid V) {epsilon : ℝ}
    (he0 : 0 < epsilon) (he1 : epsilon < 1) (hgap : epsilon < gap V) :
    ∃ t : ℝ, t ∈ Ico (0 : ℝ) 1 ∧
      lonelyAt V t ((1 + epsilon) / (2 * (V.card : ℝ))) := by
  classical
  let r : ℝ := 1 / (2 * (V.card : ℝ))
  let r' : ℝ := (1 + epsilon) / (2 * (V.card : ℝ))
  have hn : (0 : ℝ) < V.card := by exact_mod_cast valid_card_pos hV
  have hn2 : (2 : ℝ) ≤ V.card := by exact_mod_cast hV.2
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hrr' : r ≤ r' := by
    dsimp [r, r']
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hr'half : r' ≤ 1 / 2 := by
    dsimp [r']
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (V.card : ℝ))).2
    linarith
  have hwidth : 2 * (r' - r) = epsilon / (V.card : ℝ) := by
    dsimp [r, r']
    field_simp
    ring
  by_contra hnone
  have hsub : uncovered V ⊆
      ⋃ v ∈ V, forbiddenInUnit v r' \ forbiddenInUnit v r := by
    intro t ht
    have hfail : ¬ lonelyAt V t r' := by
      intro hlonely
      exact hnone ⟨t, ht.1, hlonely⟩
    unfold lonelyAt at hfail
    push Not at hfail
    obtain ⟨v, hv, k, hk⟩ := hfail
    apply Set.mem_iUnion.mpr
    refine ⟨v, Set.mem_iUnion.mpr ⟨hv, ?_⟩⟩
    refine ⟨⟨ht.1, k, hk⟩, ?_⟩
    rintro ⟨_, l, hl⟩
    exact (not_le_of_gt (ht.2 v hv l)) hl
  have hmeasure : volume (uncovered V) ≤ ENNReal.ofReal epsilon := by
    calc
      volume (uncovered V) ≤
          volume (⋃ v ∈ V, forbiddenInUnit v r' \ forbiddenInUnit v r) :=
        measure_mono hsub
      _ ≤ ∑ v ∈ V, volume (forbiddenInUnit v r' \ forbiddenInUnit v r) :=
        measure_biUnion_finset_le V _
      _ = ∑ _v ∈ V, ENNReal.ofReal (epsilon / (V.card : ℝ)) := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [forbidden_shell_measure v (hV.1 v hv) hr hrr' hr'half, hwidth]
      _ = ENNReal.ofReal epsilon := by
        rw [Finset.sum_const, ← ENNReal.ofReal_nsmul, nsmul_eq_mul]
        congr 1
        field_simp
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeasure
  rw [ENNReal.toReal_ofReal he0.le] at hreal
  exact (not_le_of_gt hgap) hreal

end LonelyRunnerNew
