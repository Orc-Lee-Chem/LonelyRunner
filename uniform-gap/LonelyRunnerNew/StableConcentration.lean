import LonelyRunnerNew.InitialTaggedState
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

noncomputable section
open scoped BigOperators

namespace LonelyRunnerNew.TaggedState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

def edgeMass (s : TaggedState Label n) : ℝ :=
  ∑ e ∈ s.edges, weight s.a s.b (s.leftValue e.1) (s.rightValue e.2)

def area (s : TaggedState Label n) : ℝ := (s.left.card : ℝ) * (s.right.card : ℝ)

theorem area_pos (s : TaggedState Label n) : 0 < s.area := by
  have hl : (0 : ℝ) < s.left.card := by exact_mod_cast s.left_nonempty.card_pos
  have hr : (0 : ℝ) < s.right.card := by exact_mod_cast s.right_nonempty.card_pos
  exact mul_pos hl hr

theorem ambient_pos (s : TaggedState Label n) : (0 : ℝ) < n := by
  exact_mod_cast lt_of_lt_of_le s.left_nonempty.card_pos s.left_budget

theorem edgeMass_nonneg (s : TaggedState Label n) : 0 ≤ s.edgeMass := by
  apply Finset.sum_nonneg
  intro e he
  unfold weight
  apply le_min (by norm_num)
  exact div_nonneg (Nat.cast_nonneg _) (le_max_of_le_left
    (mul_nonneg s.a_positive.le (Nat.cast_nonneg _)))

theorem score_identity (M A N K : ℝ) (hM : 0 ≤ M) (hA : 0 < A) (hN : 0 < N) :
    (M / A) ^ q * A * K * (A / N) ^ sigma =
      (M / A ^ (3 / 4 : ℝ)) ^ q * (K / N ^ sigma) := by
  rw [Real.div_rpow hM hA.le, Real.div_rpow hA.le hN.le,
    Real.div_rpow hM (Real.rpow_nonneg hA.le _), ← Real.rpow_mul hA.le]
  have hp : A ^ q = A ^ ((3 / 4 : ℝ) * q) * A * A ^ sigma := by
    rw [← Real.rpow_add_one hA.ne', ← Real.rpow_add hA]
    congr 1
    norm_num [q, sigma]
  rw [hp]
  have h1 := (Real.rpow_pos_of_pos hA ((3 / 4 : ℝ) * q)).ne'
  have h2 := (Real.rpow_pos_of_pos hA sigma).ne'
  have h3 := (Real.rpow_pos_of_pos hN sigma).ne'
  field_simp

theorem quality_eq_normalized_mass (s : TaggedState Label n) :
    s.quality = (s.edgeMass / s.area ^ (3 / 4 : ℝ)) ^ q *
      ((s.a * s.b) / ((n : ℝ) ^ 2) ^ sigma) :=
  score_identity s.edgeMass s.area ((n : ℝ)^2) (s.a*s.b)
    s.edgeMass_nonneg s.area_pos (sq_pos_of_pos s.ambient_pos)

/-- The rectangle concentration forced by the existing Step definition.
Positive original mass is explicit here; initialization is handled separately. -/
theorem stable_restriction_concentration (s : TaggedState Label n)
    (hstable : ∀ t, Step s t → t.quality ≤ s.quality) (hM : 0 < s.edgeMass)
    (L R : Finset Label) (hL : L ⊆ s.left) (hR : R ⊆ s.right)
    (hLN : L.Nonempty) (hRN : R.Nonempty) :
    (s.restrict L R hL hR hLN hRN).edgeMass / s.edgeMass ≤
      (((L.card : ℝ) / (s.left.card : ℝ)) *
        ((R.card : ℝ) / (s.right.card : ℝ))) ^ (3 / 4 : ℝ) := by
  let t := s.restrict L R hL hR hLN hRN
  have hc : 0 < (s.a * s.b) / ((n : ℝ)^2) ^ sigma := by
    exact div_pos (mul_pos s.a_positive s.b_positive)
      (Real.rpow_pos_of_pos (sq_pos_of_pos s.ambient_pos) _)
  have hcomp := hstable t (Step.restrict s L R hL hR hLN hRN)
  rw [quality_eq_normalized_mass, quality_eq_normalized_mass] at hcomp
  have hscale : t.a * t.b = s.a * s.b := rfl
  rw [hscale] at hcomp
  have hpow := (mul_le_mul_iff_left₀ hc).mp hcomp
  have hscore := (Real.rpow_le_rpow_iff
    (div_nonneg t.edgeMass_nonneg (Real.rpow_nonneg t.area_pos.le _))
    (div_nonneg s.edgeMass_nonneg (Real.rpow_nonneg s.area_pos.le _))
    (by norm_num [q] : 0 < q)).mp hpow
  have hcross := (div_le_div_iff₀ (Real.rpow_pos_of_pos t.area_pos (3/4:ℝ))
    (Real.rpow_pos_of_pos s.area_pos (3/4:ℝ))).mp hscore
  have hratio : t.area / s.area =
      ((L.card : ℝ) / (s.left.card : ℝ)) * ((R.card : ℝ) / (s.right.card : ℝ)) := by
    change ((L.card : ℝ)*(R.card : ℝ)) /
      ((s.left.card : ℝ)*(s.right.card : ℝ)) = _
    ring
  rw [← hratio, Real.div_rpow t.area_pos.le s.area_pos.le]
  apply (div_le_div_iff₀ hM (Real.rpow_pos_of_pos s.area_pos (3/4:ℝ))).2
  nlinarith only [hcross]

theorem edgeMass_pos_of_nonempty (s : TaggedState Label n) (hE : s.edges.Nonempty) :
    0 < s.edgeMass := by
  apply Finset.sum_pos _ hE
  intro e he
  have hm := Finset.mem_product.mp (s.edges_subset he)
  unfold weight
  apply lt_min (by norm_num)
  apply div_pos
  · exact_mod_cast Nat.gcd_pos_of_pos_left (s.rightValue e.2) (s.left_positive e.1 hm.1)
  · apply lt_max_of_lt_left
    exact mul_pos s.a_positive (by exact_mod_cast s.left_positive e.1 hm.1)

theorem quality_pos_iff_mass_pos (s : TaggedState Label n) :
    0 < s.quality ↔ 0 < s.edgeMass := by
  constructor
  · intro hq
    by_contra hM
    have hzero : s.edgeMass = 0 := le_antisymm (le_of_not_gt hM) s.edgeMass_nonneg
    rw [quality_eq_normalized_mass, hzero, zero_div,
      Real.zero_rpow (by norm_num [q] : q ≠ 0), zero_mul] at hq
    exact lt_irrefl 0 hq
  · intro hM
    rw [quality_eq_normalized_mass]
    exact mul_pos (Real.rpow_pos_of_pos
      (div_pos hM (Real.rpow_pos_of_pos s.area_pos _)) _)
      (div_pos (mul_pos s.a_positive s.b_positive)
        (Real.rpow_pos_of_pos (sq_pos_of_pos s.ambient_pos) _))

def rectangleMass (s : TaggedState Label n) (L R : Finset Label) : ℝ :=
  ∑ e ∈ s.edges.filter (fun e => e.1 ∈ L ∧ e.2 ∈ R),
    weight s.a s.b (s.leftValue e.1) (s.rightValue e.2)

/-- Includes empty rectangles, without adding a concentration hypothesis. -/
theorem stable_rectangle_concentration (s : TaggedState Label n)
    (hstable : ∀ t, Step s t → t.quality ≤ s.quality) (hM : 0 < s.edgeMass)
    (L R : Finset Label) (hL : L ⊆ s.left) (hR : R ⊆ s.right) :
    s.rectangleMass L R / s.edgeMass ≤
      (((L.card : ℝ) / (s.left.card : ℝ)) *
        ((R.card : ℝ) / (s.right.card : ℝ))) ^ (3 / 4 : ℝ) := by
  by_cases hLN : L.Nonempty
  · by_cases hRN : R.Nonempty
    · have heq : s.edges ∩ L.product R =
          s.edges.filter (fun e => e.1 ∈ L ∧ e.2 ∈ R) := by
        ext e
        simp
      simpa only [edgeMass, restrict, heq, rectangleMass] using
        stable_restriction_concentration s hstable hM L R hL hR hLN hRN
    · have hzero : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp hRN
      simp [hzero, rectangleMass]
  · have hzero : L = ∅ := Finset.not_nonempty_iff_eq_empty.mp hLN
    simp [hzero, rectangleMass]

def edgeProbability (s : TaggedState Label n) (e : Label × Label) : ℝ :=
  weight s.a s.b (s.leftValue e.1) (s.rightValue e.2) / s.edgeMass

theorem edgeProbability_nonneg (s : TaggedState Label n) (hM : 0 < s.edgeMass)
    (e : Label × Label) : 0 ≤ s.edgeProbability e := by
  apply div_nonneg _ hM.le
  unfold weight
  exact le_min (by norm_num) (div_nonneg (Nat.cast_nonneg _)
    (le_max_of_le_left (mul_nonneg s.a_positive.le (Nat.cast_nonneg _))))

theorem edgeProbability_sum (s : TaggedState Label n) (hM : 0 < s.edgeMass) :
    (∑ e ∈ s.edges, s.edgeProbability e) = 1 := by
  unfold edgeProbability
  rw [← Finset.sum_div]
  exact div_self hM.ne'

theorem empty_edges_quality_zero (s : TaggedState Label n) (hE : s.edges = ∅) :
    s.quality = 0 := by
  simp [quality, density, hE, Real.zero_rpow (by norm_num [q] : q ≠ 0)]

theorem empty_edges_stable (s : TaggedState Label n) (hE : s.edges = ∅) :
    ∀ t, Step s t → t.quality ≤ s.quality := by
  intro t hstep
  rw [empty_edges_quality_zero s hE]
  cases hstep with
  | restrict L R hL hR hLN hRN =>
    exact le_of_eq (empty_edges_quality_zero _ (by simp [restrict, hE]))
  | prime L R hL hR hLN hRN p i j hp u v hfL hfR hnL hnR =>
    exact le_of_eq (empty_edges_quality_zero _ (by simp [divideLayers, hE]))

end LonelyRunnerNew.TaggedState

namespace LonelyRunnerNew

theorem initialTaggedState_mass_pos (V : Finset ℕ) (hV : valid V) :
    0 < (initialTaggedState V hV).edgeMass := by
  apply TaggedState.edgeMass_pos_of_nonempty
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (lt_of_lt_of_le (by decide) hV.2)
  exact ⟨(x,y), by simp [initialTaggedState, initialEdges, hx, hy, hxy]⟩

/-- A checked counterexample to the inference "stability alone gives positive mass".
This state is not claimed reachable from the original V. -/
theorem stable_zero_mass_exists (V : Finset ℕ) (hV : valid V) :
    ∃ s : TaggedState ℕ V.card,
      (∀ t, TaggedState.Step s t → t.quality ≤ s.quality) ∧ s.edgeMass = 0 := by
  let s : TaggedState ℕ V.card :=
    { initialTaggedState V hV with edges := ∅, edges_subset := Finset.empty_subset _ }
  exact ⟨s, TaggedState.empty_edges_stable s rfl, by simp [TaggedState.edgeMass, s]⟩

/-- Positive mass is obtained from the original speed set, not postulated. -/
theorem positive_separated_stable_state_exists (V : Finset ℕ) (hV : valid V) (P : ℝ)
    (hsep : separated P V) :
    ∃ t : TaggedState ℕ V.card,
      Relation.ReflTransGen TaggedState.Step (initialTaggedState V hV) t ∧
      Real.rpow (W V) q / 4 ≤ t.quality ∧
      (∀ u, TaggedState.Step t u → u.quality ≤ t.quality) ∧
      TaggedState.separated P t ∧ 0 < t.edgeMass := by
  obtain ⟨t, hp, hq, hst, hsp⟩ := separated_stable_state_exists V hV P hsep
  have hinit := (TaggedState.quality_pos_iff_mass_pos (initialTaggedState V hV)).2
    (initialTaggedState_mass_pos V hV)
  rw [initialTaggedState_quality] at hinit
  exact ⟨t, hp, hq, hst, hsp, (TaggedState.quality_pos_iff_mass_pos t).1 (hinit.trans_le hq)⟩

end LonelyRunnerNew
