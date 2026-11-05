import LonelyRunnerNew.PhysicalStates

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew.PhysicalState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

inductive Step : PhysicalState Label n → PhysicalState Label n → Prop
  | restrict (s) (L R) (hL : L⊆s.geometry.left) (hR : R⊆s.geometry.right)
      (hLN : L.Nonempty) (hRN : R.Nonempty) :
      Step s (s.restrict L R hL hR hLN hRN)
  | prime (s) (L R) (hL : L⊆s.geometry.left) (hR : R⊆s.geometry.right)
      (hLN : L.Nonempty) (hRN : R.Nonempty) (p i j) (hp : Nat.Prime p) (u v)
      (hfL : ∀ x∈L,p^i*u x=s.geometry.leftValue x)
      (hfR : ∀ y∈R,p^j*v y=s.geometry.rightValue y)
      (hnL : ∀ x∈L,¬p∣u x) (hnR : ∀ y∈R,¬p∣v y) :
      Step s (s.divideLayers L R hL hR hLN hRN p i j hp u v hfL hfR)

theorem Step.geometry {s t : PhysicalState Label n} (h : Step s t) :
    TaggedState.Step s.geometry t.geometry := by
  cases h with
  | restrict L R hL hR hLN hRN => exact TaggedState.Step.restrict _ L R hL hR hLN hRN
  | prime L R hL hR hLN hRN p i j hp u v hfL hfR hnL hnR =>
    exact TaggedState.Step.prime _ L R hL hR hLN hRN p i j hp u v hfL hfR hnL hnR

theorem reachable_geometry {s t : PhysicalState Label n}
    (h : Relation.ReflTransGen Step s t) :
    Relation.ReflTransGen TaggedState.Step s.geometry t.geometry := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.tail hstep.geometry

theorem restrict_mass (s : PhysicalState Label n) (L R : Finset Label)
    (hL : L⊆s.geometry.left) (hR : R⊆s.geometry.right)
    (hLN : L.Nonempty) (hRN : R.Nonempty) :
    (s.restrict L R hL hR hLN hRN).edgeMass=s.rectangleMass L R := by
  have he : s.geometry.edges ∩ L.product R =
      s.geometry.edges.filter (fun e => e.1∈L ∧ e.2∈R) := by ext e; simp
  simp only [edgeMass,rectangleMass,restrict,TaggedState.restrict,edgeWeight,he]

theorem restrict_full_quality (s : PhysicalState Label n) (eta tau : ℝ)
    (hL : s.geometry.left⊆s.geometry.left) (hR : s.geometry.right⊆s.geometry.right)
    (hLN : s.geometry.left.Nonempty) (hRN : s.geometry.right.Nonempty) :
    (s.restrict s.geometry.left s.geometry.right hL hR hLN hRN).quality eta tau =
      s.quality eta tau := by
  have he := s.geometry.edges_subset
  simp only [quality,density,edgeMass,edgeWeight,scale,restrict,TaggedState.restrict,
    TaggedState.area,Finset.inter_eq_left.mpr he]

theorem divide_zero_full_quality (s : PhysicalState Label n) (eta tau : ℝ)
    (p : ℕ) (hp : Nat.Prime p) (u v : Label → ℕ)
    (hfL : ∀ x∈s.geometry.left,p^0*u x=s.geometry.leftValue x)
    (hfR : ∀ y∈s.geometry.right,p^0*v y=s.geometry.rightValue y) :
    (s.divideLayers s.geometry.left s.geometry.right (fun _ h => h) (fun _ h => h)
      s.geometry.left_nonempty s.geometry.right_nonempty p 0 0 hp u v hfL hfR).quality eta tau =
      s.quality eta tau := by
  let t := s.divideLayers s.geometry.left s.geometry.right (fun _ h => h) (fun _ h => h)
    s.geometry.left_nonempty s.geometry.right_nonempty p 0 0 hp u v hfL hfR
  have hmass : t.edgeMass=s.edgeMass := by
    have hsub := s.geometry.edges_subset
    simp only [edgeMass,t,divideLayers,TaggedState.divideLayers,
      Finset.inter_eq_left.mpr hsub,edgeWeight,pow_zero,div_one]
    apply Finset.sum_congr rfl
    intro e he
    have hm := Finset.mem_product.mp (s.geometry.edges_subset he)
    rw [show u e.1=s.geometry.leftValue e.1 by simpa using hfL e.1 hm.1,
      show v e.2=s.geometry.rightValue e.2 by simpa using hfR e.2 hm.2]
    simp
  have harea : t.geometry.area=s.geometry.area := rfl
  have hscale : t.scale=s.scale := by simp [scale,t,divideLayers]
  change t.quality eta tau=s.quality eta tau
  simp only [quality,density,hmass,harea,hscale]

/-- Strict physical-score improvement decreases the same natural sum of
positive values; it does not rely on improvement of the old tagged score. -/
theorem improving_step_decreases {s t : PhysicalState Label n} {eta tau : ℝ}
    (hst : Step s t) (hi : s.quality eta tau<t.quality eta tau) :
    t.potential<s.potential := by
  cases hst with
  | restrict L R hL hR hLN hRN =>
    by_cases hproper : L≠s.geometry.left ∨ R≠s.geometry.right
    · exact TaggedState.potential_restrict_lt s.geometry L R hL hR hLN hRN hproper
    · have hLeq : L=s.geometry.left := not_not.mp (not_or.mp hproper).1
      have hReq : R=s.geometry.right := not_not.mp (not_or.mp hproper).2
      subst L R
      rw [restrict_full_quality] at hi
      exact (lt_irrefl _ hi).elim
  | prime L R hL hR hLN hRN p i j hp u v hfL hfR hnL hnR =>
    by_cases hij : 0 < i ∨ 0 < j
    · exact TaggedState.divideLayers_potential_lt s.geometry L R hL hR hLN hRN p i j hp u v hfL hfR hij
    · have hi0 : i=0 := by omega
      have hj0 : j=0 := by omega
      subst i j
      by_cases hproper : L≠s.geometry.left ∨ R≠s.geometry.right
      · change (s.geometry.divideLayers L R hL hR hLN hRN p 0 0 hp u v hfL hfR).potential<_
        rw [TaggedState.divide_zero_potential]
        exact TaggedState.potential_restrict_lt s.geometry L R hL hR hLN hRN hproper
      · have hLeq : L=s.geometry.left := not_not.mp (not_or.mp hproper).1
        have hReq : R=s.geometry.right := not_not.mp (not_or.mp hproper).2
        subst L R
        have he := s.divide_zero_full_quality eta tau p hp u v hfL hfR
        have hb : s.quality eta tau<s.quality eta tau := by simpa only [he] using hi
        exact (lt_irrefl _ hb).elim

theorem stable_state_exists (s : PhysicalState Label n) (eta tau : ℝ) :
    ∃ t, Relation.ReflTransGen Step s t ∧ s.quality eta tau≤t.quality eta tau ∧
      ∀ u,Step t u → u.quality eta tau≤t.quality eta tau :=
  exists_stable_of_descent Step potential (fun t => t.quality eta tau)
    (fun _ _ h hi => improving_step_decreases h hi) s

theorem quality_pos_iff_mass (s : PhysicalState Label n) {eta tau : ℝ} (he : 0<eta) :
    0<s.quality eta tau ↔ 0<s.edgeMass := by
  constructor
  · intro h
    by_contra hm
    have hz := le_antisymm (le_of_not_gt hm) s.edgeMass_nonneg
    simp [quality,density,hz,Real.zero_rpow he.ne'] at h
  · intro h
    exact mul_pos (mul_pos (mul_pos (Real.rpow_pos_of_pos (div_pos h s.geometry.area_pos) _)
      s.geometry.area_pos) s.scale_pos)
      (Real.rpow_pos_of_pos (div_pos s.geometry.area_pos (sq_pos_of_pos s.geometry.ambient_pos)) _)

theorem stable_positive_state_exists (s : PhysicalState Label n) (eta tau : ℝ)
    (he : 0<eta) (hM : 0<s.edgeMass) :
    ∃ t, Relation.ReflTransGen Step s t ∧ s.quality eta tau≤t.quality eta tau ∧
      (∀ u,Step t u → u.quality eta tau≤t.quality eta tau) ∧ 0<t.edgeMass := by
  obtain ⟨t,hr,hq,hs⟩ := s.stable_state_exists eta tau
  exact ⟨t,hr,hq,hs,(t.quality_pos_iff_mass he).1 ((s.quality_pos_iff_mass he).2 hM |>.trans_le hq)⟩

end LonelyRunnerNew.PhysicalState
