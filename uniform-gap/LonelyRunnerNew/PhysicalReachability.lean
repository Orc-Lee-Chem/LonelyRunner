import LonelyRunnerNew.PhysicalConcentration

noncomputable section
set_option autoImplicit false
namespace LonelyRunnerNew.PhysicalState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

def InRange (s : PhysicalState Label n) : Prop :=
  (∀ x∈s.geometry.left,s.A≤(s.geometry.leftValue x:ℝ) ∧ (s.geometry.leftValue x:ℝ)<2*s.A) ∧
  (∀ y∈s.geometry.right,s.B≤(s.geometry.rightValue y:ℝ) ∧ (s.geometry.rightValue y:ℝ)<2*s.B)

theorem divide_value_range {p i : ℕ} (hp : Nat.Prime p) {A : ℝ} {x u : ℕ}
    (hf : p^i*u=x) (hx : A≤(x:ℝ) ∧ (x:ℝ)<2*A) :
    A/(p:ℝ)^i≤(u:ℝ) ∧ (u:ℝ)<2*(A/(p:ℝ)^i) := by
  have hpow : (0:ℝ)<(p:ℝ)^i := pow_pos (by exact_mod_cast hp.pos) _
  have heq : (u:ℝ)=(x:ℝ)/(p:ℝ)^i := by
    apply (eq_div_iff hpow.ne').mpr
    have hh : (p:ℝ)^i*(u:ℝ)=(x:ℝ) := by exact_mod_cast hf
    linarith
  rw [heq]
  refine ⟨div_le_div_of_nonneg_right hx.1 hpow.le,?_⟩
  have hh := div_lt_div_of_pos_right hx.2 hpow
  convert hh using 1 <;> ring

theorem Step.preserves_range {s t : PhysicalState Label n} (h : Step s t) (hr : s.InRange) :
    t.InRange := by
  cases h with
  | restrict L R hL hR hLN hRN =>
    exact ⟨fun x hx => hr.1 x (hL hx),fun y hy => hr.2 y (hR hy)⟩
  | prime L R hL hR hLN hRN p i j hp u v hfL hfR hnL hnR =>
    exact ⟨fun x hx => divide_value_range hp (hfL x hx) (hr.1 x (hL hx)),
      fun y hy => divide_value_range hp (hfR y hy) (hr.2 y (hR hy))⟩

theorem reachable_preserves_range {s t : PhysicalState Label n}
    (h : Relation.ReflTransGen Step s t) (hr : s.InRange) : t.InRange := by
  induction h with
  | refl => exact hr
  | tail _ hstep ih => exact hstep.preserves_range ih

/-- Physical-score restabilization preserves the actual scales, rough values,
and the original separation threshold exactly. Positivity, injectivity and
cardinality budgets are checked fields of the output geometry. -/
theorem stable_rough_state_exists (s : PhysicalState Label n) (eta tau : ℝ)
    (he : 0<eta) (hM : 0<s.edgeMass) (hrange : s.InRange)
    (hL : ∀ x∈s.geometry.left,rough 142 (s.geometry.leftValue x))
    (hR : ∀ y∈s.geometry.right,rough 142 (s.geometry.rightValue y))
    {P : ℝ} (hsep : TaggedState.separated P s.geometry) :
    ∃ t,Relation.ReflTransGen Step s t ∧ s.quality eta tau≤t.quality eta tau ∧
      (∀ u,Step t u → u.quality eta tau≤t.quality eta tau) ∧ 0<t.edgeMass ∧ t.InRange ∧
      (∀ x∈t.geometry.left,rough 142 (t.geometry.leftValue x)) ∧
      (∀ y∈t.geometry.right,rough 142 (t.geometry.rightValue y)) ∧
      TaggedState.separated P t.geometry := by
  obtain ⟨t,ht,hq,hs,hpos⟩ := s.stable_positive_state_exists eta tau he hM
  have hg := reachable_geometry ht
  have hrough := TaggedState.reachable_preserves_rough hg hL hR
  exact ⟨t,ht,hq,hs,hpos,reachable_preserves_range ht hrange,hrough.1,hrough.2,
    TaggedState.reachable_preserves_separation hg hsep⟩

end LonelyRunnerNew.PhysicalState
