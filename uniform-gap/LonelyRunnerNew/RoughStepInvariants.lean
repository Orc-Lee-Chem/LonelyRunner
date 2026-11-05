import LonelyRunnerNew.RoughImageState

noncomputable section
set_option autoImplicit false
namespace LonelyRunnerNew

theorem rough_of_positive_dvd {Y x y : ℕ} (hx : rough Y x) (hy : 0<y)
    (hd : y∣x) : rough Y y := by
  refine ⟨hy,?_⟩
  intro p hp hY hpy
  exact hx.2 p hp hY (hpy.trans hd)

namespace TaggedState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

theorem divideLayers_left_height (s : TaggedState Label n)
    (L R : Finset Label) (hL : L⊆s.left) (hR : R⊆s.right)
    (hLN : L.Nonempty) (hRN : R.Nonempty) (p i j : ℕ) (hp : Nat.Prime p)
    (u v : Label → ℕ) (hfL : ∀ x∈L,p^i*u x=s.leftValue x)
    (hfR : ∀ y∈R,p^j*v y=s.rightValue y)
    {x y : Label} (hx : x∈L) (hy : y∈L) :
    height ((s.divideLayers L R hL hR hLN hRN p i j hp u v hfL hfR).leftValue x)
      ((s.divideLayers L R hL hR hLN hRN p i j hp u v hfL hfR).leftValue y)=
      height (s.leftValue x) (s.leftValue y) := by
  change height (u x) (u y)=_
  rw [← hfL x hx,← hfL y hy,height_mul_left _ _ _ (pow_pos hp.pos _)]

theorem divideLayers_right_height (s : TaggedState Label n)
    (L R : Finset Label) (hL : L⊆s.left) (hR : R⊆s.right)
    (hLN : L.Nonempty) (hRN : R.Nonempty) (p i j : ℕ) (hp : Nat.Prime p)
    (u v : Label → ℕ) (hfL : ∀ x∈L,p^i*u x=s.leftValue x)
    (hfR : ∀ y∈R,p^j*v y=s.rightValue y)
    {x y : Label} (hx : x∈R) (hy : y∈R) :
    height ((s.divideLayers L R hL hR hLN hRN p i j hp u v hfL hfR).rightValue x)
      ((s.divideLayers L R hL hR hLN hRN p i j hp u v hfL hfR).rightValue y)=
      height (s.rightValue x) (s.rightValue y) := by
  change height (v x) (v y)=_
  rw [← hfR x hx,← hfR y hy,height_mul_left _ _ _ (pow_pos hp.pos _)]

/-- Roughness is inherited by positive divisors. Both Step constructors use
their original labelled support; no new diagonal condition is imposed. -/
theorem step_preserves_rough {s t : TaggedState Label n} {Y : ℕ}
    (hst : Step s t)
    (hLrough : ∀ x∈s.left,rough Y (s.leftValue x))
    (hRrough : ∀ y∈s.right,rough Y (s.rightValue y)) :
    (∀ x∈t.left,rough Y (t.leftValue x)) ∧
    (∀ y∈t.right,rough Y (t.rightValue y)) := by
  cases hst with
  | restrict L R hL hR hLN hRN =>
      exact ⟨fun x hx => hLrough x (hL hx),fun y hy => hRrough y (hR hy)⟩
  | prime L R hL hR hLN hRN p i j hp u v hfL hfR hnL hnR =>
      let t := s.divideLayers L R hL hR hLN hRN p i j hp u v hfL hfR
      constructor
      · intro x hx
        apply rough_of_positive_dvd (hLrough x (hL hx)) (t.left_positive x hx)
        refine ⟨p^i,?_⟩
        change s.leftValue x=u x*p^i
        rw [Nat.mul_comm]
        exact (hfL x hx).symm
      · intro y hy
        apply rough_of_positive_dvd (hRrough y (hR hy)) (t.right_positive y hy)
        refine ⟨p^j,?_⟩
        change s.rightValue y=v y*p^j
        rw [Nat.mul_comm]
        exact (hfR y hy).symm

theorem reachable_preserves_rough {s t : TaggedState Label n} {Y : ℕ}
    (hst : Relation.ReflTransGen Step s t)
    (hLrough : ∀ x∈s.left,rough Y (s.leftValue x))
    (hRrough : ∀ y∈s.right,rough Y (s.rightValue y)) :
    (∀ x∈t.left,rough Y (t.leftValue x)) ∧
    (∀ y∈t.right,rough Y (t.rightValue y)) := by
  induction hst with
  | refl => exact ⟨hLrough,hRrough⟩
  | tail _ hstep ih => exact step_preserves_rough hstep ih.1 ih.2

/-- Positive values, same-side injectivity, nonemptiness and ambient budgets
are the checked fields of the actual Step target. Separation uses exact height
preservation for each side's common factor, with no further peeling loss. -/
theorem step_rough_invariants {s t : TaggedState Label n} {Y : ℕ} {P : ℝ}
    (hst : Step s t)
    (hLrough : ∀ x∈s.left,rough Y (s.leftValue x))
    (hRrough : ∀ y∈s.right,rough Y (s.rightValue y)) (hsep : separated P s) :
    (∀ x∈t.left,rough Y (t.leftValue x)) ∧
    (∀ y∈t.right,rough Y (t.rightValue y)) ∧ separated P t ∧
    (∀ x∈t.left,0<t.leftValue x) ∧ (∀ y∈t.right,0<t.rightValue y) ∧
    Set.InjOn t.leftValue (t.left:Set Label) ∧ Set.InjOn t.rightValue (t.right:Set Label) ∧
    t.left.card≤n ∧ t.right.card≤n ∧ t.left.Nonempty ∧ t.right.Nonempty := by
  have hr := step_preserves_rough hst hLrough hRrough
  exact ⟨hr.1,hr.2,step_preserves_separation hst hsep,t.left_positive,t.right_positive,
    t.left_injective,t.right_injective,t.left_budget,t.right_budget,t.left_nonempty,t.right_nonempty⟩

end TaggedState
end LonelyRunnerNew
