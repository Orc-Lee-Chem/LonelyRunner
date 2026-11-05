import LonelyRunnerNew.PrimeTransport
import LonelyRunnerNew.StableDescent
import Mathlib.Algebra.Order.BigOperators.Group.Finset

noncomputable section
open scoped BigOperators

namespace LonelyRunnerNew

/-- Labels, rather than integer values, identify the vertices and edge support. -/
structure TaggedState (Label : Type*) [DecidableEq Label] (n : ℕ) where
  left : Finset Label
  right : Finset Label
  left_nonempty : left.Nonempty
  right_nonempty : right.Nonempty
  leftValue : Label → ℕ
  rightValue : Label → ℕ
  left_positive : ∀ x ∈ left, 0 < leftValue x
  right_positive : ∀ y ∈ right, 0 < rightValue y
  left_injective : Set.InjOn leftValue (left : Set Label)
  right_injective : Set.InjOn rightValue (right : Set Label)
  left_budget : left.card ≤ n
  right_budget : right.card ≤ n
  edges : Finset (Label × Label)
  edges_subset : edges ⊆ left.product right
  a : ℝ
  b : ℝ
  a_positive : 0 < a
  b_positive : 0 < b

namespace TaggedState

variable {Label : Type*} [DecidableEq Label] {n : ℕ}

def potential (s : TaggedState Label n) : ℕ :=
  (∑ x ∈ s.left, s.leftValue x) + ∑ y ∈ s.right, s.rightValue y

def density (s : TaggedState Label n) : ℝ :=
  (∑ e ∈ s.edges, weight s.a s.b (s.leftValue e.1) (s.rightValue e.2)) /
    ((s.left.card : ℝ) * (s.right.card : ℝ))

def quality (s : TaggedState Label n) : ℝ :=
  Real.rpow s.density q * ((s.left.card : ℝ) * (s.right.card : ℝ)) * (s.a * s.b) *
    Real.rpow (((s.left.card : ℝ) * (s.right.card : ℝ)) / (n : ℝ) ^ 2) sigma

theorem quality_congr (s t : TaggedState Label n)
    (hL : s.left = t.left) (hR : s.right = t.right) (hE : s.edges = t.edges)
    (ha : s.a = t.a) (hb : s.b = t.b)
    (hvL : ∀ x ∈ s.left, s.leftValue x = t.leftValue x)
    (hvR : ∀ y ∈ s.right, s.rightValue y = t.rightValue y) : s.quality = t.quality := by
  have hsum : (∑ e ∈ s.edges, weight s.a s.b (s.leftValue e.1) (s.rightValue e.2)) =
      ∑ e ∈ t.edges, weight t.a t.b (t.leftValue e.1) (t.rightValue e.2) := by
    rw [← hE]
    apply Finset.sum_congr rfl
    intro e he
    have hmem := Finset.mem_product.mp (s.edges_subset he)
    rw [ha, hb, hvL e.1 hmem.1, hvR e.2 hmem.2]
  unfold quality density
  rw [hsum, hL, hR, ha, hb]

def restrict (s : TaggedState Label n) (L R : Finset Label)
    (hL : L ⊆ s.left) (hR : R ⊆ s.right) (hLN : L.Nonempty) (hRN : R.Nonempty) :
    TaggedState Label n where
  left := L
  right := R
  left_nonempty := hLN
  right_nonempty := hRN
  leftValue := s.leftValue
  rightValue := s.rightValue
  left_positive := fun x hx => s.left_positive x (hL hx)
  right_positive := fun y hy => s.right_positive y (hR hy)
  left_injective := fun _ hx _ hy heq => s.left_injective (hL hx) (hL hy) heq
  right_injective := fun _ hx _ hy heq => s.right_injective (hR hx) (hR hy) heq
  left_budget := (Finset.card_le_card hL).trans s.left_budget
  right_budget := (Finset.card_le_card hR).trans s.right_budget
  edges := s.edges ∩ L.product R
  edges_subset := Finset.inter_subset_right
  a := s.a
  b := s.b
  a_positive := s.a_positive
  b_positive := s.b_positive

theorem potential_restrict_le (s : TaggedState Label n) (L R : Finset Label)
    (hL : L ⊆ s.left) (hR : R ⊆ s.right) (hLN : L.Nonempty) (hRN : R.Nonempty) :
    (s.restrict L R hL hR hLN hRN).potential ≤ s.potential := by
  exact Nat.add_le_add (Finset.sum_le_sum_of_subset hL) (Finset.sum_le_sum_of_subset hR)

omit [DecidableEq Label] in
theorem positive_sum_strict_subset {A B : Finset Label} (hsub : A ⊆ B) (hne : A ≠ B)
    (f : Label → ℕ) (hpos : ∀ x ∈ B, 0 < f x) :
    ∑ x ∈ A, f x < ∑ x ∈ B, f x := by
  have hnot : ¬ B ⊆ A := fun h => hne (Finset.Subset.antisymm hsub h)
  obtain ⟨x, hx, hxA⟩ := Finset.not_subset.mp hnot
  exact Finset.sum_lt_sum_of_subset hsub hx hxA (hpos x hx) (fun _ _ _ => Nat.zero_le _)

theorem potential_restrict_lt (s : TaggedState Label n) (L R : Finset Label)
    (hL : L ⊆ s.left) (hR : R ⊆ s.right) (hLN : L.Nonempty) (hRN : R.Nonempty)
    (hproper : L ≠ s.left ∨ R ≠ s.right) :
    (s.restrict L R hL hR hLN hRN).potential < s.potential := by
  rcases hproper with hl | hr
  · exact add_lt_add_of_lt_of_le
      (positive_sum_strict_subset hL hl s.leftValue s.left_positive)
      (Finset.sum_le_sum_of_subset hR)
  · exact add_lt_add_of_le_of_lt (Finset.sum_le_sum_of_subset hL)
      (positive_sum_strict_subset hR hr s.rightValue s.right_positive)

omit [DecidableEq Label] in
/-- The prime-division part of the concrete natural-potential argument. -/
theorem prime_division_mass_lt {p : ℕ} (hp : Nat.Prime p) {i : ℕ} (hi : 0 < i)
    (A : Finset Label) (hA : A.Nonempty) (old new : Label → ℕ)
    (hnew : ∀ x ∈ A, 0 < new x)
    (hfactor : ∀ x ∈ A, p ^ i * new x = old x) :
    ∑ x ∈ A, new x < ∑ x ∈ A, old x := by
  apply Finset.sum_lt_sum_of_nonempty hA
  intro x hx
  rw [← hfactor x hx]
  have hpow : 1 < p ^ i := Nat.one_lt_pow hi.ne' hp.one_lt
  simpa only [one_mul] using Nat.mul_lt_mul_of_pos_right hpow (hnew x hx)

/-- Restrict to two layers and divide their common powers, without rebuilding
the edge support from the numerical values of the new vertices. -/
def divideLayers (s : TaggedState Label n) (L R : Finset Label)
    (hL : L ⊆ s.left) (hR : R ⊆ s.right) (hLN : L.Nonempty) (hRN : R.Nonempty)
    (p i j : ℕ) (hp : Nat.Prime p) (u v : Label → ℕ)
    (hfL : ∀ x ∈ L, p ^ i * u x = s.leftValue x)
    (hfR : ∀ y ∈ R, p ^ j * v y = s.rightValue y) : TaggedState Label n where
  left := L
  right := R
  left_nonempty := hLN
  right_nonempty := hRN
  leftValue := u
  rightValue := v
  left_positive := fun x hx => Nat.pos_of_mul_pos_left
    ((hfL x hx).symm ▸ s.left_positive x (hL hx))
  right_positive := fun y hy => Nat.pos_of_mul_pos_left
    ((hfR y hy).symm ▸ s.right_positive y (hR hy))
  left_injective := by
    intro x hx y hy heq
    apply s.left_injective (hL hx) (hL hy)
    rw [← hfL x hx, ← hfL y hy, heq]
  right_injective := by
    intro x hx y hy heq
    apply s.right_injective (hR hx) (hR hy)
    rw [← hfR x hx, ← hfR y hy, heq]
  left_budget := (Finset.card_le_card hL).trans s.left_budget
  right_budget := (Finset.card_le_card hR).trans s.right_budget
  edges := s.edges ∩ L.product R
  edges_subset := Finset.inter_subset_right
  a := s.a * (p : ℝ) ^ (i - j)
  b := s.b * (p : ℝ) ^ (j - i)
  a_positive := mul_pos s.a_positive (pow_pos (by exact_mod_cast hp.pos) _)
  b_positive := mul_pos s.b_positive (pow_pos (by exact_mod_cast hp.pos) _)

theorem divideLayers_edge_weight (s : TaggedState Label n) (L R : Finset Label)
    (hL : L ⊆ s.left) (hR : R ⊆ s.right) (hLN : L.Nonempty) (hRN : R.Nonempty)
    (p i j : ℕ) (hp : Nat.Prime p) (u v : Label → ℕ)
    (hfL : ∀ x ∈ L, p ^ i * u x = s.leftValue x)
    (hfR : ∀ y ∈ R, p ^ j * v y = s.rightValue y)
    (hnL : ∀ x ∈ L, ¬ p ∣ u x) (hnR : ∀ y ∈ R, ¬ p ∣ v y)
    (x y : Label) (hx : x ∈ L) (hy : y ∈ R) :
    weight s.a s.b (s.leftValue x) (s.rightValue y) =
      weight (s.divideLayers L R hL hR hLN hRN p i j hp u v hfL hfR).a
        (s.divideLayers L R hL hR hLN hRN p i j hp u v hfL hfR).b (u x) (v y) := by
  have h := prime_layer_transport hp (hnL x hx) (hnR y hy) s.a s.b i j
  rw [hfL x hx, hfR y hy] at h
  exact h

theorem divideLayers_potential_lt (s : TaggedState Label n) (L R : Finset Label)
    (hL : L ⊆ s.left) (hR : R ⊆ s.right) (hLN : L.Nonempty) (hRN : R.Nonempty)
    (p i j : ℕ) (hp : Nat.Prime p) (u v : Label → ℕ)
    (hfL : ∀ x ∈ L, p ^ i * u x = s.leftValue x)
    (hfR : ∀ y ∈ R, p ^ j * v y = s.rightValue y) (hij : 0 < i ∨ 0 < j) :
    (s.divideLayers L R hL hR hLN hRN p i j hp u v hfL hfR).potential < s.potential := by
  let t := s.divideLayers L R hL hR hLN hRN p i j hp u v hfL hfR
  have hleL : (∑ x ∈ L, u x) ≤ ∑ x ∈ s.left, s.leftValue x := by
    apply le_trans (Finset.sum_le_sum (fun x hx => ?_)) (Finset.sum_le_sum_of_subset hL)
    rw [← hfL x hx]
    exact Nat.le_mul_of_pos_left _ (pow_pos hp.pos _)
  have hleR : (∑ y ∈ R, v y) ≤ ∑ y ∈ s.right, s.rightValue y := by
    apply le_trans (Finset.sum_le_sum (fun y hy => ?_)) (Finset.sum_le_sum_of_subset hR)
    rw [← hfR y hy]
    exact Nat.le_mul_of_pos_left _ (pow_pos hp.pos _)
  rcases hij with hi | hj
  · have hlt := lt_of_lt_of_le
      (prime_division_mass_lt hp hi L hLN s.leftValue u t.left_positive hfL)
      (Finset.sum_le_sum_of_subset hL)
    exact add_lt_add_of_lt_of_le hlt hleR
  · have hlt := lt_of_lt_of_le
      (prime_division_mass_lt hp hj R hRN s.rightValue v t.right_positive hfR)
      (Finset.sum_le_sum_of_subset hR)
    exact add_lt_add_of_le_of_lt hleL hlt

theorem divide_zero_quality (s : TaggedState Label n) (L R : Finset Label)
    (hL : L ⊆ s.left) (hR : R ⊆ s.right) (hLN : L.Nonempty) (hRN : R.Nonempty)
    (p : ℕ) (hp : Nat.Prime p) (u v : Label → ℕ)
    (hfL : ∀ x ∈ L, p ^ 0 * u x = s.leftValue x)
    (hfR : ∀ y ∈ R, p ^ 0 * v y = s.rightValue y) :
    (s.divideLayers L R hL hR hLN hRN p 0 0 hp u v hfL hfR).quality =
      (s.restrict L R hL hR hLN hRN).quality := by
  apply quality_congr (s.divideLayers L R hL hR hLN hRN p 0 0 hp u v hfL hfR)
    (s.restrict L R hL hR hLN hRN) rfl rfl rfl (by simp [divideLayers, restrict])
    (by simp [divideLayers, restrict])
  · intro x hx
    simpa only [divideLayers, restrict, pow_zero, one_mul] using hfL x hx
  · intro y hy
    simpa only [divideLayers, restrict, pow_zero, one_mul] using hfR y hy

theorem divide_zero_potential (s : TaggedState Label n) (L R : Finset Label)
    (hL : L ⊆ s.left) (hR : R ⊆ s.right) (hLN : L.Nonempty) (hRN : R.Nonempty)
    (p : ℕ) (hp : Nat.Prime p) (u v : Label → ℕ)
    (hfL : ∀ x ∈ L, p ^ 0 * u x = s.leftValue x)
    (hfR : ∀ y ∈ R, p ^ 0 * v y = s.rightValue y) :
    (s.divideLayers L R hL hR hLN hRN p 0 0 hp u v hfL hfR).potential =
      (s.restrict L R hL hR hLN hRN).potential := by
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro x hx
    simpa only [divideLayers, restrict, pow_zero, one_mul] using hfL x hx
  · apply Finset.sum_congr rfl
    intro y hy
    simpa only [divideLayers, restrict, pow_zero, one_mul] using hfR y hy

theorem restrict_full_quality (s : TaggedState Label n) (hL : s.left ⊆ s.left)
    (hR : s.right ⊆ s.right) (hLN : s.left.Nonempty) (hRN : s.right.Nonempty) :
    (s.restrict s.left s.right hL hR hLN hRN).quality = s.quality := by
  apply quality_congr (s.restrict s.left s.right hL hR hLN hRN) s rfl rfl
    (Finset.inter_eq_left.mpr s.edges_subset) rfl rfl
  · intro _ _
    rfl
  · intro _ _
    rfl

/-- Actual legal one-step operations. The prime residuals are nondivisible by p. -/
inductive Step : TaggedState Label n → TaggedState Label n → Prop
  | restrict (s) (L R) (hL : L ⊆ s.left) (hR : R ⊆ s.right)
      (hLN : L.Nonempty) (hRN : R.Nonempty) :
      Step s (s.restrict L R hL hR hLN hRN)
  | prime (s) (L R) (hL : L ⊆ s.left) (hR : R ⊆ s.right)
      (hLN : L.Nonempty) (hRN : R.Nonempty) (p i j) (hp : Nat.Prime p) (u v)
      (hfL : ∀ x ∈ L, p ^ i * u x = s.leftValue x)
      (hfR : ∀ y ∈ R, p ^ j * v y = s.rightValue y)
      (hnL : ∀ x ∈ L, ¬ p ∣ u x) (hnR : ∀ y ∈ R, ¬ p ∣ v y) :
      Step s (s.divideLayers L R hL hR hLN hRN p i j hp u v hfL hfR)

theorem improving_step_decreases {s t : TaggedState Label n} (hst : Step s t)
    (himprove : s.quality < t.quality) : t.potential < s.potential := by
  cases hst with
  | restrict L R hL hR hLN hRN =>
    by_cases hproper : L ≠ s.left ∨ R ≠ s.right
    · exact potential_restrict_lt s L R hL hR hLN hRN hproper
    · have hLeq : L = s.left := not_not.mp (not_or.mp hproper).1
      have hReq : R = s.right := not_not.mp (not_or.mp hproper).2
      subst L R
      rw [restrict_full_quality] at himprove
      exact (lt_irrefl _ himprove).elim
  | prime L R hL hR hLN hRN p i j hp u v hfL hfR hnL hnR =>
    by_cases hi : i = 0
    · by_cases hj : j = 0
      · subst i j
        rw [divide_zero_quality] at himprove
        rw [divide_zero_potential]
        by_cases hproper : L ≠ s.left ∨ R ≠ s.right
        · exact potential_restrict_lt s L R hL hR hLN hRN hproper
        · have hLeq : L = s.left := not_not.mp (not_or.mp hproper).1
          have hReq : R = s.right := not_not.mp (not_or.mp hproper).2
          subst L R
          rw [restrict_full_quality] at himprove
          exact (lt_irrefl _ himprove).elim
      · exact divideLayers_potential_lt s L R hL hR hLN hRN p i j hp u v hfL hfR
          (Or.inr (Nat.pos_of_ne_zero hj))
    · exact divideLayers_potential_lt s L R hL hR hLN hRN p i j hp u v hfL hfR
        (Or.inl (Nat.pos_of_ne_zero hi))

/-- L03 for the concrete operations, with no unproved descent premise. -/
theorem stable_state_exists (s : TaggedState Label n) :
    ∃ t, Relation.ReflTransGen Step s t ∧ s.quality ≤ t.quality ∧
      ∀ u, Step t u → u.quality ≤ t.quality :=
  exists_stable_of_descent Step potential quality
    (fun _ _ hst himprove => improving_step_decreases hst himprove) s

def separated (P : ℝ) (s : TaggedState Label n) : Prop :=
  (∀ x ∈ s.left, ∀ y ∈ s.left, x ≠ y → P < height (s.leftValue x) (s.leftValue y)) ∧
  (∀ x ∈ s.right, ∀ y ∈ s.right, x ≠ y → P < height (s.rightValue x) (s.rightValue y))

theorem separated_restrict {P : ℝ} (s : TaggedState Label n) (hs : separated P s)
    (L R : Finset Label) (hL : L ⊆ s.left) (hR : R ⊆ s.right)
    (hLN : L.Nonempty) (hRN : R.Nonempty) :
    separated P (s.restrict L R hL hR hLN hRN) := by
  constructor
  · intro x hx y hy hxy
    exact hs.1 x (hL hx) y (hL hy) hxy
  · intro x hx y hy hxy
    exact hs.2 x (hR hx) y (hR hy) hxy

theorem separated_divideLayers {P : ℝ} (s : TaggedState Label n) (hs : separated P s)
    (L R : Finset Label) (hL : L ⊆ s.left) (hR : R ⊆ s.right)
    (hLN : L.Nonempty) (hRN : R.Nonempty) (p i j : ℕ) (hp : Nat.Prime p)
    (u v : Label → ℕ) (hfL : ∀ x ∈ L, p ^ i * u x = s.leftValue x)
    (hfR : ∀ y ∈ R, p ^ j * v y = s.rightValue y) :
    separated P (s.divideLayers L R hL hR hLN hRN p i j hp u v hfL hfR) := by
  constructor
  · intro x hx y hy hxy
    have h := hs.1 x (hL hx) y (hL hy) hxy
    rw [← hfL x hx, ← hfL y hy, height_mul_left _ _ _ (pow_pos hp.pos _)] at h
    exact h
  · intro x hx y hy hxy
    have h := hs.2 x (hR hx) y (hR hy) hxy
    rw [← hfR x hx, ← hfR y hy, height_mul_left _ _ _ (pow_pos hp.pos _)] at h
    exact h

theorem step_preserves_separation {P : ℝ} {s t : TaggedState Label n}
    (hst : Step s t) (hs : separated P s) : separated P t := by
  cases hst with
  | restrict L R hL hR hLN hRN => exact separated_restrict s hs L R hL hR hLN hRN
  | prime L R hL hR hLN hRN p i j hp u v hfL hfR _ _ =>
    exact separated_divideLayers s hs L R hL hR hLN hRN p i j hp u v hfL hfR

theorem reachable_preserves_separation {P : ℝ} {s t : TaggedState Label n}
    (hst : Relation.ReflTransGen Step s t) (hs : separated P s) : separated P t := by
  induction hst with
  | refl => exact hs
  | tail _ hstep ih => exact step_preserves_separation hstep ih

theorem stable_state_exists_separated (s : TaggedState Label n) (P : ℝ)
    (hs : separated P s) :
    ∃ t, Relation.ReflTransGen Step s t ∧ s.quality ≤ t.quality ∧
      (∀ u, Step t u → u.quality ≤ t.quality) ∧ separated P t := by
  obtain ⟨t, hst, hquality, hstable⟩ := stable_state_exists s
  exact ⟨t, hst, hquality, hstable, reachable_preserves_separation hst hs⟩

end TaggedState
end LonelyRunnerNew
