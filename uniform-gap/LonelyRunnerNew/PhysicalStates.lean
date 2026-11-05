import LonelyRunnerNew.UniversalDescent
import LonelyRunnerNew.RoughStepInvariants

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew

/-- A physical state has its own denominator and two physical scales. The
underlying labelled geometry is reused; its `a,b` do not define this mass. -/
structure PhysicalState (Label : Type*) [DecidableEq Label] (n : ℕ) where
  geometry : TaggedState Label n
  A : ℝ
  B : ℝ
  D : ℝ
  A_pos : 0 < A
  B_pos : 0 < B
  D_pos : 0 < D

namespace PhysicalState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

def edgeWeight (s : PhysicalState Label n) (e : Label × Label) : ℝ :=
  min 1 ((Nat.gcd (s.geometry.leftValue e.1) (s.geometry.rightValue e.2) : ℝ)/s.D)
def edgeMass (s : PhysicalState Label n) : ℝ := ∑ e ∈ s.geometry.edges,s.edgeWeight e
def density (s : PhysicalState Label n) : ℝ := s.edgeMass/s.geometry.area
def Q0 (s : PhysicalState Label n) : ℝ := s.A*s.B/s.D^2
def scale (s : PhysicalState Label n) : ℝ := s.D^2/(s.A*s.B)
def quality (s : PhysicalState Label n) (eta tau : ℝ) : ℝ :=
  s.density^eta*s.geometry.area*s.scale*(s.geometry.area/(n:ℝ)^2)^tau
def potential (s : PhysicalState Label n) : ℕ := s.geometry.potential

theorem edgeWeight_nonneg (s : PhysicalState Label n) (e : Label × Label) :
    0 ≤ s.edgeWeight e := le_min (by norm_num) (div_nonneg (Nat.cast_nonneg _) s.D_pos.le)
theorem edgeWeight_le_one (s : PhysicalState Label n) (e : Label × Label) :
    s.edgeWeight e ≤ 1 := min_le_left _ _
theorem edgeMass_nonneg (s : PhysicalState Label n) : 0 ≤ s.edgeMass :=
  Finset.sum_nonneg (fun e _ => s.edgeWeight_nonneg e)
theorem scale_pos (s : PhysicalState Label n) : 0 < s.scale :=
  div_pos (sq_pos_of_pos s.D_pos) (mul_pos s.A_pos s.B_pos)
theorem Q0_pos (s : PhysicalState Label n) : 0 < s.Q0 :=
  div_pos (mul_pos s.A_pos s.B_pos) (sq_pos_of_pos s.D_pos)
theorem scale_eq_inv (s : PhysicalState Label n) : s.scale = 1/s.Q0 := by
  simp [scale,Q0]

def rectangleMass (s : PhysicalState Label n) (L R : Finset Label) : ℝ :=
  ∑ e ∈ s.geometry.edges.filter (fun e => e.1∈L ∧ e.2∈R),s.edgeWeight e

def restrict (s : PhysicalState Label n) (L R : Finset Label)
    (hL : L⊆s.geometry.left) (hR : R⊆s.geometry.right)
    (hLN : L.Nonempty) (hRN : R.Nonempty) : PhysicalState Label n where
  geometry := s.geometry.restrict L R hL hR hLN hRN
  A := s.A
  B := s.B
  D := s.D
  A_pos := s.A_pos
  B_pos := s.B_pos
  D_pos := s.D_pos

def divideLayers (s : PhysicalState Label n) (L R : Finset Label)
    (hL : L⊆s.geometry.left) (hR : R⊆s.geometry.right)
    (hLN : L.Nonempty) (hRN : R.Nonempty) (p i j : ℕ) (hp : Nat.Prime p)
    (u v : Label → ℕ) (hfL : ∀ x∈L,p^i*u x=s.geometry.leftValue x)
    (hfR : ∀ y∈R,p^j*v y=s.geometry.rightValue y) : PhysicalState Label n where
  geometry := s.geometry.divideLayers L R hL hR hLN hRN p i j hp u v hfL hfR
  A := s.A/(p:ℝ)^i
  B := s.B/(p:ℝ)^j
  D := s.D/(p:ℝ)^min i j
  A_pos := div_pos s.A_pos (pow_pos (by exact_mod_cast hp.pos) _)
  B_pos := div_pos s.B_pos (pow_pos (by exact_mod_cast hp.pos) _)
  D_pos := div_pos s.D_pos (pow_pos (by exact_mod_cast hp.pos) _)

theorem divideLayers_edgeWeight (s : PhysicalState Label n) (L R : Finset Label)
    (hL : L⊆s.geometry.left) (hR : R⊆s.geometry.right)
    (hLN : L.Nonempty) (hRN : R.Nonempty) (p i j : ℕ) (hp : Nat.Prime p)
    (u v : Label → ℕ) (hfL : ∀ x∈L,p^i*u x=s.geometry.leftValue x)
    (hfR : ∀ y∈R,p^j*v y=s.geometry.rightValue y)
    (hnL : ∀ x∈L,¬p∣u x) (hnR : ∀ y∈R,¬p∣v y)
    {e : Label × Label} (hx : e.1∈L) (hy : e.2∈R) :
    (s.divideLayers L R hL hR hLN hRN p i j hp u v hfL hfR).edgeWeight e=s.edgeWeight e := by
  unfold edgeWeight
  change min 1 ((Nat.gcd (u e.1) (v e.2):ℝ)/(s.D/(p:ℝ)^min i j)) = _
  rw [←hfL e.1 hx,←hfR e.2 hy,gcd_prime_layers hp (hnL _ hx) (hnR _ hy)]
  push_cast
  congr 1
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
  ring

theorem divideLayers_mass (s : PhysicalState Label n) (L R : Finset Label)
    (hL : L⊆s.geometry.left) (hR : R⊆s.geometry.right)
    (hLN : L.Nonempty) (hRN : R.Nonempty) (p i j : ℕ) (hp : Nat.Prime p)
    (u v : Label → ℕ) (hfL : ∀ x∈L,p^i*u x=s.geometry.leftValue x)
    (hfR : ∀ y∈R,p^j*v y=s.geometry.rightValue y)
    (hnL : ∀ x∈L,¬p∣u x) (hnR : ∀ y∈R,¬p∣v y) :
    (s.divideLayers L R hL hR hLN hRN p i j hp u v hfL hfR).edgeMass=s.rectangleMass L R := by
  have he : s.geometry.edges ∩ L.product R =
      s.geometry.edges.filter (fun e => e.1∈L ∧ e.2∈R) := by ext e; simp
  unfold edgeMass rectangleMass
  change (∑ e ∈ s.geometry.edges ∩ L.product R,_) = _
  rw [he]
  apply Finset.sum_congr rfl
  intro e he
  exact s.divideLayers_edgeWeight L R hL hR hLN hRN p i j hp u v hfL hfR hnL hnR
    (Finset.mem_filter.mp he).2.1 (Finset.mem_filter.mp he).2.2

theorem divideLayers_scale (s : PhysicalState Label n) (L R : Finset Label)
    (hL : L⊆s.geometry.left) (hR : R⊆s.geometry.right)
    (hLN : L.Nonempty) (hRN : R.Nonempty) (p i j : ℕ) (hp : Nat.Prime p)
    (u v : Label → ℕ) (hfL : ∀ x∈L,p^i*u x=s.geometry.leftValue x)
    (hfR : ∀ y∈R,p^j*v y=s.geometry.rightValue y) :
    (s.divideLayers L R hL hR hLN hRN p i j hp u v hfL hfR).scale =
      s.scale*(p:ℝ)^((i:ℤ)-(j:ℤ)).natAbs := by
  have hi : (p:ℝ)^i=(p:ℝ)^min i j*(p:ℝ)^(i-j) := by
    rw [←pow_add]
    congr 1
    omega
  have hj : (p:ℝ)^j=(p:ℝ)^min i j*(p:ℝ)^(j-i) := by
    rw [←pow_add]
    congr 1
    omega
  have habs : ((i:ℤ)-(j:ℤ)).natAbs=(i-j)+(j-i) := by
    rcases le_total i j with h | h
    · rw [Int.natAbs_natCast_sub_natCast_of_le h,Nat.sub_eq_zero_of_le h,zero_add]
    · rw [Int.natAbs_natCast_sub_natCast_of_ge h,Nat.sub_eq_zero_of_le h,add_zero]
  change (s.D/(p:ℝ)^min i j)^2/((s.A/(p:ℝ)^i)*(s.B/(p:ℝ)^j)) = _
  rw [hi,hj]
  rw [habs,pow_add]
  unfold scale
  have hp0 : (p:ℝ)≠0 := by exact_mod_cast hp.ne_zero
  field_simp
  <;> ring

theorem divideLayers_Q0 (s : PhysicalState Label n) (L R : Finset Label)
    (hL : L⊆s.geometry.left) (hR : R⊆s.geometry.right)
    (hLN : L.Nonempty) (hRN : R.Nonempty) (p i j : ℕ) (hp : Nat.Prime p)
    (u v : Label → ℕ) (hfL : ∀ x∈L,p^i*u x=s.geometry.leftValue x)
    (hfR : ∀ y∈R,p^j*v y=s.geometry.rightValue y) :
    (s.divideLayers L R hL hR hLN hRN p i j hp u v hfL hfR).Q0 =
      s.Q0/(p:ℝ)^((i:ℤ)-(j:ℤ)).natAbs := by
  have hs := s.divideLayers_scale L R hL hR hLN hRN p i j hp u v hfL hfR
  rw [scale_eq_inv,scale_eq_inv] at hs
  have hq := s.Q0_pos.ne'
  have ht := (s.divideLayers L R hL hR hLN hRN p i j hp u v hfL hfR).Q0_pos.ne'
  have hp0 : (p:ℝ)≠0 := by exact_mod_cast hp.ne_zero
  field_simp at hs ⊢
  nlinarith only [hs]

end PhysicalState
end LonelyRunnerNew
