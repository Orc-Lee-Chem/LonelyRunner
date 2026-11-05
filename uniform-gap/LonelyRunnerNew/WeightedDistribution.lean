import LonelyRunnerNew.LCQuantitativeRetention
import LonelyRunnerNew.PhysicalConcentration

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew

/-- A nonnegative edge measure on the existing labelled geometry. The old
`a,b` fields play no role in this measure. No concentration or LC conclusion
is postulated as a field. Physical weights instantiate this measure below. -/
structure WeightedState (Label : Type*) [DecidableEq Label] (n : ℕ)
    extends TaggedState Label n where
  kernel : Label × Label → ℝ
  kernel_nonneg : ∀ e,0≤kernel e

namespace WeightedState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

def edgeMass (s : WeightedState Label n) : ℝ := ∑ e ∈ s.edges,s.kernel e
def rectangleMass (s : WeightedState Label n) (L R : Finset Label) : ℝ :=
  ∑ e ∈ s.edges.filter (fun e => e.1∈L ∧ e.2∈R),s.kernel e
def edgeProbability (s : WeightedState Label n) (e : Label × Label) : ℝ :=
  s.kernel e/s.edgeMass
theorem edgeMass_nonneg (s : WeightedState Label n) : 0≤s.edgeMass :=
  Finset.sum_nonneg (fun e _ => s.kernel_nonneg e)
theorem edgeProbability_nonneg (s : WeightedState Label n) (hM : 0<s.edgeMass)
    (e : Label × Label) : 0≤s.edgeProbability e := div_nonneg (s.kernel_nonneg e) hM.le
theorem edgeProbability_sum (s : WeightedState Label n) (hM : 0<s.edgeMass) :
    (∑ e ∈ s.edges,s.edgeProbability e)=1 := by
  unfold edgeProbability
  rw [←Finset.sum_div]
  exact div_self hM.ne'

def leftLayer (s : WeightedState Label n) (p i : ℕ) : Finset Label :=
  s.left.filter (fun x => padicValNat p (s.leftValue x) = i)

def rightLayer (s : WeightedState Label n) (p j : ℕ) : Finset Label :=
  s.right.filter (fun y => padicValNat p (s.rightValue y) = j)

def leftValuationSupport (s : WeightedState Label n) (p : ℕ) : Finset ℕ :=
  s.left.image (fun x => padicValNat p (s.leftValue x))

def rightValuationSupport (s : WeightedState Label n) (p : ℕ) : Finset ℕ :=
  s.right.image (fun y => padicValNat p (s.rightValue y))

def alpha (s : WeightedState Label n) (p i : ℕ) : ℝ :=
  ((s.leftLayer p i).card : ℝ) / s.left.card

def beta (s : WeightedState Label n) (p j : ℕ) : ℝ :=
  ((s.rightLayer p j).card : ℝ) / s.right.card

def mu (s : WeightedState Label n) (p : ℕ) (ij : ℕ × ℕ) : ℝ :=
  s.rectangleMass (s.leftLayer p ij.1) (s.rightLayer p ij.2) / s.edgeMass

def valuationPair (s : WeightedState Label n) (p : ℕ) (e : Label × Label) : ℕ × ℕ :=
  (padicValNat p (s.leftValue e.1), padicValNat p (s.rightValue e.2))

/-- A fibre SUM, so distinct edges with the same valuation pair all contribute. -/

theorem mu_eq_fiber_sum (s : WeightedState Label n) (p : ℕ) (ij : ℕ × ℕ) :
    s.mu p ij = ∑ e ∈ s.edges.filter (fun e => s.valuationPair p e = ij),
      s.edgeProbability e := by
  have heq : s.edges.filter (fun e => e.1 ∈ s.leftLayer p ij.1 ∧
      e.2 ∈ s.rightLayer p ij.2) =
      s.edges.filter (fun e => s.valuationPair p e = ij) := by
    apply Finset.filter_congr
    intro e he
    have hm := Finset.mem_product.mp (s.edges_subset he)
    simp [leftLayer, rightLayer, hm.1, hm.2, valuationPair, Prod.ext_iff]
  unfold mu rectangleMass
  rw [heq, Finset.sum_div]
  rfl

theorem alpha_nonneg (s : WeightedState Label n) (p i : ℕ) : 0 ≤ s.alpha p i :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem beta_nonneg (s : WeightedState Label n) (p j : ℕ) : 0 ≤ s.beta p j :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem mu_nonneg (s : WeightedState Label n) (hM : 0 < s.edgeMass) (p : ℕ) (ij : ℕ × ℕ) :
    0 ≤ s.mu p ij := by
  rw [mu_eq_fiber_sum]
  exact Finset.sum_nonneg (fun e _ => s.edgeProbability_nonneg hM e)

theorem alpha_sum_subset (s : WeightedState Label n) (p : ℕ) (A : Finset ℕ) :
    (∑ i ∈ A, s.alpha p i) =
      ((s.left.filter (fun x => padicValNat p (s.leftValue x) ∈ A)).card : ℝ) / s.left.card := by
  unfold alpha leftLayer
  rw [← Finset.sum_div, ← Nat.cast_sum]
  congr 2
  exact Finset.sum_card_fiberwise_eq_card_filter _ _ _

theorem beta_sum_subset (s : WeightedState Label n) (p : ℕ) (B : Finset ℕ) :
    (∑ j ∈ B, s.beta p j) =
      ((s.right.filter (fun y => padicValNat p (s.rightValue y) ∈ B)).card : ℝ) / s.right.card := by
  unfold beta rightLayer
  rw [← Finset.sum_div, ← Nat.cast_sum]
  congr 2
  exact Finset.sum_card_fiberwise_eq_card_filter _ _ _

theorem alpha_sum_one (s : WeightedState Label n) (p : ℕ) :
    (∑ i ∈ s.leftValuationSupport p, s.alpha p i) = 1 := by
  rw [alpha_sum_subset]
  have hf : s.left.filter (fun x => padicValNat p (s.leftValue x) ∈ s.leftValuationSupport p) = s.left :=
    Finset.filter_eq_self.mpr (fun x hx => Finset.mem_image_of_mem _ hx)
  rw [hf]
  exact div_self (by exact_mod_cast s.left_nonempty.card_pos.ne')

theorem beta_sum_one (s : WeightedState Label n) (p : ℕ) :
    (∑ j ∈ s.rightValuationSupport p, s.beta p j) = 1 := by
  rw [beta_sum_subset]
  have hf : s.right.filter (fun y => padicValNat p (s.rightValue y) ∈ s.rightValuationSupport p) = s.right :=
    Finset.filter_eq_self.mpr (fun y hy => Finset.mem_image_of_mem _ hy)
  rw [hf]
  exact div_self (by exact_mod_cast s.right_nonempty.card_pos.ne')

theorem mu_sum_rectangle (s : WeightedState Label n) (p : ℕ) (A B : Finset ℕ) :
    (∑ ij ∈ A.product B, s.mu p ij) =
      s.rectangleMass (s.left.filter (fun x => padicValNat p (s.leftValue x) ∈ A))
        (s.right.filter (fun y => padicValNat p (s.rightValue y) ∈ B)) / s.edgeMass := by
  simp_rw [mu_eq_fiber_sum]
  rw [Finset.sum_fiberwise_eq_sum_filter]
  have heq : s.edges.filter (fun e => s.valuationPair p e ∈ A.product B) =
      s.edges.filter (fun e =>
        e.1 ∈ s.left.filter (fun x => padicValNat p (s.leftValue x) ∈ A) ∧
        e.2 ∈ s.right.filter (fun y => padicValNat p (s.rightValue y) ∈ B)) := by
    apply Finset.filter_congr
    intro e he
    have hm := Finset.mem_product.mp (s.edges_subset he)
    simp [valuationPair, hm.1, hm.2]
  rw [heq]
  unfold edgeProbability rectangleMass
  rw [Finset.sum_div]

theorem mu_sum_one (s : WeightedState Label n) (hM : 0 < s.edgeMass) (p : ℕ) :
    (∑ ij ∈ (s.leftValuationSupport p).product (s.rightValuationSupport p), s.mu p ij) = 1 := by
  simp_rw [mu_eq_fiber_sum]
  rw [Finset.sum_fiberwise_of_maps_to]
  · exact s.edgeProbability_sum hM
  · intro e he
    have hm := Finset.mem_product.mp (s.edges_subset he)
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hm.1, Finset.mem_image_of_mem _ hm.2⟩

theorem leftLayer_empty_of_not_support (s : WeightedState Label n) (p i : ℕ)
    (hi : i ∉ s.leftValuationSupport p) : s.leftLayer p i = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact hi (Finset.mem_image.mpr ⟨x, (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩)

theorem rightLayer_empty_of_not_support (s : WeightedState Label n) (p j : ℕ)
    (hj : j ∉ s.rightValuationSupport p) : s.rightLayer p j = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro y hy
  exact hj (Finset.mem_image.mpr ⟨y, (Finset.mem_filter.mp hy).1, (Finset.mem_filter.mp hy).2⟩)

theorem alpha_zero_off_support (s : WeightedState Label n) (p i : ℕ)
    (hi : i ∉ s.leftValuationSupport p) : s.alpha p i = 0 := by
  simp [alpha, s.leftLayer_empty_of_not_support p i hi]

theorem beta_zero_off_support (s : WeightedState Label n) (p j : ℕ)
    (hj : j ∉ s.rightValuationSupport p) : s.beta p j = 0 := by
  simp [beta, s.rightLayer_empty_of_not_support p j hj]

theorem mu_zero_off_support (s : WeightedState Label n) (p : ℕ) (ij : ℕ × ℕ)
    (hij : ij ∉ (s.leftValuationSupport p).product (s.rightValuationSupport p)) :
    s.mu p ij = 0 := by
  rcases ij with ⟨i,j⟩
  simp only [Finset.product_eq_sprod, Finset.mem_product, not_and_or] at hij
  rcases hij with hi | hj
  · simp [mu, rectangleMass, s.leftLayer_empty_of_not_support p i hi]
  · simp [mu, rectangleMass, s.rightLayer_empty_of_not_support p j hj]

/-- Formal adapter to the rectangle convention used in LargePrimeTails. -/

def valuationSupport (s : WeightedState Label n) (p : ℕ) : Finset ℕ :=
  s.leftValuationSupport p ∪ s.rightValuationSupport p

theorem alpha_sum_common_support (s : WeightedState Label n) (p : ℕ) :
    (∑ i ∈ s.valuationSupport p, s.alpha p i) = 1 := by
  rw [alpha_sum_subset]
  have hf : s.left.filter (fun x => padicValNat p (s.leftValue x) ∈ s.valuationSupport p) = s.left :=
    Finset.filter_eq_self.mpr (fun x hx => Finset.mem_union_left _ (Finset.mem_image_of_mem _ hx))
  rw [hf]
  exact div_self (by exact_mod_cast s.left_nonempty.card_pos.ne')

theorem beta_sum_common_support (s : WeightedState Label n) (p : ℕ) :
    (∑ j ∈ s.valuationSupport p, s.beta p j) = 1 := by
  rw [beta_sum_subset]
  have hf : s.right.filter (fun y => padicValNat p (s.rightValue y) ∈ s.valuationSupport p) = s.right :=
    Finset.filter_eq_self.mpr (fun y hy => Finset.mem_union_right _ (Finset.mem_image_of_mem _ hy))
  rw [hf]
  exact div_self (by exact_mod_cast s.right_nonempty.card_pos.ne')

theorem mu_sum_common_support (s : WeightedState Label n) (hM : 0 < s.edgeMass) (p : ℕ) :
    (∑ ij ∈ (s.valuationSupport p).product (s.valuationSupport p), s.mu p ij) = 1 := by
  simp_rw [mu_eq_fiber_sum]
  rw [Finset.sum_fiberwise_of_maps_to]
  · exact s.edgeProbability_sum hM
  · intro e he
    have hm := Finset.mem_product.mp (s.edges_subset he)
    exact Finset.mem_product.mpr
      ⟨Finset.mem_union_left _ (Finset.mem_image_of_mem _ hm.1),
       Finset.mem_union_right _ (Finset.mem_image_of_mem _ hm.2)⟩

/-- L04 and L05 are explicit generic theorem premises, not state fields.
PhysicalConcentration proves both from the physical score's own stability. -/
def RectangleConcentration (s : WeightedState Label n) : Prop :=
  ∀ L R : Finset Label,L⊆s.left → R⊆s.right →
    s.rectangleMass L R/s.edgeMass ≤
      (((L.card:ℝ)/s.left.card)*((R.card:ℝ)/s.right.card))^(3/4:ℝ)
def LayerConcentration (s : WeightedState Label n) : Prop :=
  ∀ p,Nat.Prime p → ∀ i j,
    s.mu p (i,j) ≤ (p:ℝ)^(-(((i:ℤ)-(j:ℤ)).natAbs:ℝ)/q)*
      (s.alpha p i*s.beta p j)^(3/4:ℝ)

theorem valuation_rectangle_concentration (s : WeightedState Label n)
    (h : s.RectangleConcentration) (p : ℕ) (A B : Finset ℕ) :
    (∑ ij ∈ A.product B,s.mu p ij) ≤
      ((∑ i ∈ A,s.alpha p i)*(∑ j ∈ B,s.beta p j))^(3/4:ℝ) := by
  rw [mu_sum_rectangle,alpha_sum_subset,beta_sum_subset]
  exact h _ _ (Finset.filter_subset _ _) (Finset.filter_subset _ _)

end WeightedState
namespace PhysicalState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

def weighted (s : PhysicalState Label n) : WeightedState Label n where
  toTaggedState := s.geometry
  kernel := s.edgeWeight
  kernel_nonneg := s.edgeWeight_nonneg

theorem weighted_mass (s : PhysicalState Label n) : s.weighted.edgeMass=s.edgeMass := rfl

theorem weighted_rectangle (s : PhysicalState Label n) {eta tau : ℝ}
    (he : 0<eta) (hc : 1+tau=eta/4)
    (hs : ∀ t,Step s t → t.quality eta tau≤s.quality eta tau) (hM : 0<s.edgeMass) :
    s.weighted.RectangleConcentration := by
  intro L R hL hR
  exact s.stable_rectangle_concentration he hc hs hM L R hL hR

theorem weighted_layer_native (s : PhysicalState Label n) {eta tau : ℝ}
    (he : 0<eta) (hc : 1+tau=eta/4)
    (hs : ∀ t,Step s t → t.quality eta tau≤s.quality eta tau) (hM : 0<s.edgeMass)
    (p : ℕ) (hp : Nat.Prime p) (i j : ℕ) :
    s.weighted.mu p (i,j) ≤ (p:ℝ)^(-(((i:ℤ)-(j:ℤ)).natAbs:ℝ)/eta)*
      (s.weighted.alpha p i*s.weighted.beta p j)^(3/4:ℝ) := by
  by_cases hL : (s.geometry.leftLayer p i).Nonempty
  · by_cases hR : (s.geometry.rightLayer p j).Nonempty
    · exact s.stable_layer_concentration_nonempty he hc hs hM p i j hp hL hR
    · have hz := Finset.not_nonempty_iff_eq_empty.mp hR
      have heq : s.weighted.rightLayer p j=∅ := hz
      simp [WeightedState.mu,WeightedState.rectangleMass,heq]
      exact mul_nonneg (Real.rpow_nonneg (by exact_mod_cast hp.pos.le) _)
        (Real.rpow_nonneg (mul_nonneg (s.weighted.alpha_nonneg p i) (s.weighted.beta_nonneg p j)) _)
  · have hz := Finset.not_nonempty_iff_eq_empty.mp hL
    have heq : s.weighted.leftLayer p i=∅ := hz
    simp [WeightedState.mu,WeightedState.rectangleMass,heq]
    exact mul_nonneg (Real.rpow_nonneg (by exact_mod_cast hp.pos.le) _)
      (Real.rpow_nonneg (mul_nonneg (s.weighted.alpha_nonneg p i) (s.weighted.beta_nonneg p j)) _)

theorem ordinary_weighted_layer (s : PhysicalState Label n)
    (hs : ∀ t,Step s t → t.quality q sigma≤s.quality q sigma) (hM : 0<s.edgeMass) :
    s.weighted.LayerConcentration := by
  intro p hp i j
  exact s.weighted_layer_native (by norm_num [q]) (by norm_num [q,sigma]) hs hM p hp i j

theorem universal_weighted_layer (s : PhysicalState Label n)
    (hs : ∀ t,Step s t → t.quality 4 0≤s.quality 4 0) (hM : 0<s.edgeMass) :
    s.weighted.LayerConcentration := by
  intro p hp i j
  exact (s.weighted_layer_native (by norm_num : (0:ℝ)<4) (by norm_num) hs hM p hp i j).trans
    (mul_le_mul_of_nonneg_right (TaggedState.universal_kernel_le_target hp _)
      (Real.rpow_nonneg (mul_nonneg (s.weighted.alpha_nonneg p i) (s.weighted.beta_nonneg p j)) _))

end PhysicalState
end LonelyRunnerNew
