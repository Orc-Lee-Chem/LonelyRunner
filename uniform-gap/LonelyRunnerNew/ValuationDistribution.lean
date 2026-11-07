import LonelyRunnerNew.ValuationLayers
import LonelyRunnerNew.LargePrimeTails

noncomputable section
open scoped BigOperators

namespace LonelyRunnerNew.TaggedState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

def leftValuationSupport (s : TaggedState Label n) (p : ℕ) : Finset ℕ :=
  s.left.image (fun x => padicValNat p (s.leftValue x))
def rightValuationSupport (s : TaggedState Label n) (p : ℕ) : Finset ℕ :=
  s.right.image (fun y => padicValNat p (s.rightValue y))
def alpha (s : TaggedState Label n) (p i : ℕ) : ℝ :=
  ((s.leftLayer p i).card : ℝ) / s.left.card
def beta (s : TaggedState Label n) (p j : ℕ) : ℝ :=
  ((s.rightLayer p j).card : ℝ) / s.right.card
def mu (s : TaggedState Label n) (p : ℕ) (ij : ℕ × ℕ) : ℝ :=
  s.rectangleMass (s.leftLayer p ij.1) (s.rightLayer p ij.2) / s.edgeMass

def valuationPair (s : TaggedState Label n) (p : ℕ) (e : Label × Label) : ℕ × ℕ :=
  (padicValNat p (s.leftValue e.1), padicValNat p (s.rightValue e.2))

/-- A fibre SUM, so distinct edges with the same valuation pair all contribute. -/
theorem mu_eq_fiber_sum (s : TaggedState Label n) (p : ℕ) (ij : ℕ × ℕ) :
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

theorem alpha_nonneg (s : TaggedState Label n) (p i : ℕ) : 0 ≤ s.alpha p i :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
theorem beta_nonneg (s : TaggedState Label n) (p j : ℕ) : 0 ≤ s.beta p j :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
theorem mu_nonneg (s : TaggedState Label n) (hM : 0 < s.edgeMass) (p : ℕ) (ij : ℕ × ℕ) :
    0 ≤ s.mu p ij := by
  rw [mu_eq_fiber_sum]
  exact Finset.sum_nonneg (fun e _ => s.edgeProbability_nonneg hM e)

theorem alpha_sum_subset (s : TaggedState Label n) (p : ℕ) (A : Finset ℕ) :
    (∑ i ∈ A, s.alpha p i) =
      ((s.left.filter (fun x => padicValNat p (s.leftValue x) ∈ A)).card : ℝ) / s.left.card := by
  unfold alpha leftLayer
  rw [← Finset.sum_div, ← Nat.cast_sum]
  congr 2
  exact Finset.sum_card_fiberwise_eq_card_filter _ _ _

theorem beta_sum_subset (s : TaggedState Label n) (p : ℕ) (B : Finset ℕ) :
    (∑ j ∈ B, s.beta p j) =
      ((s.right.filter (fun y => padicValNat p (s.rightValue y) ∈ B)).card : ℝ) / s.right.card := by
  unfold beta rightLayer
  rw [← Finset.sum_div, ← Nat.cast_sum]
  congr 2
  exact Finset.sum_card_fiberwise_eq_card_filter _ _ _

theorem alpha_sum_one (s : TaggedState Label n) (p : ℕ) :
    (∑ i ∈ s.leftValuationSupport p, s.alpha p i) = 1 := by
  rw [alpha_sum_subset]
  have hf : s.left.filter (fun x => padicValNat p (s.leftValue x) ∈ s.leftValuationSupport p) = s.left :=
    Finset.filter_eq_self.mpr (fun x hx => Finset.mem_image_of_mem _ hx)
  rw [hf]
  exact div_self (by exact_mod_cast s.left_nonempty.card_pos.ne')

theorem beta_sum_one (s : TaggedState Label n) (p : ℕ) :
    (∑ j ∈ s.rightValuationSupport p, s.beta p j) = 1 := by
  rw [beta_sum_subset]
  have hf : s.right.filter (fun y => padicValNat p (s.rightValue y) ∈ s.rightValuationSupport p) = s.right :=
    Finset.filter_eq_self.mpr (fun y hy => Finset.mem_image_of_mem _ hy)
  rw [hf]
  exact div_self (by exact_mod_cast s.right_nonempty.card_pos.ne')

theorem mu_sum_rectangle (s : TaggedState Label n) (p : ℕ) (A B : Finset ℕ) :
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

theorem mu_sum_one (s : TaggedState Label n) (hM : 0 < s.edgeMass) (p : ℕ) :
    (∑ ij ∈ (s.leftValuationSupport p).product (s.rightValuationSupport p), s.mu p ij) = 1 := by
  simp_rw [mu_eq_fiber_sum]
  rw [Finset.sum_fiberwise_of_maps_to]
  · exact s.edgeProbability_sum hM
  · intro e he
    have hm := Finset.mem_product.mp (s.edges_subset he)
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hm.1, Finset.mem_image_of_mem _ hm.2⟩

theorem layer_root {P z t exponent : ℝ} {d : ℕ} (he : 0 < exponent)
    (hP : 0 < P) (hz : 0 ≤ z) (ht : 0 ≤ t)
    (h : z ^ exponent ≤ t ^ ((3/4:ℝ)*exponent) / P ^ d) :
    z ≤ P ^ (-(d:ℝ)/exponent) * t ^ (3/4:ℝ) := by
  apply (Real.rpow_le_rpow_iff hz
    (mul_nonneg (Real.rpow_nonneg hP.le _) (Real.rpow_nonneg ht _))
    he).mp
  have hexp : (-(d:ℝ)/exponent)*exponent = -(d:ℝ) := by field_simp [he.ne']
  rw [Real.mul_rpow (Real.rpow_nonneg hP.le _) (Real.rpow_nonneg ht _),
    ← Real.rpow_mul hP.le, ← Real.rpow_mul ht, hexp, Real.rpow_neg hP.le,
    Real.rpow_natCast]
  simpa [div_eq_mul_inv, mul_comm] using h

theorem stable_layer_concentration (s : TaggedState Label n)
    (hstable : ∀ t, Step s t → t.quality ≤ s.quality) (hM : 0 < s.edgeMass)
    (p : ℕ) (hp : Nat.Prime p) (i j : ℕ) :
    s.mu p (i,j) ≤ (p:ℝ) ^ (-(((i:ℤ)-(j:ℤ)).natAbs:ℝ)/q) *
      (s.alpha p i * s.beta p j) ^ (3/4:ℝ) := by
  by_cases hL : (s.leftLayer p i).Nonempty
  · by_cases hR : (s.rightLayer p j).Nonempty
    · exact layer_root (by norm_num [q]) (by exact_mod_cast hp.pos) (s.mu_nonneg hM p (i,j))
        (mul_nonneg (s.alpha_nonneg p i) (s.beta_nonneg p j))
        (s.stable_layer_power hstable hM p i j hp hL hR)
    · have he := Finset.not_nonempty_iff_eq_empty.mp hR
      simp [mu, rectangleMass, he]
      exact mul_nonneg (Real.rpow_nonneg (by exact_mod_cast hp.pos.le) _)
        (Real.rpow_nonneg (mul_nonneg (s.alpha_nonneg p i) (s.beta_nonneg p j)) _)
  · have he := Finset.not_nonempty_iff_eq_empty.mp hL
    simp [mu, rectangleMass, he]
    exact mul_nonneg (Real.rpow_nonneg (by exact_mod_cast hp.pos.le) _)
      (Real.rpow_nonneg (mul_nonneg (s.alpha_nonneg p i) (s.beta_nonneg p j)) _)

theorem valuation_rectangle_concentration (s : TaggedState Label n)
    (hstable : ∀ t, Step s t → t.quality ≤ s.quality) (hM : 0 < s.edgeMass)
    (p : ℕ) (A B : Finset ℕ) :
    (∑ ij ∈ A.product B, s.mu p ij) ≤
      ((∑ i ∈ A, s.alpha p i) * (∑ j ∈ B, s.beta p j)) ^ (3/4:ℝ) := by
  rw [mu_sum_rectangle, alpha_sum_subset, beta_sum_subset]
  exact s.stable_rectangle_concentration hstable hM _ _
    (Finset.filter_subset _ _) (Finset.filter_subset _ _)

theorem leftLayer_empty_of_not_support (s : TaggedState Label n) (p i : ℕ)
    (hi : i ∉ s.leftValuationSupport p) : s.leftLayer p i = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact hi (Finset.mem_image.mpr ⟨x, (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩)

theorem rightLayer_empty_of_not_support (s : TaggedState Label n) (p j : ℕ)
    (hj : j ∉ s.rightValuationSupport p) : s.rightLayer p j = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro y hy
  exact hj (Finset.mem_image.mpr ⟨y, (Finset.mem_filter.mp hy).1, (Finset.mem_filter.mp hy).2⟩)

theorem alpha_zero_off_support (s : TaggedState Label n) (p i : ℕ)
    (hi : i ∉ s.leftValuationSupport p) : s.alpha p i = 0 := by
  simp [alpha, s.leftLayer_empty_of_not_support p i hi]
theorem beta_zero_off_support (s : TaggedState Label n) (p j : ℕ)
    (hj : j ∉ s.rightValuationSupport p) : s.beta p j = 0 := by
  simp [beta, s.rightLayer_empty_of_not_support p j hj]

theorem mu_zero_off_support (s : TaggedState Label n) (p : ℕ) (ij : ℕ × ℕ)
    (hij : ij ∉ (s.leftValuationSupport p).product (s.rightValuationSupport p)) :
    s.mu p ij = 0 := by
  rcases ij with ⟨i,j⟩
  simp only [Finset.product_eq_sprod, Finset.mem_product, not_and_or] at hij
  rcases hij with hi | hj
  · simp [mu, rectangleMass, s.leftLayer_empty_of_not_support p i hi]
  · simp [mu, rectangleMass, s.rightLayer_empty_of_not_support p j hj]

/-- Formal adapter to the rectangle convention used in LargePrimeTails. -/
theorem largePrime_rectangle_concentration (s : TaggedState Label n)
    (hstable : ∀ t, Step s t → t.quality ≤ s.quality) (hM : 0 < s.edgeMass)
    (p : ℕ) (A B : Finset ℕ) (hA : A ⊆ s.leftValuationSupport p)
    (hB : B ⊆ s.rightValuationSupport p) :
    LargePrime.rectangleMass ((s.leftValuationSupport p).product (s.rightValuationSupport p))
      (s.mu p) A B ≤ ((∑ i ∈ A, s.alpha p i)*(∑ j ∈ B, s.beta p j)) ^ (3/4:ℝ) := by
  have heq : ((s.leftValuationSupport p).product (s.rightValuationSupport p)).filter
      (fun ij => ij.1 ∈ A ∧ ij.2 ∈ B) = A.product B := by
    ext ⟨i,j⟩
    simp only [Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product]
    exact ⟨fun h => h.2, fun h => ⟨⟨hA h.1,hB h.2⟩,h⟩⟩
  unfold LargePrime.rectangleMass
  rw [heq]
  exact s.valuation_rectangle_concentration hstable hM p A B

theorem actual_exception_tail_bound (s : TaggedState Label n)
    (hstable : ∀ t, Step s t → t.quality ≤ s.quality) (hM : 0 < s.edgeMass)
    (p k : ℕ) :
    LargePrime.exceptionMass ((s.leftValuationSupport p).product (s.rightValuationSupport p))
      (s.mu p) k ≤
      (((∑ i ∈ (s.leftValuationSupport p).filter (· < k), s.alpha p i) +
        (∑ j ∈ (s.rightValuationSupport p).filter (· < k), s.beta p j))/2) ^ (3/2:ℝ) +
      (((∑ i ∈ (s.leftValuationSupport p).filter (k < ·), s.alpha p i) +
        (∑ j ∈ (s.rightValuationSupport p).filter (k < ·), s.beta p j))/2) ^ (3/2:ℝ) :=
  LargePrime.exceptionMass_le_tail_means _ _ _ (fun _ h => h) (s.mu p) (s.alpha p) (s.beta p)
    (fun i _ => s.alpha_nonneg p i) (fun j _ => s.beta_nonneg p j)
    (fun A hA B hB => s.largePrime_rectangle_concentration hstable hM p A B hA hB) k

theorem layer_kernel_lower_bound (s : TaggedState Label n)
    (hstable : ∀ t, Step s t → t.quality ≤ s.quality) (hM : 0 < s.edgeMass)
    (p : ℕ) (hp : Nat.Prime p) :
    1 ≤ ∑ i ∈ s.leftValuationSupport p, ∑ j ∈ s.rightValuationSupport p,
      (p:ℝ)^(-(((i:ℤ)-(j:ℤ)).natAbs:ℝ)/q) * (s.alpha p i*s.beta p j)^(3/4:ℝ) := by
  calc
    1 = ∑ ij ∈ (s.leftValuationSupport p).product (s.rightValuationSupport p), s.mu p ij :=
      (s.mu_sum_one hM p).symm
    _ ≤ ∑ ij ∈ (s.leftValuationSupport p).product (s.rightValuationSupport p),
        (p:ℝ)^(-(((ij.1:ℤ)-(ij.2:ℤ)).natAbs:ℝ)/q) *
          (s.alpha p ij.1*s.beta p ij.2)^(3/4:ℝ) :=
      Finset.sum_le_sum (fun ij _ => s.stable_layer_concentration hstable hM p hp ij.1 ij.2)
    _ = _ := by rw [Finset.product_eq_sprod, Finset.sum_product]

def valuationSupport (s : TaggedState Label n) (p : ℕ) : Finset ℕ :=
  s.leftValuationSupport p ∪ s.rightValuationSupport p

theorem alpha_sum_common_support (s : TaggedState Label n) (p : ℕ) :
    (∑ i ∈ s.valuationSupport p, s.alpha p i) = 1 := by
  rw [alpha_sum_subset]
  have hf : s.left.filter (fun x => padicValNat p (s.leftValue x) ∈ s.valuationSupport p) = s.left :=
    Finset.filter_eq_self.mpr (fun x hx => Finset.mem_union_left _ (Finset.mem_image_of_mem _ hx))
  rw [hf]
  exact div_self (by exact_mod_cast s.left_nonempty.card_pos.ne')

theorem beta_sum_common_support (s : TaggedState Label n) (p : ℕ) :
    (∑ j ∈ s.valuationSupport p, s.beta p j) = 1 := by
  rw [beta_sum_subset]
  have hf : s.right.filter (fun y => padicValNat p (s.rightValue y) ∈ s.valuationSupport p) = s.right :=
    Finset.filter_eq_self.mpr (fun y hy => Finset.mem_union_right _ (Finset.mem_image_of_mem _ hy))
  rw [hf]
  exact div_self (by exact_mod_cast s.right_nonempty.card_pos.ne')

theorem mu_sum_common_support (s : TaggedState Label n) (hM : 0 < s.edgeMass) (p : ℕ) :
    (∑ ij ∈ (s.valuationSupport p).product (s.valuationSupport p), s.mu p ij) = 1 := by
  simp_rw [mu_eq_fiber_sum]
  rw [Finset.sum_fiberwise_of_maps_to]
  · exact s.edgeProbability_sum hM
  · intro e he
    have hm := Finset.mem_product.mp (s.edges_subset he)
    exact Finset.mem_product.mpr
      ⟨Finset.mem_union_left _ (Finset.mem_image_of_mem _ hm.1),
       Finset.mem_union_right _ (Finset.mem_image_of_mem _ hm.2)⟩

def valuationKernel (s : TaggedState Label n) (p : ℕ) : ℝ :=
  ∑ i ∈ s.valuationSupport p, ∑ j ∈ s.valuationSupport p,
    (p:ℝ)^(-(((i:ℤ)-(j:ℤ)).natAbs:ℝ)/q)*(s.alpha p i*s.beta p j)^(3/4:ℝ)

theorem valuationKernel_ge_one (s : TaggedState Label n)
    (hstable : ∀ t, Step s t → t.quality ≤ s.quality) (hM : 0 < s.edgeMass)
    (p : ℕ) (hp : Nat.Prime p) : 1 ≤ s.valuationKernel p := by
  calc
    1 = ∑ ij ∈ (s.valuationSupport p).product (s.valuationSupport p),s.mu p ij :=
      (s.mu_sum_common_support hM p).symm
    _ ≤ ∑ ij ∈ (s.valuationSupport p).product (s.valuationSupport p),
      (p:ℝ)^(-(((ij.1:ℤ)-(ij.2:ℤ)).natAbs:ℝ)/q)*(s.alpha p ij.1*s.beta p ij.2)^(3/4:ℝ) :=
      Finset.sum_le_sum (fun ij _ => s.stable_layer_concentration hstable hM p hp ij.1 ij.2)
    _ = _ := by rw [Finset.product_eq_sprod,Finset.sum_product]; rfl

/-- The actual-distribution connection; hkernel is an explicit UNPROVED analytic
input until the continuous bound and its step-function bridge are formalized. -/
theorem actual_center_of_refined_bound (s : TaggedState Label n)
    (hstable : ∀ t, Step s t → t.quality ≤ s.quality) (hM : 0 < s.edgeMass)
    (p : ℕ) (hp : Nat.Prime p) (C d : ℝ) (hC : C ≤ 1) (hd : 0 < d)
    (hkernel : s.valuationKernel p ≤ C+d*(∑ i ∈ s.valuationSupport p,
      (s.alpha p i*s.beta p i)^(3/4:ℝ))) :
    ∃ k ∈ s.valuationSupport p, ((1-C)/d)^2 ≤ (s.alpha p k+s.beta p k)/2 := by
  apply LargePrime.center_of_diagonal_lower_bound (s.valuationSupport p) (s.alpha p) (s.beta p)
    (fun i _ => s.alpha_nonneg p i) (fun j _ => s.beta_nonneg p j)
    (s.alpha_sum_common_support p) (s.beta_sum_common_support p) ((1-C)/d)
    (div_nonneg (sub_nonneg.mpr hC) hd.le)
  apply (div_le_iff₀ hd).2
  have hk := s.valuationKernel_ge_one hstable hM p hp
  nlinarith only [hk,hkernel]

end LonelyRunnerNew.TaggedState
