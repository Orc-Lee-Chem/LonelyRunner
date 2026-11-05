import LonelyRunnerNew.WeightedPrimeSupport

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew.WeightedState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

def lowerLayers (s : WeightedState Label n) (p k : ℕ) : Finset ℕ :=
  (s.valuationSupport p).filter (· < k)

def upperLayers (s : WeightedState Label n) (p k : ℕ) : Finset ℕ :=
  (s.valuationSupport p).filter (k < ·)

def zMinus (s : WeightedState Label n) (p k : ℕ) : ℝ :=
  ((∑ i ∈ s.lowerLayers p k,s.alpha p i)+(∑ i ∈ s.lowerLayers p k,s.beta p i))/2

def zPlus (s : WeightedState Label n) (p k : ℕ) : ℝ :=
  ((∑ i ∈ s.upperLayers p k,s.alpha p i)+(∑ i ∈ s.upperLayers p k,s.beta p i))/2

theorem zMinus_nonneg (s : WeightedState Label n) (p k : ℕ) : 0 ≤ s.zMinus p k := by
  unfold zMinus
  exact div_nonneg (add_nonneg (Finset.sum_nonneg (fun i _ => s.alpha_nonneg p i))
    (Finset.sum_nonneg (fun i _ => s.beta_nonneg p i))) (by norm_num)

theorem zPlus_nonneg (s : WeightedState Label n) (p k : ℕ) : 0 ≤ s.zPlus p k := by
  unfold zPlus
  exact div_nonneg (add_nonneg (Finset.sum_nonneg (fun i _ => s.alpha_nonneg p i))
    (Finset.sum_nonneg (fun i _ => s.beta_nonneg p i))) (by norm_num)

theorem sum_split_directions (F : Finset ℕ) (k : ℕ) (hk : k ∈ F) (w : ℕ → ℝ) :
    (∑ i ∈ F,w i) =
      (∑ i ∈ F.filter (· < k),w i)+w k+(∑ i ∈ F.filter (k < ·),w i) := by
  have he : (∑ i ∈ F.erase k,w i) =
      (∑ i ∈ F.filter (· < k),w i)+(∑ i ∈ F.filter (k < ·),w i) := by
    have hL : F.filter (· < k) = (F.erase k).filter (· < k) := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_erase]
      exact ⟨fun h => ⟨⟨ne_of_lt h.2,h.1⟩,h.2⟩,fun h => ⟨h.1.2,h.2⟩⟩
    have hR : F.filter (k < ·) = (F.erase k).filter (k < ·) := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_erase]
      exact ⟨fun h => ⟨⟨ne_of_gt h.2,h.1⟩,h.2⟩,fun h => ⟨h.1.2,h.2⟩⟩
    rw [hL,hR]
    simp only [Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hne := (Finset.mem_erase.mp hi).1
    by_cases h : i < k
    · have hh : ¬ k < i := by omega
      simp [h,hh]
    · have hh : k < i := by omega
      simp [h,hh]
  have h := Finset.sum_erase_add F w hk
  rw [he] at h
  linarith

theorem zMinus_add_zPlus (s : WeightedState Label n) (p k : ℕ) (hk : k ∈ s.valuationSupport p) :
    s.zMinus p k+s.zPlus p k = 1-(s.alpha p k+s.beta p k)/2 := by
  have ha := sum_split_directions (s.valuationSupport p) k hk (s.alpha p)
  have hb := sum_split_directions (s.valuationSupport p) k hk (s.beta p)
  rw [s.alpha_sum_common_support p] at ha
  rw [s.beta_sum_common_support p] at hb
  unfold zMinus zPlus lowerLayers upperLayers
  linarith

theorem primeException_eq_common_support (s : WeightedState Label n) (p k : ℕ) :
    s.primeException p k = LargePrime.exceptionMass
      ((s.valuationSupport p).product (s.valuationSupport p)) (s.mu p) k := by
  classical
  unfold primeException LargePrime.exceptionMass
  simp_rw [mu_eq_fiber_sum]
  rw [Finset.sum_fiberwise_eq_sum_filter]
  congr 1
  apply Finset.filter_congr
  intro e he
  have hm := Finset.mem_product.mp (s.edges_subset he)
  have hL : (s.valuationPair p e).1 ∈ s.valuationSupport p :=
    Finset.mem_union_left _ (Finset.mem_image_of_mem _ hm.1)
  have hR : (s.valuationPair p e).2 ∈ s.valuationSupport p :=
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ hm.2)
  simp only [Finset.mem_filter,Finset.product_eq_sprod,Finset.mem_product,hL,hR,
    true_and,centerBrackets]

theorem same_direction_of_L04 (s : WeightedState Label n) (p k : ℕ)
    (hL04 : ∀ A B : Finset ℕ,(∑ ij ∈ A.product B,s.mu p ij) ≤
      ((∑ i ∈ A,s.alpha p i)*(∑ j ∈ B,s.beta p j))^(3/4:ℝ)) :
    s.primeException p k ≤ (s.zMinus p k)^(3/2:ℝ)+(s.zPlus p k)^(3/2:ℝ) := by
  rw [primeException_eq_common_support]
  apply LargePrime.exceptionMass_le_tail_means (s.valuationSupport p) (s.valuationSupport p)
    _ (fun _ h => h) _ _ _ (fun i _ => s.alpha_nonneg p i) (fun j _ => s.beta_nonneg p j)
  intro A hA B hB
  unfold LargePrime.rectangleMass
  have he : ((s.valuationSupport p).product (s.valuationSupport p)).filter
      (fun ij => ij.1 ∈ A ∧ ij.2 ∈ B) = A.product B := by
    ext ij
    simp only [Finset.mem_filter,Finset.product_eq_sprod,Finset.mem_product]
    exact ⟨fun h => h.2,fun h => ⟨⟨hA h.1,hB h.2⟩,h⟩⟩
  rw [he]
  exact hL04 A B

def oppositeMass (s : WeightedState Label n) (p k : ℕ) : ℝ :=
  (∑ i ∈ s.lowerLayers p k,∑ j ∈ s.upperLayers p k,s.mu p (i,j))+
    (∑ i ∈ s.upperLayers p k,∑ j ∈ s.lowerLayers p k,s.mu p (i,j))

theorem opposite_of_L05 (s : WeightedState Label n) (p k : ℕ) {lam : ℝ}
    (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (hL05 : ∀ i j,s.mu p (i,j) ≤ lam^((i:ℤ)-(j:ℤ)).natAbs*
      (s.alpha p i*s.beta p j)^(3/4:ℝ)) :
    s.oppositeMass p k ≤ 4^(3/4:ℝ)*((1/(1-lam^4))^(1/4:ℝ))^2*lam^2*
      (s.zMinus p k*s.zPlus p k)^(3/4:ℝ) := by
  let L := s.lowerLayers p k
  let R := s.upperLayers p k
  let C := (1/(1-lam^4))^(1/4:ℝ)*lam
  have hL : ∀ i ∈ L,i < k := fun _ hi => (Finset.mem_filter.mp hi).2
  have hR : ∀ i ∈ R,k < i := fun _ hi => (Finset.mem_filter.mp hi).2
  have h1 := LCDirection.opposite_rectangle L R k (s.alpha p) (s.beta p) (s.mu p)
    (fun i _ => s.alpha_nonneg p i) (fun j _ => s.beta_nonneg p j) hl0 hl1 hL hR
    (fun i _ j _ => hL05 i j)
  have h2 := LCDirection.opposite_rectangle L R k (s.beta p) (s.alpha p)
    (fun ij => s.mu p (ij.2,ij.1))
    (fun i _ => s.beta_nonneg p i) (fun j _ => s.alpha_nonneg p j) hl0 hl1 hL hR (by
      intro i hi j hj
      have hh := hL05 j i
      have he : ((j:ℤ)-(i:ℤ)).natAbs = ((i:ℤ)-(j:ℤ)).natAbs := by
        rw [← Int.natAbs_neg,neg_sub]
      simpa only [he,mul_comm (s.alpha p j)] using hh)
  rw [Finset.sum_comm] at h2
  have hc := LCDirection.cross_two
    (Finset.sum_nonneg (fun i (_ : i ∈ L) => s.alpha_nonneg p i))
    (Finset.sum_nonneg (fun i (_ : i ∈ L) => s.beta_nonneg p i))
    (Finset.sum_nonneg (fun i (_ : i ∈ R) => s.alpha_nonneg p i))
    (Finset.sum_nonneg (fun i (_ : i ∈ R) => s.beta_nonneg p i))
  have hmean : ((∑ i ∈ L,s.alpha p i)+(∑ i ∈ L,s.beta p i))*
      ((∑ i ∈ R,s.alpha p i)+(∑ i ∈ R,s.beta p i)) =
      4*(s.zMinus p k*s.zPlus p k) := by dsimp [zMinus,zPlus,L,R]; ring
  calc
    s.oppositeMass p k ≤ C^2*((∑ i ∈ L,s.alpha p i)*(∑ i ∈ R,s.beta p i))^(3/4:ℝ)+
        C^2*((∑ i ∈ L,s.beta p i)*(∑ i ∈ R,s.alpha p i))^(3/4:ℝ) := add_le_add h1 h2
    _ ≤ C^2*(((∑ i ∈ L,s.alpha p i)+(∑ i ∈ L,s.beta p i))*
        ((∑ i ∈ R,s.alpha p i)+(∑ i ∈ R,s.beta p i)))^(3/4:ℝ) := by
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left hc (sq_nonneg C)
    _ = _ := by
      rw [hmean,Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4)
        (mul_nonneg (s.zMinus_nonneg p k) (s.zPlus_nonneg p k))]
      dsimp [C]
      ring

def mixedHalfMass (s : WeightedState Label n) (p k : ℕ) (A : Finset ℕ) : ℝ :=
  (∑ j ∈ A,s.mu p (k,j))+(∑ i ∈ A,s.mu p (i,k))

def mixedMass (s : WeightedState Label n) (p k : ℕ) : ℝ :=
  s.mixedHalfMass p k (s.lowerLayers p k)+s.mixedHalfMass p k (s.upperLayers p k)

theorem mixed_half_of_L05 (s : WeightedState Label n) (p k : ℕ)
    (hk : k ∈ s.valuationSupport p) (A : Finset ℕ)
    (hside : (∀ i ∈ A,i < k) ∨ (∀ i ∈ A,k < i)) {lam : ℝ}
    (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (hL05 : ∀ i j,s.mu p (i,j) ≤ lam^((i:ℤ)-(j:ℤ)).natAbs*
      (s.alpha p i*s.beta p j)^(3/4:ℝ)) :
    s.mixedHalfMass p k A ≤ (1/(1-lam^4))^(1/4:ℝ)*lam*
      ((∑ i ∈ A,s.alpha p i)+(∑ i ∈ A,s.beta p i))^(3/4:ℝ)*
      (1+(1-2*(1-(s.alpha p k+s.beta p k)/2))^3)^(1/4:ℝ) := by
  let C := (1/(1-lam^4))^(1/4:ℝ)*lam
  have hl4 : lam^4 < 1 := by
    simpa using pow_lt_pow_left₀ hl1 hl0 (by decide : (4:ℕ) ≠ 0)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have ha1 : s.alpha p k ≤ 1 := by
    calc
      _ ≤ ∑ i ∈ s.valuationSupport p,s.alpha p i :=
        Finset.single_le_sum (fun i _ => s.alpha_nonneg p i) hk
      _ = 1 := s.alpha_sum_common_support p
  have hb1 : s.beta p k ≤ 1 := by
    calc
      _ ≤ ∑ i ∈ s.valuationSupport p,s.beta p i :=
        Finset.single_le_sum (fun i _ => s.beta_nonneg p i) hk
      _ = 1 := s.beta_sum_common_support p
  have hrow : (∑ j ∈ A,s.mu p (k,j)) ≤ C*
      (s.alpha p k*(∑ j ∈ A,s.beta p j))^(3/4:ℝ) :=
    (Finset.sum_le_sum (fun j _ => hL05 k j)).trans
      (LCDirection.weighted_half A k (s.beta p) (fun j _ => s.beta_nonneg p j)
        (s.alpha_nonneg p k) hl0 hl1 hside)
  have hcol : (∑ i ∈ A,s.mu p (i,k)) ≤ C*
      (s.beta p k*(∑ i ∈ A,s.alpha p i))^(3/4:ℝ) := by
    have hsum : (∑ i ∈ A,s.mu p (i,k)) ≤
        ∑ i ∈ A,lam^((k:ℤ)-(i:ℤ)).natAbs*(s.beta p k*s.alpha p i)^(3/4:ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      have hh := hL05 i k
      have he : ((i:ℤ)-(k:ℤ)).natAbs = ((k:ℤ)-(i:ℤ)).natAbs := by
        rw [← Int.natAbs_neg,neg_sub]
      simpa only [he,mul_comm (s.alpha p i)] using hh
    exact hsum.trans (LCDirection.weighted_half A k (s.alpha p)
      (fun i _ => s.alpha_nonneg p i) (s.beta_nonneg p k) hl0 hl1 hside)
  have ht := LCDirection.mixed_two (s.alpha_nonneg p k) ha1 (s.beta_nonneg p k) hb1
    (Finset.sum_nonneg (fun i (_ : i ∈ A) => s.alpha_nonneg p i))
    (Finset.sum_nonneg (fun i (_ : i ∈ A) => s.beta_nonneg p i))
    (z := 1-(s.alpha p k+s.beta p k)/2) (by ring)
  calc
    _ ≤ C*(s.alpha p k*(∑ j ∈ A,s.beta p j))^(3/4:ℝ)+
        C*(s.beta p k*(∑ i ∈ A,s.alpha p i))^(3/4:ℝ) := add_le_add hrow hcol
    _ = C*((s.alpha p k*(∑ j ∈ A,s.beta p j))^(3/4:ℝ)+
        (s.beta p k*(∑ i ∈ A,s.alpha p i))^(3/4:ℝ)) := by ring
    _ ≤ _ := by simpa only [C,mul_assoc] using mul_le_mul_of_nonneg_left ht hC

theorem mixed_of_L05 (s : WeightedState Label n) (p k : ℕ)
    (hk : k ∈ s.valuationSupport p) {lam : ℝ} (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (hL05 : ∀ i j,s.mu p (i,j) ≤ lam^((i:ℤ)-(j:ℤ)).natAbs*
      (s.alpha p i*s.beta p j)^(3/4:ℝ)) :
    s.mixedMass p k ≤ 2^(3/4:ℝ)*(1/(1-lam^4))^(1/4:ℝ)*lam*
      ((s.zMinus p k)^(3/4:ℝ)+(s.zPlus p k)^(3/4:ℝ))*
      (1+(1-2*(1-(s.alpha p k+s.beta p k)/2))^3)^(1/4:ℝ) := by
  have hm := s.mixed_half_of_L05 p k hk (s.lowerLayers p k)
    (Or.inl (fun _ hi => (Finset.mem_filter.mp hi).2)) hl0 hl1 hL05
  have hp := s.mixed_half_of_L05 p k hk (s.upperLayers p k)
    (Or.inr (fun _ hi => (Finset.mem_filter.mp hi).2)) hl0 hl1 hL05
  have heL : (∑ i ∈ s.lowerLayers p k,s.alpha p i)+(∑ i ∈ s.lowerLayers p k,s.beta p i) =
      2*s.zMinus p k := by unfold zMinus; ring
  have heR : (∑ i ∈ s.upperLayers p k,s.alpha p i)+(∑ i ∈ s.upperLayers p k,s.beta p i) =
      2*s.zPlus p k := by unfold zPlus; ring
  rw [heL,Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (s.zMinus_nonneg p k)] at hm
  rw [heR,Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (s.zPlus_nonneg p k)] at hp
  exact (add_le_add hm hp).trans_eq (by ring)

theorem primeException_eq_direction_rectangles (s : WeightedState Label n) (p k : ℕ) :
    s.primeException p k =
      (∑ i ∈ s.lowerLayers p k,∑ j ∈ s.lowerLayers p k,s.mu p (i,j))+
      (∑ i ∈ s.upperLayers p k,∑ j ∈ s.upperLayers p k,s.mu p (i,j)) := by
  classical
  rw [primeException_eq_common_support,LargePrime.exceptionMass_eq_tails]
  unfold LargePrime.lowerMass LargePrime.upperMass lowerLayers upperLayers
  simp only [Finset.sum_filter,Finset.product_eq_sprod,Finset.sum_product]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi
  all_goals
    by_cases h : i < k <;> by_cases h' : k < i <;> simp [h,h',Finset.sum_filter]



theorem directional_mass_identity (s : WeightedState Label n) (hM : 0 < s.edgeMass)
    (p k : ℕ) (hk : k ∈ s.valuationSupport p) :
    1 = s.mu p (k,k)+s.primeException p k+s.oppositeMass p k+s.mixedMass p k := by
  have hsplit (i : ℕ) := sum_split_directions (s.valuationSupport p) k hk
    (fun j => s.mu p (i,j))
  have houter := sum_split_directions (s.valuationSupport p) k hk
    (fun i => ∑ j ∈ s.valuationSupport p,s.mu p (i,j))
  have htotal := s.mu_sum_common_support hM p
  rw [Finset.product_eq_sprod,Finset.sum_product] at htotal
  rw [houter] at htotal
  simp_rw [hsplit] at htotal
  rw [primeException_eq_direction_rectangles]
  unfold oppositeMass mixedMass mixedHalfMass lowerLayers upperLayers
  simp only [Finset.sum_add_distrib] at htotal
  linarith

theorem directional_iteration_of_L04_L05 (s : WeightedState Label n) (hM : 0 < s.edgeMass)
    (p k : ℕ) (hk : k ∈ s.valuationSupport p) {lam : ℝ} (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (hL04 : ∀ A B : Finset ℕ,(∑ ij ∈ A.product B,s.mu p ij) ≤
      ((∑ i ∈ A,s.alpha p i)*(∑ j ∈ B,s.beta p j))^(3/4:ℝ))
    (hL05 : ∀ i j,s.mu p (i,j) ≤ lam^((i:ℤ)-(j:ℤ)).natAbs*
      (s.alpha p i*s.beta p j)^(3/4:ℝ)) :
    1 ≤ (1-(s.zMinus p k+s.zPlus p k))^(3/2:ℝ)+
      (s.zMinus p k)^(3/2:ℝ)+(s.zPlus p k)^(3/2:ℝ)+
      4^(3/4:ℝ)*((1/(1-lam^4))^(1/4:ℝ))^2*lam^2*
        (s.zMinus p k*s.zPlus p k)^(3/4:ℝ)+
      2^(3/4:ℝ)*(1/(1-lam^4))^(1/4:ℝ)*lam*
        ((s.zMinus p k)^(3/4:ℝ)+(s.zPlus p k)^(3/4:ℝ))*
        (1+(1-2*(s.zMinus p k+s.zPlus p k))^3)^(1/4:ℝ) := by
  have hc := hL05 k k
  simp only [sub_self,Int.natAbs_zero,pow_zero,one_mul] at hc
  have hcenter := hc.trans (LargePrime.product_rpow_le_mean (s.alpha_nonneg p k) (s.beta_nonneg p k))
  have he := s.same_direction_of_L04 p k hL04
  have ho := s.opposite_of_L05 p k hl0 hl1 hL05
  have hm := s.mixed_of_L05 p k hk hl0 hl1 hL05
  have hz := s.zMinus_add_zPlus p k hk
  rw [← hz] at hm
  have hcen : s.mu p (k,k) ≤ (1-(s.zMinus p k+s.zPlus p k))^(3/2:ℝ) := by
    rw [hz,sub_sub_cancel]
    exact hcenter
  have hid := s.directional_mass_identity hM p k hk
  linarith

theorem primeException_zero_of_zero_deficit (s : WeightedState Label n)
    (hM : 0 < s.edgeMass) (p k : ℕ) (hz : s.zMinus p k+s.zPlus p k=0)
    (hE : s.primeException p k ≤ (s.zMinus p k)^(3/2:ℝ)+(s.zPlus p k)^(3/2:ℝ)) :
    s.primeException p k=0 := by
  have hm := s.zMinus_nonneg p k
  have hp := s.zPlus_nonneg p k
  have hm0 : s.zMinus p k=0 := by linarith
  have hp0 : s.zPlus p k=0 := by linarith
  norm_num only [hm0,hp0,Real.zero_rpow (by norm_num : (3/2:ℝ)≠0),zero_add] at hE
  exact le_antisymm hE (s.primeException_nonneg hM p k)

theorem same_direction (s : WeightedState Label n) (h04 : s.RectangleConcentration) (p k : ℕ) :
    s.primeException p k≤(s.zMinus p k)^(3/2:ℝ)+(s.zPlus p k)^(3/2:ℝ) :=
  s.same_direction_of_L04 p k (s.valuation_rectangle_concentration h04 p)

theorem directional_iteration (s : WeightedState Label n) (hM : 0<s.edgeMass)
    (h04 : s.RectangleConcentration) (h05 : s.LayerConcentration)
    (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (hk : k∈s.valuationSupport p) :
    LCDirection.directionalInequality ((p:ℝ)^(-1/q)) (s.zMinus p k) (s.zPlus p k) := by
  apply s.directional_iteration_of_L04_L05 hM p k hk
    (Real.rpow_nonneg (by exact_mod_cast hp.pos.le) _)
    (Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by norm_num [q]))
    (s.valuation_rectangle_concentration h04 p)
  intro i j
  simpa only [s.layer_lambda p i j hp] using h05 p hp i j

theorem center_zero_off_primeSupport (s : WeightedState Label n) {p k : ℕ}
    (hp : Nat.Prime p) (hoff : p ∉ s.primeSupport) (hk : k ∈ s.valuationSupport p) : k = 0 := by
  rcases Finset.mem_union.mp hk with hk | hk
  · obtain ⟨x,hx,hval⟩ := Finset.mem_image.mp hk
    rw [s.left_valuation_zero_off_primeSupport hp hoff hx] at hval
    exact hval.symm
  · obtain ⟨y,hy,hval⟩ := Finset.mem_image.mp hk
    rw [s.right_valuation_zero_off_primeSupport hp hoff hy] at hval
    exact hval.symm



theorem select_large_centers (s : WeightedState Label n)
    (hc : ∀ p : ℕ,Nat.Prime p → 142 < p →
      ∃ k ∈ s.valuationSupport p,1-(s.alpha p k+s.beta p k)/2 ≤ (121/1000:ℝ)) :
    ∃ centers : ℕ → ℕ,
      (∀ p,Nat.Prime p → 142 < p → centers p ∈ s.valuationSupport p ∧
        s.zMinus p (centers p)+s.zPlus p (centers p) ≤ (121/1000:ℝ)) ∧
      (∀ p ∉ s.primeSupport,centers p = 0) := by
  classical
  let centers : ℕ → ℕ := fun p => if h : Nat.Prime p ∧ 142 < p then
    Classical.choose (hc p h.1 h.2) else 0
  have hchosen (p : ℕ) (hp : Nat.Prime p) (h142 : 142 < p) :
      centers p ∈ s.valuationSupport p ∧
        1-(s.alpha p (centers p)+s.beta p (centers p))/2 ≤ (121/1000:ℝ) := by
    simpa only [centers,dif_pos (And.intro hp h142)] using
      Classical.choose_spec (hc p hp h142)
  refine ⟨centers,?_,?_⟩
  · intro p hp h142
    have h := hchosen p hp h142
    exact ⟨h.1,(s.zMinus_add_zPlus p (centers p) h.1).trans_le h.2⟩
  · intro p hoff
    by_cases h : Nat.Prime p ∧ 142 < p
    · exact s.center_zero_off_primeSupport h.1 hoff (hchosen p h.1 h.2).1
    · simp only [centers,dif_neg h]



end LonelyRunnerNew.WeightedState
