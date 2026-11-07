import LonelyRunnerNew.WeightedDistribution

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew.WeightedState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

theorem layer_lambda (s : WeightedState Label n) (p i j : ℕ) (hp : Nat.Prime p) :
    (p:ℝ)^(-(((i:ℤ)-(j:ℤ)).natAbs:ℝ)/q) =
      ((p:ℝ)^(-1/q))^((i:ℤ)-(j:ℤ)).natAbs := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by exact_mod_cast hp.pos.le : (0:ℝ)≤p)]
  congr 1
  ring



theorem iteration_of_L04_L05 (s : WeightedState Label n) (hM : 0 < s.edgeMass)
    (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (hk : k ∈ s.valuationSupport p)
    (hz1 : 1-(s.alpha p k+s.beta p k)/2 ≤ 1/2)
    (hL04 : ∀ A B : Finset ℕ, (∑ ij ∈ A.product B,s.mu p ij) ≤
      ((∑ i ∈ A,s.alpha p i)*(∑ j ∈ B,s.beta p j))^(3/4:ℝ))
    (hL05 : ∀ i j : ℕ, s.mu p (i,j) ≤ (p:ℝ)^(-(((i:ℤ)-(j:ℤ)).natAbs:ℝ)/q)*
      (s.alpha p i*s.beta p j)^(3/4:ℝ)) :
    BootstrapInterval.iterationInequality ((p:ℝ)^(-1/q))
      (1-(s.alpha p k+s.beta p k)/2) := by
  let F := s.valuationSupport p
  let G := F.erase k
  let a := s.alpha p k
  let b := s.beta p k
  let z := 1-(a+b)/2
  let lam := (p:ℝ)^(-1/q)
  let C := (2/(1-lam^4))^(1/4:ℝ)*lam
  have ha : 0 ≤ a := s.alpha_nonneg p k
  have hb : 0 ≤ b := s.beta_nonneg p k
  have hasa := s.alpha_sum_common_support p
  have hasb := s.beta_sum_common_support p
  have ha1 : a ≤ 1 := by
    calc
      a ≤ ∑ i ∈ F, s.alpha p i := Finset.single_le_sum (fun i _ => s.alpha_nonneg p i) hk
      _ = 1 := hasa
  have hb1 : b ≤ 1 := by
    calc
      b ≤ ∑ i ∈ F, s.beta p i := Finset.single_le_sum (fun i _ => s.beta_nonneg p i) hk
      _ = 1 := hasb
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hsumA : (∑ i ∈ G, s.alpha p i) = 1-a := by
    have h := Finset.sum_erase_add F (s.alpha p) hk
    rw [hasa] at h
    linarith
  have hsumB : (∑ j ∈ G, s.beta p j) = 1-b := by
    have h := Finset.sum_erase_add F (s.beta p) hk
    rw [hasb] at h
    linarith
  have hl0 : 0 ≤ lam := Real.rpow_nonneg (by exact_mod_cast hp.pos.le) _
  have hl1 : lam < 1 := Real.rpow_lt_one_of_one_lt_of_neg
    (by exact_mod_cast hp.one_lt) (by norm_num [q])
  have hl4 : lam^4 < 1 := by simpa using pow_lt_pow_left₀ hl1 hl0 (by decide : (4:ℕ)≠0)
  have hden : 0 < 1-lam^4 := by linarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hlayer (i j : ℕ) : s.mu p (i,j) ≤ lam^((i:ℤ)-(j:ℤ)).natAbs*(s.alpha p i*s.beta p j)^(3/4:ℝ) := by
    simpa only [layer_lambda s p i j hp] using hL05 i j
  have hcenter : s.mu p (k,k) ≤ (1-z)^(3/2:ℝ) := by
    have h := hlayer k k
    simp only [sub_self, Int.natAbs_zero, pow_zero, one_mul] at h
    exact h.trans (by simpa [z] using LargePrime.product_rpow_le_mean ha hb)
  have hout : (∑ i ∈ G, ∑ j ∈ G, s.mu p (i,j)) ≤ z^(3/2:ℝ) := by
    have h := hL04 G G
    rw [Finset.product_eq_sprod, Finset.sum_product, hsumA, hsumB] at h
    exact h.trans (by
      have hmean := LargePrime.product_rpow_le_mean (sub_nonneg.mpr ha1) (sub_nonneg.mpr hb1)
      simpa only [show ((1-a)+(1-b))/2=z by dsimp [z]; ring] using hmean)
  have hrow : (∑ j ∈ G, s.mu p (k,j)) ≤ C*(a*(1-b))^(3/4:ℝ) := by
    calc
      _ ≤ ∑ j ∈ G, lam^((k:ℤ)-(j:ℤ)).natAbs*(a*s.beta p j)^(3/4:ℝ) := Finset.sum_le_sum (fun j _ => hlayer k j)
      _ ≤ _ := by
        have hh := BootstrapGeometry.weighted_row F k (s.beta p) (fun j _ => s.beta_nonneg p j) ha hl0 hl1
        change (∑ j ∈ G, lam^((k:ℤ)-(j:ℤ)).natAbs*(a*s.beta p j)^(3/4:ℝ)) ≤ C*(a*(∑ j ∈ G,s.beta p j))^(3/4:ℝ) at hh
        simpa only [hsumB] using hh
  have hcol : (∑ i ∈ G, s.mu p (i,k)) ≤ C*(b*(1-a))^(3/4:ℝ) := by
    calc
      _ ≤ ∑ i ∈ G, lam^((k:ℤ)-(i:ℤ)).natAbs*(b*s.alpha p i)^(3/4:ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        have hd : ((i:ℤ)-(k:ℤ)).natAbs=((k:ℤ)-(i:ℤ)).natAbs := by
          calc
            _ = (-((i:ℤ)-(k:ℤ))).natAbs := (Int.natAbs_neg _).symm
            _ = _ := by rw [neg_sub]
        simpa only [b,hd,mul_comm] using hlayer i k
      _ ≤ _ := by
        have hh := BootstrapGeometry.weighted_row F k (s.alpha p) (fun i _ => s.alpha_nonneg p i) hb hl0 hl1
        change (∑ i ∈ G, lam^((k:ℤ)-(i:ℤ)).natAbs*(b*s.alpha p i)^(3/4:ℝ)) ≤ C*(b*(∑ i ∈ G,s.alpha p i))^(3/4:ℝ) at hh
        simpa only [hsumA] using hh
  have hmix := BootstrapGeometry.mixed_scalar_bound ha ha1 hb hb1 hz hz1
    (show a+b=2*(1-z) by dsimp [z]; ring)
  have htotal : 1 = s.mu p (k,k)+(∑ j ∈ G, s.mu p (k,j))+
      (∑ i ∈ G, s.mu p (i,k))+(∑ i ∈ G,∑ j ∈ G,s.mu p (i,j)) := by
    have h := s.mu_sum_common_support hM p
    rw [Finset.product_eq_sprod, Finset.sum_product, BootstrapGeometry.split_center F k hk] at h
    exact h.symm
  unfold BootstrapInterval.iterationInequality
  change 1 ≤ (1-z)^(3/2:ℝ)+z^(3/2:ℝ)+C*(2*z)^(3/4:ℝ)*(1+(1-2*z)^3)^(1/4:ℝ)
  have hh := mul_le_mul_of_nonneg_left hmix hC
  nlinarith only [htotal,hcenter,hout,hrow,hcol,hh]

def fixedKernel (s : WeightedState Label n) (p : ℕ) : ℝ :=
  ∑ i ∈ s.valuationSupport p,∑ j ∈ s.valuationSupport p,
    FixedScale.lambda0^((i:ℤ)-(j:ℤ)).natAbs*(s.alpha p i*s.beta p j)^(3/4:ℝ)

theorem actual_fixed_enhanced (s : WeightedState Label n) (p : ℕ) :
    s.fixedKernel p ≤ FixedScale.C0+FixedScale.d0*
      (∑ i ∈ s.valuationSupport p,(s.alpha p i*s.beta p i)^(3/4:ℝ)) := by
  exact s.toTaggedState.actual_fixed_enhanced p

theorem fixed_lower_of_L05 (s : WeightedState Label n) (hM : 0<s.edgeMass)
    (p : ℕ) (hp : Nat.Prime p) (hp142 : 142<p)
    (hL05 : ∀ i j,s.mu p (i,j) ≤ (p:ℝ)^(-(((i:ℤ)-(j:ℤ)).natAbs:ℝ)/q)*
      (s.alpha p i*s.beta p j)^(3/4:ℝ)) : 1≤s.fixedKernel p := by
  have hl := FixedScale.prime_lambda_le hp hp142
  calc
    1 = ∑ ij ∈ (s.valuationSupport p).product (s.valuationSupport p),s.mu p ij :=
      (s.mu_sum_common_support hM p).symm
    _ ≤ ∑ ij ∈ (s.valuationSupport p).product (s.valuationSupport p),
        FixedScale.lambda0^((ij.1:ℤ)-(ij.2:ℤ)).natAbs*(s.alpha p ij.1*s.beta p ij.2)^(3/4:ℝ) := by
      apply Finset.sum_le_sum
      intro ij hij
      have hh := hL05 ij.1 ij.2
      rw [layer_lambda s p ij.1 ij.2 hp] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Real.rpow_nonneg (by exact_mod_cast hp.pos.le) _) hl _)
        (Real.rpow_nonneg (mul_nonneg (s.alpha_nonneg p _) (s.beta_nonneg p _)) _))
    _ = _ := by rw [Finset.product_eq_sprod,Finset.sum_product]; rfl

theorem initial_center_of_fixed_lower (s : WeightedState Label n) (p : ℕ) (hl : 1≤s.fixedKernel p) :
    ∃ k ∈ s.valuationSupport p,1-(s.alpha p k+s.beta p k)/2≤(89199/250000:ℝ) := by
  have hD := FixedScale.diagonal_lower (hl.trans (s.actual_fixed_enhanced p))
  obtain ⟨k,hk,hm⟩ := LargePrime.center_of_diagonal_lower_bound (s.valuationSupport p) (s.alpha p) (s.beta p)
    (fun i _ => s.alpha_nonneg p i) (fun j _ => s.beta_nonneg p j)
    (s.alpha_sum_common_support p) (s.beta_sum_common_support p) (401/500:ℝ) (by norm_num) hD
  refine ⟨k,hk,?_⟩
  nlinarith




theorem prime_center (s : WeightedState Label n) (hM : 0<s.edgeMass)
    (h04 : s.RectangleConcentration) (h05 : s.LayerConcentration)
    (p : ℕ) (hp : Nat.Prime p) (hp142 : 142<p) :
    ∃ k∈s.valuationSupport p,1-(s.alpha p k+s.beta p k)/2≤(121/1000:ℝ) := by
  obtain ⟨k,hk,hinit⟩ := s.initial_center_of_fixed_lower p (s.fixed_lower_of_L05 hM p hp hp142 (h05 p hp))
  have ha1 : s.alpha p k≤1 := by
    calc
      _ ≤ ∑ i ∈ s.valuationSupport p,s.alpha p i :=
        Finset.single_le_sum (fun i _ => s.alpha_nonneg p i) hk
      _ = 1 := s.alpha_sum_common_support p
  have hb1 : s.beta p k≤1 := by
    calc
      _ ≤ ∑ i ∈ s.valuationSupport p,s.beta p i :=
        Finset.single_le_sum (fun i _ => s.beta_nonneg p i) hk
      _ = 1 := s.beta_sum_common_support p
  refine ⟨k,hk,?_⟩
  exact BootstrapInterval.six_steps (Real.rpow_nonneg (by exact_mod_cast hp.pos.le) _)
    (BootstrapEndpoint.actual_lambda_upper hp hp142) (by linarith) (by linarith)
    (s.iteration_of_L04_L05 hM p hp k hk (by linarith)
      (s.valuation_rectangle_concentration h04 p) (h05 p hp))

end LonelyRunnerNew.WeightedState
