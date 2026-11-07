import LonelyRunnerNew.BootstrapChain
import LonelyRunnerNew.BootstrapGeometry
import LonelyRunnerNew.UniversalDescent

noncomputable section
open scoped BigOperators
namespace LonelyRunnerNew.BootstrapGeometry

theorem three_quarters_conjugate (x : ℝ) (hx : 0 ≤ x) :
    (x^(3/4:ℝ))^(4/3:ℝ)=x := by
  rw [← Real.rpow_mul hx]
  norm_num

theorem mixed_scalar_bound {a b z : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hb : 0 ≤ b) (hb1 : b ≤ 1) (hz : 0 ≤ z) (hz1 : z ≤ 1/2)
    (hmean : a+b=2*(1-z)) :
    (a*(1-b))^(3/4:ℝ)+(b*(1-a))^(3/4:ℝ) ≤
      (2*z)^(3/4:ℝ)*(1+(1-2*z)^3)^(1/4:ℝ) := by
  have hau : 0 ≤ 1-a := by linarith
  have hbv : 0 ≤ 1-b := by linarith
  have hpq : Real.HolderConjugate 4 (4/3) := by rw [Real.holderConjugate_iff]; norm_num
  have hh := Real.inner_le_Lp_mul_Lq_of_nonneg (s := ({0,1}:Finset ℕ))
    (f := fun i => if i=0 then a^(3/4:ℝ) else b^(3/4:ℝ))
    (g := fun i => if i=0 then (1-b)^(3/4:ℝ) else (1-a)^(3/4:ℝ)) hpq
    (by intro i hi; split_ifs <;> positivity)
    (by intro i hi; split_ifs <;> positivity)
  norm_num only [Finset.sum_insert, Finset.mem_singleton, zero_ne_one,
    not_false_eq_true, Finset.sum_singleton, ite_true, ite_false, ne_eq, one_ne_zero,
    Real.rpow_ofNat] at hh
  rw [BootstrapInterval.three_quarters_fourth _ ha, BootstrapInterval.three_quarters_fourth _ hb,
    three_quarters_conjugate _ hbv, three_quarters_conjugate _ hau] at hh
  norm_num only [one_div_div, div_one] at hh
  have hcube : a^3+b^3 ≤ 1+(1-2*z)^3 := by
    have hpos : 0 ≤ 3*(a+b)*(1-a)*(1-b) := by positivity
    have he : 1+(a+b-1)^3-(a^3+b^3)=3*(a+b)*(1-a)*(1-b) := by ring
    rw [hmean] at he hpos
    nlinarith only [he,hpos]
  rw [Real.mul_rpow ha hbv, Real.mul_rpow hb hau]
  calc
    _ ≤ (a^3+b^3)^(1/4:ℝ)*((1-b)+(1-a))^(3/4:ℝ) := hh
    _ ≤ (1+(1-2*z)^3)^(1/4:ℝ)*((1-b)+(1-a))^(3/4:ℝ) :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by positivity) hcube (by norm_num)) (by positivity)
    _ = _ := by rw [show (1-b)+(1-a)=2*z by linarith]; ring

theorem tail_constant {lam : ℝ} (hl0 : 0 ≤ lam) (hl1 : lam < 1) :
    (2*lam^4/(1-lam^4))^(1/4:ℝ) = (2/(1-lam^4))^(1/4:ℝ)*lam := by
  have hl4 : lam^4 < 1 := by simpa using pow_lt_pow_left₀ hl1 hl0 (by decide : (4:ℕ)≠0)
  have hroot : (lam^4)^(1/4:ℝ)=lam := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hl0]
    norm_num
  rw [show 2*lam^4/(1-lam^4)=(2/(1-lam^4))*lam^4 by ring,
    Real.mul_rpow (by positivity) (pow_nonneg hl0 _), hroot]

theorem weighted_row (F : Finset ℕ) (k : ℕ) (beta : ℕ → ℝ)
    (hb : ∀ j ∈ F.erase k, 0 ≤ beta j) {a lam : ℝ} (ha : 0 ≤ a)
    (hl0 : 0 ≤ lam) (hl1 : lam < 1) :
    (∑ j ∈ F.erase k, lam^((k:ℤ)-(j:ℤ)).natAbs*(a*beta j)^(3/4:ℝ)) ≤
      (2/(1-lam^4))^(1/4:ℝ)*lam*(a*(∑ j ∈ F.erase k, beta j))^(3/4:ℝ) := by
  have hh := mul_le_mul_of_nonneg_left (holder_row F k beta hb hl0 hl1) (Real.rpow_nonneg ha (3/4:ℝ))
  rw [tail_constant hl0 hl1] at hh
  have he : (∑ j ∈ F.erase k, lam^((k:ℤ)-(j:ℤ)).natAbs*(a*beta j)^(3/4:ℝ)) =
      a^(3/4:ℝ)*(∑ j ∈ F.erase k, lam^((k:ℤ)-(j:ℤ)).natAbs*(beta j)^(3/4:ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Real.mul_rpow ha (hb j hj)]
    ring
  rw [he, Real.mul_rpow ha (Finset.sum_nonneg hb)]
  convert hh using 1 <;> ring

theorem split_center (F : Finset ℕ) (k : ℕ) (hk : k ∈ F) (mu : ℕ × ℕ → ℝ) :
    (∑ i ∈ F, ∑ j ∈ F, mu (i,j)) = mu (k,k)+
      (∑ j ∈ F.erase k, mu (k,j))+(∑ i ∈ F.erase k, mu (i,k))+
      (∑ i ∈ F.erase k, ∑ j ∈ F.erase k, mu (i,j)) := by
  have hi := Finset.sum_erase_add F (fun i => ∑ j ∈ F, mu (i,j)) hk
  have hj (i : ℕ) := Finset.sum_erase_add F (fun j => mu (i,j)) hk
  have he (i : ℕ) : (∑ j ∈ F, mu (i,j)) = (∑ j ∈ F.erase k, mu (i,j))+mu (i,k) := (hj i).symm
  simp_rw [he] at hi
  rw [Finset.sum_add_distrib] at hi
  simp_rw [he]
  linarith

end LonelyRunnerNew.BootstrapGeometry

namespace LonelyRunnerNew.TaggedState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

theorem layer_lambda (s : TaggedState Label n) (p i j : ℕ) (hp : Nat.Prime p) :
    (p:ℝ)^(-(((i:ℤ)-(j:ℤ)).natAbs:ℝ)/q) =
      ((p:ℝ)^(-1/q))^((i:ℤ)-(j:ℤ)).natAbs := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by exact_mod_cast hp.pos.le : (0:ℝ)≤p)]
  congr 1
  ring

/-- The actual labelled-state L04/L05 implication, shared by the two scores.
The concrete wrappers below prove both concentration premises from stability. -/
theorem iteration_of_L04_L05 (s : TaggedState Label n) (hM : 0 < s.edgeMass)
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

theorem actual_iteration_inequality (s : TaggedState Label n)
    (hstable : ∀ t, Step s t → t.quality ≤ s.quality) (hM : 0 < s.edgeMass)
    (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (hk : k ∈ s.valuationSupport p)
    (hz1 : 1-(s.alpha p k+s.beta p k)/2 ≤ 1/2) :
    BootstrapInterval.iterationInequality ((p:ℝ)^(-1/q))
      (1-(s.alpha p k+s.beta p k)/2) :=
  s.iteration_of_L04_L05 hM p hp k hk hz1
    (s.valuation_rectangle_concentration hstable hM p)
    (s.stable_layer_concentration hstable hM p hp)

theorem actual_universal_iteration_inequality (s : TaggedState Label n)
    (hstable : ∀ t, Step s t → t.universalQuality ≤ s.universalQuality) (hM : 0 < s.edgeMass)
    (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (hk : k ∈ s.valuationSupport p)
    (hz1 : 1-(s.alpha p k+s.beta p k)/2 ≤ 1/2) :
    BootstrapInterval.iterationInequality ((p:ℝ)^(-1/q))
      (1-(s.alpha p k+s.beta p k)/2) :=
  s.iteration_of_L04_L05 hM p hp k hk hz1
    (s.universal_valuation_rectangle_concentration hstable hM p)
    (s.universal_layer_target_kernel hstable hM p hp)

theorem actual_six_steps (s : TaggedState Label n)
    (hstable : ∀ t, Step s t → t.quality ≤ s.quality) (hM : 0 < s.edgeMass)
    (p : ℕ) (hp : Nat.Prime p) (hp142 : 142 < p)
    (k : ℕ) (hk : k ∈ s.valuationSupport p)
    (hinit : 1-(s.alpha p k+s.beta p k)/2 ≤ (357/1000:ℝ)) :
    1-(s.alpha p k+s.beta p k)/2 ≤ (121/1000:ℝ) := by
  have ha1 : s.alpha p k ≤ 1 := by
    calc
      _ ≤ ∑ i ∈ s.valuationSupport p, s.alpha p i := Finset.single_le_sum (fun i _ => s.alpha_nonneg p i) hk
      _ = 1 := s.alpha_sum_common_support p
  have hb1 : s.beta p k ≤ 1 := by
    calc
      _ ≤ ∑ i ∈ s.valuationSupport p, s.beta p i := Finset.single_le_sum (fun i _ => s.beta_nonneg p i) hk
      _ = 1 := s.beta_sum_common_support p
  exact BootstrapInterval.six_steps (Real.rpow_nonneg (by exact_mod_cast hp.pos.le) _)
    (BootstrapEndpoint.actual_lambda_upper hp hp142) (by linarith) hinit
    (s.actual_iteration_inequality hstable hM p hp k hk (by linarith))

theorem actual_universal_six_steps (s : TaggedState Label n)
    (hstable : ∀ t, Step s t → t.universalQuality ≤ s.universalQuality) (hM : 0 < s.edgeMass)
    (p : ℕ) (hp : Nat.Prime p) (hp142 : 142 < p)
    (k : ℕ) (hk : k ∈ s.valuationSupport p)
    (hinit : 1-(s.alpha p k+s.beta p k)/2 ≤ (357/1000:ℝ)) :
    1-(s.alpha p k+s.beta p k)/2 ≤ (121/1000:ℝ) := by
  have ha1 : s.alpha p k ≤ 1 := by
    calc
      _ ≤ ∑ i ∈ s.valuationSupport p, s.alpha p i := Finset.single_le_sum (fun i _ => s.alpha_nonneg p i) hk
      _ = 1 := s.alpha_sum_common_support p
  have hb1 : s.beta p k ≤ 1 := by
    calc
      _ ≤ ∑ i ∈ s.valuationSupport p, s.beta p i := Finset.single_le_sum (fun i _ => s.beta_nonneg p i) hk
      _ = 1 := s.beta_sum_common_support p
  exact BootstrapInterval.six_steps (Real.rpow_nonneg (by exact_mod_cast hp.pos.le) _)
    (BootstrapEndpoint.actual_lambda_upper hp hp142) (by linarith) hinit
    (s.actual_universal_iteration_inequality hstable hM p hp k hk (by linarith))

end LonelyRunnerNew.TaggedState
