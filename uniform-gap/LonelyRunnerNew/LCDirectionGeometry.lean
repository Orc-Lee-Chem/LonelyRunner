import LonelyRunnerNew.BootstrapDistribution

noncomputable section
open scoped BigOperators
namespace LonelyRunnerNew.LCDirection

def directionalInequality (lam zm zp : ℝ) : Prop :=
  1 ≤ (1-(zm+zp))^(3/2:ℝ)+zm^(3/2:ℝ)+zp^(3/2:ℝ)+
    4^(3/4:ℝ)*((1/(1-lam^4))^(1/4:ℝ))^2*lam^2*(zm*zp)^(3/4:ℝ)+
    2^(3/4:ℝ)*(1/(1-lam^4))^(1/4:ℝ)*lam*(zm^(3/4:ℝ)+zp^(3/4:ℝ))*
      (1+(1-2*(zm+zp))^3)^(1/4:ℝ)

theorem half_constant_eq {lam : ℝ} (hl0 : 0 ≤ lam) (hl1 : lam < 1) :
    (1/(1-lam^4))^(1/4:ℝ)=(1-lam^4)^(-1/4:ℝ) := by
  have hl4 : lam^4 < 1 := by
    simpa using pow_lt_pow_left₀ hl1 hl0 (by decide : (4:ℕ)≠0)
  have hd : 0 ≤ 1-lam^4 := by linarith
  rw [Real.div_rpow (by norm_num : (0:ℝ) ≤ 1) hd,Real.one_rpow,
    show (-1/4:ℝ)=-(1/4:ℝ) by ring,Real.rpow_neg hd]
  exact one_div _

/-- One half-axis, with no factor 2. This is the source of the extra
`lambda^2` for the two opposite rectangles. -/
theorem holder_half (F : Finset ℕ) (k : ℕ) (w : ℕ → ℝ)
    (hw : ∀ i ∈ F, 0 ≤ w i) {lam : ℝ} (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (hside : (∀ i ∈ F, i < k) ∨ (∀ i ∈ F, k < i)) :
    (∑ i ∈ F, lam^((k:ℤ)-(i:ℤ)).natAbs * (w i)^(3/4:ℝ)) ≤
      (1/(1-lam^4))^(1/4:ℝ)*lam*(∑ i ∈ F, w i)^(3/4:ℝ) := by
  have hl4 : lam^4 < 1 := by
    simpa using pow_lt_pow_left₀ hl1 hl0 (by decide : (4:ℕ) ≠ 0)
  have hpq : Real.HolderConjugate 4 (4/3) := by
    rw [Real.holderConjugate_iff]; norm_num
  have hh := Real.inner_le_Lp_mul_Lq_of_nonneg (s := F)
    (f := fun i => lam^((k:ℤ)-(i:ℤ)).natAbs)
    (g := fun i => (w i)^(3/4:ℝ)) hpq
    (fun _ _ => pow_nonneg hl0 _) (fun i hi => Real.rpow_nonneg (hw i hi) _)
  have hf : (∑ i ∈ F, (lam^((k:ℤ)-(i:ℤ)).natAbs)^(4:ℝ)) =
      ∑ i ∈ F, (lam^4)^((k:ℤ)-(i:ℤ)).natAbs := by
    apply Finset.sum_congr rfl
    intro i hi
    norm_num only [Real.rpow_ofNat]
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  have hg : (∑ i ∈ F, ((w i)^(3/4:ℝ))^(4/3:ℝ)) = ∑ i ∈ F, w i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact BootstrapGeometry.three_quarters_conjugate _ (hw i hi)
  rw [hf,hg] at hh
  norm_num only [one_div_div,div_one] at hh
  have ht : (∑ i ∈ F, (lam^4)^((k:ℤ)-(i:ℤ)).natAbs) ≤ lam^4/(1-lam^4) := by
    rcases hside with h | h
    · exact BootstrapGeometry.lower_geometric_tail F k (pow_nonneg hl0 4) hl4 h
    · exact BootstrapGeometry.upper_geometric_tail F k (pow_nonneg hl0 4) hl4 h
  have hroot : (lam^4/(1-lam^4))^(1/4:ℝ) =
      (1/(1-lam^4))^(1/4:ℝ)*lam := by
    rw [show lam^4/(1-lam^4) = (1/(1-lam^4))*lam^4 by ring,
      Real.mul_rpow (by positivity) (pow_nonneg hl0 _)]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hl0]
    norm_num
  exact hh.trans (by
    rw [← hroot]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (by positivity) ht (by norm_num))
        (Real.rpow_nonneg (Finset.sum_nonneg hw) _))

/-- Two-term Holder with exponents 4 and 4/3. -/
theorem two_term_holder {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) :
    (a*c)^(3/4:ℝ)+(b*d)^(3/4:ℝ) ≤
      (a^3+b^3)^(1/4:ℝ)*(c+d)^(3/4:ℝ) := by
  have hpq : Real.HolderConjugate 4 (4/3) := by
    rw [Real.holderConjugate_iff]; norm_num
  have hh := Real.inner_le_Lp_mul_Lq_of_nonneg (s := ({0,1}:Finset ℕ))
    (f := fun i => if i=0 then a^(3/4:ℝ) else b^(3/4:ℝ))
    (g := fun i => if i=0 then c^(3/4:ℝ) else d^(3/4:ℝ)) hpq
    (by intro i hi; split_ifs <;> positivity)
    (by intro i hi; split_ifs <;> positivity)
  norm_num only [Finset.sum_insert,Finset.mem_singleton,zero_ne_one,
    not_false_eq_true,Finset.sum_singleton,ite_true,ite_false,ne_eq,one_ne_zero,
    Real.rpow_ofNat] at hh
  rw [BootstrapInterval.three_quarters_fourth _ ha,
    BootstrapInterval.three_quarters_fourth _ hb,
    BootstrapGeometry.three_quarters_conjugate _ hc,
    BootstrapGeometry.three_quarters_conjugate _ hd] at hh
  norm_num only [one_div_div,div_one] at hh
  simpa only [Real.mul_rpow ha hc,Real.mul_rpow hb hd] using hh

theorem cross_two {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) :
    (a*d)^(3/4:ℝ)+(b*c)^(3/4:ℝ) ≤ ((a+b)*(c+d))^(3/4:ℝ) := by
  have hcube : a^3+b^3 ≤ (a+b)^3 := by
    nlinarith [mul_nonneg ha hb, mul_nonneg (mul_nonneg ha hb) (add_nonneg ha hb)]
  calc
    _ ≤ (a^3+b^3)^(1/4:ℝ)*(d+c)^(3/4:ℝ) := two_term_holder ha hb hd hc
    _ ≤ ((a+b)^3)^(1/4:ℝ)*(d+c)^(3/4:ℝ) :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by positivity) hcube (by norm_num))
        (by positivity)
    _ = _ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (add_nonneg ha hb)]
      norm_num only [Nat.cast_ofNat]
      rw [← Real.mul_rpow (add_nonneg ha hb) (add_nonneg hd hc),add_comm d c]

/-- Center cubic control, retaining the actual deficit z. -/
theorem center_cubic {a b z : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hb : 0 ≤ b) (hb1 : b ≤ 1) (hmean : a+b=2*(1-z)) :
    a^3+b^3 ≤ 1+(1-2*z)^3 := by
  have hp : 0 ≤ 3*(a+b)*(1-a)*(1-b) := by positivity
  have he : 1+(a+b-1)^3-(a^3+b^3)=3*(a+b)*(1-a)*(1-b) := by ring
  rw [hmean] at he hp
  nlinarith only [he,hp]

theorem mixed_two {a b c d z : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hb : 0 ≤ b) (hb1 : b ≤ 1) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hmean : a+b=2*(1-z)) :
    (a*d)^(3/4:ℝ)+(b*c)^(3/4:ℝ) ≤
      (c+d)^(3/4:ℝ)*(1+(1-2*z)^3)^(1/4:ℝ) := by
  exact (two_term_holder ha hb hd hc).trans (by
    rw [add_comm d c,mul_comm ((c+d)^(3/4:ℝ))]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (by positivity) (center_cubic ha ha1 hb hb1 hmean) (by norm_num))
      (by positivity))

theorem distance_across {i k j : ℕ} (hi : i ≤ k) (hj : k ≤ j) :
    ((i:ℤ)-(j:ℤ)).natAbs = ((k:ℤ)-(i:ℤ)).natAbs+((k:ℤ)-(j:ℤ)).natAbs := by
  rw [Int.natAbs_natCast_sub_natCast_of_le (hi.trans hj),
    Int.natAbs_natCast_sub_natCast_of_ge hi,Int.natAbs_natCast_sub_natCast_of_le hj]
  omega

theorem weighted_half (F : Finset ℕ) (k : ℕ) (w : ℕ → ℝ)
    (hw : ∀ i ∈ F, 0 ≤ w i) {a lam : ℝ} (ha : 0 ≤ a)
    (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (hside : (∀ i ∈ F, i < k) ∨ (∀ i ∈ F, k < i)) :
    (∑ i ∈ F, lam^((k:ℤ)-(i:ℤ)).natAbs*(a*w i)^(3/4:ℝ)) ≤
      (1/(1-lam^4))^(1/4:ℝ)*lam*(a*(∑ i ∈ F,w i))^(3/4:ℝ) := by
  have hh := mul_le_mul_of_nonneg_left (holder_half F k w hw hl0 hl1 hside)
    (Real.rpow_nonneg ha (3/4:ℝ))
  have he : (∑ i ∈ F, lam^((k:ℤ)-(i:ℤ)).natAbs*(a*w i)^(3/4:ℝ)) =
      a^(3/4:ℝ)*(∑ i ∈ F,lam^((k:ℤ)-(i:ℤ)).natAbs*(w i)^(3/4:ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Real.mul_rpow ha (hw i hi)]
    ring
  rw [he,Real.mul_rpow ha (Finset.sum_nonneg hw)]
  convert hh using 1 <;> ring

theorem opposite_rectangle (A B : Finset ℕ) (k : ℕ) (alpha beta : ℕ → ℝ)
    (mu : ℕ × ℕ → ℝ) (ha : ∀ i ∈ A,0 ≤ alpha i) (hb : ∀ j ∈ B,0 ≤ beta j)
    {lam : ℝ} (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (hA : ∀ i ∈ A,i < k) (hB : ∀ j ∈ B,k < j)
    (hpoint : ∀ i ∈ A,∀ j ∈ B,mu (i,j) ≤
      lam^((i:ℤ)-(j:ℤ)).natAbs*(alpha i*beta j)^(3/4:ℝ)) :
    (∑ i ∈ A,∑ j ∈ B,mu (i,j)) ≤
      ((1/(1-lam^4))^(1/4:ℝ)*lam)^2 *
        ((∑ i ∈ A,alpha i)*(∑ j ∈ B,beta j))^(3/4:ℝ) := by
  have hl4 : lam^4 < 1 := by
    simpa using pow_lt_pow_left₀ hl1 hl0 (by decide : (4:ℕ) ≠ 0)
  let C := (1/(1-lam^4))^(1/4:ℝ)*lam
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hleft := holder_half A k alpha ha hl0 hl1 (Or.inl hA)
  have hright := holder_half B k beta hb hl0 hl1 (Or.inr hB)
  calc
    _ ≤ ∑ i ∈ A,∑ j ∈ B,
        (lam^((k:ℤ)-(i:ℤ)).natAbs*(alpha i)^(3/4:ℝ))*
        (lam^((k:ℤ)-(j:ℤ)).natAbs*(beta j)^(3/4:ℝ)) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      have hh := hpoint i hi j hj
      rw [distance_across (hA i hi).le (hB j hj).le,pow_add,
        Real.mul_rpow (ha i hi) (hb j hj)] at hh
      convert hh using 1 <;> ring
    _ = (∑ i ∈ A,lam^((k:ℤ)-(i:ℤ)).natAbs*(alpha i)^(3/4:ℝ))*
        (∑ j ∈ B,lam^((k:ℤ)-(j:ℤ)).natAbs*(beta j)^(3/4:ℝ)) := by
      rw [Finset.sum_mul_sum]
    _ ≤ (C*(∑ i ∈ A,alpha i)^(3/4:ℝ))*(C*(∑ j ∈ B,beta j)^(3/4:ℝ)) :=
      mul_le_mul hleft hright
        (Finset.sum_nonneg (fun j hj => mul_nonneg (pow_nonneg hl0 _)
          (Real.rpow_nonneg (hb j hj) _)))
        (mul_nonneg hC (Real.rpow_nonneg (Finset.sum_nonneg ha) _))
    _ = _ := by
      rw [Real.mul_rpow (Finset.sum_nonneg ha) (Finset.sum_nonneg hb)]
      dsimp [C]
      ring

end LonelyRunnerNew.LCDirection
