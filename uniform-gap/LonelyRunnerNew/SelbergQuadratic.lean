import LonelyRunnerNew.SelbergWeights

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew.FiniteSelberg
attribute [local instance] Classical.propDecidable

def quadratic (X : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑d∈Finset.Icc 1 X,∑e∈Finset.Icc 1 X,w d*w e/(Nat.lcm d e:ℝ)

theorem inv_lcm {d e : ℕ} (hd : 0<d) (he : 0<e) :
    1/(Nat.lcm d e:ℝ)=(Nat.gcd d e:ℝ)/((d:ℝ)*(e:ℝ)) := by
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  have heR : (0:ℝ)<e := by exact_mod_cast he
  have hlR : (0:ℝ)<Nat.lcm d e := by exact_mod_cast Nat.lcm_pos hd he
  have hmul : (Nat.gcd d e:ℝ)*(Nat.lcm d e:ℝ)=(d:ℝ)*(e:ℝ) := by
    exact_mod_cast Nat.gcd_mul_lcm d e
  apply (div_eq_div_iff hlR.ne' (mul_pos hdR heR).ne').mpr
  nlinarith only [hmul]

theorem gcd_totient_sum {X d e : ℕ} (hd : d∈Finset.Icc 1 X) (he : e∈Finset.Icc 1 X) :
    (Nat.gcd d e:ℝ)=∑r∈Finset.Icc 1 X,
      if r∣d ∧ r∣e then (r.totient:ℝ) else 0 := by
  have hd' := Finset.mem_Icc.mp hd
  have hg := Nat.gcd_pos_of_pos_left e hd'.1
  have hf : (Finset.Icc 1 X).filter (fun r => r∣d ∧ r∣e)=(Nat.gcd d e).divisors := by
    ext r
    simp only [Finset.mem_filter,Finset.mem_Icc,Nat.mem_divisors,Nat.dvd_gcd_iff]
    constructor
    · exact fun h => ⟨h.2,hg.ne'⟩
    · intro h
      exact ⟨⟨Nat.pos_of_dvd_of_pos h.1.1 hd'.1,(Nat.le_of_dvd hd'.1 h.1.1).trans hd'.2⟩,h.1⟩
  rw [←Finset.sum_filter,hf,←Nat.cast_sum,Nat.sum_totient]

theorem quadratic_diagonal (X : ℕ) (w : ℕ → ℝ) : quadratic X w=
    ∑r∈Finset.Icc 1 X,(r.totient:ℝ)*
      (∑d∈Finset.Icc 1 X,if r∣d then w d/(d:ℝ) else 0)^2 := by
  let I := Finset.Icc 1 X
  have hp (d : ℕ) (hd : d∈I) (e : ℕ) (he : e∈I) :
      w d*w e/(Nat.lcm d e:ℝ)=
        ∑r∈I,if r∣d ∧ r∣e then (r.totient:ℝ)*(w d/(d:ℝ))*(w e/(e:ℝ)) else 0 := by
    have hdpos := (Finset.mem_Icc.mp hd).1
    have hepos := (Finset.mem_Icc.mp he).1
    have hmain : w d*w e/(Nat.lcm d e:ℝ)=
        (w d/(d:ℝ))*(w e/(e:ℝ))*(Nat.gcd d e:ℝ) := by
      have hh := inv_lcm hdpos hepos
      have hfactor : w d*w e/(Nat.lcm d e:ℝ)=w d*w e*(1/(Nat.lcm d e:ℝ)) := by ring
      rw [hfactor,hh]
      ring
    rw [hmain,gcd_totient_sum hd he,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    by_cases h : r∣d ∧ r∣e <;> simp [h] <;> ring
  have hexpand : quadratic X w=∑d∈I,∑e∈I,∑r∈I,
      if r∣d ∧ r∣e then (r.totient:ℝ)*(w d/(d:ℝ))*(w e/(e:ℝ)) else 0 := by
    apply Finset.sum_congr rfl
    intro d hd
    exact Finset.sum_congr rfl (fun e he => hp d hd e he)
  rw [hexpand]
  have hswap : (∑d∈I,∑e∈I,∑r∈I,
      if r∣d ∧ r∣e then (r.totient:ℝ)*(w d/(d:ℝ))*(w e/(e:ℝ)) else 0)=
      ∑r∈I,∑d∈I,∑e∈I,
        if r∣d ∧ r∣e then (r.totient:ℝ)*(w d/(d:ℝ))*(w e/(e:ℝ)) else 0 := by
    conv_lhs => arg 2;ext d;rw [Finset.sum_comm]
    rw [Finset.sum_comm]
  rw [hswap]
  apply Finset.sum_congr rfl
  intro r hr
  change (∑d∈I,∑e∈I,if r∣d ∧ r∣e then (r.totient:ℝ)*(w d/(d:ℝ))*(w e/(e:ℝ)) else 0)=
    (r.totient:ℝ)*(∑d∈I,if r∣d then w d/(d:ℝ) else 0)^2
  rw [pow_two]
  conv_rhs => arg 2;rw [Finset.sum_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [←mul_assoc,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hrd : r∣d <;> by_cases hre : r∣e <;> simp [hrd,hre] <;> ring

theorem weight_quadratic {X : ℕ} (hX : 0<X) : quadratic X (weight X)=1/G X := by
  rw [quadratic_diagonal]
  have hG := G_pos hX
  have ht (r : ℕ) (hr : r∈Finset.Icc 1 X) :
      (r.totient:ℝ)*(∑d∈Finset.Icc 1 X,if r∣d then weight X d/(d:ℝ) else 0)^2=
        if r∈support X then (1/(r.totient:ℝ))/(G X)^2 else 0 := by
    have hp := (Finset.mem_Icc.mp hr).1
    rw [weight_multiples_sum X r hp]
    by_cases hs : r∈support X
    · rw [if_pos hs,if_pos hs]
      have hphi : (0:ℝ)<r.totient := by exact_mod_cast Nat.totient_pos.mpr hp
      have hmu : (ArithmeticFunction.moebius r:ℝ)^2=1 := by
        exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree (mem_support hs).2.2
      rw [div_pow,mul_pow,hmu]
      field_simp
    · simp [hs]
  have he := Finset.sum_congr rfl ht
  rw [he,←Finset.sum_filter]
  have hf : (Finset.Icc 1 X).filter (fun r => r∈support X)=support X := by
    ext r
    simp only [Finset.mem_filter]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨(Finset.mem_filter.mp h).1,h⟩
  rw [hf,←Finset.sum_div]
  change G X/(G X)^2=1/G X
  field_simp

end LonelyRunnerNew.FiniteSelberg
