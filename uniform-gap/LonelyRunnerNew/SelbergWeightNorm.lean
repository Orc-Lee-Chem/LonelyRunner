import LonelyRunnerNew.SelbergEulerSum
import LonelyRunnerNew.SelbergHarmonic
import Mathlib.NumberTheory.ArithmeticFunction.Misc

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew.FiniteSelberg
attribute [local instance] Classical.propDecidable

theorem weight_abs {X : ℕ} (hX : 0<X) (d : ℕ) : |weight X d|=
    (d:ℝ)/G X*(∑r∈support X,if d∣r then 1/(r.totient:ℝ) else 0) := by
  have hG := G_pos hX
  have hn : 0≤∑r∈support X,if d∣r then 1/(r.totient:ℝ) else 0 :=
    Finset.sum_nonneg (fun r hr => by split_ifs <;> positivity)
  by_cases hs : Squarefree d
  · have hm : |(ArithmeticFunction.moebius d:ℝ)|=1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree hs
    rw [weight,V_signed,abs_div,abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg d),hm,
      abs_of_nonneg hn,abs_of_pos hG]
    ring
  · have hm := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs
    have he : (∑r∈support X,if d∣r then 1/(r.totient:ℝ) else 0)=0 := by
      apply Finset.sum_eq_zero
      intro r hr
      have hn : ¬d∣r := fun h => hs ((mem_support hr).2.2.squarefree_of_dvd h)
      simp [hn]
    rw [he]
    simp [weight,V_signed,hm]

theorem squarefree_divisor_ratio {r : ℕ} (hr : Squarefree r) :
    (∑d∈r.divisors,(d:ℝ))/(r.totient:ℝ)=
      ∏p∈r.primeFactors,(1+2/((p:ℝ)-1)) := by
  have hn : (∑d∈r.divisors,d)=∏p∈r.primeFactors,(1+p) := by
    rw [Nat.sum_divisors hr.ne_zero]
    apply Finset.prod_congr rfl
    intro p hp
    have hh := Nat.mem_primeFactors.mp hp
    rw [Nat.factorization_eq_one_of_squarefree hr hh.1 hh.2.1]
    norm_num [Finset.sum_range_succ]
  rw [←Nat.cast_sum,hn,Nat.cast_prod,squarefree_totient_product hr,←Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hpr : (2:ℝ)≤p := by exact_mod_cast (Nat.mem_primeFactors.mp hp).1.two_le
  push_cast
  field_simp [show (p:ℝ)-1≠0 by linarith] <;> ring

theorem weight_abs_sum_identity {X : ℕ} (hX : 0<X) :
    (∑d∈Finset.Icc 1 X,|weight X d|)=
      (∑r∈support X,∏p∈r.primeFactors,(1+2/((p:ℝ)-1)))/G X := by
  have hd (d : ℕ) (hd : d∈Finset.Icc 1 X) : |weight X d|=
      ∑r∈support X,if d∣r then (d:ℝ)/(r.totient:ℝ)/G X else 0 := by
    rw [weight_abs hX,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    by_cases h : d∣r <;> simp [h] <;> ring
  have he := Finset.sum_congr rfl hd
  rw [he,Finset.sum_comm,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r hr
  have hh := mem_support hr
  have hf : (Finset.Icc 1 X).filter (fun d => d∣r)=r.divisors := by
    ext d
    simp only [Finset.mem_filter,Finset.mem_Icc,Nat.mem_divisors]
    constructor
    · exact fun h => ⟨h.2,hh.1.ne'⟩
    · intro h
      exact ⟨⟨Nat.pos_of_dvd_of_pos h.1 hh.1,(Nat.le_of_dvd hh.1 h.1).trans hh.2.1⟩,h.1⟩
  rw [←Finset.sum_filter,hf,←Finset.sum_div,←Finset.sum_div,squarefree_divisor_ratio hh.2.2]

/-- The actual optimized weights have total variation at most 4X/G,
proved with finite divisor sums and the finite telescoping Euler bound. -/
theorem weight_abs_sum_le {X : ℕ} (hX : 2≤X) :
    (∑d∈Finset.Icc 1 X,|weight X d|)≤4*(X:ℝ)/G X := by
  have hx0 : 0<X := by omega
  have hG := G_pos hx0
  rw [weight_abs_sum_identity hx0]
  have hs : (∑r∈support X,∏p∈r.primeFactors,(1+2/((p:ℝ)-1)))≤
      ∑r∈Finset.Icc 1 X,∏p∈r.primeFactors,(1+2/((p:ℝ)-1)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro r hr hn
    apply Finset.prod_nonneg
    intro p hp
    have hpr : (2:ℝ)≤p := by exact_mod_cast (Nat.mem_primeFactors.mp hp).1.two_le
    have hh : 0≤2/((p:ℝ)-1) := div_nonneg (by norm_num) (by linarith)
    linarith
  have he := actual_euler_average X
  have hp := eulerProduct_lt_four hX
  apply div_le_div_of_nonneg_right _ hG.le
  have hm := mul_le_mul_of_nonneg_left hp.le (Nat.cast_nonneg X: (0:ℝ)≤X)
  nlinarith

end LonelyRunnerNew.FiniteSelberg
