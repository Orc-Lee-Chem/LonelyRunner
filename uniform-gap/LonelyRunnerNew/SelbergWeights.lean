import LonelyRunnerNew.AsymmetricParameters
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Totient

noncomputable section
set_option autoImplicit false
open scoped BigOperators ArithmeticFunction.Moebius
namespace LonelyRunnerNew.FiniteSelberg
attribute [local instance] Classical.propDecidable

def support (X : ℕ) : Finset ℕ := (Finset.Icc 1 X).filter Squarefree
def G (X : ℕ) : ℝ := ∑r∈support X,1/(r.totient:ℝ)
def V (X d : ℕ) : ℝ := ∑r∈support X,
  if d∣r then (ArithmeticFunction.moebius (r/d):ℝ)*(ArithmeticFunction.moebius r:ℝ)/(r.totient:ℝ) else 0
def weight (X d : ℕ) : ℝ := (d:ℝ)*V X d/G X

theorem mem_support {X r : ℕ} (hr : r∈support X) : 0<r ∧ r≤X ∧ Squarefree r := by
  have hh := Finset.mem_filter.mp hr
  exact ⟨(Finset.mem_Icc.mp hh.1).1,(Finset.mem_Icc.mp hh.1).2,hh.2⟩

theorem G_pos {X : ℕ} (hX : 0<X) : 0<G X := by
  unfold G
  apply Finset.sum_pos' (fun r hr => by positivity)
  refine ⟨1,?_,?_⟩
  · simp [support];omega
  · norm_num

theorem moebius_divisor_sum (n : ℕ) :
    (∑d∈n.divisors,(ArithmeticFunction.moebius d:ℝ))=if n=1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R:=ℝ))
  simpa only [ArithmeticFunction.coe_mul_zeta_apply,ArithmeticFunction.intCoe_apply,
    ArithmeticFunction.one_apply] using h

theorem upper_moebius {l r : ℕ} (hl : 0<l) (hr : 0<r) (hrl : r∣l) :
    (∑d∈l.divisors,if r∣d then (ArithmeticFunction.moebius (l/d):ℝ) else 0)=
      if l=r then 1 else 0 := by
  have hc : ∀d∈l.divisors,(r∣d ↔ l/d∣l/r) := by
    intro d hd
    exact (Nat.div_dvd_div_iff_left hl (Nat.mem_divisors.mp hd).1 hrl).symm
  have he : (∑d∈l.divisors,if r∣d then (ArithmeticFunction.moebius (l/d):ℝ) else 0)=
      ∑d∈l.divisors,if l/d∣l/r then (ArithmeticFunction.moebius (l/d):ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro d hd
    simp only [hc d hd]
  rw [he]
  change (∑d∈l.divisors,(fun k : ℕ => if k∣l/r then (ArithmeticFunction.moebius k:ℝ) else 0) (l/d))=_
  rw [Nat.sum_div_divisors l (fun k : ℕ => if k∣l/r then (ArithmeticFunction.moebius k:ℝ) else 0),←Finset.sum_filter,
    Nat.divisors_filter_dvd_of_dvd hl.ne' (show l/r∣l from ⟨r,(Nat.div_mul_cancel hrl).symm⟩),moebius_divisor_sum]
  by_cases h : l=r
  · simp [h,Nat.div_self hr]
  · have hq : l/r≠1 := by
      intro hh
      have he := Nat.div_mul_cancel hrl
      rw [hh,one_mul] at he
      exact h he.symm
    simp [h,hq]

theorem V_multiples_sum (X r : ℕ) (hr : 0<r) :
    (∑d∈Finset.Icc 1 X,if r∣d then V X d else 0)=
      if r∈support X then (ArithmeticFunction.moebius r:ℝ)/(r.totient:ℝ) else 0 := by
  have he : (∑d∈Finset.Icc 1 X,if r∣d then V X d else 0)=
      ∑l∈support X,((ArithmeticFunction.moebius l:ℝ)/(l.totient:ℝ))*
        ∑d∈Finset.Icc 1 X,if d∣l ∧ r∣d then (ArithmeticFunction.moebius (l/d):ℝ) else 0 := by
    unfold V
    simp_rw [Finset.ite_sum_zero]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l hl
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hrd : r∣d <;> by_cases hdl : d∣l <;> simp [hrd,hdl] <;> ring
  rw [he]
  have hi (l : ℕ) (hl : l∈support X) :
      (∑d∈Finset.Icc 1 X,if d∣l ∧ r∣d then (ArithmeticFunction.moebius (l/d):ℝ) else 0)=
        if l=r then 1 else 0 := by
    have hs := mem_support hl
    have hfilter : (Finset.Icc 1 X).filter (fun d => d∣l)=l.divisors := by
      ext d
      simp only [Finset.mem_filter,Finset.mem_Icc,Nat.mem_divisors]
      constructor
      · exact fun h => ⟨h.2,hs.1.ne'⟩
      · intro h
        exact ⟨⟨Nat.pos_of_dvd_of_pos h.1 hs.1,(Nat.le_of_dvd hs.1 h.1).trans hs.2.1⟩,h.1⟩
    have hsum : (∑d∈Finset.Icc 1 X,if d∣l ∧ r∣d then (ArithmeticFunction.moebius (l/d):ℝ) else 0)=
        ∑d∈l.divisors,if r∣d then (ArithmeticFunction.moebius (l/d):ℝ) else 0 := by
      rw [←hfilter,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases h : d∣l <;> simp [h]
    rw [hsum]
    by_cases hrl : r∣l
    · exact upper_moebius hs.1 hr hrl
    · have hne : l≠r := by intro h;exact hrl (by rw [h])
      rw [if_neg hne]
      apply Finset.sum_eq_zero
      intro d hd
      have hnd : ¬r∣d := fun h => hrl (h.trans (Nat.mem_divisors.mp hd).1)
      simp [hnd]
  calc
    _ =∑l∈support X,((ArithmeticFunction.moebius l:ℝ)/(l.totient:ℝ))*(if l=r then 1 else 0) :=
      Finset.sum_congr rfl (fun l hl => by rw [hi l hl])
    _ =_ := by simp only [mul_ite,mul_one,mul_zero];rw [Finset.sum_ite_eq']

theorem moebius_quotient_product {r d : ℕ} (hr : Squarefree r) (hd : d∣r) :
    (ArithmeticFunction.moebius (r/d):ℝ)*(ArithmeticFunction.moebius r:ℝ)=
      (ArithmeticFunction.moebius d:ℝ) := by
  have he : d*(r/d)=r := Nat.mul_div_cancel' hd
  have hsq : Squarefree (d*(r/d)) := he.symm ▸ hr
  have hc := Nat.coprime_of_squarefree_mul hsq
  have hm := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hc
  rw [he] at hm
  have hs := ArithmeticFunction.moebius_sq_eq_one_of_squarefree
    (hr.squarefree_of_dvd (show r/d∣r from ⟨d,(Nat.div_mul_cancel hd).symm⟩))
  have hmR : (ArithmeticFunction.moebius r:ℝ)=
      (ArithmeticFunction.moebius d:ℝ)*(ArithmeticFunction.moebius (r/d):ℝ) := by exact_mod_cast hm
  have hsR : (ArithmeticFunction.moebius (r/d):ℝ)^2=1 := by exact_mod_cast hs
  rw [hmR]
  nlinarith only [congrArg (fun z : ℝ => (ArithmeticFunction.moebius d:ℝ)*z) hsR]

theorem V_signed (X d : ℕ) : V X d=(ArithmeticFunction.moebius d:ℝ)*
    ∑r∈support X,if d∣r then 1/(r.totient:ℝ) else 0 := by
  unfold V
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hd : d∣r
  · rw [if_pos hd,if_pos hd,moebius_quotient_product (mem_support hr).2.2 hd]
    ring
  · simp [hd]

theorem weight_one {X : ℕ} (hX : 0<X) : weight X 1=1 := by
  rw [weight,V_signed]
  simp only [ArithmeticFunction.moebius_apply_one,Int.cast_one,one_dvd,ite_true,one_mul,Nat.cast_one]
  exact div_self (G_pos hX).ne'

theorem weight_div (X d : ℕ) (hd : 0<d) : weight X d/(d:ℝ)=V X d/G X := by
  unfold weight
  field_simp

theorem weight_multiples_sum (X r : ℕ) (hr : 0<r) :
    (∑d∈Finset.Icc 1 X,if r∣d then weight X d/(d:ℝ) else 0)=
      if r∈support X then (ArithmeticFunction.moebius r:ℝ)/(G X*(r.totient:ℝ)) else 0 := by
  have he : (∑d∈Finset.Icc 1 X,if r∣d then weight X d/(d:ℝ) else 0)=
      (∑d∈Finset.Icc 1 X,if r∣d then V X d else 0)/G X := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d hd
    have hp := (Finset.mem_Icc.mp hd).1
    by_cases h : r∣d <;> simp only [h,ite_true,ite_false,zero_div,weight_div X d hp]
  rw [he,V_multiples_sum X r hr]
  by_cases hm : r∈support X <;> simp [hm] <;> ring

end LonelyRunnerNew.FiniteSelberg
