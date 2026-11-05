import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew.RCThirty

/-- Integer subtraction, never truncated natural subtraction. -/
def coefficient (n : ℕ) : ℤ := (n:ℤ)-(n/2:ℕ)-(n/3:ℕ)-(n/5:ℕ)+(n/30:ℕ)

theorem coefficient_mod (n : ℕ) : coefficient n=coefficient (n%30) := by
  unfold coefficient
  omega

theorem coefficient_range (n : ℕ) : coefficient n=0 ∨ coefficient n=1 := by
  rw [coefficient_mod]
  have h : n%30<30 := Nat.mod_lt _ (by norm_num)
  generalize n%30=k at *
  interval_cases k <;> norm_num [coefficient]

theorem coefficient_one {n : ℕ} (h1 : 1≤n) (h6 : n<6) : coefficient n=1 := by
  interval_cases n <;> norm_num [coefficient]

theorem coefficient_zero : coefficient 0=0 := by norm_num [coefficient]

/-- Complete divisor expansion, with a common arbitrary finite upper support.
This is used for all five factorials in J, not a sampled approximation. -/
theorem log_factorial_weighted (N M : ℕ) (hNM : N≤M) :
    Real.log (N.factorial:ℝ)=
      ∑d∈Finset.range (M+1),((N/d:ℕ):ℝ)*ArithmeticFunction.vonMangoldt d := by
  have hlog (m : ℕ) (hm1 : 0<m) (hmM : m≤M) :
      Real.log (m:ℝ)=∑d∈Finset.range (M+1),if d∣m then ArithmeticFunction.vonMangoldt d else 0 := by
    rw [←ArithmeticFunction.vonMangoldt_sum,←Finset.sum_filter]
    apply Finset.sum_subset
    · intro d hd
      have hh := Nat.mem_divisors.mp hd
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
        have := Nat.le_of_dvd hm1 hh.1
        omega),hh.1⟩
    · intro d hd hnot
      have hh := Finset.mem_filter.mp hd
      exact False.elim (hnot (Nat.mem_divisors.mpr ⟨hh.2,hm1.ne'⟩))
  have hf : Real.log (N.factorial:ℝ)=∑i∈Finset.range N,Real.log (i+1:ℝ) := by
    rw [Nat.factorial_eq_prod_range_add_one,Nat.cast_prod,Real.log_prod]
    · simp only [Nat.cast_add,Nat.cast_one]
    · intro i hi
      positivity
  rw [hf]
  have he : (∑i∈Finset.range N,Real.log (i+1:ℝ))=
      ∑i∈Finset.range N,∑d∈Finset.range (M+1),if d∣i+1 then ArithmeticFunction.vonMangoldt d else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    have him := Finset.mem_range.mp hi
    simpa only [Nat.cast_add,Nat.cast_one] using hlog (i+1) (by omega) (by omega)
  rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [←Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul,Nat.card_multiples]

def J (x : ℝ) : ℝ := Real.log ((⌊x⌋₊).factorial:ℝ)-
  Real.log ((⌊x/2⌋₊).factorial:ℝ)-Real.log ((⌊x/3⌋₊).factorial:ℝ)-
  Real.log ((⌊x/5⌋₊).factorial:ℝ)+Real.log ((⌊x/30⌋₊).factorial:ℝ)

theorem J_expansion (x : ℝ) : J x=
    ∑d∈Finset.range (⌊x⌋₊+1),
      (coefficient (⌊x⌋₊/d):ℝ)*ArithmeticFunction.vonMangoldt d := by
  unfold J
  have hdiv (k : ℕ) : ⌊x/(k:ℝ)⌋₊=⌊x⌋₊/k := Nat.floor_div_natCast x k
  norm_cast at hdiv
  rw [show (2:ℝ)=(2:ℕ) by norm_num,hdiv 2,
    show (3:ℝ)=(3:ℕ) by norm_num,hdiv 3,
    show (5:ℝ)=(5:ℕ) by norm_num,hdiv 5,
    show (30:ℝ)=(30:ℕ) by norm_num,hdiv 30]
  rw [log_factorial_weighted _ _ (le_refl _),
    log_factorial_weighted _ ⌊x⌋₊ (Nat.div_le_self _ _),
    log_factorial_weighted _ ⌊x⌋₊ (Nat.div_le_self _ _),
    log_factorial_weighted _ ⌊x⌋₊ (Nat.div_le_self _ _),
    log_factorial_weighted _ ⌊x⌋₊ (Nat.div_le_self _ _)]
  rw [←Finset.sum_sub_distrib,←Finset.sum_sub_distrib,←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [coefficient,Int.cast_add,Int.cast_sub,Int.cast_natCast,Nat.div_div_eq_div_mul]
  simp only [Nat.mul_comm]
  ring

theorem psi_eq_range (x : ℝ) : Chebyshev.psi x=
    ∑d∈Finset.range (⌊x⌋₊+1),ArithmeticFunction.vonMangoldt d := by
  unfold Chebyshev.psi
  have he : Finset.Ioc 0 ⌊x⌋₊=(Finset.range (⌊x⌋₊+1)).erase 0 := by ext d;simp;omega
  rw [he,Finset.sum_erase_eq_sub (Finset.mem_range.mpr (by omega))]
  simp

theorem J_le_psi (x : ℝ) : J x≤Chebyshev.psi x := by
  rw [J_expansion,psi_eq_range]
  apply Finset.sum_le_sum
  intro d hd
  rcases coefficient_range (⌊x⌋₊/d) with h | h <;>
    simp only [h,Int.cast_zero,Int.cast_one,zero_mul,one_mul]
  · exact ArithmeticFunction.vonMangoldt_nonneg
  · rfl

theorem psi_le_J_add (x : ℝ) : Chebyshev.psi x≤J x+Chebyshev.psi (x/6) := by
  have he : Chebyshev.psi (x/6)=∑d∈Finset.range (⌊x⌋₊+1),
      if d≤⌊x⌋₊/6 then ArithmeticFunction.vonMangoldt d else 0 := by
    rw [psi_eq_range,Nat.floor_div_ofNat]
    rw [←Finset.sum_filter]
    congr 1
    ext d
    simp only [Finset.mem_range,Finset.mem_filter]
    have := Nat.div_le_self ⌊x⌋₊ 6
    omega
  rw [psi_eq_range,J_expansion,he,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro d hd
  by_cases h0 : d=0
  · subst d;simp
  by_cases hsmall : d≤⌊x⌋₊/6
  · simp only [if_pos hsmall]
    rcases coefficient_range (⌊x⌋₊/d) with h | h <;>
      simp only [h,Int.cast_zero,Int.cast_one,zero_mul,one_mul]
    · simp
    · exact le_add_of_nonneg_left ArithmeticFunction.vonMangoldt_nonneg
  · have hdpos : 0<d := Nat.pos_of_ne_zero h0
    have hdle : d≤⌊x⌋₊ := by have := Finset.mem_range.mp hd;omega
    have hq1 : 1≤⌊x⌋₊/d := (Nat.le_div_iff_mul_le hdpos).mpr (by simpa using hdle)
    have hq6 : ⌊x⌋₊/d<6 := (Nat.div_lt_iff_lt_mul hdpos).mpr (by
      have hh := (Nat.div_lt_iff_lt_mul (by norm_num : 0<6)).mp (lt_of_not_ge hsmall)
      nlinarith)
    simp only [if_neg hsmall,coefficient_one hq1 hq6,Int.cast_one,one_mul,add_zero,le_refl]

end LonelyRunnerNew.RCThirty
