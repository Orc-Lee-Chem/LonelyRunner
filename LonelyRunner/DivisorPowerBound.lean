import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# 正约数个数的实幂上界

对应论文第 142 行的初等约数估计，以及 `lem:relations` 中短关系纤维计数的乘积界。
常数只随正指数变化，所有约数均由 `Nat.divisors` 枚举为正约数。
-/

open scoped Real
open Classical

namespace LonelyRunner

private lemma exponent_bound (x : ℝ) (hx : 1 < x) :
    ∃ N : ℕ, 0 < N ∧ (N + 1 : ℝ) ≤ x ^ N ∧
      ∀ a : ℕ, (a + 1 : ℝ) ≤ (N + 1 : ℝ) * x ^ a := by
  obtain ⟨N, hN⟩ := Real.exists_natCast_add_one_lt_pow_of_one_lt hx
  have hNpos : 0 < N := by
    by_contra h
    have : N = 0 := by omega
    subst N
    norm_num at hN
  refine ⟨N, hNpos, hN.le, ?_⟩
  intro a
  induction a using Nat.strong_induction_on with
  | h a ih =>
    by_cases ha : a < N
    · have hsmall : (a + 1 : ℝ) ≤ (N + 1 : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.le_of_lt ha)
      have hpow : (1 : ℝ) ≤ x ^ a := one_le_pow₀ (le_of_lt hx)
      nlinarith
    · let b := a - N
      have hb : b < a := by dsimp [b]; omega
      have hab : a = b + N := by dsimp [b]; omega
      have hib := ih b hb
      have hstep : (a + 1 : ℝ) ≤ (N + 1 : ℝ) * (b + 1 : ℝ) := by
        have hnat : a + 1 ≤ (N + 1) * (b + 1) := by
          rw [hab]
          nlinarith [Nat.zero_le (N * b)]
        exact_mod_cast hnat
      have hmid : (N + 1 : ℝ) * (b + 1 : ℝ) ≤ x ^ N * (b + 1 : ℝ) := by
        exact mul_le_mul_of_nonneg_right hN.le (by positivity)
      calc
        (a + 1 : ℝ) ≤ (N + 1 : ℝ) * (b + 1 : ℝ) := hstep
        _ ≤ x ^ N * (b + 1 : ℝ) := hmid
        _ ≤ x ^ N * ((N + 1 : ℝ) * x ^ b) :=
          mul_le_mul_of_nonneg_left hib (by positivity)
        _ = (N + 1 : ℝ) * x ^ a := by rw [hab, pow_add]; ring

private lemma succ_le_two_pow (a : ℕ) : a + 1 ≤ 2 ^ a := by
  induction a with
  | zero => norm_num
  | succ a ih =>
    rw [pow_succ]
    omega

private lemma nat_pow_rpow_comm (p a : ℕ) (η : ℝ) :
    (((p ^ a : ℕ) : ℝ) ^ η) = ((p : ℝ) ^ η) ^ a := by
  rw [Nat.cast_pow, ← Real.rpow_natCast (p : ℝ) a,
    ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ p), mul_comm,
    Real.rpow_mul (by positivity : (0 : ℝ) ≤ p), Real.rpow_natCast]

private lemma prod_nat_rpow (s : Finset ℕ) (f : ℕ → ℕ) (η : ℝ) :
    ((∏ p ∈ s, (f p : ℝ)) ^ η) = ∏ p ∈ s, ((f p : ℝ) ^ η) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
    simp only [Finset.prod_insert hp]
    rw [Real.mul_rpow (by positivity) (by positivity), ih]

private lemma factorization_rpow (n : ℕ) (hn : n ≠ 0) (η : ℝ) :
    (∏ p ∈ n.primeFactors, (((p ^ n.factorization p : ℕ) : ℝ) ^ η)) =
      (n : ℝ) ^ η := by
  conv_rhs => rw [Nat.prod_primeFactors_pow_factorization hn]
  simpa only [Nat.cast_prod] using
    (prod_nat_rpow n.primeFactors (fun p => p ^ n.factorization p) η).symm

private lemma prime_exponent_bound (η : ℝ) (hη : 0 < η) (N : ℕ) (hNpos : 0 < N)
    (hN : (N + 1 : ℝ) ≤ ((2 : ℝ) ^ η) ^ N)
    (hexp : ∀ a : ℕ, (a + 1 : ℝ) ≤ (N + 1 : ℝ) * ((2 : ℝ) ^ η) ^ a)
    (p a : ℕ) (hp : 2 ≤ p) :
    (a + 1 : ℝ) ≤
      (if p < 2 ^ N then (N + 1 : ℝ) else 1) *
        (((p ^ a : ℕ) : ℝ) ^ η) := by
  have hbase : (2 : ℝ) ^ η ≤ (p : ℝ) ^ η :=
    Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hp) hη.le
  have hpow : ((2 : ℝ) ^ η) ^ a ≤ (((p ^ a : ℕ) : ℝ) ^ η) := by
    rw [nat_pow_rpow_comm]
    exact pow_le_pow_left₀ (by positivity) hbase _
  split_ifs with hsmall
  · have := hexp a
    nlinarith [mul_le_mul_of_nonneg_left hpow (by positivity : (0 : ℝ) ≤ N + 1)]
  · have hT : (2 : ℝ) ≤ (((2 ^ N : ℕ) : ℝ) ^ η) := by
      rw [nat_pow_rpow_comm]
      have hNtwo : (2 : ℝ) ≤ (N + 1 : ℝ) := by
        exact_mod_cast Nat.succ_le_succ hNpos
      exact hNtwo.trans (by simpa using hN)
    have hpT : 2 ^ N ≤ p := Nat.le_of_not_gt hsmall
    have hTpow : (((2 ^ N : ℕ) : ℝ) ^ η) ≤ (p : ℝ) ^ η :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast hpT) hη.le
    have htwo : (2 : ℝ) ≤ (p : ℝ) ^ η := le_trans hT hTpow
    have h2pow : (2 : ℝ) ^ a ≤ (((p ^ a : ℕ) : ℝ) ^ η) := by
      rw [nat_pow_rpow_comm]
      exact pow_le_pow_left₀ (by norm_num) htwo _
    have hs : (a + 1 : ℝ) ≤ (2 : ℝ) ^ a := by
      exact_mod_cast succ_le_two_pow a
    simpa using hs.trans h2pow

/-- 论文第 142 行及 `lem:relations`：正整数的正约数个数至多为任意正实数幂，
其中常数仅依赖指数。 -/
theorem divisorPowerBound (η : ℝ) (hη : 0 < η) :
    ∃ Cη : ℝ, 0 < Cη ∧ ∀ n : ℕ, 1 ≤ n →
      (n.divisors.card : ℝ) ≤ Cη * (n : ℝ) ^ η := by
  let x : ℝ := (2 : ℝ) ^ η
  have hx : 1 < x := Real.one_lt_rpow (by norm_num) hη
  obtain ⟨N, hNpos, hN, hexp⟩ := exponent_bound x hx
  let T : ℕ := 2 ^ N
  let Cη : ℝ := (N + 1 : ℝ) ^ T
  have hCpos : 0 < Cη := by dsimp [Cη]; positivity
  refine ⟨Cη, hCpos, ?_⟩
  intro n hn
  by_cases hn1 : n = 1
  · subst n
    have hCone : 1 ≤ Cη := by
      dsimp [Cη]
      exact one_le_pow₀ (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N) : (1 : ℝ) ≤ N + 1)
    simpa using hCone
  have hn0 : n ≠ 0 := by omega
  let s := n.primeFactors
  let ssmall := s.filter (fun p => p < T)
  have hsmallCard : ssmall.card ≤ T := by
    have hsub : ssmall ⊆ Finset.range T := by
      intro p hp
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
    simpa using Finset.card_le_card hsub
  have hfactor (p : ℕ) (hp : p ∈ s) :
      (n.factorization p + 1 : ℝ) ≤
        (if p < T then (N + 1 : ℝ) else 1) *
          (((p ^ n.factorization p : ℕ) : ℝ) ^ η) := by
    have hpprime := Nat.prime_of_mem_primeFactors hp
    exact prime_exponent_bound η hη N hNpos hN hexp p (n.factorization p) hpprime.two_le
  have hcard : (n.divisors.card : ℝ) =
      ∏ p ∈ s, (n.factorization p + 1 : ℝ) := by
    exact_mod_cast Nat.card_divisors hn0
  have hprod : (∏ p ∈ s, (n.factorization p + 1 : ℝ)) ≤
      ∏ p ∈ s, ((if p < T then (N + 1 : ℝ) else 1) *
        (((p ^ n.factorization p : ℕ) : ℝ) ^ η)) := by
    apply Finset.prod_le_prod₀
    · intro p hp; positivity
    · intro p hp; exact hfactor p hp
  have hprodIf : (∏ p ∈ s, if p < T then (N + 1 : ℝ) else 1) =
      (N + 1 : ℝ) ^ ssmall.card := by
    simp [ssmall, Finset.prod_ite]
  have hCsmall : (N + 1 : ℝ) ^ ssmall.card ≤ Cη := by
    dsimp [Cη]
    exact pow_le_pow_right₀
      (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N) : (1 : ℝ) ≤ N + 1)
      hsmallCard
  have hrpow : (∏ p ∈ s, (((p ^ n.factorization p : ℕ) : ℝ) ^ η)) =
      (n : ℝ) ^ η := factorization_rpow n hn0 η
  have hnPow : 0 ≤ (n : ℝ) ^ η := by positivity
  calc
    (n.divisors.card : ℝ) = ∏ p ∈ s, (n.factorization p + 1 : ℝ) := hcard
    _ ≤ ∏ p ∈ s, ((if p < T then (N + 1 : ℝ) else 1) *
        (((p ^ n.factorization p : ℕ) : ℝ) ^ η)) := hprod
    _ = (N + 1 : ℝ) ^ ssmall.card * (n : ℝ) ^ η := by
      rw [Finset.prod_mul_distrib, hprodIf, hrpow]
    _ ≤ Cη * (n : ℝ) ^ η := mul_le_mul_of_nonneg_right hCsmall hnPow

private lemma square_rpow_square (x η : ℝ) (hx : 0 ≤ x) :
    (((x ^ 2) ^ η) ^ 2) = x ^ (4 * η) := by
  rw [← Real.rpow_natCast ((x ^ 2) ^ η) 2,
    ← Real.rpow_mul (sq_nonneg x),
    ← Real.rpow_natCast x 2,
    ← Real.rpow_mul hx]
  congr 1
  ring

/-- 论文 `lem:relations` 的纤维计数输入：沿用主定理的同一个 `Cη`，
对所有 `m ≥ 1` 和 `1 ≤ u,v ≤ m²` 同时控制两个约数函数的乘积。 -/
theorem divisorPowerBound_energy (η : ℝ) (hη : 0 < η) :
    ∃ Cη : ℝ, 0 < Cη ∧
      (∀ n : ℕ, 1 ≤ n → (n.divisors.card : ℝ) ≤ Cη * (n : ℝ) ^ η) ∧
      ∀ m u v : ℕ, 1 ≤ m → 1 ≤ u → 1 ≤ v → u ≤ m ^ 2 → v ≤ m ^ 2 →
        (u.divisors.card : ℝ) * (v.divisors.card : ℝ) ≤
          Cη ^ 2 * (m : ℝ) ^ (4 * η) := by
  obtain ⟨Cη, hCη, hbound⟩ := divisorPowerBound η hη
  refine ⟨Cη, hCη, hbound, ?_⟩
  intro m u v hm hu hv hum hvm
  have huReal : (u : ℝ) ≤ (m : ℝ) ^ 2 := by exact_mod_cast hum
  have hvReal : (v : ℝ) ≤ (m : ℝ) ^ 2 := by exact_mod_cast hvm
  have hpowu : (u : ℝ) ^ η ≤ ((m : ℝ) ^ 2) ^ η :=
    Real.rpow_le_rpow (by positivity) huReal hη.le
  have hpowv : (v : ℝ) ^ η ≤ ((m : ℝ) ^ 2) ^ η :=
    Real.rpow_le_rpow (by positivity) hvReal hη.le
  have hdu : (u.divisors.card : ℝ) ≤ Cη * ((m : ℝ) ^ 2) ^ η :=
    (hbound u hu).trans (mul_le_mul_of_nonneg_left hpowu hCη.le)
  have hdv : (v.divisors.card : ℝ) ≤ Cη * ((m : ℝ) ^ 2) ^ η :=
    (hbound v hv).trans (mul_le_mul_of_nonneg_left hpowv hCη.le)
  have hprod := mul_le_mul hdu hdv
    (by positivity : 0 ≤ (v.divisors.card : ℝ))
    (by positivity : 0 ≤ Cη * ((m : ℝ) ^ 2) ^ η)
  calc
    (u.divisors.card : ℝ) * (v.divisors.card : ℝ) ≤
        (Cη * ((m : ℝ) ^ 2) ^ η) * (Cη * ((m : ℝ) ^ 2) ^ η) := hprod
    _ = Cη ^ 2 * (m : ℝ) ^ (4 * η) := by
      rw [← sq, mul_pow, square_rpow_square (m : ℝ) η (by positivity)]

end LonelyRunner
