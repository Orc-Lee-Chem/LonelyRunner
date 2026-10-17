import LonelyRunner.ShortRelationSum
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# GCD 核的整数代数基础

对应论文 `lem:relations` 后所需的 GCD 和工具。本文件不证明 Bondarenko–Seip 估计。
-/

open Classical
open scoped Real

namespace LonelyRunner

/-- 正整数上的 GCD 核 `K_σ(a,b)`。 -/
noncomputable def gcdKernel (σ : ℝ) (a b : ℕ) : ℝ :=
  (((Nat.gcd a b : ℝ) ^ 2) / ((a : ℝ) * (b : ℝ))) ^ σ

private theorem gcdKernel_ratio_bounds (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    0 < ((Nat.gcd a b : ℝ) ^ 2) / ((a : ℝ) * (b : ℝ)) ∧
      ((Nat.gcd a b : ℝ) ^ 2) / ((a : ℝ) * (b : ℝ)) ≤ 1 := by
  have hga : (Nat.gcd a b : ℝ) ≤ a := by
    exact_mod_cast (Nat.gcd_le_left b ha)
  have hgb : (Nat.gcd a b : ℝ) ≤ b := by
    exact_mod_cast (Nat.gcd_le_right a hb)
  have hgpNat : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha
  have hgp : (0 : ℝ) < Nat.gcd a b := by
    exact_mod_cast hgpNat
  have har : (0 : ℝ) < a := by exact_mod_cast ha
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  have hsq : (Nat.gcd a b : ℝ) ^ 2 ≤ (a : ℝ) * b := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hga) (sub_nonneg.mpr hgb)]
  constructor
  · positivity
  · exact (div_le_iff₀ (mul_pos har hbr)).2 (by nlinarith)

/-- GCD 核对称，且正指数下严格为正、不超过一。 -/
theorem gcdKernel_symm (σ : ℝ) (a b : ℕ) :
    gcdKernel σ a b = gcdKernel σ b a := by
  simp [gcdKernel, Nat.gcd_comm, mul_comm]

theorem gcdKernel_pos_le_one (σ : ℝ) (hσ : 0 < σ)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    0 < gcdKernel σ a b ∧ gcdKernel σ a b ≤ 1 := by
  obtain ⟨hpos, hle⟩ := gcdKernel_ratio_bounds a b ha hb
  constructor
  · exact Real.rpow_pos_of_pos hpos _
  · simpa [gcdKernel] using
      (Real.rpow_le_rpow hpos.le hle hσ.le)

/-- 对角项恒等于一，包括 `a=1`。 -/
theorem gcdKernel_diag (σ : ℝ) (a : ℕ) (ha : 0 < a) :
    gcdKernel σ a a = 1 := by
  have har : (a : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ha)
  simp [gcdKernel, har, pow_two]

/-- 半次核等于 `gcd(a,b)/√(ab)`。 -/
theorem gcdKernel_half (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    gcdKernel ((1 : ℝ) / 2) a b =
      (Nat.gcd a b : ℝ) / Real.sqrt ((a : ℝ) * b) := by
  have hgp : (0 : ℝ) ≤ Nat.gcd a b := by positivity
  have hden : (0 : ℝ) ≤ (a : ℝ) * b := by positivity
  rw [gcdKernel, ← Real.sqrt_eq_rpow,
    Real.sqrt_div (sq_nonneg (Nat.gcd a b : ℝ)) _,
    Real.sqrt_sq_eq_abs, abs_of_nonneg hgp]

/-- 一般核是半次核的 `2σ` 次幂。 -/
theorem gcdKernel_eq_half_rpow (σ : ℝ) (hσ : 0 < σ)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    gcdKernel σ a b = (gcdKernel ((1 : ℝ) / 2) a b) ^ (2 * σ) := by
  have hbase := (gcdKernel_ratio_bounds a b ha hb).1.le
  unfold gcdKernel
  rw [← Real.rpow_mul hbase]
  congr 1
  ring

/-- 将一个实际整除 `ab` 的正整数的分解扩展到 `ab` 的素因子集。 -/
private theorem gcdKernel_factor_prod (n a b : ℕ)
    (hn : 0 < n) (ha : 0 < a) (hb : 0 < b) (hdiv : n ∣ a * b) :
    (n : ℝ) = ∏ p ∈ (a * b).primeFactors,
      (p : ℝ) ^ n.factorization p := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hab0 : a * b ≠ 0 := mul_ne_zero (Nat.ne_of_gt ha) (Nat.ne_of_gt hb)
  have hsub : n.primeFactors ⊆ (a * b).primeFactors :=
    Nat.primeFactors_mono hdiv hab0
  have hcast : (n : ℝ) = ∏ p ∈ n.primeFactors,
      (p : ℝ) ^ n.factorization p := by
    exact_mod_cast Nat.prod_primeFactors_pow_factorization hn0
  rw [hcast]
  apply Finset.prod_subset hsub
  intro p hp hpnot
  have hz : n.factorization p = 0 :=
    Finsupp.notMem_support_iff.mp (by simpa [Nat.support_factorization] using hpnot)
  simp [hz]

/-- 素数处的最小赋值恒等式。 -/
private theorem gcdKernel_prime_factor (p x y : ℕ) (hp : 0 < p) :
    (((p : ℝ) ^ min x y) ^ 2) /
        (((p : ℝ) ^ x) * ((p : ℝ) ^ y)) =
      (p : ℝ) ^ (-|((x : ℝ) - (y : ℝ))|) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hexp :
      (((min x y : ℕ) : ℝ) + ((min x y : ℕ) : ℝ)) -
        ((x : ℝ) + (y : ℝ)) = -|((x : ℝ) - (y : ℝ))| := by
    rcases le_total x y with hxy | hyx
    · have hxyR : (x : ℝ) ≤ y := by exact_mod_cast hxy
      rw [min_eq_left hxy, abs_of_nonpos (by linarith : (x : ℝ) - y ≤ 0)]
      ring
    · have hyxR : (y : ℝ) ≤ x := by exact_mod_cast hyx
      rw [min_eq_right hyx, abs_of_nonneg (by linarith : 0 ≤ (x : ℝ) - y)]
      ring
  calc
    _ = ((p : ℝ) ^ (((min x y : ℕ) : ℝ)) *
        (p : ℝ) ^ (((min x y : ℕ) : ℝ))) /
        ((p : ℝ) ^ (x : ℝ) * (p : ℝ) ^ (y : ℝ)) := by
          simp only [Real.rpow_natCast, pow_two]
    _ = (p : ℝ) ^ ((((min x y : ℕ) : ℝ) + ((min x y : ℕ) : ℝ)) -
        ((x : ℝ) + (y : ℝ))) := by
          rw [← Real.rpow_add hpR, ← Real.rpow_add hpR,
            Real.rpow_sub hpR]
    _ = _ := by rw [hexp]

/-- 由 `ab` 的实际素因子集给出的有限乘积；`a=1` 或 `b=1` 均包含在内。 -/
private theorem gcdKernel_ratio_prod (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ((Nat.gcd a b : ℝ) ^ 2) / ((a : ℝ) * (b : ℝ)) =
      ∏ p ∈ (a * b).primeFactors,
        (p : ℝ) ^ (-|((a.factorization p : ℝ) - (b.factorization p : ℝ))|) := by
  let S := (a * b).primeFactors
  have hga : Nat.gcd a b ∣ a * b :=
    dvd_mul_of_dvd_left (Nat.gcd_dvd_left a b) b
  have hgpos : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha
  have haProd : (a : ℝ) = ∏ p ∈ S, (p : ℝ) ^ a.factorization p :=
    gcdKernel_factor_prod a a b ha ha hb (dvd_mul_right a b)
  have hbProd : (b : ℝ) = ∏ p ∈ S, (p : ℝ) ^ b.factorization p :=
    gcdKernel_factor_prod b a b hb ha hb (dvd_mul_left b a)
  have hgProd : (Nat.gcd a b : ℝ) =
      ∏ p ∈ S, (p : ℝ) ^ (Nat.gcd a b).factorization p :=
    gcdKernel_factor_prod (Nat.gcd a b) a b hgpos ha hb hga
  calc
    _ = ((∏ p ∈ S, (p : ℝ) ^ (Nat.gcd a b).factorization p) ^ 2) /
        ((∏ p ∈ S, (p : ℝ) ^ a.factorization p) *
          (∏ p ∈ S, (p : ℝ) ^ b.factorization p)) := by
            rw [← haProd, ← hbProd, ← hgProd]
    _ = ∏ p ∈ S,
        (((p : ℝ) ^ (Nat.gcd a b).factorization p) ^ 2) /
          (((p : ℝ) ^ a.factorization p) *
            ((p : ℝ) ^ b.factorization p)) := by
            rw [Finset.prod_div_distrib, Finset.prod_pow,
              Finset.prod_mul_distrib]
    _ = ∏ p ∈ S,
        (p : ℝ) ^ (-|((a.factorization p : ℝ) - (b.factorization p : ℝ))|) := by
          apply Finset.prod_congr rfl
          intro p hp
          rw [Nat.factorization_gcd (Nat.ne_of_gt ha) (Nat.ne_of_gt hb),
            Finsupp.inf_apply]
          exact gcdKernel_prime_factor p _ _
            (Nat.pos_of_mem_primeFactors hp)

/-- GCD 核的精确有限素数乘积公式，乘积指标来自实际的 `ab`。 -/
theorem gcdKernel_factorization (σ : ℝ) (hσ : 0 < σ)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    gcdKernel σ a b =
      ∏ p ∈ (a * b).primeFactors,
        (p : ℝ) ^ (-σ * |((a.factorization p : ℝ) - (b.factorization p : ℝ))|) := by
  let S := (a * b).primeFactors
  have hprod := gcdKernel_ratio_prod a b ha hb
  have hfactor : ∀ p ∈ S,
      0 ≤ (p : ℝ) ^ (-|((a.factorization p : ℝ) - (b.factorization p : ℝ))|) := by
    intro p hp
    positivity
  calc
    gcdKernel σ a b =
        (∏ p ∈ S,
          (p : ℝ) ^ (-|((a.factorization p : ℝ) - (b.factorization p : ℝ))|)) ^ σ := by
            rw [gcdKernel, hprod]
    _ = ∏ p ∈ S,
        ((p : ℝ) ^ (-|((a.factorization p : ℝ) - (b.factorization p : ℝ))|)) ^ σ := by
          rw [Real.finsetProd_rpow S _ hfactor σ]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [← Real.rpow_mul (by positivity : 0 ≤ (p : ℝ))]
      congr 1
      ring

/-- 对每对正整数，原有 GCD 比值不超过半次核。 -/
theorem gcdRatio_le_kernel_half (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (Nat.gcd a b : ℝ) / (max a b : ℝ) ≤
      gcdKernel ((1 : ℝ) / 2) a b := by
  rw [gcdKernel_half a b ha hb]
  have har : (0 : ℝ) < a := by exact_mod_cast ha
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  have hg : (0 : ℝ) ≤ Nat.gcd a b := by positivity
  have hmax : (0 : ℝ) < (max a b : ℝ) := by positivity
  have hprod : (a : ℝ) * b ≤ (max a b : ℝ) ^ 2 := by
    rcases le_total a b with hab | hba
    · have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
      rw [max_eq_right habR]
      nlinarith
    · have hbaR : (b : ℝ) ≤ a := by exact_mod_cast hba
      rw [max_eq_left hbaR]
      nlinarith
  have hsqrt : Real.sqrt ((a : ℝ) * b) ≤ (max a b : ℝ) := by
    have hs0 : 0 ≤ Real.sqrt ((a : ℝ) * b) := Real.sqrt_nonneg _
    have hs2 : (Real.sqrt ((a : ℝ) * b)) ^ 2 = (a : ℝ) * b :=
      Real.sq_sqrt (mul_nonneg har.le hbr.le)
    nlinarith
  have hspos : 0 < Real.sqrt ((a : ℝ) * b) :=
    Real.sqrt_pos.2 (mul_pos har hbr)
  exact div_le_div_of_nonneg_left hg hspos hsqrt

/-- 现有 `S₂(V)` 不超过半次 GCD 核的有序双重和。 -/
theorem inversePairGcdSum_le_kernel_half (V : Finset ℕ)
    (hV : ∀ v ∈ V, 0 < v) :
    inversePairGcdSum V ≤
      ∑ a ∈ V, ∑ b ∈ V, gcdKernel ((1 : ℝ) / 2) a b := by
  unfold inversePairGcdSum
  apply Finset.sum_le_sum
  intro a ha
  apply Finset.sum_le_sum
  intro b hb
  exact gcdRatio_le_kernel_half a b (hV a ha) (hV b hb)

/-- 平凡但无条件的上界：`S₂(V) ≤ |V|²`，包含空集。 -/
theorem inversePairGcdSum_le_card_sq (V : Finset ℕ)
    (hV : ∀ v ∈ V, 0 < v) :
    inversePairGcdSum V ≤ (V.card : ℝ) ^ 2 := by
  unfold inversePairGcdSum
  calc
    _ ≤ ∑ a ∈ V, ∑ b ∈ V, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      have hga : Nat.gcd a b ≤ max a b :=
        (Nat.gcd_le_left b (hV a ha)).trans (le_max_left a b)
      have hmaxNat : 0 < max a b :=
        (hV a ha).trans_le (le_max_left a b)
      have hden : (0 : ℝ) < (max a b : ℝ) := by exact_mod_cast hmaxNat
      have hgaR : (Nat.gcd a b : ℝ) ≤ (max a b : ℝ) := by
        exact_mod_cast hga
      apply (div_le_iff₀ hden).2
      simpa using hgaR
    _ = (V.card : ℝ) ^ 2 := by simp; ring

end LonelyRunner
