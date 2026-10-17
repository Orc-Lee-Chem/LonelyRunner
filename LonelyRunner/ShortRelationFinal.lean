import LonelyRunner.GcdSumSubpower
import LonelyRunner.ShortRelationCount
import LonelyRunner.ShortRelationSum

/-!
# 论文 `lem:relations` 所需的无条件短关系界

本项目用有限 Poisson 矩方法证明论文所需的 GCD 弱幂次界；
没有形式化 Bondarenko–Seip 的精细指数界。
-/

open scoped Real

namespace LonelyRunner

/-- 论文 `lem:relations`：无条件短关系计数 `N_V(H) ≪_η m^(2+η)H²`。 -/
theorem shortRelationCount_final (η : ℝ) (hη : 0 < η) :
    ∃ Cη : ℝ, 0 < Cη ∧
      ∀ (V : Finset ℕ) (hV : ∀ v ∈ V, 0 < v)
        (H : ℕ) (hm : 1 ≤ V.card) (hH : 1 ≤ H) (hHm : H ≤ V.card),
        ((shortTriples V H).card : ℝ) ≤
          Cη * (V.card : ℝ) ^ (2 + η) * (H : ℝ) ^ 2 := by
  have hθ : 0 < η / 8 := by positivity
  obtain ⟨C, hC, hcount⟩ := shortRelationCount_bound (η / 8) hθ
  have hε : 0 < η / 2 := by positivity
  obtain ⟨K, hK, hgcd⟩ := inversePairGcdSum_subpower (η / 2) hε
  let A : ℝ := K ^ ((2 : ℝ) / 3)
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨C * (A + 2), by positivity, ?_⟩
  intro V hV H hm hH hHm
  let m : ℝ := V.card
  have hmR : 1 ≤ m := by
    change (1 : ℝ) ≤ (V.card : ℝ)
    exact_mod_cast hm
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hmR
  have hHR : (0 : ℝ) ≤ H := by positivity
  have hHmR : (H : ℝ) ≤ m := by
    change (H : ℝ) ≤ (V.card : ℝ)
    exact_mod_cast hHm
  have hS : 0 ≤ inversePairGcdSum V := by
    unfold inversePairGcdSum
    positivity
  have hSpow : (inversePairGcdSum V) ^ ((2 : ℝ) / 3) ≤
      A * m ^ ((1 + η / 2) * ((2 : ℝ) / 3)) := by
    calc
      _ ≤ (K * m ^ (1 + η / 2)) ^ ((2 : ℝ) / 3) :=
        Real.rpow_le_rpow hS (by simpa [m] using hgcd V hV) (by norm_num)
      _ = A * m ^ ((1 + η / 2) * ((2 : ℝ) / 3)) := by
        rw [Real.mul_rpow hK.le (by positivity), ← Real.rpow_mul hm0.le]
  have hExp :
      m ^ ((4 : ℝ) / 3 + 8 * (η / 8) / 3) *
        m ^ ((1 + η / 2) * ((2 : ℝ) / 3)) =
          m ^ (2 + 2 * η / 3) := by
    rw [← Real.rpow_add hm0]
    congr 1
    ring
  have hpow : m ^ (2 + 2 * η / 3) ≤ m ^ (2 + η) :=
    Real.rpow_le_rpow_of_exponent_le hmR (by linarith)
  have hpow2 : m ^ 2 ≤ m ^ (2 + η) := by
    calc
      m ^ 2 = m ^ (2 : ℝ) := (Real.rpow_natCast m 2).symm
      _ ≤ m ^ (2 + η) :=
        Real.rpow_le_rpow_of_exponent_le hmR (by linarith)
  have hterm : m ^ ((4 : ℝ) / 3 + 8 * (η / 8) / 3) *
        (inversePairGcdSum V) ^ ((2 : ℝ) / 3) * (H : ℝ) ^ 2 ≤
      A * m ^ (2 + η) * (H : ℝ) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hSpow
      (by positivity : 0 ≤ m ^ ((4 : ℝ) / 3 + 8 * (η / 8) / 3))
    have h1 : m ^ ((4 : ℝ) / 3 + 8 * (η / 8) / 3) *
        (inversePairGcdSum V) ^ ((2 : ℝ) / 3) ≤
        A * m ^ (2 + 2 * η / 3) := by
      calc
        _ ≤ m ^ ((4 : ℝ) / 3 + 8 * (η / 8) / 3) *
          (A * m ^ ((1 + η / 2) * ((2 : ℝ) / 3))) := hh
        _ = A * m ^ (2 + 2 * η / 3) := by rw [← hExp]; ring
    have h2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg (H : ℝ))
    have h3 := mul_le_mul_of_nonneg_left hpow hA.le
    have h4 := mul_le_mul_of_nonneg_right h3 (sq_nonneg (H : ℝ))
    nlinarith [h2, h4]
  have hterm2 : m ^ 2 * (H : ℝ) ^ 2 ≤
      m ^ (2 + η) * (H : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_right hpow2 (sq_nonneg (H : ℝ))
  have hterm3 : m * (H : ℝ) ^ 3 ≤
      m ^ (2 + η) * (H : ℝ) ^ 2 := by
    have habsorb : m * (H : ℝ) ^ 3 ≤ m ^ 2 * (H : ℝ) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hHmR)
        (mul_nonneg hm0.le (sq_nonneg (H : ℝ)))]
    exact habsorb.trans hterm2
  have hraw := hcount V hV H hm hH hHm
  change ((shortTriples V H).card : ℝ) ≤
    C * (m ^ ((4 : ℝ) / 3 + 8 * (η / 8) / 3) *
      (inversePairGcdSum V) ^ ((2 : ℝ) / 3) * (H : ℝ) ^ 2 +
      m ^ 2 * (H : ℝ) ^ 2 + m * (H : ℝ) ^ 3) at hraw
  change ((shortTriples V H).card : ℝ) ≤
    C * (A + 2) * m ^ (2 + η) * (H : ℝ) ^ 2
  have hsum := add_le_add (add_le_add hterm hterm2) hterm3
  have hmul := mul_le_mul_of_nonneg_left hsum hC.le
  nlinarith [hraw, hmul]

/-- `ShortRelationSum` 的倒数和与三阶矩模块已有的 `L(V)` 是同一个有限和。 -/
theorem shortRelationInverseSum_eq_tripleRelationLambdaSum (V : Finset ℕ) :
    shortRelationInverseSum V = tripleRelationLambdaSum V := by
  rfl

/-- 论文 `lem:relations`：不带外部 GCD 假设的短关系倒数和界，含空速度集。 -/
theorem shortRelationInverseSum_final (η : ℝ) (hη : 0 < η) :
    ∃ Cη : ℝ, 0 < Cη ∧ ∀ (V : Finset ℕ),
      (∀ v ∈ V, 0 < v) →
        shortRelationInverseSum V ≤
          Cη * (V.card : ℝ) ^ ((5 : ℝ) / 2 + η) := by
  obtain ⟨Cη, hCη, hmain⟩ :=
    shortRelationInverseSum_bound_of_gcd inversePairGcdSum_subpower η hη
  refine ⟨Cη, hCη, ?_⟩
  intro V hV
  by_cases hEmpty : V = ∅
  · subst V
    simp [shortRelationInverseSum, increasingTriples]
    positivity
  · have hnonempty : V.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
    exact hmain V hV (Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero.mpr hnonempty))

/-- 三阶矩模块 `L(V)` 的同一无条件上界，直接复用已有定义。 -/
theorem tripleRelationLambdaSum_final (η : ℝ) (hη : 0 < η) :
    ∃ Cη : ℝ, 0 < Cη ∧ ∀ (V : Finset ℕ),
      (∀ v ∈ V, 0 < v) →
        tripleRelationLambdaSum V ≤
          Cη * (V.card : ℝ) ^ ((5 : ℝ) / 2 + η) := by
  obtain ⟨Cη, hCη, hmain⟩ := shortRelationInverseSum_final η hη
  refine ⟨Cη, hCη, ?_⟩
  intro V hV
  rw [← shortRelationInverseSum_eq_tripleRelationLambdaSum]
  exact hmain V hV

end LonelyRunner
