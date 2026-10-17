import LonelyRunner.GcdTripleInverse
import LonelyRunner.GcdSumSubpower

/-!
# 公共因子三重和的弱幂次界

对应论文 `lem:inverse`（第 323–336 行）取 `Y=m³` 的推论。
-/

namespace LonelyRunner

/-- 对应论文 `lem:inverse` 的对数吸收：常数仅依赖 `η`，对所有 `m≥2` 成立。 -/
private theorem inverse_log_cube_bound (η : ℝ) (hη : 0 < η) :
    ∃ L : ℝ, 0 < L ∧ ∀ m : ℕ, 2 ≤ m →
      Real.log (2 * (m : ℝ) ^ 3) ≤ L * (m : ℝ) ^ (η / 2) := by
  let s : ℝ := η / 6
  have hs : 0 < s := by dsimp [s]; linarith
  let L : ℝ := 2 ^ s / s
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨L, hL, ?_⟩
  intro m hm
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hpow : (2 * (m : ℝ) ^ 3) ^ s =
      2 ^ s * (m : ℝ) ^ (η / 2) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity : 0 ≤ (m : ℝ) ^ 3)]
    rw [← Real.rpow_natCast_mul hm0 3 s]
    congr 1
    dsimp [s]
    ring
  calc
    Real.log (2 * (m : ℝ) ^ 3) ≤
        (2 * (m : ℝ) ^ 3) ^ s / s :=
      Real.log_le_rpow_div (by positivity) hs
    _ = L * (m : ℝ) ^ (η / 2) := by rw [hpow]; dsimp [L]; ring

/-- 论文 `lem:inverse` 的 `Y=m³` 推论：`G₃(W)` 由局部倍数密度与弱 GCD 和界控制。
`W` 可以为空；常数不依赖速度高度。 -/
theorem tripleGcdSum_subpower (η : ℝ) (hη : 0 < η) :
    ∃ Cη : ℝ, 0 < Cη ∧
      ∀ (W : Finset ℕ) (_hW : ∀ v ∈ W, 0 < v)
        (m : ℕ) (_hm : 2 ≤ m) (_hcard : W.card ≤ m),
        tripleGcdSum W ≤
          Cη * (inverseK W ((m : ℝ) ^ 3) : ℝ) *
            (m : ℝ) ^ (1 + η) + 1 := by
  obtain ⟨K, hK, hpair⟩ := inversePairGcdSum_subpower (η / 2) (by linarith)
  obtain ⟨L, hL, hlog⟩ := inverse_log_cube_bound η hη
  refine ⟨2 * K * L, by positivity, ?_⟩
  intro W hW m hm hcard
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hm1 : (1 : ℝ) ≤ m := by linarith
  have hcardR : (W.card : ℝ) ≤ m := by exact_mod_cast hcard
  have hY : (2 : ℝ) ≤ (m : ℝ) ^ 3 := by nlinarith [sq_nonneg ((m : ℝ) - 2)]
  have hmain := inverseGcdTripleBound W m ((m : ℝ) ^ 3) hW hcard hY
  have hpairW := hpair W hW
  have hcardPow : (W.card : ℝ) ^ (1 + η / 2) ≤
      (m : ℝ) ^ (1 + η / 2) :=
    Real.rpow_le_rpow (by positivity) hcardR (by linarith)
  have hpairM : inversePairGcdSum W ≤ K * (m : ℝ) ^ (1 + η / 2) :=
    hpairW.trans (mul_le_mul_of_nonneg_left hcardPow hK.le)
  have hlogM := hlog m hm
  have hlogNonneg : 0 ≤ Real.log (2 * (m : ℝ) ^ 3) :=
    Real.log_nonneg (by nlinarith [hY] : (1 : ℝ) ≤ 2 * (m : ℝ) ^ 3)
  have hpairNonneg : 0 ≤ inversePairGcdSum W := by
    unfold inversePairGcdSum
    positivity
  have hKnonneg : (0 : ℝ) ≤ inverseK W ((m : ℝ) ^ 3) := by positivity
  have hpow1 : 0 ≤ (m : ℝ) ^ (1 + η / 2) := by positivity
  have hpow2 : 0 ≤ (m : ℝ) ^ (η / 2) := by positivity
  have hterm :
      2 * (inverseK W ((m : ℝ) ^ 3) : ℝ) * inversePairGcdSum W *
        Real.log (2 * (m : ℝ) ^ 3) ≤
      2 * K * L * (inverseK W ((m : ℝ) ^ 3) : ℝ) *
        (m : ℝ) ^ (1 + η) := by
    have h1 := mul_le_mul_of_nonneg_left hpairM (mul_nonneg (by positivity : (0:ℝ)≤2) hKnonneg)
    have h2 := mul_le_mul_of_nonneg_right h1 hlogNonneg
    have h3 := mul_le_mul_of_nonneg_left hlogM
      (mul_nonneg (mul_nonneg (by positivity : (0:ℝ)≤2) hKnonneg)
        (mul_nonneg hK.le hpow1))
    have hpow : (m : ℝ) ^ (1 + η / 2) * (m : ℝ) ^ (η / 2) =
        (m : ℝ) ^ (1 + η) := by
      rw [← Real.rpow_add hm0]
      congr 1
      ring
    rw [← hpow]
    nlinarith [h2, h3]
  have hcube : (m : ℝ) ^ 3 / (m : ℝ) ^ 3 = 1 := by
    apply div_self
    positivity
  rw [hcube] at hmain
  exact hmain.trans (add_le_add hterm le_rfl)

end LonelyRunner
