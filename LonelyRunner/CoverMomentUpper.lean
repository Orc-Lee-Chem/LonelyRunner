import LonelyRunner.CoverMomentTriple
import LonelyRunner.ShortRelationFinal

/-!
# 三阶覆盖矩的统一上界

对应论文 `lem:moments` 证明第 468–479 行。这里的子族无需覆盖圆周。
公共因子项的系数选为与 `η` 无关的绝对常数。
-/

open MeasureTheory
open scoped Real

namespace LonelyRunner

private theorem coverMoment_delta_bounds (m : ℕ) (hm : 3 ≤ m)
    (δ : ℝ) (hδ : δ ≤ 3 / (4 * (m : ℝ))) :
    δ ≤ 1 / 4 ∧ δ ≤ 1 / (m : ℝ) := by
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hden : (0 : ℝ) < 4 * (m : ℝ) := by positivity
  constructor
  · calc
      δ ≤ 3 / (4 * (m : ℝ)) := hδ
      _ ≤ 1 / 4 := by
        apply (div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 4)).2
        nlinarith
  · calc
      δ ≤ 3 / (4 * (m : ℝ)) := hδ
      _ ≤ 1 / (m : ℝ) := by
        apply (div_le_div_iff₀ hden hm0).2
        nlinarith

private theorem tripleRelationLambdaSum_nonneg (W : Finset ℕ) :
    0 ≤ tripleRelationLambdaSum W := by
  unfold tripleRelationLambdaSum
  positivity

private theorem tripleGcdSum_nonneg (W : Finset ℕ) :
    0 ≤ tripleGcdSum W := by
  unfold tripleGcdSum
  positivity

/-- 论文 `lem:moments` 第 468–479 行：三阶矩上界，绝对常数在 `η` 外选取。 -/
theorem coverThirdMoment_upper :
    ∃ Cstar : ℝ, 0 < Cstar ∧
      ∀ η : ℝ, 0 < η → ∃ Cη : ℝ, 0 < Cη ∧
        ∀ (W : Finset ℕ) (_hW : ∀ v ∈ W, 0 < v)
          (m : ℕ) (_hm : 3 ≤ m) (_hcard : W.card ≤ m)
          (δ : ℝ) (_hδ : 0 < δ) (_hδm : δ ≤ 3 / (4 * (m : ℝ))),
          coverThirdMoment W δ ≤
            Cη * (m : ℝ) ^ ((1 : ℝ) / 2 + η) +
              Cstar * tripleGcdSum W / (m : ℝ) := by
  let Cstar : ℝ := 72 * Real.pi ^ 6
  have hCstar : 0 < Cstar := by dsimp [Cstar]; positivity
  refine ⟨Cstar, hCstar, ?_⟩
  intro η hη
  obtain ⟨K, hK, hL⟩ := tripleRelationLambdaSum_final η hη
  refine ⟨Cstar * (1 + K), by positivity, ?_⟩
  intro W hW m hm hcard δ hδ hδm
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hmOne : (1 : ℝ) ≤ m := by linarith
  have hwR : (W.card : ℝ) ≤ m := by exact_mod_cast hcard
  have hδ4 := (coverMoment_delta_bounds m hm δ hδm).1
  have hδinv := (coverMoment_delta_bounds m hm δ hδm).2
  have hmδ : (m : ℝ) * δ ≤ 1 := by
    have h := (le_div_iff₀ hm0).mp hδinv
    nlinarith
  have hwδ : (W.card : ℝ) * δ ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hwR hδ.le
    linarith
  have hfirst : (W.card : ℝ) ^ 3 * δ ^ 3 ≤ 1 := by
    have hp := pow_le_pow_left₀
      (mul_nonneg (by positivity : (0 : ℝ) ≤ W.card) hδ.le) hwδ 3
    simpa only [mul_pow, one_pow] using hp
  have hLnonneg := tripleRelationLambdaSum_nonneg W
  have hGnonneg := tripleGcdSum_nonneg W
  have hLraw := hL W hW
  have hWpow : (W.card : ℝ) ^ ((5 : ℝ) / 2 + η) ≤
      (m : ℝ) ^ ((5 : ℝ) / 2 + η) :=
    Real.rpow_le_rpow (by positivity) hwR (by linarith)
  have hLbound : tripleRelationLambdaSum W ≤
      K * (m : ℝ) ^ ((5 : ℝ) / 2 + η) :=
    hLraw.trans (mul_le_mul_of_nonneg_left hWpow hK.le)
  have hmpow : (m : ℝ) ^ ((5 : ℝ) / 2 + η) =
      (m : ℝ) ^ 2 * (m : ℝ) ^ ((1 : ℝ) / 2 + η) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hm0]
    congr 1
    ring
  have hsq : ((m : ℝ) * δ) ^ 2 ≤ 1 := by
    simpa using (pow_le_pow_left₀ (mul_nonneg hm0.le hδ.le) hmδ 2)
  have hmδsq : δ ^ 2 * (m : ℝ) ^ 2 ≤ 1 := by
    nlinarith [hsq]
  have hsecond : δ ^ 2 * tripleRelationLambdaSum W ≤
      K * (m : ℝ) ^ ((1 : ℝ) / 2 + η) := by
    calc
      _ ≤ δ ^ 2 * (K * (m : ℝ) ^ ((5 : ℝ) / 2 + η)) :=
        mul_le_mul_of_nonneg_left hLbound (sq_nonneg δ)
      _ = (δ ^ 2 * (m : ℝ) ^ 2) *
          (K * (m : ℝ) ^ ((1 : ℝ) / 2 + η)) := by rw [hmpow]; ring
      _ ≤ 1 * (K * (m : ℝ) ^ ((1 : ℝ) / 2 + η)) :=
        mul_le_mul_of_nonneg_right hmδsq (by positivity)
      _ = _ := one_mul _
  have hthird : δ * tripleGcdSum W ≤ tripleGcdSum W / (m : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hδinv hGnonneg
    simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using h
  have hmain := coverThirdMoment_le_card_cube W δ hW hδ hδ4
  have hmexp : 1 ≤ (m : ℝ) ^ ((1 : ℝ) / 2 + η) := by
    calc
      1 = (m : ℝ) ^ (0 : ℝ) := (Real.rpow_zero _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hmOne (by linarith)
  change coverThirdMoment W δ ≤
    Cstar * (1 + K) * (m : ℝ) ^ ((1 : ℝ) / 2 + η) +
      Cstar * tripleGcdSum W / (m : ℝ)
  change coverThirdMoment W δ ≤
    Cstar * ((W.card : ℝ) ^ 3 * δ ^ 3 +
      δ ^ 2 * tripleRelationLambdaSum W + δ * tripleGcdSum W) at hmain
  calc
    coverThirdMoment W δ ≤ Cstar *
        ((W.card : ℝ) ^ 3 * δ ^ 3 +
          δ ^ 2 * tripleRelationLambdaSum W + δ * tripleGcdSum W) := hmain
    _ ≤ Cstar * (1 + K * (m : ℝ) ^ ((1 : ℝ) / 2 + η) +
        tripleGcdSum W / (m : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ hCstar.le
          linarith
    _ ≤ Cstar * ((m : ℝ) ^ ((1 : ℝ) / 2 + η) +
        K * (m : ℝ) ^ ((1 : ℝ) / 2 + η) +
        tripleGcdSum W / (m : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ hCstar.le
          linarith
    _ = Cstar * (1 + K) * (m : ℝ) ^ ((1 : ℝ) / 2 + η) +
        Cstar * tripleGcdSum W / (m : ℝ) := by ring

end LonelyRunner
