import LonelyRunnerNew.InitialState
import LonelyRunnerNew.NumericEndgame

noncomputable section
open scoped BigOperators

namespace LonelyRunnerNew

theorem W_nonneg (V : Finset ℕ) (hpos : positive V) : 0 ≤ W V := by
  unfold W
  apply div_nonneg _ (sq_nonneg _)
  apply Finset.sum_nonneg
  intro x hx
  apply Finset.sum_nonneg
  intro y hy
  split_ifs
  · exact le_rfl
  · exact le_min (by norm_num) (div_nonneg (by positivity) (height_pos (hpos x hx)).le)

theorem W_le_of_separated {P : ℝ} (hP : 0 < P) (V : Finset ℕ)
    (hn : 0 < V.card) (hsep : separated P V) :
    W V ≤ 2 * (V.card : ℝ) / P := by
  have hnR : (0 : ℝ) < V.card := by exact_mod_cast hn
  unfold W
  apply (div_le_iff₀ (sq_pos_of_pos hnR)).2
  calc
    (∑ x ∈ V, ∑ y ∈ V,
      if x = y then 0 else min 1 (2 * (V.card : ℝ) / height x y)) ≤
        ∑ x ∈ V, ∑ y ∈ V, 2 * (V.card : ℝ) / P := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro y hy
      split_ifs with hxy
      · positivity
      · exact le_trans (min_le_right _ _)
          (div_le_div_of_nonneg_left (by positivity) hP (hsep x hx y hy hxy).le)
    _ = (2 * (V.card : ℝ) / P) * (V.card : ℝ) ^ 2 := by simp; ring

/-- The small-cardinality branch of L14, with its strict conclusion. -/
theorem small_n {P d : ℝ} (hP : 0 < P) (V : Finset ℕ) (hn : 0 < V.card)
    (hsep : separated P V) (hsmall : (V.card : ℝ) < d * P / 2) : W V < d := by
  apply lt_of_le_of_lt (W_le_of_separated hP V hn hsep)
  apply (div_lt_iff₀ hP).2
  linarith

/-- The ambient cardinality is kept fixed when bounding the error term. -/
theorem roughConstant_le_largeNConstant (n : ℕ)
    (hn : (1 / 20 : ℝ) * Real.exp 6880 / 2 ≤ (n : ℝ)) :
    roughConstant 4130 n ≤ Endgame.largeNConstant := by
  have hE : 0 < Real.exp (6880 : ℝ) := Real.exp_pos _
  have hnR : (0 : ℝ) < n := by linarith
  have hratio : 0 < Endgame.entropyRatio := by norm_num [Endgame.entropyRatio]
  have hbase : 2 / ((27 / 50 : ℝ) * (1 / 1000) * (n : ℝ)) ≤
      Endgame.entropyRatio / Real.exp 6880 := by
    apply (div_le_div_iff₀ (by positivity) hE).2
    norm_num [Endgame.entropyRatio]
    linarith
  have hpow := Real.rpow_le_rpow (z := sigma) (by positivity) hbase
    (by norm_num [sigma])
  have heq : (Endgame.entropyRatio / Real.exp 6880) ^ sigma =
      Real.exp (sigma * (Real.log Endgame.entropyRatio - 6880)) := by
    rw [Real.rpow_def_of_pos (div_pos hratio hE),
      Real.log_div hratio.ne' hE.ne', Real.log_exp]
    congr 1
    ring
  rw [heq] at hpow
  unfold roughConstant Endgame.largeNConstant
  simp only [Real.rpow_eq_pow]
  have hcoeff : (0 : ℝ) ≤ 8 / (19 / 100 : ℝ) ^ 2 := by norm_num
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hpow hcoeff)

end LonelyRunnerNew
