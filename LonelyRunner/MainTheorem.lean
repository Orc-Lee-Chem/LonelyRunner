import LonelyRunner.CoverReduction
import LonelyRunner.NearCoverContradiction

/-!
# 论文主定理

对应 `paper/lonely_runner_zh.tex` 的 `thm:main`。先排除反设尺度的逐点覆盖，
再由同一个未覆盖圆周点得到所有速度的距离下界。全部正参数通过
`min κ (1/8)` 归约到小参数；最终声明不保留结构或覆盖假设。
-/

namespace LonelyRunner

/-- 反设半径与论文目标表达式完全相等；幂和除法均为实数运算。 -/
theorem mainTheorem_radius_identity (n : ℕ) (hn : 0 < n) (κ : ℝ) :
    (1 + (n : ℝ)^(-(1/2+κ))) / (2 * (n : ℝ)) =
      1 / (2 * (n : ℝ)) + 1 / (2 * (n : ℝ)^(3/2+κ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpow : (n : ℝ)^(3/2+κ) = (n : ℝ)^(1/2+κ) * (n : ℝ) := by
    calc
      _ = (n : ℝ)^((1/2+κ)+1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hnR, Real.rpow_one]
  rw [add_div, Real.rpow_neg hnR.le, hpow]
  congr 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- 小参数的非覆盖结论。原起点取至少两倍矛盾定理起点；
约化覆盖的基数至少为原基数的一半，故确实达到同一矛盾门槛。 -/
theorem mainTheorem_noncover :
    ∀ κ : ℝ, 0 < κ → κ < 1/4 → ∃ N : ℕ, 4 ≤ N ∧
      ∀ V : Finset ℕ, (∀ v ∈ V, 0 < v) → N ≤ V.card →
        ¬ Covers V ((1 + (V.card : ℝ)^(-(1/2+κ))) / (2 * (V.card : ℝ))) := by
  intro κ hκ hκ4
  obtain ⟨M, hcontra⟩ := nearCoverContradiction κ hκ hκ4
  refine ⟨max 4 (2*M), le_max_left _ _, ?_⟩
  intro V hV hN hcover
  have hn4 : 4 ≤ V.card := (le_max_left _ _).trans hN
  have hnM : 2 * M ≤ V.card := (le_max_right _ _).trans hN
  let δ₀ := (1 + (V.card : ℝ)^(-(1/2+κ))) / (2 * (V.card : ℝ))
  obtain ⟨U, hU, hirr, hgcd, hm2, hmn, hhalf, hεpos, hεn, hεm⟩ :=
    coverReduction_nearCover V V.card κ hV rfl hn4 hκ hκ4 hcover
  have hUM : M ≤ U.card := by
    have hh : (2 : ℝ) * (M : ℝ) ≤ (V.card : ℝ) := by exact_mod_cast hnM
    have hh' : (M : ℝ) ≤ (U.card : ℝ) := by linarith
    exact_mod_cast hh'
  obtain ⟨hδ, hδhalf, _⟩ := coverReduction_radius_bounds V.card κ hn4 hκ
  exact hcontra U δ₀ hU hUM hirr hgcd hδ hδhalf hεpos (hεn.trans hεm)

/-- 小参数主结论：非覆盖给出一个对所有速度同时成立的严格距离下界，
再放宽为论文要求的非严格下界。保留闭弧端点，不替换为几乎处处条件。 -/
theorem mainTheorem_small_parameter :
    ∀ κ : ℝ, 0 < κ → κ < 1/4 → ∃ N : ℕ, 2 ≤ N ∧
      ∀ V : Finset ℕ, (∀ v ∈ V, 0 < v) → N ≤ V.card →
        ∃ t : UnitAddCircle, ∀ v ∈ V,
          1 / (2 * (V.card : ℝ)) + 1 / (2 * (V.card : ℝ)^(3/2+κ)) ≤
            dist (v • t) 0 := by
  intro κ hκ hκ4
  obtain ⟨N, hN4, hnoncover⟩ := mainTheorem_noncover κ hκ hκ4
  refine ⟨N, by omega, ?_⟩
  intro V hV hN
  have hn4 : 4 ≤ V.card := hN4.trans hN
  obtain ⟨hδ, hδhalf, _⟩ := coverReduction_radius_bounds V.card κ hn4 hκ
  have hnc := hnoncover V hV hN
  unfold Covers at hnc
  push Not at hnc
  obtain ⟨t, ht⟩ := hnc
  refine ⟨t, ?_⟩
  intro v hv
  have hstrict : (1 + (V.card : ℝ)^(-(1/2+κ))) / (2 * (V.card : ℝ)) <
      dist (v • t) 0 := by
    apply lt_of_not_ge
    intro hdist
    exact ht v hv ((mem_bohrSet_iff_dist v _ hδ.le hδhalf t).mpr hdist)
  rw [mainTheorem_radius_identity V.card (by omega) κ] at hstrict
  exact hstrict.le

/-- 论文原始主定理 `thm:main`：对每个正参数，足够大的任意有限正整数速度族，
存在同一个圆周时刻使所有距离满足所述下界。起点先于速度族选取，
不保留不可约性、gcd、覆盖、维数、模型或外部数学估计参数。 -/
theorem mainTheorem :
    ∀ κ : ℝ, 0 < κ → ∃ N : ℕ, 2 ≤ N ∧
      ∀ V : Finset ℕ, (∀ v ∈ V, 0 < v) → N ≤ V.card →
        ∃ t : UnitAddCircle, ∀ v ∈ V,
          1 / (2 * (V.card : ℝ)) + 1 / (2 * (V.card : ℝ)^(3/2+κ)) ≤
            dist (v • t) 0 := by
  intro κ hκ
  let κ' := min κ (1/8)
  have hκ' : 0 < κ' := lt_min hκ (by norm_num)
  have hκ'4 : κ' < 1/4 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hκ'κ : κ' ≤ κ := min_le_left _ _
  obtain ⟨N, hN2, hsmall⟩ := mainTheorem_small_parameter κ' hκ' hκ'4
  refine ⟨N, hN2, ?_⟩
  intro V hV hN
  obtain ⟨t, ht⟩ := hsmall V hV hN
  have hn2 : 2 ≤ V.card := hN2.trans hN
  have hnR : (1 : ℝ) ≤ V.card := by exact_mod_cast (show 1 ≤ V.card by omega)
  have hpowers : (V.card : ℝ)^(3/2+κ') ≤ (V.card : ℝ)^(3/2+κ) :=
    Real.rpow_le_rpow_of_exponent_le hnR (by linarith)
  have hfrac : 1 / (2 * (V.card : ℝ)^(3/2+κ)) ≤
      1 / (2 * (V.card : ℝ)^(3/2+κ')) := by
    apply one_div_le_one_div_of_le
    · positivity
    · nlinarith
  refine ⟨t, ?_⟩
  intro v hv
  have hvt := ht v hv
  linarith

#print mainTheorem
#print axioms mainTheorem_radius_identity
#print axioms mainTheorem_noncover
#print axioms mainTheorem_small_parameter
#print axioms mainTheorem

end LonelyRunner
