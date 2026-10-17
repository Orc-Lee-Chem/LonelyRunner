import LonelyRunner.BlockMerge
import LonelyRunner.CoreExceptions
import LonelyRunner.DenominatorDimension

/-!
# 论文 `prop:dimension`：不可约近覆盖的统一 2-解离子集界

对应 `paper/lonely_runner_zh.tex` 第 656–672 行。取 `η=κ/10`，实际取得
合并核心、两类例外及共同分母，再接入子集和维数估计。
-/

namespace LonelyRunner

/-- 论文 `prop:dimension` 最后一步所需的粗幂次估计：`mε≤√m`、
`mεm^η≤√m`，以及适用例外定理的 `ε≤1/2`。 -/
theorem nearCover_sqrt_estimates (m : ℕ) (κ η ε : ℝ)
    (hm : 4 ≤ m) (hκ : 0 < κ) (hηκ : η ≤ κ)
    (hε : ε ≤ (m : ℝ) ^ (-(1 / 2 + κ))) :
    (m : ℝ) * ε ≤ Real.sqrt (m : ℝ) ∧
      (m : ℝ) * ε * (m : ℝ) ^ η ≤ Real.sqrt (m : ℝ) ∧ ε ≤ 1 / 2 := by
  have hm4 : (4 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hm1 : (1 : ℝ) ≤ m := by linarith
  have hpow : (m : ℝ) * (m : ℝ) ^ (-(1 / 2 + κ)) =
      (m : ℝ) ^ (1 / 2 - κ) := by
    nth_rewrite 1 [← Real.rpow_one (m : ℝ)]
    rw [← Real.rpow_add hm0]
    congr 1
    ring
  have hfirst : (m : ℝ) * ε ≤ Real.sqrt (m : ℝ) := by
    calc
      _ ≤ (m : ℝ) * (m : ℝ) ^ (-(1 / 2 + κ)) :=
        mul_le_mul_of_nonneg_left hε hm0.le
      _ = (m : ℝ) ^ (1 / 2 - κ) := hpow
      _ ≤ (m : ℝ) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hm1 (by linarith)
      _ = Real.sqrt (m : ℝ) := (Real.sqrt_eq_rpow _).symm
  have hsecond : (m : ℝ) * ε * (m : ℝ) ^ η ≤ Real.sqrt (m : ℝ) := by
    calc
      _ ≤ ((m : ℝ) * (m : ℝ) ^ (-(1 / 2 + κ))) * (m : ℝ) ^ η := by
        gcongr
      _ = (m : ℝ) ^ (1 / 2 - κ + η) := by rw [hpow, ← Real.rpow_add hm0]
      _ ≤ (m : ℝ) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hm1 (by linarith)
      _ = Real.sqrt (m : ℝ) := (Real.sqrt_eq_rpow _).symm
  have hsqrt2 : (2 : ℝ) ≤ Real.sqrt (m : ℝ) := by
    exact (Real.le_sqrt (by norm_num) hm0.le).2 (by nlinarith)
  have hsqrt : Real.sqrt (m : ℝ) ^ 2 = m := Real.sq_sqrt hm0.le
  have hhalf : Real.sqrt (m : ℝ) ≤ (m : ℝ) / 2 := by nlinarith
  refine ⟨hfirst, hsecond, ?_⟩
  nlinarith [hfirst.trans hhalf]

/-- 论文 `eq:subsetcount`：高度 `R=(mT)^4` 给出对数界，所有对数参数为正。 -/
theorem nearCover_height_log (m T : ℕ) (hm : 1 ≤ m) (hT : 1 ≤ T) :
    Real.log ((1 + m * (m * T)^4 : ℕ) : ℝ) ≤
      Real.log 2 + 5 * Real.log (m : ℝ) + 4 * Real.log (T : ℝ) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hTR : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hm0 : (0 : ℝ) < m := by linarith
  have hT0 : (0 : ℝ) < T := by linarith
  have hprod : (1 : ℝ) ≤ (m : ℝ) * ((m : ℝ) * T)^4 := by
    have hmt : (1 : ℝ) ≤ (m : ℝ) * T := by nlinarith
    have hp : (1 : ℝ) ≤ ((m : ℝ) * T)^4 := one_le_pow₀ hmt
    nlinarith
  have hcompare : ((1 + m * (m * T)^4 : ℕ) : ℝ) ≤
      2 * (m : ℝ)^5 * (T : ℝ)^4 := by
    push_cast
    nlinarith only [hprod]
  have hlog := Real.log_le_log (by positivity :
    (0 : ℝ) < ((1 + m * (m * T)^4 : ℕ) : ℝ)) hcompare
  have heq : Real.log (2 * (m : ℝ)^5 * (T : ℝ)^4) =
      Real.log 2 + 5 * Real.log (m : ℝ) + 4 * Real.log (T : ℝ) := by
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow]
    norm_num
  rwa [heq] at hlog

/-- 论文 `prop:dimension` 的最后整理：由 `e≤16√m` 及核心高度界，
将共同分母维数估计吸收到单个 `√m log(2m)` 项。 -/
theorem nearCover_dimension_estimate (m T : ℕ) (e B : ℝ)
    (hm : 4 ≤ m) (hT : 1 ≤ T) (hB : 0 < B)
    (he : e ≤ 16 * Real.sqrt (m : ℝ))
    (hlogT : Real.log (T : ℝ) ≤
      B * (Real.sqrt (m : ℝ) + 1) * Real.log (2 * (m : ℝ))) :
    e + (Real.log ((1 + m * (m * T)^4 : ℕ) : ℝ) +
      (8 * e + 9 * Real.sqrt (m : ℝ)) * Real.log (2 * (m : ℝ))) /
        Real.log 2 ≤
      ((159 + 8 * B) / Real.log 2) * Real.sqrt (m : ℝ) *
        Real.log (2 * (m : ℝ)) := by
  let s := Real.sqrt (m : ℝ)
  let L := Real.log (2 * (m : ℝ))
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hs : 1 ≤ s := by simpa [s] using Real.one_le_sqrt.mpr hmR
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h2L : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by nlinarith)
  have hL : 0 ≤ L := le_trans hlog2.le h2L
  have hmL : Real.log (m : ℝ) ≤ L :=
    Real.log_le_log (by linarith) (by nlinarith)
  have hTlog : Real.log (T : ℝ) ≤ 2 * B * s * L := by
    have hbound : B * (s + 1) * L ≤ 2 * B * s * L := by
      nlinarith [mul_nonneg hB.le hL, mul_le_mul_of_nonneg_right hs
        (mul_nonneg hB.le hL)]
    exact hlogT.trans hbound
  have hsmallLog : Real.log ((1 + m * (m * T)^4 : ℕ) : ℝ) ≤
      (6 + 8 * B) * s * L := by
    have h := nearCover_height_log m T (by omega) hT
    have hLs : L ≤ s * L := by nlinarith [mul_le_mul_of_nonneg_right hs hL]
    calc
      _ ≤ Real.log 2 + 5 * Real.log (m : ℝ) + 4 * Real.log (T : ℝ) := h
      _ ≤ L + 5 * L + 4 * (2 * B * s * L) := by linarith
      _ ≤ (6 + 8 * B) * s * L := by nlinarith
  have heLog : e * Real.log 2 ≤ 16 * s * L := by
    calc
      e * Real.log 2 ≤ (16 * s) * Real.log 2 := mul_le_mul_of_nonneg_right he hlog2.le
      _ ≤ 16 * s * L := mul_le_mul_of_nonneg_left h2L (by dsimp [s]; positivity)
  have heTerm : (8 * e + 9 * s) * L ≤ 137 * s * L := by
    exact mul_le_mul_of_nonneg_right (by nlinarith [he]) hL
  calc
    _ = (e * Real.log 2 + Real.log ((1 + m * (m * T)^4 : ℕ) : ℝ) +
        (8 * e + 9 * s) * L) / Real.log 2 := by dsimp [s, L]; field_simp; ring
    _ ≤ ((159 + 8 * B) * s * L) / Real.log 2 := by
      apply (div_le_div_iff_of_pos_right hlog2).2
      nlinarith [heLog, hsmallLog, heTerm]
    _ = _ := by dsimp [s, L]; ring

/-- 论文 `prop:dimension` / `eq:dimension`：对固定 `0<κ<1/4`，存在只依赖
`κ` 的正数 `Aκ` 和自然数起点 `Mκ`。不可约、最大公因数为一的近覆盖中，
每个 2-解离子集都满足 `|D|≤Aκ√m log(2m)`。

核心、例外集与共同分母均由已证定理取得，不作为外加假设。
本项目未另定义最大 2-解离维数，故直接给出所有子集的统一结论。 -/
theorem nearCover_dimension_bound :
    ∀ κ : ℝ, 0 < κ → κ < 1 / 4 →
      ∃ Aκ : ℝ, 0 < Aκ ∧ ∃ Mκ : ℕ,
        ∀ (V : Finset ℕ) (δ : ℝ),
          (∀ v ∈ V, 0 < v) → Mκ ≤ V.card →
          IrreducibleCover V δ → V.gcd id = 1 →
          0 < δ → δ < 1 / 2 →
          let ε := 2 * δ * (V.card : ℝ) - 1
          0 < ε → ε ≤ (V.card : ℝ) ^ (-(1 / 2 + κ)) →
          ∀ D : Finset ℕ, D ⊆ V → TwoDissociatedSpeeds D →
            (D.card : ℝ) ≤ Aκ * Real.sqrt (V.card : ℝ) *
              Real.log (2 * (V.card : ℝ)) := by
  intro κ hκ hκ4
  let η := κ / 10
  have hη : 0 < η := by dsimp [η]; positivity
  have hηκ : η < κ / 4 := by dsimp [η]; linarith
  have hηκ' : η ≤ κ := by dsimp [η]; linarith
  obtain ⟨B, hB, hmerge⟩ := blockMerge η hη
  obtain ⟨M₁, hmergeM⟩ := hmerge κ hηκ hκ4
  obtain ⟨M₂, hM₂, hexceptions⟩ := coreExceptions_bound
  let Aκ : ℝ := (159 + 8 * B) / Real.log 2
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hAκ : 0 < Aκ := by dsimp [Aκ]; positivity
  refine ⟨Aκ, hAκ, max 4 (max M₁ M₂), ?_⟩
  intro V δ hV hM hirr hgcd hδ hδhalf ε hε hεbound
  let m := V.card
  have hm4 : 4 ≤ m := (le_max_left _ _).trans hM
  have hmM₁ : M₁ ≤ m := (le_max_left _ _).trans ((le_max_right _ _).trans hM)
  have hmM₂ : M₂ ≤ m := (le_max_right _ _).trans ((le_max_right _ _).trans hM)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  obtain ⟨hεsqrt, hεηsqrt, hεhalf⟩ :=
    nearCover_sqrt_estimates m κ η ε hm4 hκ hηκ' hεbound
  obtain ⟨C, G, T, hCV, hG, hT, hGgcd, hCmajor, hcore, hlogT⟩ :=
    hmergeM V m δ hV rfl hmM₁ hirr.1 hδ hδhalf hε hεbound
  let E := coreExceptions V G m T δ
  obtain ⟨hEsub, heBound, hgood⟩ := hexceptions V C G m T δ hmM₂
    hV rfl hCV hCmajor hG hT hcore hirr.1 hδ hδhalf hε.le hεhalf
  change E ⊆ V \ C at hEsub
  change (E.card : ℝ) ≤ 16 * (m : ℝ) * ε at heBound
  have heSqrt : (E.card : ℝ) ≤ 16 * Real.sqrt (m : ℝ) := by
    nlinarith [heBound, hεsqrt]
  have hlogT' : Real.log (T : ℝ) ≤
      B * (Real.sqrt (m : ℝ) + 1) * Real.log (2 * (m : ℝ)) := by
    have hL : 0 ≤ Real.log (2 * (m : ℝ)) := Real.log_nonneg (by
      have hmR : (4 : ℝ) ≤ m := by exact_mod_cast hm4
      linarith)
    have hadd : (m : ℝ) * ε * (m : ℝ) ^ η + 1 ≤ Real.sqrt (m : ℝ) + 1 := by
      linarith [hεηsqrt]
    exact hlogT.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hadd hB.le) hL)
  have hEV : E ⊆ V := fun v hv => (Finset.mem_sdiff.mp (hEsub hv)).1
  have hEC : Disjoint E C := Finset.disjoint_left.mpr (fun v hvE hvC =>
    (Finset.mem_sdiff.mp (hEsub hvE)).2 hvC)
  have hCcard : (m : ℝ) / 2 ≤ (C.card : ℝ) := by
    have h : (m : ℝ) ≤ 2 * (C.card : ℝ) := by exact_mod_cast hCmajor
    linarith
  have hGdiv : ∀ c ∈ C, G ∣ c := by
    intro c hc
    obtain ⟨k, hk, hkT, heq⟩ := hcore c hc
    exact ⟨k, heq⟩
  have hqbound : ∀ v ∈ V \ E, reducedDenominator G v ≤ 2 * m := by
    intro v hv
    have h := (hgood v hv).1.trans (hgood v hv).2.1
    exact_mod_cast h
  have hReal : ∀ v ∈ V \ E,
      (v : ℝ) / (G : ℝ) ≤ (((m * T)^4 : ℕ) : ℝ) :=
    fun v hv => (hgood v hv).2.2.1
  have hR : 0 < (m * T)^4 := by
    have hmnat : 0 < m := by omega
    have hTnat : 0 < T := by omega
    positivity
  have hδeq : 2 * (m : ℝ) * δ = 1 + ε := by dsimp [ε, m]; ring
  intro D hDV hD
  have hdim := denominator_dimension_bound V C E D m E.card G ((m * T)^4) δ ε
    rfl rfl hV hδ hδhalf hirr hgcd hCV hCcard hG hGdiv hEV hEC hδeq
    hε.le hεhalf hqbound hR hReal hDV hD
  exact hdim.trans (nearCover_dimension_estimate m T E.card B hm4 hT hB heSqrt hlogT')

#print axioms nearCover_dimension_bound

end LonelyRunner
