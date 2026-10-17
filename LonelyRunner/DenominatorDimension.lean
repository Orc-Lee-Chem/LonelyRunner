import LonelyRunner.SubsetSumDimension

/-! 论文 `paper/lonely_runner_zh.tex` 第 663–667 行，命题 `prop:dimension` 证明中
共同分母与有限子集和计数的衔接。 -/

namespace LonelyRunner

/-- 论文第 663 行：`Q` 整除 `G` 时，`H=G/Q` 是正整数。
此处 `Q=commonDenominator V E G`，包括空指标时的 `Q=1`。 -/
theorem commonDenominator_quotient_pos (V E : Finset ℕ) (G : ℕ)
    (hG : 0 < G) : 0 < G / commonDenominator V E G := by
  obtain ⟨hQpos, hQdvd⟩ := commonDenominator_pos_dvd V E G hG
  exact Nat.div_pos (Nat.le_of_dvd hG hQdvd) hQpos

/-- 论文第 663 行：每个非例外速度都被 `H=G/Q` 整除，且由
`v/G≤R` 得到自然数商 `v/H≤R Q`。整除性从 `q_v∣Q` 推出。 -/
theorem commonDenominator_quotient_divides_and_bound
    (V E : Finset ℕ) (G R : ℕ) (hG : 0 < G)
    (hReal : ∀ v ∈ V \ E, (v : ℝ) / (G : ℝ) ≤ (R : ℝ)) :
    ∀ v ∈ V \ E,
      G / commonDenominator V E G ∣ v ∧
        v / (G / commonDenominator V E G) ≤
          R * commonDenominator V E G := by
  intro v hv
  let Q := commonDenominator V E G
  let H := G / Q
  have hQpos : 0 < Q := (commonDenominator_pos_dvd V E G hG).1
  have hQdvdG : Q ∣ G := (commonDenominator_pos_dvd V E G hG).2
  have hHpos : 0 < H := commonDenominator_quotient_pos V E G hG
  have hqdvdQ : reducedDenominator G v ∣ Q :=
    Finset.dvd_lcm hv
  have hGdivq : G / reducedDenominator G v = Nat.gcd G v := by
    unfold reducedDenominator
    exact Nat.div_div_self (Nat.gcd_dvd_left G v) hG.ne'
  have hHdvdg : H ∣ Nat.gcd G v := by
    have hh := Nat.div_dvd_div_left hQdvdG hqdvdQ
    simpa only [H, hGdivq] using hh
  have hHdvdv : H ∣ v := hHdvdg.trans (Nat.gcd_dvd_right G v)
  have hGfactor : H * Q = G := by
    simpa [H, mul_comm] using Nat.div_mul_cancel hQdvdG
  have hvfactor : H * (v / H) = v := by
    simpa [mul_comm] using Nat.div_mul_cancel hHdvdv
  have hratio : (v : ℝ) ≤ (R : ℝ) * (G : ℝ) :=
    (div_le_iff₀ (Nat.cast_pos.mpr hG)).mp (hReal v hv)
  have hGfactorReal : (G : ℝ) = (H : ℝ) * (Q : ℝ) := by
    exact_mod_cast hGfactor.symm
  have hvfactorReal : (v : ℝ) = (H : ℝ) * ((v / H : ℕ) : ℝ) := by
    exact_mod_cast hvfactor.symm
  have hquotReal : ((v / H : ℕ) : ℝ) ≤ ((R * Q : ℕ) : ℝ) := by
    apply (mul_le_mul_iff_of_pos_left (Nat.cast_pos.mpr hHpos)).mp
    rw [← hvfactorReal, Nat.cast_mul]
    rw [hGfactorReal] at hratio
    nlinarith [hratio]
  exact ⟨hHdvdv, by exact_mod_cast hquotReal⟩

/-- 论文第 663–665 行：由共同分母的整除性接入子集和计数，得到
`|D|≤|E|+log₂(1+|V| R Q)`。这是对每个 2-解离子集的结论。 -/
theorem commonDenominator_subsetSum_log_bound
    (V E D : Finset ℕ) (G R : ℕ)
    (hG : 0 < G) (hR : 0 < R)
    (hDV : D ⊆ V) (hD : TwoDissociatedSpeeds D)
    (hReal : ∀ v ∈ V \ E, (v : ℝ) / (G : ℝ) ≤ (R : ℝ)) :
    (D.card : ℝ) ≤ (E.card : ℝ) +
      Real.logb 2 ((1 + V.card * R * commonDenominator V E G : ℕ) : ℝ) := by
  let Q := commonDenominator V E G
  let H := G / Q
  have hH : 0 < H := commonDenominator_quotient_pos V E G hG
  have hRQ : 0 < R * Q := Nat.mul_pos hR (commonDenominator_pos_dvd V E G hG).1
  have hV : ∀ v ∈ V, v ∉ E → H ∣ v ∧ v / H ≤ R * Q := by
    intro v hvV hvE
    exact commonDenominator_quotient_divides_and_bound V E G R hG hReal v
      (Finset.mem_sdiff.mpr ⟨hvV, hvE⟩)
  have h := subsetSumDimension_log_bound V D E H (R * Q) hH hRQ hDV hD hV
  simpa only [Nat.mul_assoc] using h

/-- 论文第 663–667 行：在 `lem:denominator` 的完整覆盖假设下，
把 `log Q ≤ (8e+9√m)log(2m)` 代入有限子集和界。
这是明确的有限维数估计；核心和例外集的存在性不在本定理内。 -/
theorem denominator_dimension_bound
    (V C E D : Finset ℕ) (m e G R : ℕ) (δ ε : ℝ)
    (hm : m = V.card) (he : e = E.card)
    (hVpos : ∀ v ∈ V, 0 < v)
    (hδ0 : 0 < δ) (hδhalf : δ < 1 / 2)
    (hirr : IrreducibleCover V δ) (hgcd : V.gcd id = 1)
    (hCV : C ⊆ V) (hCcard : (m : ℝ) / 2 ≤ (C.card : ℝ))
    (hGpos : 0 < G) (hGdiv : ∀ v ∈ C, G ∣ v)
    (hEV : E ⊆ V) (hEC : Disjoint E C)
    (hδeq : 2 * (m : ℝ) * δ = 1 + ε)
    (hε0 : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2)
    (hqbound : ∀ v ∈ V \ E, reducedDenominator G v ≤ 2 * m)
    (hRpos : 0 < R)
    (hReal : ∀ v ∈ V \ E, (v : ℝ) / (G : ℝ) ≤ (R : ℝ))
    (hDV : D ⊆ V) (hD : TwoDissociatedSpeeds D) :
    (D.card : ℝ) ≤ (e : ℝ) +
      (Real.log ((1 + m * R : ℕ) : ℝ) +
        (8 * (e : ℝ) + 9 * Real.sqrt (m : ℝ)) *
          Real.log (2 * (m : ℝ))) / Real.log 2 := by
  let Q := commonDenominator V E G
  have hQpos : 0 < Q := (commonDenominator_pos_dvd V E G hGpos).1
  have hQlog := (denominator_divides_and_log_bound V C E m e G δ ε
    hm he hVpos hδ0 hδhalf hirr hgcd hCV hCcard hGpos hGdiv
    hEV hEC hδeq hε0 hεhalf hqbound).2
  have hdim := commonDenominator_subsetSum_log_bound V E D G R
    hGpos hRpos hDV hD hReal
  have hdim' : (D.card : ℝ) ≤ (e : ℝ) +
      Real.logb 2 ((1 + m * R * Q : ℕ) : ℝ) := by
    simpa only [hm, he, Nat.mul_assoc] using hdim
  have hQone : 1 ≤ Q := hQpos
  have hnat : 1 + m * R * Q ≤ (1 + m * R) * Q := by
    nlinarith
  have hUpos : (0 : ℝ) < ((1 + m * R * Q : ℕ) : ℝ) := by positivity
  have hTpos : (0 : ℝ) < ((1 + m * R : ℕ) : ℝ) := by positivity
  have hQrealpos : (0 : ℝ) < (Q : ℝ) := Nat.cast_pos.mpr hQpos
  have hlogU : Real.log ((1 + m * R * Q : ℕ) : ℝ) ≤
      Real.log ((1 + m * R : ℕ) : ℝ) +
        (8 * (e : ℝ) + 9 * Real.sqrt (m : ℝ)) *
          Real.log (2 * (m : ℝ)) := by
    have hcast : ((1 + m * R * Q : ℕ) : ℝ) ≤
        (((1 + m * R) * Q : ℕ) : ℝ) := by exact_mod_cast hnat
    have hlogle := Real.log_le_log hUpos hcast
    have hlogmul : Real.log (((1 + m * R) * Q : ℕ) : ℝ) =
        Real.log ((1 + m * R : ℕ) : ℝ) + Real.log (Q : ℝ) := by
      rw [Nat.cast_mul, Real.log_mul hTpos.ne' hQrealpos.ne']
    rw [hlogmul] at hlogle
    linarith
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogb : Real.logb 2 ((1 + m * R * Q : ℕ) : ℝ) ≤
      (Real.log ((1 + m * R : ℕ) : ℝ) +
        (8 * (e : ℝ) + 9 * Real.sqrt (m : ℝ)) *
          Real.log (2 * (m : ℝ))) / Real.log 2 := by
    unfold Real.logb
    exact (div_le_div_iff_of_pos_right hlog2).2 hlogU
  linarith

#print axioms LonelyRunner.denominator_dimension_bound

end LonelyRunner
