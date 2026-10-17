import LonelyRunner.CoverGcdMass
import LonelyRunner.GcdTripleSubpower
import LonelyRunner.GcdTripleInverse
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# 近覆盖的公共倍数块抽取

对应论文 `lem:extract`（`paper/lonely_runner_zh.tex` 第 483–518 行）。
所有块都从当前剩余集合中完整截取，但覆盖条件始终只用于原集合 `V`。
-/

open Filter
open scoped Topology

namespace LonelyRunner

/-- 完整的截距块 `W∩g[Y]`，沿用 `inverseBoundedMultiples` 的正整数倍定义。 -/
noncomputable def extractionBlock (W : Finset ℕ) (g : ℕ) (Y : ℝ) : Finset ℕ := by
  classical
  exact W.filter (fun v => v ∈ inverseBoundedMultiples g Y)

theorem extractionBlock_card (W : Finset ℕ) (g : ℕ) (Y : ℝ) :
    (extractionBlock W g Y).card = inverseMultiplesCount W g Y := by
  rfl

theorem extractionBlock_subset (W : Finset ℕ) (g : ℕ) (Y : ℝ) :
    extractionBlock W g Y ⊆ W := by
  classical
  intro v hv
  exact (Finset.mem_filter.mp hv).1

theorem extractionBlock_mem_multiples (W : Finset ℕ) (g : ℕ) (Y : ℝ)
    {v : ℕ} (hv : v ∈ extractionBlock W g Y) :
    v ∈ inverseBoundedMultiples g Y := by
  classical
  exact (Finset.mem_filter.mp hv).2

/-- 论文 `lem:extract` 第 505–512 行：当 `W` 占原族至少四分之一时，
存在完整块 `W∩g[m³]`，且其大小至少 `cη/(εm^η)`。
`cη` 在 `κ` 前选取，门槛仅依赖 `κ,η`。 -/
theorem extractionBlock_one :
    ∀ η : ℝ, 0 < η → ∃ cη : ℝ, 0 < cη ∧
      ∀ κ : ℝ, η < κ → κ < 1 / 4 →
        ∃ M : ℕ,
          ∀ (V : Finset ℕ) (m : ℕ) (δ : ℝ) (W : Finset ℕ),
            (∀ v ∈ V, 0 < v) → m = V.card → M ≤ m →
              Covers V δ → 0 < δ → δ < 1 / 2 →
                let ε : ℝ := 2 * δ * (m : ℝ) - 1
                0 < ε → ε ≤ (m : ℝ) ^ (-(1 / 2 + κ)) →
                  W ⊆ V → m ≤ 4 * W.card →
                    ∃ g : ℕ, 0 < g ∧
                      cη / (ε * (m : ℝ) ^ η) ≤
                        ((extractionBlock W g ((m : ℝ) ^ 3)).card : ℝ) := by
  obtain ⟨c0, hc0, hmass⟩ := coverGcdMass_lower
  intro η hη
  obtain ⟨Cη, hCη, hGcd⟩ := tripleGcdSum_subpower η hη
  let cη : ℝ := c0 / (2 * Cη)
  have hcη : 0 < cη := by dsimp [cη]; positivity
  refine ⟨cη, hcη, ?_⟩
  intro κ hηκ hκ4
  have hκ : 0 < κ := lt_trans hη hηκ
  obtain ⟨M0, hMassM⟩ := hmass κ hκ hκ4
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / 2 + κ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by linarith : 0 < (1 : ℝ) / 2 + κ)).comp
      tendsto_natCast_atTop_atTop
  obtain ⟨M1, hM1⟩ := eventually_atTop.1
    (ht.eventually (eventually_lt_nhds (by linarith : 0 < c0 / 2)))
  refine ⟨max 2 (max M0 M1), ?_⟩
  intro V m δ W hV hmEq hmM hcover hδ hδhalf ε hε hεbound hWV hWlarge
  have hm2 : 2 ≤ m := (le_max_left 2 (max M0 M1)).trans hmM
  have hmM0 : M0 ≤ m := (le_max_left M0 M1).trans
    ((le_max_right 2 (max M0 M1)).trans hmM)
  have hmM1 : M1 ≤ m := (le_max_right M0 M1).trans
    ((le_max_right 2 (max M0 M1)).trans hmM)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hεsmall : ε ≤ c0 / 2 := hεbound.trans (le_of_lt (hM1 m hmM1))
  have hmassW : c0 * (m : ℝ) / ε ≤ tripleGcdSum W :=
    hMassM V m δ W hV hmEq hmM0 hcover hδ hδhalf hε hεbound hWV hWlarge
  have hWpos : ∀ v ∈ W, 0 < v := fun v hv => hV v (hWV hv)
  have hGcdW := hGcd W hWpos m hm2 (by rw [hmEq]; exact Finset.card_le_card hWV)
  have hOne : 1 ≤ c0 * (m : ℝ) / (2 * ε) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * ε)).2
    have hmul := mul_le_mul_of_nonneg_left hm1 hc0.le
    nlinarith
  have hKterm : c0 * (m : ℝ) / (2 * ε) ≤
      Cη * (inverseK W ((m : ℝ) ^ 3) : ℝ) * (m : ℝ) ^ (1 + η) := by
    have hchain := hmassW.trans hGcdW
    have hdouble : c0 * (m : ℝ) / ε =
        2 * (c0 * (m : ℝ) / (2 * ε)) := by ring
    rw [hdouble] at hchain
    linarith
  obtain ⟨g, hg, hgK⟩ := inverseK_attained W ((m : ℝ) ^ 3)
  refine ⟨g, hg, ?_⟩
  have hpow : (m : ℝ) ^ (1 + η) = (m : ℝ) * (m : ℝ) ^ η := by
    rw [Real.rpow_add hm0]
    simp
  have hmpow0 : 0 < (m : ℝ) ^ η := Real.rpow_pos_of_pos hm0 _
  have hden : 0 < Cη * (m : ℝ) ^ (1 + η) := by positivity
  have hK : c0 * (m : ℝ) / (2 * ε * (Cη * (m : ℝ) ^ (1 + η))) ≤
      (inverseK W ((m : ℝ) ^ 3) : ℝ) := by
    have hK' : (c0 * (m : ℝ) / (2 * ε)) /
        (Cη * (m : ℝ) ^ (1 + η)) ≤
          (inverseK W ((m : ℝ) ^ 3) : ℝ) :=
      (div_le_iff₀ hden).2 (by convert hKterm using 1 <;> ring)
    convert hK' using 1 <;> ring
  have hsimplify : c0 * (m : ℝ) / (2 * ε * (Cη * (m : ℝ) ^ (1 + η))) =
      cη / (ε * (m : ℝ) ^ η) := by
    rw [hpow]
    dsimp [cη]
    field_simp
  rw [← hsimplify, extractionBlock_card, hgK]
  exact hK

/-- 有限块族的并集。 -/
noncomputable def extractionUnion (F : Finset (Finset ℕ)) : Finset ℕ := by
  classical
  exact F.biUnion id

private theorem extractionUnion_insert (F : Finset (Finset ℕ)) (I : Finset ℕ) :
    extractionUnion (insert I F) = I ∪ extractionUnion F := by
  classical
  simp [extractionUnion, Finset.biUnion_insert]

private structure ExtractionPack (W : Finset ℕ) (m : ℕ) (Y K : ℝ) where
  blocks : Finset (Finset ℕ)
  remainder : Finset ℕ
  remainder_subset : remainder ⊆ W
  remainder_small : 4 * remainder.card < m
  block_spec : ∀ I ∈ blocks, I.Nonempty ∧ I ⊆ W ∧ K ≤ (I.card : ℝ) ∧
    ∃ g : ℕ, 0 < g ∧ ∀ v ∈ I, v ∈ inverseBoundedMultiples g Y
  pairwise : ∀ I ∈ blocks, ∀ J ∈ blocks, I ≠ J → Disjoint I J
  remainder_disjoint : Disjoint remainder (extractionUnion blocks)
  union_eq : W = remainder ∪ extractionUnion blocks
  count_bound : (blocks.card : ℝ) * K ≤ (W.card : ℝ)

/-- 基数强归纳：每次从剩余集完整移去一个非空块。
抽取假设仅是辅助组合引理的参数，最终定理会用 `extractionBlock_one` 消去。 -/
private theorem extractionBlocks_induction (V : Finset ℕ) (m : ℕ) (Y K : ℝ)
    (hK : 0 < K)
    (horacle : ∀ W : Finset ℕ, W ⊆ V → m ≤ 4 * W.card →
      ∃ (g : ℕ) (I : Finset ℕ), 0 < g ∧ I = extractionBlock W g Y ∧
        K ≤ (I.card : ℝ)) :
    ∀ W : Finset ℕ, W ⊆ V → Nonempty (ExtractionPack W m Y K) := by
  classical
  intro W
  refine W.strongInductionOn ?_
  intro W ih
  intro hWV
  by_cases hsmall : 4 * W.card < m
  · refine ⟨{ blocks := ∅
              remainder := W
              remainder_subset := by intro v hv; exact hv
              remainder_small := hsmall
              block_spec := ?_
              pairwise := ?_
              remainder_disjoint := ?_
              union_eq := ?_
              count_bound := ?_ }⟩
    · intro I hI
      simp at hI
    · intro I hI
      simp at hI
    · simp [extractionUnion]
    · simp [extractionUnion]
    · simp
  · have hlarge : m ≤ 4 * W.card := by omega
    obtain ⟨g, I, hg, hIeq, hIsize⟩ := horacle W hWV hlarge
    have hIW : I ⊆ W := by
      rw [hIeq]
      exact extractionBlock_subset W g Y
    have hIne : I.Nonempty := by
      have hcardpos : (0 : ℝ) < (I.card : ℝ) := lt_of_lt_of_le hK hIsize
      exact Finset.card_pos.mp (by exact_mod_cast hcardpos)
    let U := W \ I
    have hUsub : U ⊆ V := (Finset.sdiff_subset).trans hWV
    obtain ⟨P⟩ := ih U (Finset.sdiff_ssubset hIW hIne) hUsub
    have hIU : Disjoint I U := by
      apply Finset.disjoint_left.mpr
      intro v hvI hvU
      exact (Finset.mem_sdiff.mp hvU).2 hvI
    have hINot : I ∉ P.blocks := by
      intro hIP
      obtain ⟨v, hvI⟩ := hIne
      have hvU := (P.block_spec I hIP).2.1 hvI
      exact (Finset.disjoint_left.mp hIU hvI) hvU
    have hNewDisj (J : Finset ℕ) (hJ : J ∈ P.blocks) : Disjoint I J := by
      apply Finset.disjoint_left.mpr
      intro v hvI hvJ
      have hvU := (P.block_spec J hJ).2.1 hvJ
      exact (Finset.disjoint_left.mp hIU hvI) hvU
    have hRDisjI : Disjoint P.remainder I := by
      apply Finset.disjoint_left.mpr
      intro v hvR hvI
      have hvU := P.remainder_subset hvR
      exact (Finset.disjoint_left.mp hIU hvI) hvU
    have hWU : W = I ∪ U := by
      ext v
      constructor
      · intro hvW
        by_cases hvI : v ∈ I
        · exact Finset.mem_union.mpr (Or.inl hvI)
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hvW, hvI⟩))
      · intro hv
        rcases Finset.mem_union.mp hv with hvI | hvU
        · exact hIW hvI
        · exact (Finset.mem_sdiff.mp hvU).1
    refine ⟨{ blocks := insert I P.blocks
              remainder := P.remainder
              remainder_subset := P.remainder_subset.trans Finset.sdiff_subset
              remainder_small := P.remainder_small
              block_spec := ?_
              pairwise := ?_
              remainder_disjoint := ?_
              union_eq := ?_
              count_bound := ?_ }⟩
    · intro J hJ
      rcases Finset.mem_insert.mp hJ with rfl | hJold
      · refine ⟨hIne, hIW, hIsize, g, hg, ?_⟩
        intro v hvI
        rw [hIeq] at hvI
        exact extractionBlock_mem_multiples W g Y hvI
      · obtain ⟨hJne, hJsub, hJsize, gJ, hgJ, hgJmem⟩ := P.block_spec J hJold
        exact ⟨hJne, hJsub.trans Finset.sdiff_subset,
          hJsize, gJ, hgJ, hgJmem⟩
    · intro A hA B hB hne
      rcases Finset.mem_insert.mp hA with rfl | hAold
      · rcases Finset.mem_insert.mp hB with rfl | hBold
        · exact False.elim (hne rfl)
        · exact hNewDisj B hBold
      · rcases Finset.mem_insert.mp hB with rfl | hBold
        · exact (hNewDisj A hAold).symm
        · exact P.pairwise A hAold B hBold hne
    · rw [extractionUnion_insert]
      apply Finset.disjoint_left.mpr
      intro v hvR hv
      rcases Finset.mem_union.mp hv with hvI | hvOld
      · exact (Finset.disjoint_left.mp hRDisjI hvR) hvI
      · exact (Finset.disjoint_left.mp P.remainder_disjoint hvR) hvOld
    · rw [extractionUnion_insert]
      calc
        W = I ∪ U := hWU
        _ = I ∪ (P.remainder ∪ extractionUnion P.blocks) :=
          congrArg (I ∪ ·) P.union_eq
        _ = P.remainder ∪ (I ∪ extractionUnion P.blocks) := by
          ext v
          simp only [Finset.mem_union]
          tauto
    · have hCard : ((U.card : ℝ) + (I.card : ℝ)) = (W.card : ℝ) := by
        exact_mod_cast Finset.card_sdiff_add_card_eq_card hIW
      calc
        ((insert I P.blocks).card : ℝ) * K = ((P.blocks.card : ℝ) + 1) * K := by
          rw [Finset.card_insert_of_notMem hINot]
          push_cast
          ring
        _ = (P.blocks.card : ℝ) * K + K := by ring
        _ ≤ (U.card : ℝ) + (I.card : ℝ) := add_le_add P.count_bound hIsize
        _ = (W.card : ℝ) := hCard

/-- 论文 `lem:extract` 第 483–518 行：有限个两两不交的公共倍数块。
`g I` 是每个块的正整数尺度；所有块共用同一个 `cη` 和门槛。
原族 `V` 覆盖，剩余族在归纳中无需覆盖。 -/
theorem blockExtraction :
    ∀ η : ℝ, 0 < η → ∃ cη : ℝ, 0 < cη ∧
      ∀ κ : ℝ, η < κ → κ < 1 / 4 →
        ∃ M : ℕ,
          ∀ (V : Finset ℕ) (m : ℕ) (δ : ℝ),
            (∀ v ∈ V, 0 < v) → m = V.card → M ≤ m →
              Covers V δ → 0 < δ → δ < 1 / 2 →
                let ε : ℝ := 2 * δ * (m : ℝ) - 1
                0 < ε → ε ≤ (m : ℝ) ^ (-(1 / 2 + κ)) →
                  ∃ F : Finset (Finset ℕ), ∃ g : Finset ℕ → ℕ,
                    (∀ I ∈ F, I.Nonempty ∧ I ⊆ V ∧ 0 < g I ∧
                      (∀ v ∈ I, v ∈ inverseBoundedMultiples (g I) ((m : ℝ) ^ 3)) ∧
                        cη / (ε * (m : ℝ) ^ η) ≤ (I.card : ℝ)) ∧
                    (∀ I ∈ F, ∀ J ∈ F, I ≠ J → Disjoint I J) ∧
                    3 * (m : ℝ) / 4 < ((extractionUnion F).card : ℝ) ∧
                    (F.card : ℝ) * (cη / (ε * (m : ℝ) ^ η)) ≤ (m : ℝ) := by
  classical
  intro η hη
  obtain ⟨cη, hcη, hone⟩ := extractionBlock_one η hη
  refine ⟨cη, hcη, ?_⟩
  intro κ hηκ hκ4
  obtain ⟨M, hOneM⟩ := hone κ hηκ hκ4
  refine ⟨max 2 M, ?_⟩
  intro V m δ hV hmEq hmM hcover hδ hδhalf ε hε hεbound
  have hm2 : 2 ≤ m := (le_max_left 2 M).trans hmM
  have hmM0 : M ≤ m := (le_max_right 2 M).trans hmM
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  let K : ℝ := cη / (ε * (m : ℝ) ^ η)
  have hK : 0 < K := by dsimp [K]; positivity
  have hOracle : ∀ W : Finset ℕ, W ⊆ V → m ≤ 4 * W.card →
      ∃ (g : ℕ) (I : Finset ℕ), 0 < g ∧
        I = extractionBlock W g ((m : ℝ) ^ 3) ∧ K ≤ (I.card : ℝ) := by
    intro W hWV hlarge
    obtain ⟨g, hg, hsize⟩ := hOneM V m δ W hV hmEq hmM0
      hcover hδ hδhalf hε hεbound hWV hlarge
    exact ⟨g, extractionBlock W g ((m : ℝ) ^ 3), hg, rfl, hsize⟩
  obtain ⟨P⟩ := extractionBlocks_induction V m ((m : ℝ) ^ 3) K hK hOracle
    V (by simp)
  have hWitness (I : Finset ℕ) :
      ∃ g : ℕ, I ∈ P.blocks →
        0 < g ∧ ∀ v ∈ I, v ∈ inverseBoundedMultiples g ((m : ℝ) ^ 3) := by
    by_cases hI : I ∈ P.blocks
    · obtain ⟨g, hg, hmem⟩ := (P.block_spec I hI).2.2.2
      exact ⟨g, fun _ => ⟨hg, hmem⟩⟩
    · exact ⟨1, fun h => False.elim (hI h)⟩
  let gfun : Finset ℕ → ℕ := fun I => Classical.choose (hWitness I)
  have hgfun (I : Finset ℕ) (hI : I ∈ P.blocks) :
      0 < gfun I ∧ ∀ v ∈ I,
        v ∈ inverseBoundedMultiples (gfun I) ((m : ℝ) ^ 3) :=
    Classical.choose_spec (hWitness I) hI
  refine ⟨P.blocks, gfun, ?_, P.pairwise, ?_, ?_⟩
  · intro I hI
    obtain ⟨hIne, hIV, hIsize, _⟩ := P.block_spec I hI
    obtain ⟨hgI, hIin⟩ := hgfun I hI
    exact ⟨hIne, hIV, hgI, hIin, hIsize⟩
  · have hpart : m = P.remainder.card + (extractionUnion P.blocks).card := by
      calc
        m = V.card := hmEq
        _ = (P.remainder ∪ extractionUnion P.blocks).card :=
          congrArg Finset.card P.union_eq
        _ = P.remainder.card + (extractionUnion P.blocks).card :=
          Finset.card_union_of_disjoint P.remainder_disjoint
    have hcoverNat : 3 * m < 4 * (extractionUnion P.blocks).card := by
      have hrem := P.remainder_small
      omega
    have hcoverReal : (3 : ℝ) * (m : ℝ) <
        4 * ((extractionUnion P.blocks).card : ℝ) := by
      exact_mod_cast hcoverNat
    linarith
  · simpa only [K, ← hmEq] using P.count_bound

end LonelyRunner
