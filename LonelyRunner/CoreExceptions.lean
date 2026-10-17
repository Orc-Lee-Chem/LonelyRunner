import LonelyRunner.HeightExceptions

/-!
# 论文 `lem:exceptions`（第 580–615 行）：多数核心以外的两类例外

沿用 `denominatorExceptions` 和 `heightExceptions`，不重复定义 Bohr 集或测度。
自然数高度 `T` 对应 `blockMerge` 的实际输出。
-/

namespace LonelyRunner

/-- 论文第 615 行：两类例外的并；不假定它们互不相交。 -/
noncomputable def coreExceptions (V : Finset ℕ) (G m T : ℕ) (δ : ℝ) : Finset ℕ :=
  denominatorExceptions V G δ ∪ heightExceptions V G m T

/-- 论文 `lem:exceptions` 的完整例外结论：起点为绝对常数，例外数至多 `16mε`。
非例外速度同时满足既约分母界和实数高度界；另外给出自然数乘法界及除法界。
所有平滑误差、频率分离和交集下界均已在上游实际证明。 -/
theorem coreExceptions_bound :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ (V C : Finset ℕ) (G m T : ℕ) (δ : ℝ),
      M ≤ m → (∀ v ∈ V, 0 < v) → m = V.card →
      C ⊆ V → m ≤ 2 * C.card → 0 < G → 1 ≤ T →
      (∀ c ∈ C, c ∈ inverseBoundedMultiples G (T : ℝ)) →
      Covers V δ → 0 < δ → δ < 1 / 2 →
      0 ≤ 2 * δ * (m : ℝ) - 1 → 2 * δ * (m : ℝ) - 1 ≤ 1 / 2 →
      let E := coreExceptions V G m T δ
      E ⊆ V \ C ∧
        (E.card : ℝ) ≤ 16 * (m : ℝ) * (2 * δ * (m : ℝ) - 1) ∧
        (∀ v ∈ V \ E,
          (reducedDenominator G v : ℝ) ≤ 1 / δ ∧
          1 / δ ≤ 2 * (m : ℝ) ∧
          (v : ℝ) / (G : ℝ) ≤ (((m * T)^4 : ℕ) : ℝ) ∧
          v ≤ (m * T)^4 * G ∧ v / G ≤ (m * T)^4) := by
  obtain ⟨M, hM2, hheight⟩ := heightExceptions_bound
  refine ⟨M, hM2, ?_⟩
  intro V C G m T δ hM hV hm hC hmajor hG hT hcore hcover hδ hδhalf hε0 hεhalf
  classical
  have hm2 : 2 ≤ m := hM2.trans hM
  have hCdvd : ∀ c ∈ C, G ∣ c := by
    intro c hc
    obtain ⟨k, hk, hkT, heq⟩ := hcore c hc
    exact ⟨k, heq⟩
  obtain ⟨hqsub, hqcard, hdenom⟩ := denominatorExceptions_bound V C G m δ
    hV hm hm2 hC hmajor hG hCdvd hcover hδ hδhalf hε0 hεhalf
  obtain ⟨hhsub, hhcard, hoverlap, hmass⟩ := hheight V C G m T δ hM
    hV hm hC hmajor hG hT hcore hcover hδ hδhalf hε0 hεhalf
  change (denominatorExceptions V G δ ∪ heightExceptions V G m T) ⊆ V \ C ∧ _
  refine ⟨Finset.union_subset hqsub hhsub, ?_, ?_⟩
  · have hcard : ((denominatorExceptions V G δ ∪ heightExceptions V G m T).card : ℝ) ≤
        ((denominatorExceptions V G δ).card : ℝ) +
          ((heightExceptions V G m T).card : ℝ) := by
      exact_mod_cast Finset.card_union_le (denominatorExceptions V G δ)
        (heightExceptions V G m T)
    change ((denominatorExceptions V G δ ∪ heightExceptions V G m T).card : ℝ) ≤ _
    linarith
  · intro v hv
    have hvV : v ∈ V := (Finset.mem_sdiff.mp hv).1
    have hvnot : v ∉ denominatorExceptions V G δ ∪ heightExceptions V G m T :=
      (Finset.mem_sdiff.mp hv).2
    have hvq : v ∈ V \ denominatorExceptions V G δ :=
      Finset.mem_sdiff.mpr ⟨hvV, fun h => hvnot (Finset.mem_union_left _ h)⟩
    obtain ⟨hq, hδbound⟩ := hdenom v hvq
    have hvheight : v ≤ (m * T)^4 * G := by
      by_contra hbad
      have hvh : v ∈ heightExceptions V G m T :=
        Finset.mem_filter.mpr ⟨hvV, by omega⟩
      exact hvnot (Finset.mem_union_right _ hvh)
    have hGR : (0 : ℝ) < G := by exact_mod_cast hG
    have hvreal : (v : ℝ) / (G : ℝ) ≤ (((m * T)^4 : ℕ) : ℝ) := by
      apply (div_le_iff₀ hGR).2
      exact_mod_cast hvheight
    have hvnat : v / G ≤ (m * T)^4 :=
      Nat.div_le_of_le_mul (by simpa [Nat.mul_comm] using hvheight)
    exact ⟨hq, hδbound, hvreal, hvheight, hvnat⟩

#print axioms coreExceptions_bound

end LonelyRunner
