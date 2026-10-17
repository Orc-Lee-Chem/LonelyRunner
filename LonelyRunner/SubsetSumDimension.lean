import LonelyRunner.PrimePowerAllocation
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Finset.Powerset

/-! 论文 `paper/lonely_runner_zh.tex` 第 114、663–667 行：
`prop:dimension` 证明中的有限子集和计数部分。 -/

namespace LonelyRunner

/-- 论文第 114 行：有限整数集的 2-解离性。整数系数限制为
`{-2,-1,0,1,2}`，和为零时所有系数必须为零。 -/
def TwoDissociatedInt (D : Finset ℤ) : Prop :=
  ∀ c : ℤ → ℤ,
    (∀ d ∈ D, c d ∈ Set.Icc (-2 : ℤ) 2) →
    (∑ d ∈ D, c d * d = 0) →
    ∀ d ∈ D, c d = 0

/-- 论文第 663 行：自然数速度集按整数嵌入后的 2-解离性。 -/
def TwoDissociatedSpeeds (D : Finset ℕ) : Prop :=
  TwoDissociatedInt (D.image (fun (v : ℕ) => (v : ℤ)))

/-- 论文第 663–665 行：整数定义在正整数速度上的关系形式。 -/
theorem TwoDissociatedSpeeds.relation (D : Finset ℕ)
    (hD : TwoDissociatedSpeeds D) (c : ℕ → ℤ)
    (hc : ∀ v ∈ D, c v ∈ Set.Icc (-2 : ℤ) 2)
    (hsum : ∑ v ∈ D, c v * (v : ℤ) = 0) :
    ∀ v ∈ D, c v = 0 := by
  classical
  let cZ : ℤ → ℤ := fun z => c z.toNat
  have hcZ : ∀ z ∈ D.image (fun (v : ℕ) => (v : ℤ)), cZ z ∈ Set.Icc (-2 : ℤ) 2 := by
    intro z hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    simpa [cZ] using hc v hv
  have hsumZ : ∑ z ∈ D.image (fun (v : ℕ) => (v : ℤ)), cZ z * z = 0 := by
    rw [Finset.sum_image]
    simpa [cZ] using hsum
    intro a ha b hb hab
    exact Nat.cast_injective hab
  have hzero := hD cZ hcZ hsumZ
  intro v hv
  have hvZ : (v : ℤ) ∈ D.image (fun (v : ℕ) => (v : ℤ)) :=
    Finset.mem_image.mpr ⟨v, hv, rfl⟩
  simpa [cZ] using hzero (v : ℤ) hvZ

/-- 论文 `prop:dimension` 证明第 663–665 行：整除后的子集和映射。
对 `A ⊆ D \ E`，其值为 `∑ v∈A, v/H`。 -/
def normalizedSubsetSum (H : ℕ) (A : Finset ℕ) : ℕ := ∑ v ∈ A, v / H

/-- 论文 `prop:dimension` 证明第 663–665 行：2-解离性使归一化子集和单射。
这里从子集和相等构造系数在 `{-1,0,1}` 的整数关系，再使用 2-解离性。 -/
theorem normalizedSubsetSum_injOn (V D E : Finset ℕ) (H : ℕ)
    (hDV : D ⊆ V) (hD : TwoDissociatedSpeeds D)
    (hdiv : ∀ v ∈ V, v ∉ E → H ∣ v) :
    Set.InjOn (normalizedSubsetSum H) (D \ E).powerset := by
  classical
  intro A hA B hB heq
  have hAD : A ⊆ D := (Finset.mem_powerset.mp hA).trans (Finset.sdiff_subset)
  have hBD : B ⊆ D := (Finset.mem_powerset.mp hB).trans (Finset.sdiff_subset)
  have hAs : A ⊆ D \ E := Finset.mem_powerset.mp hA
  have hBs : B ⊆ D \ E := Finset.mem_powerset.mp hB
  have hsumA : (∑ v ∈ A, v) = H * normalizedSubsetSum H A := by
    rw [normalizedSubsetSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    have hvS := hAs hv
    have hvdiv := hdiv v (hDV (Finset.sdiff_subset hvS)) (Finset.mem_sdiff.mp hvS).2
    simpa [mul_comm] using (Nat.div_mul_cancel hvdiv).symm
  have hsumB : (∑ v ∈ B, v) = H * normalizedSubsetSum H B := by
    rw [normalizedSubsetSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    have hvS := hBs hv
    have hvdiv := hdiv v (hDV (Finset.sdiff_subset hvS)) (Finset.mem_sdiff.mp hvS).2
    simpa [mul_comm] using (Nat.div_mul_cancel hvdiv).symm
  have hsumNat : (∑ v ∈ A, v) = ∑ v ∈ B, v := by
    rw [hsumA, hsumB, heq]
  have hsumInt : (∑ v ∈ A, (v : ℤ)) = ∑ v ∈ B, (v : ℤ) := by
    simpa only [Nat.cast_sum] using congrArg (fun n : ℕ => (n : ℤ)) hsumNat
  let c : ℕ → ℤ := fun v => (if v ∈ A then 1 else 0) - (if v ∈ B then 1 else 0)
  have hc : ∀ v ∈ D, c v ∈ Set.Icc (-2 : ℤ) 2 := by
    intro v hv
    simp only [c, Set.mem_Icc]
    split_ifs <;> omega
  have hAindicator : (∑ v ∈ D, (if v ∈ A then (v : ℤ) else 0)) =
      ∑ v ∈ A, (v : ℤ) := by
    rw [← Finset.sum_filter]
    congr 1
    ext v
    simp [hAD]
  have hBindicator : (∑ v ∈ D, (if v ∈ B then (v : ℤ) else 0)) =
      ∑ v ∈ B, (v : ℤ) := by
    rw [← Finset.sum_filter]
    congr 1
    ext v
    simp [hBD]
  have hrel : (∑ v ∈ D, c v * (v : ℤ)) = 0 := by
    simp only [c, sub_mul, Finset.sum_sub_distrib]
    simp only [ite_mul, one_mul, zero_mul, hAindicator, hBindicator]
    omega
  have hzero := TwoDissociatedSpeeds.relation D hD c hc hrel
  ext v
  constructor
  · intro hvA
    have hvD := hAD hvA
    have hz := hzero v hvD
    by_cases hvB : v ∈ B
    · exact hvB
    · simp [c, hvA, hvB] at hz
  · intro hvB
    have hvD := hBD hvB
    have hz := hzero v hvD
    by_cases hvA : v ∈ A
    · exact hvA
    · simp [c, hvA, hvB] at hz

/-- 论文 `prop:dimension` 证明第 665–666 行：不同子集和均在
`0, …, |V| B` 中，因此 `2^|D\\E| ≤ 1+|V| B`。 -/
theorem subsetSumDimension_count (V D E : Finset ℕ) (H B : ℕ)
    (_hH : 0 < H) (_hB : 0 < B) (hDV : D ⊆ V)
    (hD : TwoDissociatedSpeeds D)
    (hV : ∀ v ∈ V, v ∉ E → H ∣ v ∧ v / H ≤ B) :
    2 ^ (D \ E).card ≤ 1 + V.card * B := by
  classical
  have hinj : Set.InjOn (normalizedSubsetSum H) (D \ E).powerset :=
    normalizedSubsetSum_injOn V D E H hDV hD (fun v hv hne => (hV v hv hne).1)
  have hsumBound : ∀ A ∈ (D \ E).powerset,
      normalizedSubsetSum H A ≤ V.card * B := by
    intro A hA
    have hAV : A ⊆ V :=
      (Finset.mem_powerset.mp hA).trans (Finset.sdiff_subset.trans hDV)
    calc
      normalizedSubsetSum H A = ∑ v ∈ A, v / H := rfl
      _ ≤ ∑ _v ∈ A, B := Finset.sum_le_sum (by
        intro v hv
        have hvS := Finset.mem_powerset.mp hA hv
        exact (hV v (hAV hv) (Finset.mem_sdiff.mp hvS).2).2)
      _ = A.card * B := by simp
      _ ≤ V.card * B := Nat.mul_le_mul_right B (Finset.card_le_card hAV)
  have hsubset : (D \ E).powerset.image (normalizedSubsetSum H) ⊆
      Finset.range (1 + V.card * B) := by
    intro n hn
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hn
    apply Finset.mem_range.mpr
    simpa [Nat.succ_eq_add_one, Nat.add_comm] using Nat.lt_succ_of_le (hsumBound A hA)
  have hcard := Finset.card_le_card hsubset
  rw [Finset.card_image_of_injOn hinj, Finset.card_powerset,
    Finset.card_range] at hcard
  exact hcard

/-- 论文 `prop:dimension` 证明第 666–667 行：对计数界取以 2 为底的对数，
并用 `D ⊆ (D\\E) ∪ E` 得到 `|D| ≤ |E| + log₂(1+|V| B)`。
本定理只覆盖该命题的有限子集和计数步骤。 -/
theorem subsetSumDimension_log_bound (V D E : Finset ℕ) (H B : ℕ)
    (hH : 0 < H) (hB : 0 < B) (hDV : D ⊆ V)
    (hD : TwoDissociatedSpeeds D)
    (hV : ∀ v ∈ V, v ∉ E → H ∣ v ∧ v / H ≤ B) :
    (D.card : ℝ) ≤ (E.card : ℝ) +
      Real.logb 2 ((1 + V.card * B : ℕ) : ℝ) := by
  have hcount := subsetSumDimension_count V D E H B hH hB hDV hD hV
  have hlog : ((D \ E).card : ℝ) ≤
      Real.logb 2 ((1 + V.card * B : ℕ) : ℝ) := by
    apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2)
      (by positivity : (0 : ℝ) < ((1 + V.card * B : ℕ) : ℝ))).2
    have hcountReal : (2 : ℝ) ^ (D \ E).card ≤
        ((1 + V.card * B : ℕ) : ℝ) := by
      exact_mod_cast hcount
    simpa only [Real.rpow_natCast] using hcountReal
  have hpart : D ⊆ (D \ E) ∪ E := by
    intro v hv
    by_cases hE : v ∈ E
    · exact Finset.mem_union_right _ hE
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hv, hE⟩)
  have hcardNat : D.card ≤ (D \ E).card + E.card := by
    exact (Finset.card_le_card hpart).trans (Finset.card_union_le _ _)
  have hcardReal : (D.card : ℝ) ≤ ((D \ E).card : ℝ) + (E.card : ℝ) := by
    exact_mod_cast hcardNat
  linarith

#print axioms LonelyRunner.subsetSumDimension_count
#print axioms LonelyRunner.subsetSumDimension_log_bound

end LonelyRunner
