import LonelyRunner.SubsetSumDimension
import Mathlib.Data.ZMod.Basic

/-!
# 二解离维数与模素数群中的有界系数张成

对应论文 `paper/lonely_runner_zh.tex` 第 114 行的二解离定义、
第 744 行的有限幂集维数，以及 `prop:bedert` 的建模所需代数基础。
本文件不进行模型压缩。
-/

namespace LonelyRunner
open Finset

section General
variable {A : Type*} [AddCommGroup A]

/-- 一般加法交换群的二解离性：`[-2,2]` 整数系数的零和只能是零关系。 -/
def TwoDissociated (D : Finset A) : Prop :=
  ∀ c : A → ℤ, (∀ x ∈ D, c x ∈ Set.Icc (-2 : ℤ) 2) →
    (∑ x ∈ D, c x • x = 0) → ∀ x ∈ D, c x = 0

/-- 空集二解离，因此维数的候选集合总非空。 -/
theorem twoDissociated_empty : TwoDissociated (∅ : Finset A) := by
  simp [TwoDissociated]

/-- 二解离性对子集遗传；将关系系数在子集之外延拓为零。 -/
theorem TwoDissociated.mono {D E : Finset A} (hE : TwoDissociated E) (hDE : D ⊆ E) :
    TwoDissociated D := by
  classical
  intro c hc hs x hx
  let f : A → ℤ := fun y => if y ∈ D then c y else 0
  have hf : ∀ y ∈ E, f y ∈ Set.Icc (-2 : ℤ) 2 := by
    intro y hy
    by_cases h : y ∈ D
    · simpa [f, h] using hc y h
    · simp [f, h]
  have hsum : ∑ y ∈ E, f y • y = 0 := by
    calc
      _ = ∑ y ∈ D, f y • y := (sum_subset hDE (by intro y hy hn; simp [f, hn])).symm
      _ = 0 := by simpa [f] using hs
  simpa [f, hx] using hE f hf hsum x (hDE hx)

/-- 在有限幂集中取二解离子集基数的最大值；不重新定义整数解离性。 -/
noncomputable def twoDissociatedDimension (B : Finset A) : ℕ := by
  classical
  exact (B.powerset.filter TwoDissociated).sup Finset.card

/-- 每个二解离子集的大小不超过二解离维数。 -/
theorem card_le_twoDissociatedDimension {D B : Finset A}
    (hDB : D ⊆ B) (hD : TwoDissociated D) : D.card ≤ twoDissociatedDimension B := by
  classical
  exact Finset.le_sup (f := Finset.card) (mem_filter.mpr ⟨mem_powerset.mpr hDB, hD⟩)

/-- 最大二解离子集的基数实际取到，包括空母集。 -/
theorem twoDissociatedDimension_attained (B : Finset A) :
    ∃ D ⊆ B, TwoDissociated D ∧ D.card = twoDissociatedDimension B := by
  classical
  have hn : (B.powerset.filter TwoDissociated).Nonempty :=
    ⟨∅, mem_filter.mpr ⟨mem_powerset.mpr (empty_subset B), twoDissociated_empty⟩⟩
  obtain ⟨D, hD, heq⟩ := Finset.exists_mem_eq_sup _ hn Finset.card
  exact ⟨D, mem_powerset.mp (mem_filter.mp hD).1, (mem_filter.mp hD).2, heq.symm⟩

/-- 空集的最大二解离维数为零。 -/
@[simp] theorem twoDissociatedDimension_empty : twoDissociatedDimension (∅ : Finset A) = 0 := by
  classical
  simp [twoDissociatedDimension, twoDissociated_empty]

/-- 母集扩大时最大二解离维数不减。 -/
theorem twoDissociatedDimension_mono {B C : Finset A} (hBC : B ⊆ C) :
    twoDissociatedDimension B ≤ twoDissociatedDimension C := by
  obtain ⟨D, hDB, hD, heq⟩ := twoDissociatedDimension_attained B
  rw [← heq]
  exact card_le_twoDissociatedDimension (hDB.trans hBC) hD

/-- 按包含关系极大：任何介于它与母集之间的二解离集都等于它。 -/
def IsMaximalTwoDissociated (B D : Finset A) : Prop :=
  D ⊆ B ∧ TwoDissociated D ∧
    ∀ E : Finset A, D ⊆ E → E ⊆ B → TwoDissociated E → E = D

/-- 取到最大基数的二解离子集必然按包含关系极大。 -/
theorem maximalTwoDissociated_of_card_eq {B D : Finset A} (hDB : D ⊆ B)
    (hD : TwoDissociated D) (hcard : D.card = twoDissociatedDimension B) :
    IsMaximalTwoDissociated B D := by
  refine ⟨hDB, hD, ?_⟩
  intro E hDE hEB hE
  exact (eq_of_subset_of_card_le hDE (by rw [hcard]; exact card_le_twoDissociatedDimension hEB hE)).symm

/-- 极大二解离子集存在，而且可以选取到最大维数。 -/
theorem maximalTwoDissociated_exists (B : Finset A) :
    ∃ D, IsMaximalTwoDissociated B D ∧ D.card = twoDissociatedDimension B := by
  obtain ⟨D, hDB, hD, heq⟩ := twoDissociatedDimension_attained B
  exact ⟨D, maximalTwoDissociated_of_card_eq hDB hD heq, heq⟩

/-- 元素具有由 `D` 的元素组成的 `[-2,2]` 整数系数表示。 -/
def TwoBoundedSpan (D : Finset A) (b : A) : Prop :=
  ∃ c : A → ℤ, (∀ x ∈ D, c x ∈ Set.Icc (-2 : ℤ) 2) ∧ ∑ x ∈ D, c x • x = b

/-- 有界表示可以向更大的有限支撑延拓为零。 -/
theorem TwoBoundedSpan.mono {D E : Finset A} {b : A} (hb : TwoBoundedSpan D b)
    (hDE : D ⊆ E) : TwoBoundedSpan E b := by
  classical
  obtain ⟨c, hc, hs⟩ := hb
  let f : A → ℤ := fun x => if x ∈ D then c x else 0
  refine ⟨f, ?_, ?_⟩
  · intro x hx
    by_cases h : x ∈ D
    · simpa [f, h] using hc x h
    · simp [f, h]
  · calc
      _ = ∑ x ∈ D, f x • x := (sum_subset hDE (by intro x hx hn; simp [f, hn])).symm
      _ = b := by simpa [f] using hs

/-- 极大性实际给出插入新元素的非平凡关系，新元素的系数非零。 -/
theorem maximalTwoDissociated_relation {B D : Finset A}
    (hD : IsMaximalTwoDissociated B D) {b : A} (hb : b ∈ B) (hbn : b ∉ D) :
    ∃ c : A → ℤ, (∀ x ∈ D, c x ∈ Set.Icc (-2 : ℤ) 2) ∧
      c b ∈ Set.Icc (-2 : ℤ) 2 ∧ c b ≠ 0 ∧
        (∑ x ∈ D, c x • x) + c b • b = 0 := by
  classical
  have hn : ¬ TwoDissociated (insert b D) := by
    intro hi
    have heq := hD.2.2 (insert b D) (subset_insert b D)
      (insert_subset hb hD.1) hi
    exact hbn (heq ▸ mem_insert_self b D)
  unfold TwoDissociated at hn
  push Not at hn
  obtain ⟨c, hc, hs, x, hx, hcx⟩ := hn
  have hcD : ∀ x ∈ D, c x ∈ Set.Icc (-2 : ℤ) 2 :=
    fun x hx => hc x (mem_insert_of_mem hx)
  have hcb : c b ≠ 0 := by
    intro hz
    have hsum : ∑ x ∈ D, c x • x = 0 := by simpa [sum_insert hbn, hz] using hs
    rcases mem_insert.mp hx with rfl | hxD
    · exact hcx hz
    · exact hcx (hD.2.1 c hcD hsum x hxD)
  refine ⟨c, hcD, hc b (mem_insert_self b D), hcb, ?_⟩
  simpa [sum_insert hbn, add_comm] using hs

end General

/-- 群版本在整数上与旧的 `TwoDissociatedInt` 完全等价。 -/
theorem twoDissociated_int_iff (D : Finset ℤ) :
    TwoDissociated D ↔ TwoDissociatedInt D := by
  simp [TwoDissociated, TwoDissociatedInt]

/-- 自然数速度经实际整数嵌入后的群定义与旧速度定义等价。 -/
theorem twoDissociated_speeds_iff (D : Finset ℕ) :
    TwoDissociated (D.image (fun v : ℕ => (v : ℤ))) ↔ TwoDissociatedSpeeds D :=
  twoDissociated_int_iff _

section Field
variable {K : Type*} [Field K] [DecidableEq K]

/-- 除以二把有界系数表示搬到实际像集；利用二可逆证明像映射单射。 -/
theorem twoBoundedSpan_half (D : Finset K) (c : K → ℤ)
    (hc : ∀ x ∈ D, c x ∈ Set.Icc (-2 : ℤ) 2) (h2 : (2 : K) ≠ 0) :
    TwoBoundedSpan (D.image (fun x => x / 2)) ((∑ x ∈ D, c x • x) / 2) := by
  classical
  have hcancel (x : K) : 2 * (x / 2) = x := by field_simp
  refine ⟨fun y => c (2 * y), ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
    simpa only [hcancel] using hc x hx
  · rw [sum_image]
    · simp only [hcancel, zsmul_eq_mul]
      rw [sum_div]
      apply sum_congr rfl
      intro x hx
      ring
    · intro x hx y hy heq
      exact (div_left_inj' h2).mp heq

/-- 只要二可逆，极大二解离集及其二分之一就有界系数张成母集。
这由插入元素产生的非零系数关系证明，不以张成作为假设。 -/
theorem maximalTwoDissociated_span_half {B D₀ : Finset K}
    (hD : IsMaximalTwoDissociated B D₀) (h2 : (2 : K) ≠ 0) :
    ∀ b ∈ B, TwoBoundedSpan (D₀ ∪ D₀.image (fun x => x / 2)) b := by
  classical
  intro b hb
  by_cases hbin : b ∈ D₀
  · apply TwoBoundedSpan.mono (D := D₀) (hDE := subset_union_left)
    refine ⟨fun x => if x = b then 1 else 0, ?_, ?_⟩
    · intro x hx
      by_cases h : x = b <;> simp [h]
    · simp [Finset.sum_ite_eq', hbin]
  · obtain ⟨c, hc, hcb, hcb0, hrel⟩ := maximalTwoDissociated_relation hD hb hbin
    let s := ∑ x ∈ D₀, c x • x
    have hplain : TwoBoundedSpan D₀ s := ⟨c, hc, rfl⟩
    have hcneg : ∀ x ∈ D₀, -c x ∈ Set.Icc (-2 : ℤ) 2 := by
      intro x hx
      obtain ⟨hlo, hhi⟩ := hc x hx
      constructor <;> omega
    have hsneg : (∑ x ∈ D₀, (-c x) • x) = -s := by
      simp [s, sum_neg_distrib]
    have hneg : TwoBoundedSpan D₀ (-s) := ⟨fun x => -c x, hcneg, hsneg⟩
    have hhalf : TwoBoundedSpan (D₀.image (fun x => x / 2)) (s / 2) :=
      twoBoundedSpan_half D₀ c hc h2
    have hneghalf : TwoBoundedSpan (D₀.image (fun x => x / 2)) ((-s) / 2) := by
      simpa only [hsneg] using twoBoundedSpan_half D₀ (fun x => -c x) hcneg h2
    have hrelation : s + (c b : K) * b = 0 := by
      simpa only [s, zsmul_eq_mul] using hrel
    have hcases : c b = -2 ∨ c b = -1 ∨ c b = 1 ∨ c b = 2 := by
      obtain ⟨hlo, hhi⟩ := hcb
      omega
    rcases hcases with heq | heq | heq | heq
    · have hbval : b = s / 2 := by
        apply (eq_div_iff h2).2
        norm_num [heq] at hrelation
        linear_combination -hrelation
      rw [hbval]
      exact hhalf.mono subset_union_right
    · have hbval : b = s := by
        norm_num [heq] at hrelation
        linear_combination -hrelation
      rw [hbval]
      exact hplain.mono subset_union_left
    · have hbval : b = -s := by
        norm_num [heq] at hrelation
        linear_combination hrelation
      rw [hbval]
      exact hneg.mono subset_union_left
    · have hbval : b = (-s) / 2 := by
        apply (eq_div_iff h2).2
        norm_num [heq] at hrelation
        linear_combination hrelation
      rw [hbval]
      exact hneghalf.mono subset_union_right

end Field

/-- 奇素数模群中的建模基础：实际构造 `D=D₀∪(D₀/2)`，
其大小至多两倍，并以 `[-2,2]` 整数系数张成 `B`。空集亦适用。 -/
theorem zmod_maximalTwoDissociated_span (p : ℕ) [Fact p.Prime] (hodd : p ≠ 2)
    (B D₀ : Finset (ZMod p)) (hD : IsMaximalTwoDissociated B D₀) :
    let D := D₀ ∪ D₀.image (fun x => x / 2)
    D.card ≤ 2 * D₀.card ∧ ∀ b ∈ B, TwoBoundedSpan D b := by
  classical
  have hp : p.Prime := Fact.out
  have h2 : (2 : ZMod p) ≠ 0 := by
    change ¬ (2 : ZMod p) = 0
    intro hd
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hd
    have heq := (Nat.dvd_prime Nat.prime_two).mp hd
    rcases heq with heq | heq
    · exact hp.ne_one heq
    · exact hodd heq
  refine ⟨?_, maximalTwoDissociated_span_half hD h2⟩
  exact (card_union_le _ _).trans (by
    have h := card_image_le (s := D₀) (f := fun x : ZMod p => x / 2)
    omega)

/-- 可选到最大维数的极大子集，且其扩充集满足同一张成结论。 -/
theorem zmod_twoDissociatedDimension_spanning (p : ℕ) [Fact p.Prime] (hodd : p ≠ 2)
    (B : Finset (ZMod p)) :
    ∃ D₀ ⊆ B, TwoDissociated D₀ ∧ D₀.card = twoDissociatedDimension B ∧
      (D₀ ∪ D₀.image (fun x => x / 2)).card ≤ 2 * twoDissociatedDimension B ∧
      ∀ b ∈ B, TwoBoundedSpan (D₀ ∪ D₀.image (fun x => x / 2)) b := by
  obtain ⟨D₀, hD, hcard⟩ := maximalTwoDissociated_exists B
  obtain ⟨hbound, hspan⟩ := zmod_maximalTwoDissociated_span p hodd B D₀ hD
  exact ⟨D₀, hD.1, hD.2.1, hcard, by simpa [hcard] using hbound, hspan⟩

#print axioms twoDissociated_int_iff
#print axioms twoDissociated_speeds_iff
#print axioms twoDissociatedDimension_attained
#print axioms twoDissociatedDimension_mono
#print axioms maximalTwoDissociated_of_card_eq
#print axioms zmod_maximalTwoDissociated_span
#print axioms zmod_twoDissociatedDimension_spanning

end LonelyRunner
