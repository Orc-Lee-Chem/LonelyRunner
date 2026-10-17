import LonelyRunner.TwoDissociatedDimension
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# 模素数群的同时压缩

对应论文 `prop:bedert` 建模输入所需的同时逼近步骤。
以标准代表的实际分箱映射应用抽屉原理，再沿 `TwoBoundedSpan` 延拓。
本文件不声称压缩后的代表互异或非零。
-/

namespace LonelyRunner
open Finset

/-- 第一个坐标编码：自然数除法是非负实商的向下取整。 -/
def modularCompressionBin (p L : ℕ) (a x : ZMod p) : ℕ :=
  L * (a * x).val / p

/-- 分箱确实等于题述的 `floor(L (ax).val / p)`，不是抽象的逼近假设。 -/
theorem modularCompressionBin_eq_floor (p L : ℕ) (a x : ZMod p) :
    modularCompressionBin p L a x =
      ⌊(L : ℝ) * ((a * x).val : ℝ) / (p : ℝ)⌋₊ := by
  rw [← Nat.cast_mul, Nat.floor_div_eq_div]
  rfl

/-- 每个分箱坐标属于 `0,…,L-1`。 -/
theorem modularCompressionBin_lt (p L : ℕ) (hp : 0 < p) (hL : 0 < L)
    (a x : ZMod p) : modularCompressionBin p L a x < L := by
  have : NeZero p := ⟨hp.ne'⟩
  apply (Nat.div_lt_iff_lt_mul hp).2
  have hv := (a * x).val_lt
  nlinarith

/-- 两个标准代表落在同一分箱时，其实数差的绝对值严格小于 `p/L`。 -/
theorem modularCompressionBin_same (p L : ℕ) (hp : 0 < p) (hL : 0 < L)
    (a b x : ZMod p)
    (heq : modularCompressionBin p L a x = modularCompressionBin p L b x) :
    |((a * x).val : ℝ) - ((b * x).val : ℝ)| < (p : ℝ) / (L : ℝ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  let u := (L : ℝ) * ((a * x).val : ℝ) / (p : ℝ)
  let v := (L : ℝ) * ((b * x).val : ℝ) / (p : ℝ)
  have huv : ⌊u⌋₊ = ⌊v⌋₊ := by
    simpa only [modularCompressionBin_eq_floor] using heq
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have huLo : (⌊u⌋₊ : ℝ) * p ≤ (L : ℝ) * (a * x).val :=
    (le_div_iff₀ hpR).mp (Nat.floor_le hu0)
  have hvLo : (⌊v⌋₊ : ℝ) * p ≤ (L : ℝ) * (b * x).val :=
    (le_div_iff₀ hpR).mp (Nat.floor_le hv0)
  have huHi : (L : ℝ) * (a * x).val < ((⌊u⌋₊ : ℝ) + 1) * p :=
    (div_lt_iff₀ hpR).mp (Nat.lt_floor_add_one u)
  have hvHi : (L : ℝ) * (b * x).val < ((⌊v⌋₊ : ℝ) + 1) * p :=
    (div_lt_iff₀ hpR).mp (Nat.lt_floor_add_one v)
  rw [huv] at huLo huHi
  apply abs_lt.mpr
  constructor
  · apply (mul_lt_mul_iff_right₀ hLR).mp
    rw [mul_neg, mul_div_cancel₀ _ hLR.ne']
    nlinarith
  · apply (mul_lt_mul_iff_right₀ hLR).mp
    rw [mul_div_cancel₀ _ hLR.ne']
    nlinarith

/-- 实际的分箱映射：每个 `a` 给出 `|D|` 个 `Fin L` 坐标。 -/
def modularCompressionBoxes (p L : ℕ) (hp : 0 < p) (hL : 0 < L)
    (D : Finset (ZMod p)) (a : ZMod p) : D → Fin L :=
  fun x => ⟨modularCompressionBin p L a x, modularCompressionBin_lt p L hp hL a x⟩

/-- 同时压缩：箱数恰为 `L^|D|`。不同的 `a,b` 产生非零 `λ=a-b`，
并以标准代表之差为每个坐标构造整数代表。包含 `D=∅`。 -/
theorem modularSimultaneousCompression (p : ℕ) (hp : p.Prime)
    (D : Finset (ZMod p)) (L : ℕ) (hL : 0 < L) (hsize : L ^ D.card < p) :
    ∃ lam : ZMod p, lam ≠ 0 ∧ ∃ z : ZMod p → ℤ, ∀ x ∈ D,
      (z x : ZMod p) = lam * x ∧ |(z x : ℝ)| < (p : ℝ) / (L : ℝ) := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  have hcard : Fintype.card (D → Fin L) < Fintype.card (ZMod p) := by
    simpa using hsize
  obtain ⟨a, b, hab, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (modularCompressionBoxes p L hp.pos hL D) hcard
  refine ⟨a - b, sub_ne_zero.mpr hab,
    fun x => ((a * x).val : ℤ) - ((b * x).val : ℤ), ?_⟩
  intro x hx
  have hbin : modularCompressionBin p L a x = modularCompressionBin p L b x :=
    congrArg Fin.val (congrFun heq ⟨x, hx⟩)
  constructor
  · simp only [Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val, sub_mul]
  · simpa only [Int.cast_sub, Int.cast_natCast] using
      modularCompressionBin_same p L hp.pos hL a b x hbin

/-- 有界系数张成元素的代表由实际整数线性组合构造；
三角不等式及每项系数绝对值至多二给出 `2|D|p/L`。 -/
theorem TwoBoundedSpan.compressedRepresentative {p L : ℕ} (D : Finset (ZMod p))
    (lam : ZMod p) (z : ZMod p → ℤ) (hL : 0 < L)
    (hz : ∀ x ∈ D, (z x : ZMod p) = lam * x ∧
      |(z x : ℝ)| ≤ (p : ℝ) / (L : ℝ))
    {v : ZMod p} (hv : TwoBoundedSpan D v) :
    ∃ w : ℤ, (w : ZMod p) = lam * v ∧
      |(w : ℝ)| ≤ 2 * (D.card : ℝ) * (p : ℝ) / (L : ℝ) := by
  obtain ⟨c, hc, hs⟩ := hv
  refine ⟨∑ x ∈ D, c x * z x, ?_, ?_⟩
  · push_cast
    calc
      _ = ∑ x ∈ D, (c x : ZMod p) * (lam * x) := by
        apply sum_congr rfl
        intro x hx
        rw [(hz x hx).1]
      _ = lam * (∑ x ∈ D, c x • x) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro x hx
        simp only [zsmul_eq_mul]
        ring
      _ = lam * v := by rw [hs]
  · have hpL : (0 : ℝ) ≤ (p : ℝ) / (L : ℝ) := by positivity
    calc
      _ = |∑ x ∈ D, (c x : ℝ) * (z x : ℝ)| := by push_cast; rfl
      _ ≤ ∑ x ∈ D, |(c x : ℝ) * (z x : ℝ)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _x ∈ D, 2 * ((p : ℝ) / (L : ℝ)) := by
        apply sum_le_sum
        intro x hx
        have hcx : |(c x : ℝ)| ≤ 2 := by
          apply abs_le.mpr
          constructor
          · exact_mod_cast (hc x hx).1
          · exact_mod_cast (hc x hx).2
        rw [abs_mul]
        exact mul_le_mul hcx (hz x hx).2 (abs_nonneg _) (by norm_num)
      _ = _ := by simp; ring

/-- 同一个非零缩放同时压缩生成集及其有界系数张成的全部母集元素。
不假设代表互异或非零；空生成集和空母集亦适用。 -/
theorem modularSimultaneousCompression_of_twoBoundedSpan (p : ℕ) (hp : p.Prime)
    (D B : Finset (ZMod p)) (L : ℕ) (hL : 0 < L) (hsize : L ^ D.card < p)
    (hspan : ∀ v ∈ B, TwoBoundedSpan D v) :
    ∃ lam : ZMod p, lam ≠ 0 ∧
      (∀ x ∈ D, ∃ z : ℤ, (z : ZMod p) = lam * x ∧
        |(z : ℝ)| < (p : ℝ) / (L : ℝ)) ∧
      (∀ v ∈ B, ∃ z : ℤ, (z : ZMod p) = lam * v ∧
        |(z : ℝ)| ≤ 2 * (D.card : ℝ) * (p : ℝ) / (L : ℝ)) := by
  obtain ⟨lam, hlam, z, hz⟩ := modularSimultaneousCompression p hp D L hL hsize
  refine ⟨lam, hlam, (fun x hx => ⟨z x, hz x hx⟩), ?_⟩
  intro v hv
  exact (hspan v hv).compressedRepresentative D lam z hL
    (fun x hx => ⟨(hz x hx).1, (hz x hx).2.le⟩)

#print axioms modularCompressionBin_eq_floor
#print axioms modularCompressionBin_same
#print axioms modularSimultaneousCompression
#print axioms TwoBoundedSpan.compressedRepresentative
#print axioms modularSimultaneousCompression_of_twoBoundedSpan

end LonelyRunner
