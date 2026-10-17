import LonelyRunner.SelbergIntervalWeights
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# 自然数区间中的素数上界

精确计数区间为 `(x,x+y]`，有限筛误差不依赖区间起点。
随后取 `z=floor(y^(1/8))`，得到统一的 `C y/log y` 上界。
-/

namespace LonelyRunner
open Finset

/-- 题述区间内的真实有限素数集合。 -/
def primeIntervalPrimes (x y : ℕ) : Finset ℕ :=
  (Ioc x (x + y)).filter Nat.Prime

/-- `π(x,y)`，区间左端严格、右端包含。 -/
def primeIntervalCount (x y : ℕ) : ℕ := (primeIntervalPrimes x y).card

/-- 区间中整除计数的精确自然数商公式，不需要限制区间起点。 -/
theorem intervalMultiples_card (x y d : ℕ) :
    ((Ioc x (x + y)).filter (fun n => d ∣ n)).card = (x + y) / d - x / d := by
  classical
  have hsub : (Ioc 0 x).filter (fun n => d ∣ n) ⊆
      (Ioc 0 (x + y)).filter (fun n => d ∣ n) := by
    intro n hn
    obtain ⟨hnI, hd⟩ := mem_filter.mp hn
    obtain ⟨hn0, hnx⟩ := mem_Ioc.mp hnI
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hn0, by omega⟩, hd⟩
  have heq : (Ioc x (x + y)).filter (fun n => d ∣ n) =
      ((Ioc 0 (x + y)).filter (fun n => d ∣ n)) \
        ((Ioc 0 x).filter (fun n => d ∣ n)) := by
    ext n
    simp only [mem_filter, mem_Ioc, mem_sdiff]
    omega
  rw [heq, card_sdiff_of_subset hsub, Nat.Ioc_filter_dvd_card_eq_div,
    Nat.Ioc_filter_dvd_card_eq_div]

/-- 自然数商先转为实数，再与实数除法比较；误差绝对值至多一。 -/
theorem intervalMultiples_error (x y d : ℕ) (hd : 0 < d) :
    |((((Ioc x (x + y)).filter (fun n => d ∣ n)).card : ℝ) - (y : ℝ) / (d : ℝ))| ≤ 1 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hle : x / d ≤ (x + y) / d := Nat.div_le_div_right (by omega : x ≤ x + y)
  rw [intervalMultiples_card, Nat.cast_sub hle]
  have hx : (x : ℝ) = (d : ℝ) * (x / d : ℕ) + (x % d : ℕ) := by
    exact_mod_cast (Nat.div_add_mod x d).symm
  have hu : (x : ℝ) + (y : ℝ) =
      (d : ℝ) * ((x + y) / d : ℕ) + ((x + y) % d : ℕ) := by
    exact_mod_cast (Nat.div_add_mod (x + y) d).symm
  have hxm : ((x % d : ℕ) : ℝ) < d := by exact_mod_cast Nat.mod_lt x hd
  have hum : (((x + y) % d : ℕ) : ℝ) < d := by exact_mod_cast Nat.mod_lt (x + y) hd
  have hxm0 : (0 : ℝ) ≤ (x % d : ℕ) := Nat.cast_nonneg _
  have hum0 : (0 : ℝ) ≤ ((x + y) % d : ℕ) := Nat.cast_nonneg _
  have hdiv : ((y : ℝ) / (d : ℝ)) * (d : ℝ) = y := div_mul_cancel₀ _ hdR.ne'
  apply abs_le.mpr
  constructor
  · apply (mul_le_mul_iff_of_pos_right hdR).mp
    nlinarith [hx, hu, hxm, hum, hdiv]
  · apply (mul_le_mul_iff_of_pos_right hdR).mp
    nlinarith [hx, hu, hxm, hum, hdiv]

/-- 实际筛后集合：区间中与 `P=primorial z` 互素的整数。 -/
def primeIntervalSifted (x y z : ℕ) : Finset ℕ :=
  (Ioc x (x + y)).filter (fun n => (primorial z).Coprime n)

/-- 与 `P` 互素时，权重和只剩约数一，故平方恰为一。 -/
theorem intervalWeight_sum_of_coprime (z n : ℕ) (hz : 1 ≤ z)
    (hcop : (primorial z).Coprime n) :
    (∑ d ∈ (primorial z).divisors, if d ∣ n then selbergIntervalWeight z d else 0) = 1 := by
  classical
  rw [← sum_filter]
  have hfilter : ((primorial z).divisors.filter (fun d => d ∣ n)) = {1} := by
    ext d
    simp only [mem_filter, Nat.mem_divisors, mem_singleton]
    constructor
    · rintro ⟨⟨hdP, hP⟩, hdn⟩
      exact Nat.eq_one_of_dvd_coprimes hcop hdP hdn
    · rintro rfl
      exact ⟨⟨one_dvd _, primorial_ne_zero z⟩, one_dvd _⟩
  rw [hfilter, sum_singleton, selbergIntervalWeight_one z hz]

/-- 逐项平方展开，只涉及有限和；整除条件精确合并为最小公倍数整除。 -/
theorem intervalWeight_square_expand (z n : ℕ) :
    (∑ d ∈ (primorial z).divisors, if d ∣ n then selbergIntervalWeight z d else 0)^2 =
      ∑ d ∈ (primorial z).divisors, ∑ e ∈ (primorial z).divisors,
        if Nat.lcm d e ∣ n then selbergIntervalWeight z d * selbergIntervalWeight z e else 0 := by
  rw [sq, sum_mul_sum]
  apply sum_congr rfl
  intro d hd
  apply sum_congr rfl
  intro e he
  simp only [Nat.lcm_dvd_iff]
  by_cases hdn : d ∣ n <;> by_cases hen : e ∣ n <;> simp [hdn, hen]

/-- 用平方非负性控制其余整数，实际交换有限和并取得约数计数展开。 -/
theorem primeIntervalSifted_le_weighted_multiples (x y z : ℕ) (hz : 1 ≤ z) :
    ((primeIntervalSifted x y z).card : ℝ) ≤
      ∑ d ∈ (primorial z).divisors, ∑ e ∈ (primorial z).divisors,
        selbergIntervalWeight z d * selbergIntervalWeight z e *
          (((Ioc x (x + y)).filter (fun n => Nat.lcm d e ∣ n)).card : ℝ) := by
  classical
  have hpoint (n : ℕ) : (if (primorial z).Coprime n then (1 : ℝ) else 0) ≤
      (∑ d ∈ (primorial z).divisors, if d ∣ n then selbergIntervalWeight z d else 0)^2 := by
    by_cases hcop : (primorial z).Coprime n
    · rw [ite_eq_left hcop, intervalWeight_sum_of_coprime z n hz hcop]
      norm_num
    · rw [ite_eq_right hcop]
      exact sq_nonneg _
  calc
    _ = ∑ n ∈ Ioc x (x + y), if (primorial z).Coprime n then (1 : ℝ) else 0 := by
      simp [primeIntervalSifted]
    _ ≤ ∑ n ∈ Ioc x (x + y),
        (∑ d ∈ (primorial z).divisors, if d ∣ n then selbergIntervalWeight z d else 0)^2 :=
      sum_le_sum (fun n hn => hpoint n)
    _ = _ := by
      simp_rw [intervalWeight_square_expand]
      rw [sum_comm]
      apply sum_congr rfl
      intro d hd
      rw [sum_comm]
      apply sum_congr rfl
      intro e he
      rw [← sum_filter]
      simp [mul_comm]

/-- 将整除计数误差乘上任意实系数，包括负权重乘积。 -/
theorem intervalWeight_error (w a b : ℝ) (h : |a - b| ≤ 1) : w * a ≤ w * b + |w| := by
  have hprod := mul_le_mul_of_nonneg_left h (abs_nonneg w)
  have habs := le_abs_self (w * (a - b))
  rw [abs_mul] at habs
  nlinarith

/-- 有限筛后的计数：主项由既有精确二次型取得，误差由权重总绝对值的平方控制。 -/
theorem primeIntervalSifted_bound (x y z : ℕ) (hz : 1 ≤ z) :
    ((primeIntervalSifted x y z).card : ℝ) ≤
      (y : ℝ) / squarefreeTotientSum z + (z : ℝ)^4 := by
  let w := selbergIntervalWeight z
  let D := (primorial z).divisors
  have hterm (d : ℕ) (hd : d ∈ D) (e : ℕ) (he : e ∈ D) :
      w d * w e * (((Ioc x (x + y)).filter (fun n => Nat.lcm d e ∣ n)).card : ℝ) ≤
        (y : ℝ) * (w d * w e / (Nat.lcm d e : ℝ)) + |w d| * |w e| := by
    have hl := Nat.lcm_pos (Nat.pos_of_mem_divisors hd) (Nat.pos_of_mem_divisors he)
    have h := intervalWeight_error (w d * w e) _ _ (intervalMultiples_error x y (Nat.lcm d e) hl)
    rw [abs_mul] at h
    convert h using 1 <;> ring
  have hcollect :
      (∑ d ∈ D, ∑ e ∈ D,
        ((y : ℝ) * (w d * w e / (Nat.lcm d e : ℝ)) + |w d| * |w e|)) =
      (y : ℝ) * (∑ d ∈ D, ∑ e ∈ D, w d * w e / (Nat.lcm d e : ℝ)) +
        (∑ d ∈ D, |w d|)^2 := by
    simp only [sum_add_distrib, mul_sum, sum_mul, sq]
    simp only [mul_comm]
  have hq := (selbergIntervalWeight_quadratic z hz).1.trans
    (selbergIntervalWeight_quadratic z hz).2
  have habs := selbergIntervalWeight_abs_sum z hz
  have hsum0 : 0 ≤ ∑ d ∈ D, |w d| := sum_nonneg (fun d hd => abs_nonneg _)
  have herr : (∑ d ∈ D, |w d|)^2 ≤ (z : ℝ)^4 := by
    calc
      _ ≤ ((z : ℝ)^2)^2 := by gcongr
      _ = _ := by ring
  calc
    _ ≤ ∑ d ∈ D, ∑ e ∈ D,
        w d * w e * (((Ioc x (x + y)).filter (fun n => Nat.lcm d e ∣ n)).card : ℝ) :=
      primeIntervalSifted_le_weighted_multiples x y z hz
    _ ≤ ∑ d ∈ D, ∑ e ∈ D,
        ((y : ℝ) * (w d * w e / (Nat.lcm d e : ℝ)) + |w d| * |w e|) :=
      sum_le_sum (fun d hd => sum_le_sum (fun e he => hterm d hd e he))
    _ = (y : ℝ) * (∑ d ∈ D, ∑ e ∈ D, w d * w e / (Nat.lcm d e : ℝ)) +
        (∑ d ∈ D, |w d|)^2 := hcollect
    _ = (y : ℝ) / squarefreeTotientSum z + (∑ d ∈ D, |w d|)^2 := by
      change (y : ℝ) * (∑ d ∈ (primorial z).divisors, ∑ e ∈ (primorial z).divisors,
        selbergIntervalWeight z d * selbergIntervalWeight z e / (Nat.lcm d e : ℝ)) + _ = _
      rw [hq]
      ring
    _ ≤ _ := by linarith [herr]

/-- 大于 `z` 的素数与 `P` 互素，其余素数放入至多有 `z` 个元素的正整数区间。 -/
theorem primeIntervalCount_le_sifted_add (x y z : ℕ) :
    primeIntervalCount x y ≤ (primeIntervalSifted x y z).card + z := by
  classical
  have hsub : primeIntervalPrimes x y ⊆ primeIntervalSifted x y z ∪ Icc 1 z := by
    intro p hp
    obtain ⟨hpI, hprime⟩ := mem_filter.mp hp
    by_cases hpz : p ≤ z
    · exact mem_union_right _ (mem_Icc.mpr ⟨hprime.one_le, hpz⟩)
    · have hnot : ¬ p ∣ primorial z := fun hd => hpz (hprime.dvd_primorial_iff.mp hd)
      have hcop : (primorial z).Coprime p := (hprime.coprime_iff_not_dvd.mpr hnot).symm
      exact mem_union_left _ (mem_filter.mpr ⟨hpI, hcop⟩)
  calc
    _ ≤ (primeIntervalSifted x y z ∪ Icc 1 z).card := card_le_card hsub
    _ ≤ (primeIntervalSifted x y z).card + (Icc 1 z).card := card_union_le _ _
    _ = _ := by simp

/-- 题述有限区间筛估计，对所有自然数 `x,y` 以及 `z≥1` 成立。 -/
theorem primeIntervalUpper_finite (x y z : ℕ) (hz : 1 ≤ z) :
    (primeIntervalCount x y : ℝ) ≤
      (y : ℝ) / squarefreeTotientSum z + (z : ℝ)^4 + (z : ℝ) := by
  have hsmall : (primeIntervalCount x y : ℝ) ≤
      ((primeIntervalSifted x y z).card : ℝ) + (z : ℝ) := by
    exact_mod_cast primeIntervalCount_le_sifted_add x y z
  have h := primeIntervalSifted_bound x y z hz
  linarith

/-- 实际取整的筛层参数：`z=floor(y^(1/8))`。其对数和误差界对全部 `y≥2` 一致。 -/
theorem primeInterval_sieve_level_bounds (y : ℕ) (hy : 2 ≤ y) :
    let z := ⌊(y : ℝ) ^ (1 / 8 : ℝ)⌋₊
    1 ≤ z ∧ Real.log (y : ℝ) / 16 ≤ squarefreeTotientSum z ∧
      (z : ℝ)^4 + (z : ℝ) ≤ 4 * (y : ℝ) / Real.log (y : ℝ) := by
  intro z
  have hy2 : (2 : ℝ) ≤ y := by exact_mod_cast hy
  have hy0 : (0 : ℝ) < y := by linarith
  have hy1 : (1 : ℝ) ≤ y := by linarith
  have hlogpos : 0 < Real.log (y : ℝ) := Real.log_pos (by linarith)
  let a : ℝ := (y : ℝ) ^ (1 / 8 : ℝ)
  let b : ℝ := (y : ℝ) ^ (1 / 2 : ℝ)
  have ha0 : 0 < a := Real.rpow_pos_of_pos hy0 _
  have hb0 : 0 < b := Real.rpow_pos_of_pos hy0 _
  have ha1 : 1 ≤ a := Real.one_le_rpow hy1 (by norm_num)
  have hz1 : 1 ≤ z := Nat.floor_pos.mpr ha1
  have hzle : (z : ℝ) ≤ a := Nat.floor_le ha0.le
  have halt : a < (z : ℝ) + 1 := Nat.lt_floor_add_one a
  have hlog : (1 / 8 : ℝ) * Real.log (y : ℝ) ≤ Real.log ((z : ℝ) + 1) := by
    have h := Real.log_le_log ha0 halt.le
    change Real.log ((y : ℝ) ^ (1 / 8 : ℝ)) ≤ _ at h
    rwa [Real.log_rpow hy0] at h
  have hGharm := (squarefreeHarmonicSum_log_lower z hz1).trans
    (squarefreeHarmonicSum_le_totientSum z)
  have hGlower : Real.log (y : ℝ) / 16 ≤ squarefreeTotientSum z := by
    linarith [hlog, hGharm]
  have ha4 : a^4 = b := by
    dsimp [a, b]
    rw [← Real.rpow_mul_natCast hy0.le]
    norm_num
  have hz4 : (z : ℝ)^4 ≤ b := by
    rw [← ha4]
    gcongr
  have hab : a ≤ b := Real.rpow_le_rpow_of_exponent_le hy1 (by norm_num)
  have hzhalf : (z : ℝ) ≤ b := hzle.trans hab
  have hb2 : b^2 = (y : ℝ) := by
    dsimp [b]
    rw [← Real.rpow_mul_natCast hy0.le]
    norm_num
  have hloghalf : Real.log (y : ℝ) ≤ 2 * b := by
    have h := Real.log_le_rpow_div hy0.le (by norm_num : (0 : ℝ) < 1 / 2)
    change Real.log (y : ℝ) ≤ b / (1 / 2 : ℝ) at h
    linarith
  have hhalfAbsorb : b ≤ 2 * (y : ℝ) / Real.log (y : ℝ) := by
    apply (le_div_iff₀ hlogpos).2
    have h := mul_le_mul_of_nonneg_left hloghalf hb0.le
    nlinarith [hb2, h]
  refine ⟨hz1, hGlower, ?_⟩
  calc
    (z : ℝ)^4 + (z : ℝ) ≤ 2 * b := by linarith [hz4, hzhalf]
    _ ≤ 2 * (2 * (y : ℝ) / Real.log (y : ℝ)) :=
      mul_le_mul_of_nonneg_left hhalfAbsorb (by norm_num)
    _ = _ := by ring

/-- 明确的统一数值版本：对任意自然数起点及所有 `y≥2`，可取常数二十。 -/
theorem primeIntervalUpper_explicit (x y : ℕ) (hy : 2 ≤ y) :
    (primeIntervalCount x y : ℝ) ≤ 20 * (y : ℝ) / Real.log (y : ℝ) := by
  let z := ⌊(y : ℝ) ^ (1 / 8 : ℝ)⌋₊
  obtain ⟨hz, hG, htail⟩ := primeInterval_sieve_level_bounds y hy
  have hy2 : (2 : ℝ) ≤ y := by exact_mod_cast hy
  have hlogpos : 0 < Real.log (y : ℝ) := Real.log_pos (by linarith)
  have hmain : (y : ℝ) / squarefreeTotientSum z ≤
      16 * (y : ℝ) / Real.log (y : ℝ) := by
    calc
      _ ≤ (y : ℝ) / (Real.log (y : ℝ) / 16) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg y) (by positivity) hG
      _ = _ := by ring
  have hfinite := primeIntervalUpper_finite x y z hz
  calc
    _ ≤ (y : ℝ) / squarefreeTotientSum z + ((z : ℝ)^4 + (z : ℝ)) := by
      linarith [hfinite]
    _ ≤ 16 * (y : ℝ) / Real.log (y : ℝ) + 4 * (y : ℝ) / Real.log (y : ℝ) :=
      add_le_add hmain htail
    _ = _ := by ring

/-- 题述统一区间素数上界：常数与起点均先于任意区间选取，且独立于 `x`。
这里实际给出 `C=20`、`Y₀=2`，没有加入起点或速度高度条件。 -/
theorem primeIntervalUpper_uniform :
    ∃ C : ℝ, 0 < C ∧ ∃ Y₀ : ℕ, 2 ≤ Y₀ ∧
      ∀ (x y : ℕ), Y₀ ≤ y →
        (primeIntervalCount x y : ℝ) ≤ C * (y : ℝ) / Real.log (y : ℝ) :=
  ⟨20, by norm_num, 2, le_rfl, fun x y hy => primeIntervalUpper_explicit x y hy⟩

#print axioms intervalMultiples_card
#print axioms intervalMultiples_error
#print axioms primeIntervalUpper_finite
#print axioms primeIntervalUpper_explicit
#print axioms primeIntervalUpper_uniform

end LonelyRunner
