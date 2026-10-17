import LonelyRunner.PrimeIntervalUpper
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# 好余数素数的对数总量

实际使用 Chebyshev 带误差下界与任意起点的区间素数上界。
坏余数在倍数附近的短整数区间内统一计数，不使用素数定理。
-/

namespace LonelyRunner
open Finset Filter Asymptotics
open scoped Topology

/-- 题述真实有限集合：上端 `p≤X`，余数下界为自然数比较，上界为实数比较。 -/
noncomputable def goodResiduePrimes (m X : ℕ) (c : ℝ) : Finset ℕ := by
  classical
  exact (Nat.primesLE X).filter (fun p =>
    2 ≤ p % (2 * m) ∧ ((p % (2 * m) : ℕ) : ℝ) ≤ (1 - c) * (2 * (m : ℝ)))

/-- 坏素数为实际补集；包括余数零、一及超过实数截断的余数。 -/
noncomputable def badResiduePrimes (m X : ℕ) (c : ℝ) : Finset ℕ :=
  Nat.primesLE X \ goodResiduePrimes m X c

/-- 从 Mathlib 的 Chebyshev 带误差下界实际吸收误差，得到绝对起点后的 `θ(X)≥X/2`。 -/
theorem chebyshev_theta_half_eventually :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ X : ℕ, N ≤ X → (X : ℝ) / 2 ≤ Chebyshev.theta (X : ℝ) := by
  let a : ℝ := (Real.log 2 - 1 / 2) / 4
  have ha : 0 < a := by dsimp [a]; linarith [Real.log_two_gt_d9]
  have hsmall := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).bound ha
  have hnat := tendsto_natCast_atTop_atTop.eventually hsmall
  obtain ⟨N, hN⟩ := eventually_atTop.1 hnat
  refine ⟨max 2 N, le_max_left _ _, ?_⟩
  intro X hX
  have hX2 : 2 ≤ X := (le_max_left _ _).trans hX
  have hXN : N ≤ X := (le_max_right _ _).trans hX
  have hXR : (2 : ℝ) ≤ X := by exact_mod_cast hX2
  have hX0 : (0 : ℝ) < X := by linarith
  have hlog0 : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by linarith)
  have hsqrt1 : 1 ≤ Real.sqrt (X : ℝ) := Real.one_le_sqrt.mpr (by linarith)
  have hlogBound : Real.log (X : ℝ) ≤ a * Real.sqrt (X : ℝ) := by
    have h := hN X hXN
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlog0,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg X) (1 / 2)),
      ← Real.sqrt_eq_rpow, abs_of_nonneg (Real.sqrt_nonneg (X : ℝ))] using h
  have hlog2 : Real.log 2 ≤ Real.log (X : ℝ) := Real.log_le_log (by norm_num) hXR
  have hlogNext : Real.log ((X : ℝ) + 1) ≤ 2 * Real.log (X : ℝ) := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < (X : ℝ) + 1)
      (by linarith : (X : ℝ) + 1 ≤ 2 * (X : ℝ))
    rw [Real.log_mul (by norm_num) hX0.ne'] at h
    linarith
  have herror : Real.log ((X : ℝ) + 1) + 2 * Real.sqrt (X : ℝ) * Real.log (X : ℝ) ≤
      (Real.log 2 - 1 / 2) * (X : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_right hsqrt1 hlog0
    have h2 := mul_le_mul_of_nonneg_left hlogBound (Real.sqrt_nonneg (X : ℝ))
    have hsq := Real.sq_sqrt hX0.le
    dsimp [a] at hlogBound h2
    nlinarith [hlogNext, h1, h2, hsq]
  have hcheb := Chebyshev.theta_ge X
  linarith

/-- 近倍数区间宽度，向上取整后再增加两个单位以包含余数零、一和端点。 -/
noncomputable def badResidueIntervalWidth (m : ℕ) (c : ℝ) : ℕ :=
  ⌈2 * c * (m : ℝ)⌉₊ + 2

/-- 自然数减法自动处理首区间被零截断；区间右端始终至少达到 `2mj+2`。 -/
noncomputable def badResidueIntervalStart (m : ℕ) (c : ℝ) (j : ℕ) : ℕ :=
  2 * m * j - ⌈2 * c * (m : ℝ)⌉₊

/-- 坏素数的实际有限短区间覆盖。余数零、一取当前倍数，尾余数取下一个倍数；
索引包括首、尾区间，不遗漏取整或实数截断端点。 -/
theorem badResiduePrimes_cover (m X : ℕ) (c : ℝ) (hm : 0 < m) (hc : 0 < c) :
    badResiduePrimes m X c ⊆
      (range (X / (2 * m) + 2)).biUnion (fun j =>
        primeIntervalPrimes (badResidueIntervalStart m c j) (badResidueIntervalWidth m c)) := by
  classical
  intro p hp
  obtain ⟨hpX, hpNot⟩ := mem_sdiff.mp hp
  obtain ⟨hpXle, hpPrime⟩ := Nat.mem_primesLE.mp hpX
  have hp0 : 0 < p := hpPrime.pos
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  let L := ⌈2 * c * (m : ℝ)⌉₊
  have hLpos : 0 < L := Nat.ceil_pos.mpr (by positivity)
  have hLreal : 2 * c * (m : ℝ) ≤ (L : ℝ) := Nat.le_ceil _
  have hdiv : p = 2 * m * (p / (2 * m)) + p % (2 * m) :=
    (Nat.div_add_mod p (2 * m)).symm
  have hqX : p / (2 * m) ≤ X / (2 * m) := Nat.div_le_div_right hpXle
  have hrlt : p % (2 * m) < 2 * m := Nat.mod_lt _ (by omega)
  by_cases hr : p % (2 * m) < 2
  · let j := p / (2 * m)
    have hj : j ∈ range (X / (2 * m) + 2) := mem_range.mpr (by dsimp [j]; omega)
    have hstart : badResidueIntervalStart m c j < p := by
      dsimp [badResidueIntervalStart, j]
      omega
    have hend : p ≤ badResidueIntervalStart m c j + badResidueIntervalWidth m c := by
      dsimp [badResidueIntervalStart, badResidueIntervalWidth, j]
      omega
    exact mem_biUnion.mpr ⟨j, hj, mem_filter.mpr ⟨mem_Ioc.mpr ⟨hstart, hend⟩, hpPrime⟩⟩
  · have hr2 : 2 ≤ p % (2 * m) := by omega
    have hbad : (1 - c) * (2 * (m : ℝ)) < ((p % (2 * m) : ℕ) : ℝ) := by
      by_contra h
      apply hpNot
      exact mem_filter.mpr ⟨hpX, hr2, le_of_not_gt h⟩
    have hgap : 2 * m - p % (2 * m) < L := by
      have hrle : p % (2 * m) ≤ 2 * m := by omega
      have hreal : (((2 * m - p % (2 * m) : ℕ)) : ℝ) < (L : ℝ) := by
        rw [Nat.cast_sub hrle]
        push_cast
        nlinarith [hLreal, hbad]
      exact_mod_cast hreal
    let j := p / (2 * m) + 1
    have hj : j ∈ range (X / (2 * m) + 2) := mem_range.mpr (by dsimp [j]; omega)
    have hnext : 2 * m * j = 2 * m * (p / (2 * m)) + 2 * m := by dsimp [j]; ring
    have hstart : badResidueIntervalStart m c j < p := by
      dsimp [badResidueIntervalStart]
      rw [hnext]
      omega
    have hend : p ≤ badResidueIntervalStart m c j + badResidueIntervalWidth m c := by
      dsimp [badResidueIntervalStart, badResidueIntervalWidth]
      rw [hnext]
      omega
    exact mem_biUnion.mpr ⟨j, hj, mem_filter.mpr ⟨mem_Ioc.mpr ⟨hstart, hend⟩, hpPrime⟩⟩

/-- 短区间宽度的实际取整控制。两条小量条件将在固定绝对 `c` 后由统一起点保证。 -/
theorem badResidueInterval_bounds (m : ℕ) (c : ℝ) (hm : 2 ≤ m) (hc : 0 < c)
    (hcm : 2 ≤ c * (m : ℝ)) (hsq : 1 ≤ 4 * c^2 * (m : ℝ)) :
    2 ≤ badResidueIntervalWidth m c ∧
      (badResidueIntervalWidth m c : ℝ) ≤ 4 * c * (m : ℝ) ∧
      (1 / 2 : ℝ) * Real.log (m : ℝ) ≤ Real.log (badResidueIntervalWidth m c : ℝ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hW2 : 2 ≤ badResidueIntervalWidth m c := by unfold badResidueIntervalWidth; omega
  have hceil := Nat.ceil_lt_add_one (by positivity : 0 ≤ 2 * c * (m : ℝ))
  have hupper : (badResidueIntervalWidth m c : ℝ) ≤ 4 * c * (m : ℝ) := by
    unfold badResidueIntervalWidth
    push_cast
    linarith
  have hsqrt : Real.sqrt (m : ℝ) ≤ 2 * c * (m : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have h := mul_le_mul_of_nonneg_right hsq hmR.le
    nlinarith
  have hceilLower := Nat.le_ceil (2 * c * (m : ℝ))
  have hlower : Real.sqrt (m : ℝ) ≤ (badResidueIntervalWidth m c : ℝ) := by
    unfold badResidueIntervalWidth
    push_cast
    linarith
  have hlog := Real.log_le_log (Real.sqrt_pos.mpr hmR) hlower
  rw [Real.sqrt_eq_rpow, Real.log_rpow hmR] at hlog
  exact ⟨hW2, hupper, hlog⟩

/-- 至多 `X/(2m)+2` 个区间；`X≥2m` 时其数量不超过实数 `2X/m`。 -/
theorem badResidueInterval_number (m X : ℕ) (hm : 0 < m) (hX : 2 * m ≤ X) :
    ((X / (2 * m) + 2 : ℕ) : ℝ) ≤ 2 * (X : ℝ) / (m : ℝ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hq : (2 * m) * (X / (2 * m)) ≤ X := by
    simpa only [Nat.mul_comm] using Nat.div_mul_le_self X (2 * m)
  have hcount : (X / (2 * m) + 2) * m ≤ 2 * X := by nlinarith
  apply (le_div_iff₀ hmR).2
  exact_mod_cast hcount

/-- 实际有限并计数后调用任意起点的 `primeIntervalUpper_explicit`。 -/
theorem badResiduePrimes_card_bound (m X : ℕ) (c : ℝ) (hm : 0 < m) (hc : 0 < c) :
    ((badResiduePrimes m X c).card : ℝ) ≤
      ((X / (2 * m) + 2 : ℕ) : ℝ) *
        (20 * (badResidueIntervalWidth m c : ℝ) / Real.log (badResidueIntervalWidth m c : ℝ)) := by
  classical
  let W := badResidueIntervalWidth m c
  have hW : 2 ≤ W := by dsimp [W, badResidueIntervalWidth]; omega
  have hcard : (badResiduePrimes m X c).card ≤
      ∑ j ∈ range (X / (2 * m) + 2),
        (primeIntervalPrimes (badResidueIntervalStart m c j) W).card :=
    (card_le_card (badResiduePrimes_cover m X c hm hc)).trans card_biUnion_le
  calc
    _ ≤ ((∑ j ∈ range (X / (2 * m) + 2),
        (primeIntervalPrimes (badResidueIntervalStart m c j) W).card : ℕ) : ℝ) := by
      exact_mod_cast hcard
    _ = ∑ j ∈ range (X / (2 * m) + 2),
        (primeIntervalCount (badResidueIntervalStart m c j) W : ℝ) := by push_cast; rfl
    _ ≤ ∑ _j ∈ range (X / (2 * m) + 2), (20 * (W : ℝ) / Real.log (W : ℝ)) :=
      sum_le_sum (fun j hj => primeIntervalUpper_explicit (badResidueIntervalStart m c j) W hW)
    _ = _ := by simp [W]

/-- 在固定 `c` 之前取得绝对系数 `B=640`：坏素数的对数总量至多 `640 c X`。
仅使用 `2m≤X≤m²`，不包含好素数密度或素数分布参数。 -/
theorem badResiduePrimes_log_le (m X : ℕ) (c : ℝ) (hm : 2 ≤ m) (hc : 0 < c)
    (hXlo : 2 * m ≤ X) (hXhi : X ≤ m^2)
    (hcm : 2 ≤ c * (m : ℝ)) (hsq : 1 ≤ 4 * c^2 * (m : ℝ)) :
    (∑ p ∈ badResiduePrimes m X c, Real.log (p : ℝ)) ≤ 640 * c * (X : ℝ) := by
  let W := badResidueIntervalWidth m c
  let J := X / (2 * m) + 2
  have hmpos : 0 < m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hm2R : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hXpos : 0 < X := by omega
  have hXR : (0 : ℝ) < X := by exact_mod_cast hXpos
  have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos (by linarith)
  obtain ⟨hW2, hWupper, hlogW⟩ := badResidueInterval_bounds m c hm hc hcm hsq
  have hWR : (2 : ℝ) ≤ W := by exact_mod_cast hW2
  have hWpos : (0 : ℝ) < W := by linarith
  have hlogWpos : 0 < Real.log (W : ℝ) := Real.log_pos (by linarith)
  have hXlog : Real.log (X : ℝ) ≤ 2 * Real.log (m : ℝ) := by
    have hhi : (X : ℝ) ≤ (m : ℝ)^2 := by exact_mod_cast hXhi
    have h := Real.log_le_log hXR hhi
    rw [Real.log_pow] at h
    norm_num at h
    exact h
  have hratio : Real.log (X : ℝ) / Real.log (W : ℝ) ≤ 4 := by
    apply (div_le_iff₀ hlogWpos).2
    linarith [hlogW, hXlog]
  have hlogX0 : 0 ≤ Real.log (X : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (by omega : 1 ≤ X)
  have hJ := badResidueInterval_number m X hmpos hXlo
  have hcount := badResiduePrimes_card_bound m X c hmpos hc
  have hsum : (∑ p ∈ badResiduePrimes m X c, Real.log (p : ℝ)) ≤
      ((badResiduePrimes m X c).card : ℝ) * Real.log (X : ℝ) := by
    calc
      _ ≤ ∑ _p ∈ badResiduePrimes m X c, Real.log (X : ℝ) := by
        apply sum_le_sum
        intro p hp
        have hp' := (mem_sdiff.mp hp).1
        obtain ⟨hpX, hpprime⟩ := Nat.mem_primesLE.mp hp'
        exact Real.log_le_log (by exact_mod_cast hpprime.pos) (by exact_mod_cast hpX)
      _ = _ := by simp
  calc
    _ ≤ ((badResiduePrimes m X c).card : ℝ) * Real.log (X : ℝ) := hsum
    _ ≤ ((J : ℝ) * (20 * (W : ℝ) / Real.log (W : ℝ))) * Real.log (X : ℝ) :=
      mul_le_mul_of_nonneg_right hcount hlogX0
    _ = (20 * (J : ℝ) * (W : ℝ)) * (Real.log (X : ℝ) / Real.log (W : ℝ)) := by ring
    _ ≤ (20 * (J : ℝ) * (W : ℝ)) * 4 :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = 80 * (J : ℝ) * (W : ℝ) := by ring
    _ ≤ 80 * (2 * (X : ℝ) / (m : ℝ)) * (4 * c * (m : ℝ)) := by gcongr
    _ = _ := by field_simp; ring

/-- 好、坏集合是实际素数集合的互不相交分拆，所以两部分对数和恰为 `θ(X)`。 -/
theorem good_bad_residue_theta (m X : ℕ) (c : ℝ) :
    Chebyshev.theta (X : ℝ) =
      (∑ p ∈ goodResiduePrimes m X c, Real.log (p : ℝ)) +
        (∑ p ∈ badResiduePrimes m X c, Real.log (p : ℝ)) := by
  classical
  have hsub : goodResiduePrimes m X c ⊆ Nat.primesLE X := filter_subset _ _
  have hunion : goodResiduePrimes m X c ∪ badResiduePrimes m X c = Nat.primesLE X :=
    union_sdiff_of_subset hsub
  have hdisj : Disjoint (goodResiduePrimes m X c) (badResiduePrimes m X c) := disjoint_sdiff
  rw [Chebyshev.theta_eq_sum_primesLE_log, ← hunion, sum_union hdisj]

/-- 题述好素数对数总量：先固定绝对常数 `c=1/4096`，再取得绝对起点。
起点不依赖 `m,X`；结论没有保留 Chebyshev、坏余数计数或好素数密度假设。 -/
theorem primeGoodResidues_log_mass :
    ∃ c : ℝ, 0 < c ∧ c < 1 / 4 ∧ ∃ M : ℕ,
      ∀ (m X : ℕ), M ≤ m → 2 * m ≤ X → X ≤ m^2 →
        (X : ℝ) / 4 ≤ ∑ p ∈ goodResiduePrimes m X c, Real.log (p : ℝ) := by
  obtain ⟨N, hN2, htheta⟩ := chebyshev_theta_half_eventually
  let c : ℝ := 1 / 4096
  have hc : 0 < c := by norm_num [c]
  have hc4 : c < 1 / 4 := by norm_num [c]
  refine ⟨c, hc, hc4, max 16777216 N, ?_⟩
  intro m X hm hXlo hXhi
  have hmAbs : 16777216 ≤ m := (le_max_left _ _).trans hm
  have hmN : N ≤ m := (le_max_right _ _).trans hm
  have hmR : (16777216 : ℝ) ≤ m := by exact_mod_cast hmAbs
  have hm2 : 2 ≤ m := by omega
  have hcm : 2 ≤ c * (m : ℝ) := by dsimp [c]; nlinarith
  have hsq : 1 ≤ 4 * c^2 * (m : ℝ) := by dsimp [c]; nlinarith
  have hbad := badResiduePrimes_log_le m X c hm2 hc hXlo hXhi hcm hsq
  have hbadQuarter : (∑ p ∈ badResiduePrimes m X c, Real.log (p : ℝ)) ≤ (X : ℝ) / 4 := by
    have hcoef : 640 * c ≤ 1 / 4 := by norm_num [c]
    calc
      _ ≤ 640 * c * (X : ℝ) := hbad
      _ ≤ (1 / 4 : ℝ) * (X : ℝ) := mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg X)
      _ = _ := by ring
  have hthetaX := htheta X (by omega : N ≤ X)
  have hsplit := good_bad_residue_theta m X c
  linarith

#print axioms chebyshev_theta_half_eventually
#print axioms badResiduePrimes_cover
#print axioms badResiduePrimes_log_le
#print axioms primeGoodResidues_log_mass

end LonelyRunner
