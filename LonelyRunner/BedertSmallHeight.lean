import LonelyRunner.PrimeGoodResidues
import LonelyRunner.BedertPrimeGrid

/-!
# 本论文所需范围内的 Bedert 小高度结论

对应 `paper/lonely_runner_zh.tex` 的命题 `prop:bedert` 第二项。
这是在 `log T≤m^(3/4)` 范围内的替代证明，不宣称覆盖 Bedert 原命题的
全部高度范围。好素数及其避除性均从已证的对数总量和有限乘积整除取得。
-/

namespace LonelyRunner
open Finset

/-- 正整数速度互异且都不超过自然数高度 `T`，故速度数不超过 `T`。 -/
theorem positiveSpeeds_card_le_height (V : Finset ℕ) (T : ℕ)
    (hV : ∀ v ∈ V, 0 < v) (hT : ∀ v ∈ V, v ≤ T) : V.card ≤ T := by
  have hsub : V ⊆ Icc 1 T := fun v hv => mem_Icc.mpr ⟨hV v hv, hT v hv⟩
  exact (card_le_card hsub).trans_eq (by simp)

/-- 实际处理 `X=ceil(8m log T)`：固定起点 `6561=9^4` 足以保证所有范围。
起点独立于自然数高度 `T`。 -/
theorem bedertSmallHeight_level_bounds (m T : ℕ) (hm : 6561 ≤ m) (hT : 2 ≤ T)
    (hheight : Real.log (T : ℝ) ≤ (m : ℝ) ^ (3 / 4 : ℝ)) :
    let X := ⌈8 * (m : ℝ) * Real.log (T : ℝ)⌉₊
    2 * m ≤ X ∧ X ≤ m^2 ∧
      (X : ℝ) ≤ 9 * (m : ℝ) * Real.log (T : ℝ) ∧
      8 * (m : ℝ) * Real.log (T : ℝ) ≤ (X : ℝ) := by
  intro X
  have hmR : (6561 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hm2 : (2 : ℝ) ≤ m := by linarith
  have hTR : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hlog : (1 / 2 : ℝ) < Real.log (T : ℝ) := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hTR
    linarith [Real.log_two_gt_d9]
  have hscale : (1 : ℝ) ≤ (m : ℝ) * Real.log (T : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hlog.le hm0.le
    nlinarith
  have hquarter : (9 : ℝ) ≤ (m : ℝ) ^ (1 / 4 : ℝ) := by
    calc
      (9 : ℝ) = (9 : ℝ)^((4 : ℝ) * (1 / 4 : ℝ)) := by norm_num
      _ = ((9 : ℝ)^4) ^ (1 / 4 : ℝ) := Real.rpow_natCast_mul (by norm_num) 4 (1 / 4)
      _ ≤ (m : ℝ) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow (by positivity) (by norm_num; exact hm) (by norm_num)
  have hpow : (m : ℝ) ^ (3 / 4 : ℝ) * (m : ℝ) ^ (1 / 4 : ℝ) = m := by
    rw [← Real.rpow_add hm0]
    norm_num
  have hpowerBound : 9 * (m : ℝ) ^ (3 / 4 : ℝ) ≤ m := by
    have h := mul_le_mul_of_nonneg_left hquarter
      (Real.rpow_nonneg hm0.le (3 / 4 : ℝ))
    rw [hpow] at h
    nlinarith
  have hceil : 8 * (m : ℝ) * Real.log (T : ℝ) ≤ (X : ℝ) := Nat.le_ceil _
  have hceilUpper : (X : ℝ) < 8 * (m : ℝ) * Real.log (T : ℝ) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hXupper : (X : ℝ) ≤ 9 * (m : ℝ) * Real.log (T : ℝ) := by
    nlinarith [hceilUpper, hscale]
  have hXlower : 2 * m ≤ X := by
    have h := mul_le_mul_of_nonneg_left hlog.le hm0.le
    have hr : (2 : ℝ) * (m : ℝ) ≤ X := by nlinarith [hceil, h]
    exact_mod_cast hr
  have hXsquare : X ≤ m^2 := by
    have h1 := mul_le_mul_of_nonneg_left hheight (by positivity : (0 : ℝ) ≤ 9 * (m : ℝ))
    have h2 := mul_le_mul_of_nonneg_left hpowerBound hm0.le
    have hr : (X : ℝ) ≤ (m : ℝ)^2 := by nlinarith [hXupper, h1, h2]
    exact_mod_cast hr
  exact ⟨hXlower, hXsquare, hXupper, hceil⟩

/-- 若每个互异素数都整除某个速度，则它们的乘积整除所有速度的乘积。
实际调用有限互异素数的乘积整除定理，不把乘积整除作为假设。 -/
theorem primeCover_product_dvd (V S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hcover : ∀ p ∈ S, ∃ v ∈ V, p ∣ v) :
    (∏ p ∈ S, p) ∣ ∏ v ∈ V, v := by
  apply Finset.prod_primes_dvd _ (fun p hp => (hS p hp).prime)
  intro p hp
  obtain ⟨v, hv, hpv⟩ := hcover p hp
  exact hpv.trans (dvd_prod_of_mem (fun v : ℕ => v) hv)

/-- 乘积整除和正性给出素数对数总量上界，再用速度高度逐项控制。 -/
theorem primeCover_log_sum_le (V S : Finset ℕ) (T : ℕ)
    (hV : ∀ v ∈ V, 0 < v) (hheight : ∀ v ∈ V, v ≤ T)
    (hS : ∀ p ∈ S, p.Prime) (hcover : ∀ p ∈ S, ∃ v ∈ V, p ∣ v) :
    (∑ p ∈ S, Real.log (p : ℝ)) ≤ (V.card : ℝ) * Real.log (T : ℝ) := by
  have hVprod : 0 < ∏ v ∈ V, v := prod_pos hV
  have hSprod : 0 < ∏ p ∈ S, p := prod_pos (fun p hp => (hS p hp).pos)
  have hle : (∏ p ∈ S, p) ≤ ∏ v ∈ V, v :=
    Nat.le_of_dvd hVprod (primeCover_product_dvd V S hS hcover)
  have hlog := Real.log_le_log (by exact_mod_cast hSprod)
    (by exact_mod_cast hle : ((∏ p ∈ S, p : ℕ) : ℝ) ≤ ((∏ v ∈ V, v : ℕ) : ℝ))
  have hlogS : Real.log ((∏ p ∈ S, p : ℕ) : ℝ) = ∑ p ∈ S, Real.log (p : ℝ) := by
    rw [Nat.cast_prod]
    exact Real.log_prod (fun p hp => by exact_mod_cast (hS p hp).ne_zero)
  have hlogV : Real.log ((∏ v ∈ V, v : ℕ) : ℝ) = ∑ v ∈ V, Real.log (v : ℝ) := by
    rw [Nat.cast_prod]
    exact Real.log_prod (fun v hv => by exact_mod_cast (hV v hv).ne')
  rw [hlogS, hlogV] at hlog
  calc
    _ ≤ ∑ v ∈ V, Real.log (v : ℝ) := hlog
    _ ≤ ∑ _v ∈ V, Real.log (T : ℝ) := by
      apply sum_le_sum
      intro v hv
      exact Real.log_le_log (by exact_mod_cast hV v hv) (by exact_mod_cast hheight v hv)
    _ = _ := by simp

/-- 本论文所需高度范围内的 Bedert 替代结论：正常数与起点均独立于速度集和高度。
先固定好余数常数，再由实际素数乘积的整除排除“所有好素数都命中速度”的可能。
不宣称处理 Bedert 原命题的全部高度范围。 -/
theorem bedert_small_height :
    ∃ b : ℝ, 0 < b ∧ ∃ M : ℕ,
      ∀ (V : Finset ℕ) (T : ℕ),
        (∀ v ∈ V, 0 < v) → M ≤ V.card → 2 ≤ T →
        (∀ v ∈ V, v ≤ T) →
        Real.log (T : ℝ) ≤ (V.card : ℝ) ^ (3 / 4 : ℝ) →
        ∃ t : UnitAddCircle, ∀ v ∈ V,
          1 / (2 * (V.card : ℝ)) + b / ((V.card : ℝ) * Real.log (T : ℝ)) ≤
            dist (v • t) 0 := by
  obtain ⟨c, hc, hc4, M₀, hgood⟩ := primeGoodResidues_log_mass
  let b := c / 9
  refine ⟨b, by dsimp [b]; positivity, max 6561 M₀, ?_⟩
  intro V T hV hM hT hheight hlogheight
  let m := V.card
  have hm6561 : 6561 ≤ m := (le_max_left _ _).trans hM
  have hmM₀ : M₀ ≤ m := (le_max_right _ _).trans hM
  have hmpos : 0 < m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hmT : m ≤ T := positiveSpeeds_card_le_height V T hV hheight
  have hlogm : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have hlogT : 0 < Real.log (T : ℝ) := hlogm.trans_le
    (Real.log_le_log hmR (by exact_mod_cast hmT))
  let X := ⌈8 * (m : ℝ) * Real.log (T : ℝ)⌉₊
  obtain ⟨hXlo, hXhi, hXupper, hXceil⟩ :=
    bedertSmallHeight_level_bounds m T hm6561 hT hlogheight
  have hSp : ∀ p ∈ goodResiduePrimes m X c, p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primesLE (mem_filter.mp hp).1
  have hex : ∃ p ∈ goodResiduePrimes m X c, ∀ v ∈ V, ¬ p ∣ v := by
    by_contra hnone
    push Not at hnone
    have upper := primeCover_log_sum_le V (goodResiduePrimes m X c) T
      hV hheight hSp hnone
    have mass := hgood m X hmM₀ hXlo hXhi
    have hmulpos : 0 < (m : ℝ) * Real.log (T : ℝ) := mul_pos hmR hlogT
    change (∑ p ∈ goodResiduePrimes m X c, Real.log (p : ℝ)) ≤
      (m : ℝ) * Real.log (T : ℝ) at upper
    nlinarith
  obtain ⟨p, hp, havoid⟩ := hex
  obtain ⟨hpLE, hr2, hrc⟩ := mem_filter.mp hp
  have hpprime := Nat.prime_of_mem_primesLE hpLE
  have hpX := Nat.le_of_mem_primesLE hpLE
  have hVne : V.Nonempty := Finset.card_pos.mp hmpos
  obtain ⟨t, ht⟩ := bedert_prime_grid_good_remainder V p c hVne hV hpprime havoid
    hc (by linarith) hr2 hrc
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
  have hpBound : (p : ℝ) ≤ 9 * (m : ℝ) * Real.log (T : ℝ) :=
    (by exact_mod_cast hpX : (p : ℝ) ≤ X).trans hXupper
  have hgain : b / ((m : ℝ) * Real.log (T : ℝ)) ≤ c / (p : ℝ) := by
    apply (div_le_div_iff₀ (mul_pos hmR hlogT) hpR).2
    dsimp [b]
    nlinarith [mul_le_mul_of_nonneg_left hpBound hc.le]
  refine ⟨t, ?_⟩
  intro v hv
  have hvbound := ht v hv
  change 1 / (2 * (m : ℝ)) + b / ((m : ℝ) * Real.log (T : ℝ)) ≤ _
  change 1 / (2 * (m : ℝ)) + c / (p : ℝ) ≤ _ at hvbound
  linarith

#print axioms positiveSpeeds_card_le_height
#print axioms bedertSmallHeight_level_bounds
#print axioms primeCover_product_dvd
#print axioms primeCover_log_sum_le
#print axioms bedert_small_height

end LonelyRunner
