import LonelyRunner.CoverMomentLower

/-!
# 主定理反设中的覆盖约化

对应 `paper/lonely_runner_zh.tex` 第 683–697 行：选取最小基数子覆盖，
除以实际 gcd，保持逐点覆盖及不可约性，再核对近覆盖参数。
-/

namespace LonelyRunner

/-- 论文主定理证明第 687 行：用覆盖子集的最小基数实际取得不可约子覆盖。 -/
theorem irreducibleSubcover_exists (V : Finset ℕ) (δ : ℝ) (hcover : Covers V δ) :
    ∃ W : Finset ℕ, W ⊆ V ∧ IrreducibleCover W δ := by
  classical
  have hex : ∃ n : ℕ, ∃ W : Finset ℕ, W ⊆ V ∧ Covers W δ ∧ W.card = n :=
    ⟨V.card, V, Finset.Subset.refl V, hcover, rfl⟩
  obtain ⟨W, hWV, hWcover, hcard⟩ := Nat.find_spec hex
  refine ⟨W, hWV, hWcover, ?_⟩
  intro S hSW hScover
  have hmin : Nat.find hex ≤ S.card := Nat.find_min' hex
    ⟨S, hSW.subset.trans hWV, hScover, rfl⟩
  have hlt := Finset.card_lt_card hSW
  omega

/-- 逐点覆盖的有限速度集必非空（在圆周零点处应用覆盖）。 -/
theorem covers_nonempty (W : Finset ℕ) (δ : ℝ) (hcover : Covers W δ) : W.Nonempty := by
  obtain ⟨v, hv, ht⟩ := hcover 0
  exact ⟨v, hv⟩

/-- 论文第 695 行：非空正整数速度集的实际最大公因数为正。 -/
theorem positiveSpeeds_gcd_pos (W : Finset ℕ) (hW : W.Nonempty)
    (hpos : ∀ w ∈ W, 0 < w) : 0 < W.gcd id := by
  obtain ⟨w, hw⟩ := hW
  exact Nat.pos_of_dvd_of_pos (Finset.gcd_dvd hw) (hpos w hw)

/-- 论文第 695 行：将速度除以其实际 gcd 后得到的有限集合。 -/
def gcdNormalizedSpeeds (W : Finset ℕ) : Finset ℕ :=
  W.image (fun w => w / W.gcd id)

/-- 归一化映射在原集合上单射：将相等的商乘回 gcd 即恢复原速度。 -/
theorem gcdNormalizedSpeeds_inj (W : Finset ℕ) :
    Set.InjOn (fun w => w / W.gcd id) (W : Set ℕ) := by
  intro w hw z hz heq
  have hwEq : W.gcd id * (w / W.gcd id) = w := by
    simpa [Nat.mul_comm] using Nat.div_mul_cancel (Finset.gcd_dvd hw : W.gcd id ∣ w)
  have hzEq : W.gcd id * (z / W.gcd id) = z := by
    simpa [Nat.mul_comm] using Nat.div_mul_cancel (Finset.gcd_dvd hz : W.gcd id ∣ z)
  change w / W.gcd id = z / W.gcd id at heq
  rw [← hwEq, ← hzEq, heq]

/-- 论文第 695 行：gcd 归一化保持基数。 -/
theorem gcdNormalizedSpeeds_card (W : Finset ℕ) : (gcdNormalizedSpeeds W).card = W.card :=
  Finset.card_image_iff.mpr (gcdNormalizedSpeeds_inj W)

/-- 归一化后乘回 gcd，精确恢复原速度集。 -/
theorem gcdNormalizedSpeeds_image (W : Finset ℕ) :
    (gcdNormalizedSpeeds W).image (fun v => W.gcd id * v) = W := by
  ext w
  constructor
  · intro hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hv
    have heq : W.gcd id * (z / W.gcd id) = z := by
      simpa [Nat.mul_comm] using Nat.div_mul_cancel (Finset.gcd_dvd hz : W.gcd id ∣ z)
    rw [heq]
    exact hz
  · intro hw
    refine Finset.mem_image.mpr ⟨w / W.gcd id, Finset.mem_image.mpr ⟨w, hw, rfl⟩, ?_⟩
    simpa [Nat.mul_comm] using Nat.div_mul_cancel (Finset.gcd_dvd hw : W.gcd id ∣ w)

/-- 非空正整数速度集归一化后仍全为正整数。 -/
theorem gcdNormalizedSpeeds_pos (W : Finset ℕ) (hW : W.Nonempty)
    (hpos : ∀ w ∈ W, 0 < w) : ∀ v ∈ gcdNormalizedSpeeds W, 0 < v := by
  intro v hv
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
  have hd := positiveSpeeds_gcd_pos W hW hpos
  exact Nat.div_pos (Nat.le_of_dvd (hpos w hw) (Finset.gcd_dvd hw)) hd

/-- 论文第 695 行：实际 gcd 归一化后，最大公因数恰为一。
调用 Mathlib 的有限集 gcd 除法定理，并接通真实 image 定义。 -/
theorem gcdNormalizedSpeeds_gcd (W : Finset ℕ) (hW : W.Nonempty)
    (hpos : ∀ w ∈ W, 0 < w) : (gcdNormalizedSpeeds W).gcd id = 1 := by
  obtain ⟨w, hw⟩ := hW
  rw [gcdNormalizedSpeeds, Finset.gcd_image]
  simpa [Function.comp_def] using Finset.gcd_div_id_eq_one hw (hpos w hw).ne'

/-- 正整数倍圆周映射满射：给实代表除以该正整数，再映到圆周。 -/
theorem circle_nsmul_surjective (d : ℕ) (hd : 0 < d) :
    Function.Surjective (fun t : UnitAddCircle => d • t) := by
  intro t
  induction t using Quotient.inductionOn with
  | _ x =>
    refine ⟨((x / (d : ℝ) : ℝ) : UnitAddCircle), ?_⟩
    change d • ((x / (d : ℝ) : ℝ) : UnitAddCircle) = (x : UnitAddCircle)
    rw [← QuotientAddGroup.mk_nsmul]
    congr 1
    rw [nsmul_eq_mul]
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    field_simp

/-- 原 Bohr 集的乘法成员恒等式；定义和闭区间端点完全保持。 -/
theorem mem_bohrSet_mul_iff (d v : ℕ) (δ : ℝ) (t : UnitAddCircle) :
    t ∈ bohrSet (d * v) δ ↔ d • t ∈ bohrSet v δ := by
  change (d * v) • t ∈ closedArc (-δ) (2 * δ) ↔
    v • (d • t) ∈ closedArc (-δ) (2 * δ)
  rw [← mul_nsmul, Nat.mul_comm d v]

/-- 论文第 695 行：正整数尺度下任意有限子族的逐点覆盖等价。
反向恢复原圆周时刻使用已证明的满射性。 -/
theorem covers_scaled_iff (W : Finset ℕ) (d : ℕ) (δ : ℝ) (hd : 0 < d) :
    Covers (W.image (fun v => d * v)) δ ↔ Covers W δ := by
  constructor
  · intro hcover t
    obtain ⟨s, hs⟩ := circle_nsmul_surjective d hd t
    obtain ⟨w, hw, hws⟩ := hcover s
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    refine ⟨v, hv, ?_⟩
    rw [← hs]
    exact (mem_bohrSet_mul_iff d v δ s).mp hws
  · intro hcover t
    obtain ⟨v, hv, hvt⟩ := hcover (d • t)
    exact ⟨d * v, Finset.mem_image_of_mem _ hv, (mem_bohrSet_mul_iff d v δ t).mpr hvt⟩

/-- 论文第 695 行：原速度集与除以 gcd 后的速度集覆盖等价。 -/
theorem covers_gcdNormalizedSpeeds_iff (W : Finset ℕ) (δ : ℝ)
    (hW : W.Nonempty) (hpos : ∀ w ∈ W, 0 < w) :
    Covers (gcdNormalizedSpeeds W) δ ↔ Covers W δ := by
  have h := covers_scaled_iff (gcdNormalizedSpeeds W) (W.gcd id) δ
    (positiveSpeeds_gcd_pos W hW hpos)
  rw [gcdNormalizedSpeeds_image] at h
  exact h.symm

/-- 论文第 695 行：除以 gcd 保留不可约性。若归一化后有真子覆盖，
乘回 gcd 就得到原集的真子覆盖；严格性由基数保持及真子集基数不等式证明。 -/
theorem irreducibleCover_gcdNormalizedSpeeds (W : Finset ℕ) (δ : ℝ)
    (hpos : ∀ w ∈ W, 0 < w) (hirr : IrreducibleCover W δ) :
    IrreducibleCover (gcdNormalizedSpeeds W) δ := by
  have hW := covers_nonempty W δ hirr.1
  have hd := positiveSpeeds_gcd_pos W hW hpos
  refine ⟨(covers_gcdNormalizedSpeeds_iff W δ hW hpos).mpr hirr.1, ?_⟩
  intro S hSV hScover
  let B := S.image (fun v => W.gcd id * v)
  have hBsub : B ⊆ W := by
    rw [← gcdNormalizedSpeeds_image W]
    exact Finset.image_subset_image hSV.subset
  have hcard : B.card < W.card := by
    calc
      B.card ≤ S.card := Finset.card_image_le
      _ < (gcdNormalizedSpeeds W).card := Finset.card_lt_card hSV
      _ = W.card := gcdNormalizedSpeeds_card W
  have hBstrict : B ⊂ W := Finset.ssubset_iff_subset_ne.mpr ⟨hBsub, by
    intro heq
    rw [heq] at hcard
    omega⟩
  exact hirr.2 B hBstrict ((covers_scaled_iff S (W.gcd id) δ hd).mpr hScover)

/-- 论文主定理反设第 684–687 行：`δ₀` 严格介于零和二分之一，
且反设修正量 `n^(-1/2-κ)` 不超过一，包含最小允许值 `n=4`。 -/
theorem coverReduction_radius_bounds (n : ℕ) (κ : ℝ)
    (hn : 4 ≤ n) (hκ : 0 < κ) :
    let x := (n : ℝ) ^ (-(1 / 2 + κ))
    0 < (1 + x) / (2 * (n : ℝ)) ∧
      (1 + x) / (2 * (n : ℝ)) < 1 / 2 ∧ x ≤ 1 := by
  intro x
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hxpos : 0 < x := Real.rpow_pos_of_pos hn0 _
  have hxone : x ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
    (by linarith) (by linarith)
  refine ⟨by positivity, ?_, hxone⟩
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (n : ℝ))).2
  linarith

/-- 论文主定理反设第 687–697 行：实际选取不可约子覆盖并除以 gcd，
得到同一 `δ₀` 下的正整数不可约覆盖及原始反设所需的尺度。

`m≥n/2` 从逐点覆盖的积分推导；`ε>0` 调用已证的覆盖二阶矩下界。
没有速度高度限制，也没有外加的最小性、满射性或严格正超额参数。 -/
theorem coverReduction_nearCover (V₀ : Finset ℕ) (n : ℕ) (κ : ℝ)
    (hV₀ : ∀ v ∈ V₀, 0 < v) (hn : n = V₀.card) (hn4 : 4 ≤ n)
    (hκ : 0 < κ) (_hκ4 : κ < 1 / 4) :
    let δ₀ := (1 + (n : ℝ) ^ (-(1 / 2 + κ))) / (2 * (n : ℝ))
    Covers V₀ δ₀ →
      ∃ V : Finset ℕ,
        (∀ v ∈ V, 0 < v) ∧ IrreducibleCover V δ₀ ∧ V.gcd id = 1 ∧
        let m := V.card
        2 ≤ m ∧ m ≤ n ∧ (n : ℝ) / 2 ≤ (m : ℝ) ∧
        let ε := 2 * δ₀ * (m : ℝ) - 1
        0 < ε ∧ ε ≤ (n : ℝ) ^ (-(1 / 2 + κ)) ∧
          (n : ℝ) ^ (-(1 / 2 + κ)) ≤ (m : ℝ) ^ (-(1 / 2 + κ)) := by
  intro δ₀ hcover
  obtain ⟨hδpos, hδhalf, hxone⟩ := coverReduction_radius_bounds n κ hn4 hκ
  obtain ⟨W, hWV₀, hWirr⟩ := irreducibleSubcover_exists V₀ δ₀ hcover
  have hWpos : ∀ w ∈ W, 0 < w := fun w hw => hV₀ w (hWV₀ hw)
  have hWnonempty := covers_nonempty W δ₀ hWirr.1
  let V := gcdNormalizedSpeeds W
  have hVpos : ∀ v ∈ V, 0 < v := gcdNormalizedSpeeds_pos W hWnonempty hWpos
  have hVirr : IrreducibleCover V δ₀ := irreducibleCover_gcdNormalizedSpeeds W δ₀ hWpos hWirr
  have hgcd : V.gcd id = 1 := gcdNormalizedSpeeds_gcd W hWnonempty hWpos
  let m := V.card
  have hmW : m = W.card := gcdNormalizedSpeeds_card W
  have hmn : m ≤ n := by
    rw [hmW, hn]
    exact Finset.card_le_card hWV₀
  have hmpos : 0 < m := by
    rw [hmW]
    exact Finset.card_pos.mpr hWnonempty
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn4R : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hδeq : 2 * δ₀ * (n : ℝ) = 1 + (n : ℝ) ^ (-(1 / 2 + κ)) := by
    dsimp [δ₀]
    field_simp
  have hδlower := cover_delta_lower_of_covers V δ₀ hVpos hδpos hδhalf hVirr.1 m rfl hmpos
  have hmeasure : (1 : ℝ) ≤ 2 * δ₀ * (m : ℝ) := by
    have h := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (m : ℝ))).1 hδlower
    nlinarith
  have hnm : (n : ℝ) ≤ 2 * (m : ℝ) := by
    have hprod := mul_le_mul_of_nonneg_left hmeasure hnR.le
    have heqm : 2 * δ₀ * (n : ℝ) * (m : ℝ) =
        (1 + (n : ℝ) ^ (-(1 / 2 + κ))) * (m : ℝ) := by rw [hδeq]
    have hxmul := mul_le_mul_of_nonneg_right hxone hmR.le
    nlinarith [hprod, heqm, hxmul]
  have hhalf : (n : ℝ) / 2 ≤ (m : ℝ) := by linarith
  have hm2 : 2 ≤ m := by
    have : (2 : ℝ) ≤ m := by linarith
    exact_mod_cast this
  have hεlower := (coverSecondMoment_and_epsilon_lower_of_covers V δ₀
    hVpos hδpos hδhalf hVirr.1 m rfl hm2).2
  have hεpos : 0 < 2 * δ₀ * (m : ℝ) - 1 :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < 1 / (8 * (m : ℝ))) hεlower
  have hεupper : 2 * δ₀ * (m : ℝ) - 1 ≤ (n : ℝ) ^ (-(1 / 2 + κ)) := by
    have hprod := mul_le_mul_of_nonneg_left hmnR (by positivity : 0 ≤ 2 * δ₀)
    linarith [hδeq, hprod]
  have hpower : (n : ℝ) ^ (-(1 / 2 + κ)) ≤ (m : ℝ) ^ (-(1 / 2 + κ)) :=
    Real.rpow_le_rpow_of_nonpos hmR hmnR (by linarith)
  exact ⟨V, hVpos, hVirr, hgcd, hm2, hmn, hhalf, hεpos, hεupper, hpower⟩

#print axioms irreducibleSubcover_exists
#print axioms gcdNormalizedSpeeds_inj
#print axioms gcdNormalizedSpeeds_gcd
#print axioms covers_gcdNormalizedSpeeds_iff
#print axioms irreducibleCover_gcdNormalizedSpeeds
#print axioms coverReduction_nearCover

end LonelyRunner
