import LonelyRunner.CoverMomentTriple
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-! 论文 `paper/lonely_runner_zh.tex` 第 323–336 行：公共因子项的逆估计。
所有速度都为正整数；`g[Y]` 精确表示 `g*k`、`1≤k≤Y` 的倍数。 -/

namespace LonelyRunner

/-- 论文 `lem:inverse` 第 323 行：有序对的最大公因子和 `S₂(W)`。 -/
noncomputable def inversePairGcdSum (W : Finset ℕ) : ℝ :=
  ∑ a ∈ W, ∑ b ∈ W, (Nat.gcd a b : ℝ) / (max a b : ℝ)

/-- 论文 `lem:inverse` 第 324 行：`g[Y]={g*k : k∈ℕ,1≤k≤Y}`；
`Y` 为实数，右端的界通过自然数到实数的强制转换解释。 -/
def inverseBoundedMultiples (g : ℕ) (Y : ℝ) : Set ℕ :=
  {v | ∃ k : ℕ, 1 ≤ k ∧ (k : ℝ) ≤ Y ∧ v = g * k}

/-- 论文第 324 行：`|W∩g[Y]|` 的有限集合基数。 -/
noncomputable def inverseMultiplesCount (W : Finset ℕ) (g : ℕ) (Y : ℝ) : ℕ := by
  classical
  exact (W.filter (fun v => v ∈ inverseBoundedMultiples g Y)).card

/-- 论文第 324 行：`K_W(Y)`，用 `1≤g≤max(1,max W)` 的有限最大值定义。 -/
noncomputable def inverseK (W : Finset ℕ) (Y : ℝ) : ℕ :=
  (Finset.Icc 1 (max 1 (W.sup id))).sup (fun g => inverseMultiplesCount W g Y)

theorem inverseMultiplesCount_le_inverseK (W : Finset ℕ) (Y : ℝ)
    (g : ℕ) (hg : 0 < g) : inverseMultiplesCount W g Y ≤ inverseK W Y := by
  by_cases hgb : g ≤ max 1 (W.sup id)
  · exact Finset.le_sup (f := fun j => inverseMultiplesCount W j Y)
      (Finset.mem_Icc.mpr ⟨hg, hgb⟩)
  · have hzero : inverseMultiplesCount W g Y = 0 := by
      classical
      unfold inverseMultiplesCount
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_of_forall_notMem
      intro v hv
      obtain ⟨hvW, k, hk1, hkY, rfl⟩ := Finset.mem_filter.mp hv
      have hvmax : g * k ≤ W.sup id := Finset.le_sup (f := id) hvW
      have hgle : g ≤ g * k := Nat.le_mul_of_pos_right g hk1
      omega
    simp [hzero]

/-- 论文第 324、511 行：全体正整数 `g` 上的最大值确实取到，空集也由 `g=1` 处理。 -/
theorem inverseK_attained (W : Finset ℕ) (Y : ℝ) :
    ∃ g : ℕ, 0 < g ∧ inverseMultiplesCount W g Y = inverseK W Y := by
  let I := Finset.Icc 1 (max 1 (W.sup id))
  have hI : I.Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, le_max_left _ _⟩⟩
  obtain ⟨g, hgI, hsup⟩ := Finset.exists_mem_eq_sup I hI
    (fun g => inverseMultiplesCount W g Y)
  refine ⟨g, (Finset.mem_Icc.mp hgI).1, ?_⟩
  exact hsup.symm

/-- 论文第 330 行：本原高度不超过 `Y` 的递增三元组。 -/
noncomputable def inverseSmallTriples (W : Finset ℕ) (Y : ℝ) :
    Finset ((ℕ × ℕ) × ℕ) := by
  classical
  exact (increasingTriples W).filter
    (fun p => (relationC p.1.1 p.1.2 p.2 : ℝ) ≤ Y)

/-- 论文第 330 行：本原高度严格大于 `Y` 的递增三元组。 -/
noncomputable def inverseLargeTriples (W : Finset ℕ) (Y : ℝ) :
    Finset ((ℕ × ℕ) × ℕ) := by
  classical
  exact (increasingTriples W).filter
    (fun p => Y < (relationC p.1.1 p.1.2 p.2 : ℝ))

noncomputable def inverseSmallGcdSum (W : Finset ℕ) (Y : ℝ) : ℝ :=
  ∑ p ∈ inverseSmallTriples W Y, 1 / (relationC p.1.1 p.1.2 p.2 : ℝ)

noncomputable def inverseLargeGcdSum (W : Finset ℕ) (Y : ℝ) : ℝ :=
  ∑ p ∈ inverseLargeTriples W Y, 1 / (relationC p.1.1 p.1.2 p.2 : ℝ)

/-- 论文第 330 行：`G₃(W)` 按本原高度 `≤Y` 与 `>Y` 精确拆分。 -/
theorem tripleGcdSum_eq_small_add_large (W : Finset ℕ) (Y : ℝ)
    (hWpos : ∀ v ∈ W, 0 < v) :
    tripleGcdSum W = inverseSmallGcdSum W Y + inverseLargeGcdSum W Y := by
  classical
  rw [tripleGcdSum_eq_sum_inv_relationC W hWpos]
  unfold inverseSmallGcdSum inverseLargeGcdSum inverseSmallTriples inverseLargeTriples
  simp only [← not_le]
  rw [Finset.sum_filter_add_sum_filter_not]

/-- 论文第 330 行：大高度三元组总贡献至多 `m³/Y`。 -/
theorem inverseLargeGcdSum_le_cube_div (W : Finset ℕ) (Y : ℝ) (m : ℕ)
    (_hWpos : ∀ v ∈ W, 0 < v) (hY : 2 ≤ Y) (hcard : W.card ≤ m) :
    inverseLargeGcdSum W Y ≤ (m : ℝ) ^ 3 / Y := by
  have hYpos : 0 < Y := by linarith
  have hlargeNat : (inverseLargeTriples W Y).card ≤ m ^ 3 := by
    have hsubset : inverseLargeTriples W Y ⊆ increasingTriples W := by
      classical
      exact Finset.filter_subset _ _
    have hpow : W.card ^ 3 ≤ m ^ 3 := by gcongr
    exact (Finset.card_le_card hsubset).trans
      ((increasingTriples_card_le_cube W).trans hpow)
  have hlarge : ((inverseLargeTriples W Y).card : ℝ) ≤ (m : ℝ) ^ 3 := by
    exact_mod_cast hlargeNat
  unfold inverseLargeGcdSum
  calc
    (∑ p ∈ inverseLargeTriples W Y,
        1 / (relationC p.1.1 p.1.2 p.2 : ℝ)) ≤
      ∑ _p ∈ inverseLargeTriples W Y, 1 / Y := by
        apply Finset.sum_le_sum
        intro p hp
        have hpLarge : Y < (relationC p.1.1 p.1.2 p.2 : ℝ) := by
          classical
          exact (Finset.mem_filter.mp hp).2
        have hCpos : (0 : ℝ) < relationC p.1.1 p.1.2 p.2 := by linarith
        apply (div_le_div_iff₀ hCpos hYpos).2
        nlinarith
    _ = ((inverseLargeTriples W Y).card : ℝ) / Y := by
      simp [div_eq_mul_inv]
    _ ≤ (m : ℝ) ^ 3 / Y := by
      exact div_le_div_of_nonneg_right hlarge hYpos.le

/-- 论文第 330 行：固定 `a<c`，取 `D=gcd(a,c)`、`q=c/D`、
`d=D/gcd(D,b)`；则 `d∣D`、本原高度为 `qd`，且中间速度
属于精确的正倍数集合 `(D/d)[qd]`。 -/
theorem inverse_fixed_pair_arithmetic (a b c : ℕ)
    (_ha : 0 < a) (hb : 0 < b) (hbc : b < c) :
    let D := Nat.gcd a c
    let q := c / D
    let d := D / Nat.gcd D b
    d ∣ D ∧ relationC a b c = q * d ∧
      b ∈ inverseBoundedMultiples (D / d) ((q * d : ℕ) : ℝ) := by
  dsimp
  let D := Nat.gcd a c
  let E := Nat.gcd D b
  let q := c / D
  let d := D / E
  have hDpos : 0 < D := Nat.gcd_pos_of_pos_right a (lt_trans hb hbc)
  have hEpos : 0 < E := Nat.gcd_pos_of_pos_left b hDpos
  have hdD : D ∣ c := Nat.gcd_dvd_right a c
  have hdE : E ∣ D := Nat.gcd_dvd_left D b
  have hEb : E ∣ b := Nat.gcd_dvd_right D b
  have hDmul : d * E = D := Nat.div_mul_cancel hdE
  have hcMul : q * D = c := Nat.div_mul_cancel hdD
  have hdpos : 0 < d := Nat.div_pos (Nat.le_of_dvd hDpos hdE) hEpos
  have hGcd : relationGcd a b c = E := by
    dsimp [relationGcd, E, D]
    ac_rfl
  have hcEq : c = (q * d) * E := by
    calc
      c = q * D := hcMul.symm
      _ = q * (d * E) := by rw [hDmul]
      _ = (q * d) * E := by ring
  have hDdiv : D / d = E := by
    rw [← hDmul, Nat.mul_div_cancel_left E hdpos]
  have hC : relationC a b c = q * d := by
    rw [relationC, hGcd, hcEq, mul_comm (q * d) E,
      Nat.mul_div_cancel_left (q * d) hEpos]
  have hddvd : d ∣ D := ⟨E, hDmul.symm⟩
  let k := b / E
  have hkMul : k * E = b := Nat.div_mul_cancel hEb
  have hkpos : 1 ≤ k := by
    by_contra h
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos h
    have hb0 : b = 0 := by simpa [hk0] using hkMul.symm
    omega
  have hkbc : k * E ≤ (q * d) * E := by
    rw [hkMul, ← hcEq]
    omega
  have hkle : k ≤ q * d := Nat.le_of_mul_le_mul_right hkbc hEpos
  refine ⟨hddvd, hC, ?_⟩
  refine ⟨k, hkpos, ?_, ?_⟩
  · exact_mod_cast hkle
  · rw [hDdiv]
    simpa [mul_comm] using hkMul.symm

private def inversePairD (a c : ℕ) : ℕ := Nat.gcd a c
private def inversePairQ (a c : ℕ) : ℕ := c / inversePairD a c
private def inverseMiddleD (a b c : ℕ) : ℕ :=
  inversePairD a c / Nat.gcd (inversePairD a c) b

/-- 论文第 330–332 行：固定 `a<c` 与 `d` 后，满足小高度条件的中间速度集合。 -/
noncomputable def inverseMiddleFiber (W : Finset ℕ) (Y : ℝ)
    (a c d : ℕ) : Finset ℕ := by
  classical
  exact W.filter (fun b => a < b ∧ b < c ∧
    (relationC a b c : ℝ) ≤ Y ∧ inverseMiddleD a b c = d)

/-- 论文第 331 行：固定 `d` 的中间速度数不超过真实倍数最大值 `K_W(Y)`。 -/
theorem inverseMiddleFiber_card_le_K (W : Finset ℕ) (Y : ℝ)
    (a c d : ℕ) (ha : 0 < a) :
    (inverseMiddleFiber W Y a c d).card ≤ inverseK W Y := by
  classical
  by_cases hF : (inverseMiddleFiber W Y a c d).Nonempty
  · obtain ⟨b₀, hb₀⟩ := hF
    obtain ⟨hb₀W, hab₀, hbc₀, hheight₀, hd₀⟩ :
        b₀ ∈ W ∧ a < b₀ ∧ b₀ < c ∧
          (relationC a b₀ c : ℝ) ≤ Y ∧ inverseMiddleD a b₀ c = d := by
      simpa [inverseMiddleFiber] using hb₀
    let g := inversePairD a c / d
    have hmem₀ : b₀ ∈ inverseBoundedMultiples g Y := by
      have hdata := inverse_fixed_pair_arithmetic a b₀ c ha (lt_trans ha hab₀) hbc₀
      dsimp [inversePairD, inversePairQ, inverseMiddleD] at g hd₀ ⊢
      dsimp at hdata
      rw [hd₀] at hdata
      obtain ⟨_, hC, k, hk1, hkq, hkEq⟩ := hdata
      exact ⟨k, hk1, hkq.trans (by simpa [hC] using hheight₀), hkEq⟩
    have hg : 0 < g := by
      obtain ⟨k, _, _, hkEq⟩ := hmem₀
      by_contra h
      have hg0 : g = 0 := Nat.eq_zero_of_not_pos h
      have hb0 : b₀ = 0 := by simpa [hg0] using hkEq
      omega
    have hsubset : inverseMiddleFiber W Y a c d ⊆
        W.filter (fun b => b ∈ inverseBoundedMultiples g Y) := by
      intro b hb
      obtain ⟨hbW, hab, hbc, hheight, hd⟩ :
          b ∈ W ∧ a < b ∧ b < c ∧
            (relationC a b c : ℝ) ≤ Y ∧ inverseMiddleD a b c = d := by
        simpa [inverseMiddleFiber] using hb
      apply Finset.mem_filter.mpr
      refine ⟨hbW, ?_⟩
      have hdata := inverse_fixed_pair_arithmetic a b c ha (lt_trans ha hab) hbc
      dsimp [inversePairD, inversePairQ, inverseMiddleD] at g hd ⊢
      dsimp at hdata
      rw [hd] at hdata
      obtain ⟨_, hC, k, hk1, hkq, hkEq⟩ := hdata
      exact ⟨k, hk1, hkq.trans (by simpa [hC] using hheight), hkEq⟩
    exact (Finset.card_le_card hsubset).trans
      (inverseMultiplesCount_le_inverseK W Y g hg)
  · have hzero : inverseMiddleFiber W Y a c d = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hF
    simp [hzero]

private noncomputable def inverseMiddleSet (W : Finset ℕ) (Y : ℝ)
    (a c : ℕ) : Finset ℕ := by
  classical
  exact W.filter (fun b => a < b ∧ b < c ∧ (relationC a b c : ℝ) ≤ Y)

private theorem inverseMiddleFiber_eq_filter (W : Finset ℕ) (Y : ℝ)
    (a c d : ℕ) :
    inverseMiddleFiber W Y a c d =
      (inverseMiddleSet W Y a c).filter (fun b => inverseMiddleD a b c = d) := by
  classical
  ext b
  simp [inverseMiddleFiber, inverseMiddleSet, and_assoc]

private theorem inverseMiddleD_mem_Icc_floor (W : Finset ℕ) (Y : ℝ)
    (a c b : ℕ) (ha : 0 < a) (hb : b ∈ inverseMiddleSet W Y a c) :
    inverseMiddleD a b c ∈ Finset.Icc 1 ⌊Y⌋₊ := by
  classical
  obtain ⟨hbW, hab, hbc, hheight⟩ :
      b ∈ W ∧ a < b ∧ b < c ∧ (relationC a b c : ℝ) ≤ Y := by
    simpa [inverseMiddleSet] using hb
  have hdata := inverse_fixed_pair_arithmetic a b c ha (lt_trans ha hab) hbc
  dsimp [inversePairD, inversePairQ, inverseMiddleD] at hdata ⊢
  obtain ⟨hddvd, hC, _⟩ := hdata
  let D := Nat.gcd a c
  let d := D / Nat.gcd D b
  let q := c / D
  change d ∣ D at hddvd
  change relationC a b c = q * d at hC
  have hDpos : 0 < D := Nat.gcd_pos_of_pos_right a (lt_trans (lt_trans ha hab) hbc)
  have hdpos : 0 < d := by
    by_contra h
    have hd0 : d = 0 := Nat.eq_zero_of_not_pos h
    rw [hd0] at hddvd
    simp at hddvd
    omega
  have hqpos : 0 < q := Nat.div_pos
    (Nat.le_of_dvd (lt_trans (lt_trans ha hab) hbc) (Nat.gcd_dvd_right a c)) hDpos
  have hdq : d ≤ q * d := by nlinarith
  have hdY : (d : ℝ) ≤ Y := by
    have hcast : (d : ℝ) ≤ (q * d : ℕ) := by exact_mod_cast hdq
    rw [← hC] at hcast
    exact hcast.trans hheight
  exact Finset.mem_Icc.mpr ⟨hdpos, Nat.le_floor hdY⟩

private theorem inverseMiddleSet_sum_le_K_harmonic (W : Finset ℕ) (Y : ℝ)
    (a c : ℕ) (ha : 0 < a) (hc : 0 < c) :
    (∑ b ∈ inverseMiddleSet W Y a c, 1 / (relationC a b c : ℝ)) ≤
      (inverseK W Y : ℝ) / (inversePairQ a c : ℝ) *
        ∑ d ∈ Finset.Icc 1 ⌊Y⌋₊, 1 / (d : ℝ) := by
  classical
  let I := Finset.Icc 1 ⌊Y⌋₊
  let M := inverseMiddleSet W Y a c
  let q := inversePairQ a c
  have hq : 0 < q := by
    dsimp [q, inversePairQ, inversePairD]
    exact Nat.div_pos (Nat.le_of_dvd hc (Nat.gcd_dvd_right a c))
      (Nat.gcd_pos_of_pos_right a hc)
  have hgroup : (∑ b ∈ M, 1 / (relationC a b c : ℝ)) =
      ∑ d ∈ I, ∑ b ∈ inverseMiddleFiber W Y a c d,
        1 / (relationC a b c : ℝ) := by
    have hm : ∀ b ∈ M, inverseMiddleD a b c ∈ I := by
      intro b hb
      exact inverseMiddleD_mem_Icc_floor W Y a c b ha hb
    simpa only [M, I, inverseMiddleFiber_eq_filter] using
      (Finset.sum_fiberwise_of_maps_to hm
        (fun b => 1 / (relationC a b c : ℝ))).symm
  rw [hgroup]
  calc
    (∑ d ∈ I, ∑ b ∈ inverseMiddleFiber W Y a c d,
        1 / (relationC a b c : ℝ)) ≤
        ∑ d ∈ I, (inverseK W Y : ℝ) / (q : ℝ) * (1 / (d : ℝ)) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
      have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
      have hdposR : (0 : ℝ) < d := by exact_mod_cast hdpos
      calc
        (∑ b ∈ inverseMiddleFiber W Y a c d, 1 / (relationC a b c : ℝ)) =
            ((inverseMiddleFiber W Y a c d).card : ℝ) / ((q : ℝ) * d) := by
          have hterm : ∀ b ∈ inverseMiddleFiber W Y a c d,
              (relationC a b c : ℝ) = (q : ℝ) * d := by
            intro b hb
            obtain ⟨_, hab, hbc, _, hdb⟩ :
                b ∈ W ∧ a < b ∧ b < c ∧
                (relationC a b c : ℝ) ≤ Y ∧ inverseMiddleD a b c = d := by
              simpa [inverseMiddleFiber] using hb
            have hdata := inverse_fixed_pair_arithmetic a b c ha
              (lt_trans ha hab) hbc
            dsimp [inversePairD, inversePairQ, inverseMiddleD] at q hdb ⊢
            dsimp at hdata
            rw [hdb] at hdata
            exact_mod_cast hdata.2.1
          calc
            (∑ b ∈ inverseMiddleFiber W Y a c d, 1 / (relationC a b c : ℝ)) =
                ∑ _b ∈ inverseMiddleFiber W Y a c d, 1 / ((q : ℝ) * d) := by
              apply Finset.sum_congr rfl
              intro b hb
              rw [hterm b hb]
            _ = ((inverseMiddleFiber W Y a c d).card : ℝ) / ((q : ℝ) * d) := by
              simp [div_eq_mul_inv]
        _ ≤ (inverseK W Y : ℝ) / ((q : ℝ) * d) := by
          apply div_le_div_of_nonneg_right
          · exact_mod_cast inverseMiddleFiber_card_le_K W Y a c d ha
          · positivity
        _ = (inverseK W Y : ℝ) / (q : ℝ) * (1 / (d : ℝ)) := by
          field_simp
    _ = (inverseK W Y : ℝ) / (inversePairQ a c : ℝ) *
          ∑ d ∈ Finset.Icc 1 ⌊Y⌋₊, 1 / (d : ℝ) := by
      simp [I, q, Finset.mul_sum]
/-- 论文 `lem:inverse` 第 332 行：实数上界的调和和由 `log(2Y)` 控制。 -/
theorem inverse_harmonic_le_log (Y : ℝ) (hY : 2 ≤ Y) :
    (∑ d ∈ Finset.Icc 1 ⌊Y⌋₊, 1 / (d : ℝ)) ≤
      2 * Real.log (2 * Y) := by
  have hYpos : 0 < Y := by linarith
  have hlogY : 0 ≤ Real.log Y := Real.log_nonneg (by linarith)
  have hlog2 : 1 / 2 ≤ Real.log (2 : ℝ) := by
    have h := Real.log_two_gt_d9
    norm_num at h ⊢
    linarith
  have hmul : Real.log (2 * Y) = Real.log 2 + Real.log Y := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hYpos)]
  have hharm : (∑ d ∈ Finset.Icc 1 ⌊Y⌋₊, 1 / (d : ℝ)) ≤
      1 + Real.log Y := by
    have h := harmonic_floor_le_one_add_log Y (by linarith)
    simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
      Rat.cast_natCast, one_div] using h
  rw [hmul]
  linarith

private theorem inverseSmallGcdSum_eq_pair_middle (W : Finset ℕ) (Y : ℝ) :
    inverseSmallGcdSum W Y =
      ∑ a ∈ W, ∑ c ∈ W,
        ∑ b ∈ inverseMiddleSet W Y a c, 1 / (relationC a b c : ℝ) := by
  classical
  unfold inverseSmallGcdSum inverseSmallTriples increasingTriples inverseMiddleSet
  simp only [Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro b hb
  by_cases h₁ : a < b ∧ b < c <;>
    by_cases h₂ : (relationC a b c : ℝ) ≤ Y <;>
      simp [h₁, h₂]

private theorem inverse_pair_middle_le_S2_term (W : Finset ℕ) (Y : ℝ)
    (a c : ℕ) (ha : 0 < a) (hc : 0 < c) (hY : 2 ≤ Y) :
    (∑ b ∈ inverseMiddleSet W Y a c, 1 / (relationC a b c : ℝ)) ≤
      2 * (inverseK W Y : ℝ) *
        ((Nat.gcd a c : ℝ) / (max a c : ℝ)) * Real.log (2 * Y) := by
  classical
  by_cases hac : a < c
  · let D := Nat.gcd a c
    let q := inversePairQ a c
    have hDpos : 0 < D := Nat.gcd_pos_of_pos_right a hc
    have hqpos : 0 < q := Nat.div_pos
      (Nat.le_of_dvd hc (Nat.gcd_dvd_right a c)) hDpos
    have hqMul : q * D = c := Nat.div_mul_cancel (Nat.gcd_dvd_right a c)
    have hqMulR : (q : ℝ) * (D : ℝ) = (c : ℝ) := by exact_mod_cast hqMul
    have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
    have hcR : (0 : ℝ) < c := by exact_mod_cast hc
    have hK : (0 : ℝ) ≤ inverseK W Y := Nat.cast_nonneg _
    have hH := inverseMiddleSet_sum_le_K_harmonic W Y a c ha hc
    have hHarm := inverse_harmonic_le_log Y hY
    calc
      (∑ b ∈ inverseMiddleSet W Y a c, 1 / (relationC a b c : ℝ)) ≤
          (inverseK W Y : ℝ) / (q : ℝ) *
            ∑ d ∈ Finset.Icc 1 ⌊Y⌋₊, 1 / (d : ℝ) := hH
      _ ≤ (inverseK W Y : ℝ) / (q : ℝ) * (2 * Real.log (2 * Y)) := by
        exact mul_le_mul_of_nonneg_left hHarm (div_nonneg hK hqR.le)
      _ = 2 * (inverseK W Y : ℝ) *
          ((Nat.gcd a c : ℝ) / (max a c : ℝ)) * Real.log (2 * Y) := by
        have hacR : (a : ℝ) < c := by exact_mod_cast hac
        rw [max_eq_right_of_lt hacR]
        change (inverseK W Y : ℝ) / (q : ℝ) * (2 * Real.log (2 * Y)) =
          2 * (inverseK W Y : ℝ) * ((D : ℝ) / c) * Real.log (2 * Y)
        have hqInv : (1 : ℝ) / (q : ℝ) = (D : ℝ) / (c : ℝ) := by
          apply (div_eq_div_iff (ne_of_gt hqR) (ne_of_gt hcR)).2
          nlinarith [hqMulR]
        calc
          (inverseK W Y : ℝ) / (q : ℝ) * (2 * Real.log (2 * Y)) =
              (inverseK W Y : ℝ) * (1 / (q : ℝ)) *
                (2 * Real.log (2 * Y)) := by ring
          _ = (inverseK W Y : ℝ) * ((D : ℝ) / c) *
                (2 * Real.log (2 * Y)) := by rw [hqInv]
          _ = 2 * (inverseK W Y : ℝ) * ((D : ℝ) / c) *
                Real.log (2 * Y) := by ring
  · have hzero : inverseMiddleSet W Y a c = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro b hb
      have hab : a < b := (Finset.mem_filter.mp hb).2.1
      have hbc : b < c := (Finset.mem_filter.mp hb).2.2.1
      omega
    simp only [hzero, Finset.sum_empty]
    have hlog : 0 ≤ Real.log (2 * Y) := Real.log_nonneg (by nlinarith)
    positivity

/-- 论文 `lem:inverse` 第 330–333 行：小高度三元组由有序对的 `S₂` 控制。 -/
theorem inverseSmallGcdSum_le_pairGcdSum (W : Finset ℕ) (Y : ℝ)
    (hWpos : ∀ v ∈ W, 0 < v) (hY : 2 ≤ Y) :
    inverseSmallGcdSum W Y ≤
      2 * (inverseK W Y : ℝ) * inversePairGcdSum W * Real.log (2 * Y) := by
  rw [inverseSmallGcdSum_eq_pair_middle]
  calc
    (∑ a ∈ W, ∑ c ∈ W,
        ∑ b ∈ inverseMiddleSet W Y a c, 1 / (relationC a b c : ℝ)) ≤
        ∑ a ∈ W, ∑ c ∈ W,
          2 * (inverseK W Y : ℝ) *
            ((Nat.gcd a c : ℝ) / (max a c : ℝ)) * Real.log (2 * Y) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro c hc
      exact inverse_pair_middle_le_S2_term W Y a c (hWpos a ha) (hWpos c hc) hY
    _ = 2 * (inverseK W Y : ℝ) * inversePairGcdSum W *
          Real.log (2 * Y) := by
      unfold inversePairGcdSum
      simp only [Finset.mul_sum, Finset.sum_mul]

/-- 论文 `lem:inverse` 第 323–336 行：`G₃(W)` 的逆向估计，绝对常数取 `2`。
`m` 是实数基数上界所用的自然数；`W` 的每个速度严格为正。 -/
theorem inverseGcdTripleBound (W : Finset ℕ) (m : ℕ) (Y : ℝ)
    (hWpos : ∀ v ∈ W, 0 < v) (hcard : W.card ≤ m) (hY : 2 ≤ Y) :
    tripleGcdSum W ≤
      2 * (inverseK W Y : ℝ) * inversePairGcdSum W * Real.log (2 * Y) +
        (m : ℝ) ^ 3 / Y := by
  rw [tripleGcdSum_eq_small_add_large W Y hWpos]
  exact add_le_add
    (inverseSmallGcdSum_le_pairGcdSum W Y hWpos hY)
    (inverseLargeGcdSum_le_cube_div W Y m hWpos hY hcard)

/-- 论文 `lem:inverse`：存在独立于速度高度、`W`、`m`、`Y` 的正绝对常数。
此处具体给出 `C=2`。 -/
theorem inverseGcdTripleBound_exists_constant :
    ∃ C : ℝ, 0 < C ∧
      ∀ (W : Finset ℕ) (m : ℕ) (Y : ℝ),
        (∀ v ∈ W, 0 < v) → W.card ≤ m → 2 ≤ Y →
          tripleGcdSum W ≤
            C * (inverseK W Y : ℝ) * inversePairGcdSum W * Real.log (2 * Y) +
              (m : ℝ) ^ 3 / Y := by
  refine ⟨2, by norm_num, ?_⟩
  intro W m Y hWpos hcard hY
  exact inverseGcdTripleBound W m Y hWpos hcard hY

#print axioms inverseGcdTripleBound
#print axioms inverseGcdTripleBound_exists_constant
end LonelyRunner
