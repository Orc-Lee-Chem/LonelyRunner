import LonelyRunner.CoverMoments
import LonelyRunner.BohrTripleIntersection

/-! 论文 `paper/lonely_runner_zh.tex` 第 468–473 行：三阶矩的有限三元组展开。 -/

namespace LonelyRunner

open MeasureTheory

/-- 论文第 468–469 行：有限速度集中的严格递增三元组 `(a,b,c)`。 -/
def increasingTriples (W : Finset ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  ((W ×ˢ W) ×ˢ W).filter (fun p => p.1.1 < p.1.2 ∧ p.1.2 < p.2)

theorem mem_increasingTriples_iff (W : Finset ℕ) (p : (ℕ × ℕ) × ℕ) :
    p ∈ increasingTriples W ↔
      p.1.1 ∈ W ∧ p.1.2 ∈ W ∧ p.2 ∈ W ∧ p.1.1 < p.1.2 ∧ p.1.2 < p.2 := by
  simp [increasingTriples, and_assoc]

/-- 论文第 468 行：有序、两两不同的三元组。 -/
def orderedDistinctTriples (W : Finset ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  (W.offDiag ×ˢ W).filter (fun p => p.2 ≠ p.1.1 ∧ p.2 ≠ p.1.2)

theorem mem_orderedDistinctTriples_iff (W : Finset ℕ) (p : (ℕ × ℕ) × ℕ) :
    p ∈ orderedDistinctTriples W ↔
      p.1.1 ∈ W ∧ p.1.2 ∈ W ∧ p.2 ∈ W ∧
        p.1.1 ≠ p.1.2 ∧ p.1.1 ≠ p.2 ∧ p.1.2 ≠ p.2 := by
  simp [orderedDistinctTriples, and_assoc, and_comm, and_left_comm, ne_comm]

private theorem indicator_cube_idem (v : ℕ) (δ : ℝ) (t : UnitAddCircle) :
    bohrIndicator v δ t * bohrIndicator v δ t = bohrIndicator v δ t := by
  by_cases ht : t ∈ bohrSet v δ <;> simp [bohrIndicator, ht]

private theorem sum_idem_pair (W : Finset ℕ) (f : ℕ → ℝ)
    (hf : ∀ v ∈ W, f v * f v = f v) :
    (∑ v ∈ W, f v) * ((∑ v ∈ W, f v) - 1) =
      ∑ p ∈ W.offDiag, f p.1 * f p.2 := by
  classical
  have hdiag : (∑ p ∈ W.diag, f p.1 * f p.2) = ∑ v ∈ W, f v := by
    rw [Finset.sum_diag]
    exact Finset.sum_congr rfl hf
  have hsplit :
      (∑ p ∈ W ×ˢ W, f p.1 * f p.2) =
        (∑ p ∈ W.diag, f p.1 * f p.2) +
          (∑ p ∈ W.offDiag, f p.1 * f p.2) := by
    rw [← Finset.sum_union (Finset.disjoint_diag_offDiag W), Finset.diag_union_offDiag]
  calc
    (∑ v ∈ W, f v) * ((∑ v ∈ W, f v) - 1) =
        (∑ v ∈ W, f v) * (∑ v ∈ W, f v) - (∑ v ∈ W, f v) := by ring
    _ = (∑ p ∈ W ×ˢ W, f p.1 * f p.2) -
          (∑ p ∈ W.diag, f p.1 * f p.2) := by
      rw [Finset.sum_mul_sum, Finset.sum_product, hdiag]
    _ = ∑ p ∈ W.offDiag, f p.1 * f p.2 := by rw [hsplit]; ring

private theorem pair_mul_remaining (W : Finset ℕ) (f : ℕ → ℝ)
    (hf : ∀ v ∈ W, f v * f v = f v)
    (a b : ℕ) (ha : a ∈ W) (hb : b ∈ W) (hab : a ≠ b) :
    f a * f b * ((∑ v ∈ W, f v) - 2) =
      ∑ c ∈ W, if c ≠ a ∧ c ≠ b then f a * f b * f c else 0 := by
  classical
  let W' := (W.erase a).erase b
  have hb' : b ∈ W.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩
  have hsum : (∑ v ∈ W, f v) = f a + f b + ∑ v ∈ W', f v := by
    have h1 := Finset.add_sum_erase W f ha
    have h2 := Finset.add_sum_erase (W.erase a) f hb'
    dsimp [W']
    linarith
  have hrest :
      (∑ c ∈ W, if c ≠ a ∧ c ≠ b then f a * f b * f c else 0) =
        f a * f b * (∑ c ∈ W', f c) := by
    rw [← Finset.sum_filter, ← Finset.mul_sum]
    have hfilter : W.filter (fun c => c ≠ a ∧ c ≠ b) = W' := by
      ext c
      simp [W', ne_comm, and_comm, and_left_comm, and_assoc]
    rw [hfilter]
  rw [hrest, hsum]
  have hfa := hf a ha
  have hfb := hf b hb
  calc
    f a * f b * (f a + f b + (∑ v ∈ W', f v) - 2) =
        (f a * f a) * f b + f a * (f b * f b) +
          f a * f b * (∑ v ∈ W', f v) - 2 * (f a * f b) := by ring
    _ = f a * f b * (∑ v ∈ W', f v) := by rw [hfa, hfb]; ring

/-- 论文第 468 行：三阶下降阶乘在每个圆周点展开为两两不同的有序三元组。 -/
theorem coverThirdMoment_pointwise_ordered (W : Finset ℕ) (δ : ℝ)
    (t : UnitAddCircle) :
    coverMultiplicity W δ t * (coverMultiplicity W δ t - 1) *
        (coverMultiplicity W δ t - 2) =
      ∑ p ∈ orderedDistinctTriples W,
        bohrIndicator p.1.1 δ t * bohrIndicator p.1.2 δ t *
          bohrIndicator p.2 δ t := by
  classical
  let f : ℕ → ℝ := fun v => bohrIndicator v δ t
  have hf : ∀ v ∈ W, f v * f v = f v := fun v _ => indicator_cube_idem v δ t
  have hpair := sum_idem_pair W f hf
  change (∑ v ∈ W, f v) * ((∑ v ∈ W, f v) - 1) *
    ((∑ v ∈ W, f v) - 2) = _
  rw [hpair, Finset.sum_mul]
  calc
    (∑ p ∈ W.offDiag, f p.1 * f p.2 * ((∑ v ∈ W, f v) - 2)) =
        ∑ p ∈ W.offDiag, ∑ c ∈ W,
          if c ≠ p.1 ∧ c ≠ p.2 then f p.1 * f p.2 * f c else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      obtain ⟨ha, hb, hab⟩ := Finset.mem_offDiag.mp hp
      exact pair_mul_remaining W f hf p.1 p.2 ha hb hab
    _ = ∑ p ∈ orderedDistinctTriples W,
          f p.1.1 * f p.1.2 * f p.2 := by
      simp only [orderedDistinctTriples, Finset.sum_filter, Finset.sum_product]

private theorem tripleCase132_eq_123 (W : Finset ℕ) (f : ℕ → ℝ) :
    (∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W,
      if a < c ∧ c < b then f a * f b * f c else 0) =
      ∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W,
        if a < b ∧ b < c then f a * f b * f c else 0 := by
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  split_ifs <;> ring

private def tripleSum (W : Finset ℕ) (F : ℕ → ℕ → ℕ → ℝ) : ℝ :=
  ∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, F a b c

private theorem tripleSum_swap12 (W : Finset ℕ) (F : ℕ → ℕ → ℕ → ℝ) :
    tripleSum W (fun a b c => F b a c) = tripleSum W F := by
  simp only [tripleSum]
  rw [Finset.sum_comm]

private theorem tripleSum_swap23 (W : Finset ℕ) (F : ℕ → ℕ → ℕ → ℝ) :
    tripleSum W (fun a b c => F a c b) = tripleSum W F := by
  simp only [tripleSum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]

private theorem triple_order_cases (a b c : ℕ) (x : ℝ) :
    (if a ≠ b ∧ a ≠ c ∧ b ≠ c then x else 0) =
      (if a < b ∧ b < c then x else 0) +
      (if a < c ∧ c < b then x else 0) +
      (if b < a ∧ a < c then x else 0) +
      (if b < c ∧ c < a then x else 0) +
      (if c < a ∧ a < b then x else 0) +
      (if c < b ∧ b < a then x else 0) := by
  split_ifs <;> simp_all <;> omega

private theorem ordered_triple_sum_eq_six_increasing
    (W : Finset ℕ) (f : ℕ → ℝ) :
    (∑ p ∈ orderedDistinctTriples W, f p.1.1 * f p.1.2 * f p.2) =
      6 * ∑ p ∈ increasingTriples W, f p.1.1 * f p.1.2 * f p.2 := by
  classical
  let s123 := tripleSum W (fun a b c =>
    if a < b ∧ b < c then f a * f b * f c else 0)
  let s132 := tripleSum W (fun a b c =>
    if a < c ∧ c < b then f a * f b * f c else 0)
  let s213 := tripleSum W (fun a b c =>
    if b < a ∧ a < c then f a * f b * f c else 0)
  let s231 := tripleSum W (fun a b c =>
    if b < c ∧ c < a then f a * f b * f c else 0)
  let s312 := tripleSum W (fun a b c =>
    if c < a ∧ a < b then f a * f b * f c else 0)
  let s321 := tripleSum W (fun a b c =>
    if c < b ∧ b < a then f a * f b * f c else 0)
  have h132 : s132 = s123 := tripleCase132_eq_123 W f
  have h213 : s213 = s123 := by
    calc
      s213 = tripleSum W (fun a b c =>
          if b < a ∧ a < c then f b * f a * f c else 0) := by
        dsimp [s213]
        congr 1
        funext a b c
        split_ifs <;> ring
      _ = s123 := tripleSum_swap12 W _
  have h231 : s231 = s132 := by
    calc
      s231 = tripleSum W (fun a b c =>
          if b < c ∧ c < a then f b * f a * f c else 0) := by
        dsimp [s231]
        congr 1
        funext a b c
        split_ifs <;> ring
      _ = s132 := tripleSum_swap12 W _
  have h312 : s312 = s213 := by
    calc
      s312 = tripleSum W (fun a b c =>
          if c < a ∧ a < b then f a * f c * f b else 0) := by
        dsimp [s312]
        congr 1
        funext a b c
        split_ifs <;> ring
      _ = s213 := tripleSum_swap23 W _
  have h321 : s321 = s312 := by
    calc
      s321 = tripleSum W (fun a b c =>
          if c < b ∧ b < a then f b * f a * f c else 0) := by
        dsimp [s321]
        congr 1
        funext a b c
        split_ifs <;> ring
      _ = s312 := tripleSum_swap12 W _
  have hO : orderedDistinctTriples W =
      (((W ×ˢ W) ×ˢ W).filter (fun p : (ℕ × ℕ) × ℕ =>
        p.1.1 ≠ p.1.2 ∧ p.1.1 ≠ p.2 ∧ p.1.2 ≠ p.2)) := by
    ext p
    simp [mem_orderedDistinctTriples_iff, and_comm, and_left_comm, and_assoc, ne_comm]
  have hordered :
      (∑ p ∈ orderedDistinctTriples W, f p.1.1 * f p.1.2 * f p.2) =
        tripleSum W (fun a b c =>
          if a ≠ b ∧ a ≠ c ∧ b ≠ c then f a * f b * f c else 0) := by
    rw [hO]
    simp only [tripleSum, Finset.sum_filter, Finset.sum_product]
  have hcases :
      tripleSum W (fun a b c =>
        if a ≠ b ∧ a ≠ c ∧ b ≠ c then f a * f b * f c else 0) =
          s123 + s132 + s213 + s231 + s312 + s321 := by
    simp only [tripleSum]
    simp_rw [triple_order_cases, Finset.sum_add_distrib]
    dsimp [s123, s132, s213, s231, s312, s321, tripleSum]
  have hinc : (∑ p ∈ increasingTriples W,
      f p.1.1 * f p.1.2 * f p.2) = s123 := by
    simp only [s123, increasingTriples, tripleSum,
      Finset.sum_filter, Finset.sum_product]
  calc
    (∑ p ∈ orderedDistinctTriples W, f p.1.1 * f p.1.2 * f p.2) =
        s123 + s132 + s213 + s231 + s312 + s321 := hordered.trans hcases
    _ = 6 * s123 := by
      rw [h321, h312, h231, h213, h132]
      ring
    _ = 6 * ∑ p ∈ increasingTriples W, f p.1.1 * f p.1.2 * f p.2 := by
      rw [hinc]

private theorem tripleIndicator_eq_inter_indicator (a b c : ℕ) (δ : ℝ)
    (t : UnitAddCircle) :
    bohrIndicator a δ t * bohrIndicator b δ t * bohrIndicator c δ t =
      (bohrSet a δ ∩ bohrSet b δ ∩ bohrSet c δ).indicator
        (1 : UnitAddCircle → ℝ) t := by
  by_cases ha : t ∈ bohrSet a δ <;>
    by_cases hb : t ∈ bohrSet b δ <;>
      by_cases hc : t ∈ bohrSet c δ <;>
        simp [bohrIndicator, ha, hb, hc, Set.mem_inter_iff]

/-- 论文 `lem:moments` 第 468–469 行：三阶矩等于严格递增三元组
三重 Bohr 交集测度之和的六倍。六种排列和有限积分交换均在证明中完成。 -/
theorem coverThirdMoment_eq_six_sum_triple_intersections
    (W : Finset ℕ) (δ : ℝ)
    (hWpos : ∀ v ∈ W, 0 < v) (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    coverThirdMoment W δ =
      6 * ∑ p ∈ increasingTriples W,
        circleHaar.real (bohrSet p.1.1 δ ∩ bohrSet p.1.2 δ ∩
          bohrSet p.2 δ) := by
  classical
  have hpoint (t : UnitAddCircle) :
      coverMultiplicity W δ t * (coverMultiplicity W δ t - 1) *
          (coverMultiplicity W δ t - 2) =
        6 * ∑ p ∈ increasingTriples W,
          bohrIndicator p.1.1 δ t * bohrIndicator p.1.2 δ t *
            bohrIndicator p.2 δ t :=
    (coverThirdMoment_pointwise_ordered W δ t).trans
      (ordered_triple_sum_eq_six_increasing W
        (fun v => bohrIndicator v δ t))
  have hterm (p : (ℕ × ℕ) × ℕ) (hp : p ∈ increasingTriples W) :
      Integrable (fun t : UnitAddCircle =>
        bohrIndicator p.1.1 δ t * bohrIndicator p.1.2 δ t *
          bohrIndicator p.2 δ t) circleHaar := by
    rw [funext (fun t => tripleIndicator_eq_inter_indicator p.1.1 p.1.2 p.2 δ t)]
    obtain ⟨ha, hb, hc, _, _⟩ := mem_increasingTriples_iff W p |>.mp hp
    exact (integrable_const 1).indicator
      (((bohrSet_measurable_measure p.1.1 δ (hWpos _ ha) hδ hδhalf).1.inter
        (bohrSet_measurable_measure p.1.2 δ (hWpos _ hb) hδ hδhalf).1).inter
        (bohrSet_measurable_measure p.2 δ (hWpos _ hc) hδ hδhalf).1)
  unfold coverThirdMoment
  simp_rw [hpoint]
  rw [integral_const_mul, integral_finsetSum (increasingTriples W) hterm]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  rw [funext (fun t => tripleIndicator_eq_inter_indicator p.1.1 p.1.2 p.2 δ t)]
  obtain ⟨ha, hb, hc, _, _⟩ := mem_increasingTriples_iff W p |>.mp hp
  exact integral_indicator_one
    (((bohrSet_measurable_measure p.1.1 δ (hWpos _ ha) hδ hδhalf).1.inter
      (bohrSet_measurable_measure p.1.2 δ (hWpos _ hb) hδ hδhalf).1).inter
      (bohrSet_measurable_measure p.2 δ (hWpos _ hc) hδ hδhalf).1)

/-- 论文第 472 行：严格递增三元组的短整数关系倒数和 `L(W)`。 -/
noncomputable def tripleRelationLambdaSum (W : Finset ℕ) : ℝ :=
  ∑ p ∈ increasingTriples W,
    1 / (relationLambda p.1.1 p.1.2 p.2 : ℝ)

/-- 论文第 472–473 行：`G₃(W)=Σ gcd(a,b,c)/c`，除法在实数中进行。 -/
noncomputable def tripleGcdSum (W : Finset ℕ) : ℝ :=
  ∑ p ∈ increasingTriples W,
    (relationGcd p.1.1 p.1.2 p.2 : ℝ) / (p.2 : ℝ)

/-- 论文第 472–473 行：每项 `gcd(a,b,c)/c = 1/relationC a b c`；
先用自然数整除恒等式，再转换为实数除法。 -/
theorem relationGcd_div_c_eq_inv_relationC (a b c : ℕ) (hc : 0 < c) :
    (relationGcd a b c : ℝ) / (c : ℝ) =
      1 / (relationC a b c : ℝ) := by
  have hd : relationGcd a b c ∣ c := Nat.gcd_dvd_right _ _
  have hmulNat : relationC a b c * relationGcd a b c = c := by
    exact Nat.div_mul_cancel hd
  have hmul : (relationC a b c : ℝ) * (relationGcd a b c : ℝ) = c := by
    exact_mod_cast hmulNat
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  have hCR : (relationC a b c : ℝ) ≠ 0 := by
    exact_mod_cast (relationHeight_pos a b c hc).ne'
  rw [div_eq_div_iff hcR hCR]
  nlinarith [hmul]

/-- 论文第 472–473 行：整个 `G₃(W)` 等于本原法向量高度的倒数和。 -/
theorem tripleGcdSum_eq_sum_inv_relationC (W : Finset ℕ)
    (hWpos : ∀ v ∈ W, 0 < v) :
    tripleGcdSum W = ∑ p ∈ increasingTriples W,
      1 / (relationC p.1.1 p.1.2 p.2 : ℝ) := by
  unfold tripleGcdSum
  apply Finset.sum_congr rfl
  intro p hp
  have hc := (mem_increasingTriples_iff W p).mp hp |>.2.2.1
  exact relationGcd_div_c_eq_inv_relationC p.1.1 p.1.2 p.2 (hWpos _ hc)

/-- 论文第 468–472 行：递增三元组数不超过 `|W|³`。 -/
theorem increasingTriples_card_le_cube (W : Finset ℕ) :
    (increasingTriples W).card ≤ W.card ^ 3 := by
  calc
    (increasingTriples W).card ≤ ((W ×ˢ W) ×ˢ W).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = W.card ^ 3 := by simp [Finset.card_product, pow_succ]

/-- 论文第 468–473 行中只使用已证 `lem:triple` 的有限求和部分：
`A₃(W)≤72π⁶ (|T(W)|δ³+δ²L(W)+δG₃(W))`。不要求 `W` 覆盖。 -/
theorem coverThirdMoment_le_triple_sums (W : Finset ℕ) (δ : ℝ)
    (hWpos : ∀ v ∈ W, 0 < v) (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) :
    coverThirdMoment W δ ≤
      72 * Real.pi ^ 6 *
        (((increasingTriples W).card : ℝ) * δ ^ 3 +
          δ ^ 2 * tripleRelationLambdaSum W + δ * tripleGcdSum W) := by
  let T := increasingTriples W
  have hδhalf : δ < 1 / 2 := by linarith
  have hsum :
      (∑ p ∈ T, circleHaar.real
        (bohrSet p.1.1 δ ∩ bohrSet p.1.2 δ ∩ bohrSet p.2 δ)) ≤
      ∑ p ∈ T, 12 * Real.pi ^ 6 *
        (δ ^ 3 + δ ^ 2 / (relationLambda p.1.1 p.1.2 p.2 : ℝ) +
          δ / (relationC p.1.1 p.1.2 p.2 : ℝ)) := by
    apply Finset.sum_le_sum
    intro p hp
    obtain ⟨ha, hb, hc, hab, hbc⟩ := mem_increasingTriples_iff W p |>.mp hp
    exact bohr_triple_intersection_bound p.1.1 p.1.2 p.2 δ
      (hWpos _ ha) hab hbc hδ hδ4
  have hsumID :
      (∑ p ∈ T, 12 * Real.pi ^ 6 *
        (δ ^ 3 + δ ^ 2 / (relationLambda p.1.1 p.1.2 p.2 : ℝ) +
          δ / (relationC p.1.1 p.1.2 p.2 : ℝ))) =
      12 * Real.pi ^ 6 *
        ((T.card : ℝ) * δ ^ 3 +
          δ ^ 2 * tripleRelationLambdaSum W + δ * tripleGcdSum W) := by
    rw [← Finset.mul_sum]
    rw [tripleGcdSum_eq_sum_inv_relationC W hWpos]
    simp only [tripleRelationLambdaSum]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp only [div_eq_mul_inv, one_mul, ← Finset.mul_sum,
      Finset.sum_const, nsmul_eq_mul, T]
  calc
    coverThirdMoment W δ = 6 * ∑ p ∈ T,
        circleHaar.real (bohrSet p.1.1 δ ∩ bohrSet p.1.2 δ ∩
          bohrSet p.2 δ) :=
      coverThirdMoment_eq_six_sum_triple_intersections W δ hWpos hδ hδhalf
    _ ≤ 6 * ∑ p ∈ T, 12 * Real.pi ^ 6 *
        (δ ^ 3 + δ ^ 2 / (relationLambda p.1.1 p.1.2 p.2 : ℝ) +
          δ / (relationC p.1.1 p.1.2 p.2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = 72 * Real.pi ^ 6 *
        ((T.card : ℝ) * δ ^ 3 +
          δ ^ 2 * tripleRelationLambdaSum W + δ * tripleGcdSum W) := by
      rw [hsumID]
      ring

/-- 论文第 472–473 行的较宽松有限求和界：以 `|W|³` 代替递增三元组数。
短关系总和 `L(W)` 仍保留，未使用尚未证明的关系总和估计。 -/
theorem coverThirdMoment_le_card_cube (W : Finset ℕ) (δ : ℝ)
    (hWpos : ∀ v ∈ W, 0 < v) (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) :
    coverThirdMoment W δ ≤
      72 * Real.pi ^ 6 *
        ((W.card : ℝ) ^ 3 * δ ^ 3 +
          δ ^ 2 * tripleRelationLambdaSum W + δ * tripleGcdSum W) := by
  have hcard : ((increasingTriples W).card : ℝ) ≤ (W.card : ℝ) ^ 3 := by
    exact_mod_cast increasingTriples_card_le_cube W
  have hfirst : ((increasingTriples W).card : ℝ) * δ ^ 3 ≤
      (W.card : ℝ) ^ 3 * δ ^ 3 :=
    mul_le_mul_of_nonneg_right hcard (by positivity)
  have hrest :
      ((increasingTriples W).card : ℝ) * δ ^ 3 +
          δ ^ 2 * tripleRelationLambdaSum W + δ * tripleGcdSum W ≤
        (W.card : ℝ) ^ 3 * δ ^ 3 +
          δ ^ 2 * tripleRelationLambdaSum W + δ * tripleGcdSum W := by
    linarith
  exact (coverThirdMoment_le_triple_sums W δ hWpos hδ hδ4).trans
    (mul_le_mul_of_nonneg_left hrest (by positivity))

#print axioms LonelyRunner.coverThirdMoment_pointwise_ordered
#print axioms LonelyRunner.coverThirdMoment_eq_six_sum_triple_intersections
#print axioms LonelyRunner.relationGcd_div_c_eq_inv_relationC
#print axioms LonelyRunner.tripleGcdSum_eq_sum_inv_relationC
#print axioms LonelyRunner.coverThirdMoment_le_triple_sums
#print axioms LonelyRunner.coverThirdMoment_le_card_cube

end LonelyRunner
