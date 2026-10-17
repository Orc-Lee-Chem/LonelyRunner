import LonelyRunner.CoverMultiplicity
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! 论文 `paper/lonely_runner_zh.tex` 第 428–456 行：覆盖重数的二、三阶阶乘矩。 -/

namespace LonelyRunner

open MeasureTheory

/-- 论文第 429 行：`A₂(W)=∫Y_W(Y_W−1)dμ`。 -/
noncomputable def coverSecondMoment (W : Finset ℕ) (δ : ℝ) : ℝ :=
  ∫ t, coverMultiplicity W δ t * (coverMultiplicity W δ t - 1) ∂circleHaar

/-- 论文第 429 行：`A₃(W)=∫Y_W(Y_W−1)(Y_W−2)dμ`。 -/
noncomputable def coverThirdMoment (W : Finset ℕ) (δ : ℝ) : ℝ :=
  ∫ t, coverMultiplicity W δ t * (coverMultiplicity W δ t - 1) *
    (coverMultiplicity W δ t - 2) ∂circleHaar

private theorem coverMultiplicity_le_card (W : Finset ℕ) (δ : ℝ)
    (t : UnitAddCircle) : coverMultiplicity W δ t ≤ (W.card : ℝ) := by
  classical
  rw [coverMultiplicity_eq_card_filter]
  exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)

private theorem coverExcess_point_bounds (W : Finset ℕ) (δ : ℝ)
    (t : UnitAddCircle) :
    0 ≤ max (coverMultiplicity W δ t - 1) 0 ∧
      max (coverMultiplicity W δ t - 1) 0 ≤ (W.card : ℝ) := by
  constructor
  · exact le_max_right _ _
  · apply max_le
    · have hY := coverMultiplicity_le_card W δ t
      linarith
    · exact Nat.cast_nonneg _

/-- 论文第 449–451 行：整数值重数满足 `Y(Y−1)=Y(Y−1)_+`。 -/
theorem coverSecondMoment_pointwise (W : Finset ℕ) (δ : ℝ)
    (t : UnitAddCircle) :
    coverMultiplicity W δ t * (coverMultiplicity W δ t - 1) =
      coverMultiplicity W δ t * max (coverMultiplicity W δ t - 1) 0 := by
  rw [coverMultiplicity_eq_card_filter]
  by_cases hzero : (bohrHits W δ t).card = 0
  · simp [hzero]
  · have hpos : 1 ≤ ((bohrHits W δ t).card : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hzero
    rw [max_eq_left (by linarith)]

/-- 论文第 451 行：整数值重数满足 `Y²(Y−1)_+=Y(Y−1)(Y−2)+2Y(Y−1)`。 -/
theorem coverThirdMoment_pointwise (W : Finset ℕ) (δ : ℝ)
    (t : UnitAddCircle) :
    coverMultiplicity W δ t ^ 2 * max (coverMultiplicity W δ t - 1) 0 =
      coverMultiplicity W δ t * (coverMultiplicity W δ t - 1) *
        (coverMultiplicity W δ t - 2) +
      2 * (coverMultiplicity W δ t * (coverMultiplicity W δ t - 1)) := by
  rw [coverMultiplicity_eq_card_filter]
  by_cases hzero : (bohrHits W δ t).card = 0
  · simp [hzero]
  · have hpos : 1 ≤ ((bohrHits W δ t).card : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hzero
    rw [max_eq_left (by linarith)]
    ring

private theorem coverY_abs_bound (W : Finset ℕ) (δ : ℝ)
    (t : UnitAddCircle) :
    |coverMultiplicity W δ t| ≤ (W.card : ℝ) + 2 := by
  rw [abs_of_nonneg (coverMultiplicity_nonneg W δ t)]
  have h := coverMultiplicity_le_card W δ t
  linarith

private theorem coverY_sub_abs_bound (W : Finset ℕ) (δ : ℝ)
    (k : ℝ) (hk : 0 ≤ k) (hkm : k ≤ 2) (t : UnitAddCircle) :
    |coverMultiplicity W δ t - k| ≤ (W.card : ℝ) + 2 := by
  apply abs_le.mpr
  constructor
  · have h := coverMultiplicity_nonneg W δ t
    have hc : (0 : ℝ) ≤ W.card := Nat.cast_nonneg _
    linarith
  · have h := coverMultiplicity_le_card W δ t
    linarith

private theorem coverSqrtExcess_abs_bound (W : Finset ℕ) (δ : ℝ)
    (t : UnitAddCircle) :
    |Real.sqrt (max (coverMultiplicity W δ t - 1) 0)| ≤
      (W.card : ℝ) + 2 := by
  let e := max (coverMultiplicity W δ t - 1) 0
  have he0 : 0 ≤ e := (coverExcess_point_bounds W δ t).1
  have hem : e ≤ (W.card : ℝ) := (coverExcess_point_bounds W δ t).2
  have hroot := Real.sqrt_nonneg e
  have hsquare := Real.sq_sqrt he0
  rw [abs_of_nonneg hroot]
  have hm : 0 ≤ (W.card : ℝ) := Nat.cast_nonneg _
  nlinarith

private theorem integrable_of_measurable_bound {f : UnitAddCircle → ℝ}
    (hf : Measurable f) (C : ℝ) (hC : ∀ t, |f t| ≤ C) :
    Integrable f circleHaar := by
  apply Integrable.of_bound hf.aestronglyMeasurable C
  filter_upwards [] with t
  simpa [Real.norm_eq_abs] using hC t

private theorem abs_mul_bound {f g : UnitAddCircle → ℝ} {a b : ℝ}
    (ha : 0 ≤ a) (_hb : 0 ≤ b)
    (hf : ∀ t, |f t| ≤ a) (hg : ∀ t, |g t| ≤ b) (t : UnitAddCircle) :
    |f t * g t| ≤ a * b := by
  rw [abs_mul]
  exact mul_le_mul (hf t) (hg t) (abs_nonneg _) ha

/-- 论文第 428–456 行：有界整数值重数所生成的正部、平方根、平方、
柯西乘积及二、三阶矩被积函数均可测。 -/
theorem coverMoments_measurable (W : Finset ℕ) (δ : ℝ)
    (hWpos : ∀ v ∈ W, 0 < v) (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    let Y := coverMultiplicity W δ
    let E := fun t => max (Y t - 1) 0
    let S := fun t => Real.sqrt (E t)
    Measurable Y ∧ Measurable E ∧ Measurable S ∧
    Measurable (fun t => Y t * S t) ∧
    Measurable (fun t => S t ^ 2) ∧
    Measurable (fun t => (Y t * S t) ^ 2) ∧
    Measurable (fun t => S t * (Y t * S t)) ∧
    Measurable (fun t => Y t * (Y t - 1)) ∧
    Measurable (fun t => Y t * (Y t - 1) * (Y t - 2)) := by
  dsimp
  have hY := (coverMultiplicity_measurable_integrable W δ hWpos hδ hδhalf).1
  have hE : Measurable (fun t => max (coverMultiplicity W δ t - 1) 0) :=
    (hY.sub measurable_const).max measurable_const
  have hS : Measurable (fun t => Real.sqrt (max (coverMultiplicity W δ t - 1) 0)) :=
    hE.sqrt
  have hYS : Measurable (fun t => coverMultiplicity W δ t *
      Real.sqrt (max (coverMultiplicity W δ t - 1) 0)) := hY.mul hS
  have hY1 : Measurable (fun t => coverMultiplicity W δ t *
      (coverMultiplicity W δ t - 1)) := hY.mul (hY.sub measurable_const)
  exact ⟨hY, hE, hS, hYS, hS.pow_const 2, hYS.pow_const 2,
    hS.mul hYS, hY1, hY1.mul (hY.sub measurable_const)⟩

/-- 论文第 428–456 行：重数、正部、平方根及二、三阶矩的被积函数可测且可积；
特别包括应用积分柯西时的平方和乘积。 -/
theorem coverMoments_measurable_integrable (W : Finset ℕ) (δ : ℝ)
    (hWpos : ∀ v ∈ W, 0 < v) (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    let Y := coverMultiplicity W δ
    let E := fun t => max (Y t - 1) 0
    let S := fun t => Real.sqrt (E t)
    (Measurable S ∧ Integrable S circleHaar) ∧
    (Measurable (fun t => Y t * S t) ∧
      Integrable (fun t => Y t * S t) circleHaar) ∧
    Integrable (fun t => S t ^ 2) circleHaar ∧
    Integrable (fun t => (Y t * S t) ^ 2) circleHaar ∧
    Integrable (fun t => S t * (Y t * S t)) circleHaar ∧
    Integrable (fun t => Y t * (Y t - 1)) circleHaar ∧
    Integrable (fun t => Y t * (Y t - 1) * (Y t - 2)) circleHaar := by
  dsimp
  let C : ℝ := (W.card : ℝ) + 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hY := (coverMultiplicity_measurable_integrable W δ hWpos hδ hδhalf).1
  have hE : Measurable (fun t => max (coverMultiplicity W δ t - 1) 0) :=
    (hY.sub measurable_const).max measurable_const
  have hS : Measurable (fun t => Real.sqrt (max (coverMultiplicity W δ t - 1) 0)) :=
    hE.sqrt
  have hYb : ∀ t, |coverMultiplicity W δ t| ≤ C := coverY_abs_bound W δ
  have h1b : ∀ t, |coverMultiplicity W δ t - 1| ≤ C := by
    intro t
    exact coverY_sub_abs_bound W δ 1 (by norm_num) (by norm_num) t
  have h2b : ∀ t, |coverMultiplicity W δ t - 2| ≤ C := by
    intro t
    exact coverY_sub_abs_bound W δ 2 (by norm_num) (by norm_num) t
  have hSb : ∀ t, |Real.sqrt (max (coverMultiplicity W δ t - 1) 0)| ≤ C :=
    coverSqrtExcess_abs_bound W δ
  have hYS : Measurable (fun t => coverMultiplicity W δ t *
      Real.sqrt (max (coverMultiplicity W δ t - 1) 0)) := hY.mul hS
  have hYSb : ∀ t, |coverMultiplicity W δ t *
      Real.sqrt (max (coverMultiplicity W δ t - 1) 0)| ≤ C * C :=
    abs_mul_bound hC hC hYb hSb
  have hY1 : Measurable (fun t => coverMultiplicity W δ t *
      (coverMultiplicity W δ t - 1)) := hY.mul (hY.sub measurable_const)
  have hY1b : ∀ t, |coverMultiplicity W δ t *
      (coverMultiplicity W δ t - 1)| ≤ C * C :=
    abs_mul_bound hC hC hYb h1b
  have hCC : 0 ≤ C * C := mul_nonneg hC hC
  refine ⟨⟨hS, integrable_of_measurable_bound hS C hSb⟩,
    ⟨hYS, integrable_of_measurable_bound hYS (C*C) hYSb⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact integrable_of_measurable_bound (hS.pow_const 2) (C*C) (by
      intro t
      simpa [pow_two, abs_mul] using
        abs_mul_bound hC hC hSb hSb t)
  · exact integrable_of_measurable_bound (hYS.pow_const 2) ((C*C)*(C*C)) (by
      intro t
      simpa [pow_two, abs_mul] using
        abs_mul_bound hCC hCC hYSb hYSb t)
  · exact integrable_of_measurable_bound (hS.mul hYS) (C*(C*C))
      (abs_mul_bound hC hCC hSb hYSb)
  · exact integrable_of_measurable_bound hY1 (C*C) hY1b
  · exact integrable_of_measurable_bound (hY1.mul (hY.sub measurable_const))
      ((C*C)*C) (abs_mul_bound hCC hC hY1b h2b)

/-- 论文第 439–443、449–456 行：对任何有限正速度子族，实际应用积分柯西得到
`A₂(W)^2 ≤ e_W(A₃(W)+2A₂(W))`；无需假定 `W` 自身覆盖。 -/
theorem coverSecondMoment_sq_le_excess_mul (W : Finset ℕ) (δ : ℝ)
    (hWpos : ∀ v ∈ W, 0 < v) (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    coverSecondMoment W δ ^ 2 ≤
      coverExcess W δ * (coverThirdMoment W δ + 2 * coverSecondMoment W δ) := by
  let Y := coverMultiplicity W δ
  let E := fun t => max (Y t - 1) 0
  let S := fun t => Real.sqrt (E t)
  have hdata := coverMoments_measurable_integrable W δ hWpos hδ hδhalf
  dsimp only at hdata
  rcases hdata with ⟨⟨hSm, hSi⟩, ⟨hYSm, hYSi⟩, hS2i, hYS2i,
    hSYSi, hA2i, hA3i⟩
  have hEi : Integrable E circleHaar := coverExcess_integrable W δ hWpos hδ hδhalf
  have hE0 (t : UnitAddCircle) : 0 ≤ E t := le_max_right _ _
  have hY0 (t : UnitAddCircle) : 0 ≤ Y t := coverMultiplicity_nonneg W δ t
  have hS0 (t : UnitAddCircle) : 0 ≤ S t := Real.sqrt_nonneg _
  have hYS0 (t : UnitAddCircle) : 0 ≤ Y t * S t := mul_nonneg (hY0 t) (hS0 t)
  let C : ℝ := (W.card : ℝ) + 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hSb : ∀ t, |S t| ≤ C := coverSqrtExcess_abs_bound W δ
  have hYb : ∀ t, |Y t| ≤ C := coverY_abs_bound W δ
  have hYSb : ∀ t, |Y t * S t| ≤ C*C :=
    abs_mul_bound hC hC hYb hSb
  have hSLp : MemLp S (ENNReal.ofReal (2:ℝ)) circleHaar :=
    MemLp.of_bound hSm.aestronglyMeasurable C (by
      filter_upwards [] with t
      simpa [Real.norm_eq_abs] using hSb t)
  have hYSLp : MemLp (fun t => Y t * S t) (ENNReal.ofReal (2:ℝ)) circleHaar :=
    MemLp.of_bound hYSm.aestronglyMeasurable (C*C) (by
      filter_upwards [] with t
      simpa [Real.norm_eq_abs] using hYSb t)
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg
    Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall hS0) (Filter.Eventually.of_forall hYS0)
    hSLp hYSLp
  have hCross : (∫ t, S t * (Y t * S t) ∂circleHaar) = coverSecondMoment W δ := by
    change (∫ t, S t * (Y t * S t) ∂circleHaar) =
      ∫ t, Y t * (Y t - 1) ∂circleHaar
    congr 1
    funext t
    have hsq : S t ^ 2 = E t := Real.sq_sqrt (hE0 t)
    rw [coverSecondMoment_pointwise W δ t]
    calc
      S t * (Y t * S t) = Y t * S t ^ 2 := by ring
      _ = Y t * E t := by rw [hsq]
  have hSsquare : (∫ t, S t ^ 2 ∂circleHaar) = coverExcess W δ := by
    change (∫ t, S t ^ 2 ∂circleHaar) = ∫ t, E t ∂circleHaar
    congr 1
    funext t
    exact Real.sq_sqrt (hE0 t)
  have hYSsquare : (∫ t, (Y t * S t) ^ 2 ∂circleHaar) =
      coverThirdMoment W δ + 2 * coverSecondMoment W δ := by
    have hpoint (t : UnitAddCircle) :
        (Y t * S t) ^ 2 = Y t * (Y t - 1) * (Y t - 2) +
          2 * (Y t * (Y t - 1)) := by
      have hsq : S t ^ 2 = E t := Real.sq_sqrt (hE0 t)
      have hthird := coverThirdMoment_pointwise W δ t
      dsimp [Y, E, S] at hsq hthird ⊢
      nlinarith
    calc
      _ = ∫ t, (Y t * (Y t - 1) * (Y t - 2) +
          2 * (Y t * (Y t - 1))) ∂circleHaar := by
            congr 1
            funext t
            exact hpoint t
      _ = coverThirdMoment W δ + 2 * coverSecondMoment W δ := by
        rw [integral_add hA3i (hA2i.const_mul 2), integral_const_mul]
        rfl
  simp only [Real.rpow_two] at hCS
  rw [hCross, hSsquare, hYSsquare] at hCS
  have hCS' : coverSecondMoment W δ ≤
      Real.sqrt (coverExcess W δ) *
        Real.sqrt (coverThirdMoment W δ + 2 * coverSecondMoment W δ) := by
    simpa [Real.sqrt_eq_rpow] using hCS
  have he0 : 0 ≤ coverExcess W δ := by
    change 0 ≤ ∫ t, E t ∂circleHaar
    exact integral_nonneg hE0
  have hb0 : 0 ≤ coverThirdMoment W δ + 2 * coverSecondMoment W δ := by
    rw [← hYSsquare]
    exact integral_nonneg (fun t => sq_nonneg _)
  have ha0 : 0 ≤ coverSecondMoment W δ := by
    rw [← hCross]
    exact integral_nonneg (fun t => mul_nonneg (hS0 t) (hYS0 t))
  have hrootE := Real.sq_sqrt he0
  have hrootB := Real.sq_sqrt hb0
  have hprod0 : 0 ≤ Real.sqrt (coverExcess W δ) *
      Real.sqrt (coverThirdMoment W δ + 2 * coverSecondMoment W δ) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsquare := mul_nonneg (sub_nonneg.mpr hCS') (add_nonneg hprod0 ha0)
  nlinarith

/-- 论文第 433、443 行：若 `V` 逐点覆盖，则 `A₂(V)≤mε`，其中
`m=|V|` 且 `ε=2δm−1`。 -/
theorem coverSecondMoment_le_card_mul_epsilon (V : Finset ℕ) (δ : ℝ)
    (hVpos : ∀ v ∈ V, 0 < v) (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hcover : Covers V δ) (m : ℕ) (ε : ℝ)
    (hm : m = V.card) (hε : ε = 2 * δ * (m : ℝ) - 1) :
    coverSecondMoment V δ ≤ (m : ℝ) * ε := by
  have hA2i := (coverMoments_measurable_integrable V δ hVpos hδ hδhalf).2.2.2.2.2.1
  have hEi := coverExcess_integrable V δ hVpos hδ hδhalf
  have hpoint (t : UnitAddCircle) :
      coverMultiplicity V δ t * (coverMultiplicity V δ t - 1) ≤
        (V.card : ℝ) * max (coverMultiplicity V δ t - 1) 0 := by
    rw [coverSecondMoment_pointwise V δ t]
    exact mul_le_mul_of_nonneg_right (coverMultiplicity_le_card V δ t)
      (le_max_right _ _)
  have hle := integral_mono hA2i (hEi.const_mul (V.card : ℝ)) hpoint
  rw [integral_const_mul] at hle
  change coverSecondMoment V δ ≤ (V.card : ℝ) * coverExcess V δ at hle
  rw [coverExcess_eq_epsilon V δ hVpos hδ hδhalf hcover] at hle
  subst m
  subst ε
  exact hle

#print axioms LonelyRunner.coverSecondMoment_sq_le_excess_mul
#print axioms LonelyRunner.coverSecondMoment_le_card_mul_epsilon

end LonelyRunner
