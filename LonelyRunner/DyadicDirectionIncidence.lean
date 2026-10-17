import LonelyRunner.PrimitiveDirectionLines
import LonelyRunner.RationalInterceptBounds
import LonelyRunner.RationalInterceptEnergy
import LonelyRunner.WeightedST
import Mathlib.Data.Int.Interval

open Classical
open scoped Real

namespace LonelyRunner

/-- 论文短关系计数的二进方向层：本原整数方向，且最大坐标处于 `[M,2M)`。 -/
def primitiveDirections (M : ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (1 : ℤ) (2 * M : ℤ)).product
    (Finset.Icc (-(2 * M : ℤ)) (2 * M : ℤ))).filter fun z =>
      z.2 ≠ 0 ∧ Nat.gcd z.1.natAbs z.2.natAbs = 1 ∧
        M ≤ max z.1.natAbs z.2.natAbs ∧
        max z.1.natAbs z.2.natAbs < 2 * M

/-- 方向层的成员条件恰是论文所用的四项条件。 -/
theorem mem_primitiveDirections_iff (M : ℕ) (p q : ℤ) :
    (p,q) ∈ primitiveDirections M ↔
      0 < p ∧ q ≠ 0 ∧ Nat.gcd p.natAbs q.natAbs = 1 ∧
        M ≤ max p.natAbs q.natAbs ∧ max p.natAbs q.natAbs < 2 * M := by
  classical
  simp only [primitiveDirections, Finset.mem_filter]
  constructor
  · rintro ⟨hpair, hq0, hg, hlo, hhi⟩
    obtain ⟨hp, _hq⟩ := Finset.mem_product.mp hpair
    exact ⟨by have := (Finset.mem_Icc.mp hp).1; omega, hq0, hg, hlo, hhi⟩
  · rintro ⟨hp0, hq0, hg, hlo, hhi⟩
    have hpabs : p.natAbs < 2 * M := lt_of_le_of_lt (le_max_left ..) hhi
    have hqabs : q.natAbs < 2 * M := lt_of_le_of_lt (le_max_right ..) hhi
    have hpI : p ∈ Finset.Icc (1 : ℤ) (2 * M : ℤ) := by
      apply Finset.mem_Icc.mpr
      constructor
      · omega
      · have habs : (p.natAbs : ℤ) = |p| := Int.natCast_natAbs p
        omega
    have hqI : q ∈ Finset.Icc (-(2 * M : ℤ)) (2 * M : ℤ) := by
      apply Finset.mem_Icc.mpr
      have habs : (q.natAbs : ℤ) = |q| := Int.natCast_natAbs q
      constructor <;> omega
    exact ⟨Finset.mem_product.mpr ⟨hpI, hqI⟩, hq0, hg, hlo, hhi⟩

/-- 二进层方向数至多 `16 M²`，包括可能的空层。 -/
theorem primitiveDirections_card_le (M : ℕ) (hM : 1 ≤ M) :
    (primitiveDirections M).card ≤ 16 * M ^ 2 := by
  classical
  have hsubset : (primitiveDirections M).card ≤
      (((Finset.Icc (1 : ℤ) (2 * M : ℤ)).product
        (Finset.Icc (-(2 * M : ℤ)) (2 * M : ℤ))).card) := by
    exact Finset.card_filter_le _ _
  have hp : (Finset.Icc (1 : ℤ) (2 * M : ℤ)).card = 2 * M := by
    rw [Int.card_Icc]
    omega
  have hq : (Finset.Icc (-(2 * M : ℤ)) (2 * M : ℤ)).card = 4 * M + 1 := by
    rw [Int.card_Icc]
    omega
  have hprod :
      (((Finset.Icc (1 : ℤ) (2 * M : ℤ)).product
        (Finset.Icc (-(2 * M : ℤ)) (2 * M : ℤ))).card) =
        (2 * M) * (4 * M + 1) := by
    exact (Finset.card_product _ _).trans (by rw [hp, hq])
  rw [hprod] at hsubset
  nlinarith

private abbrev DirectionMember (M : ℕ) :=
  {z : ℤ × ℤ // z ∈ primitiveDirections M}

private theorem directionPositive (M : ℕ) (z : DirectionMember M) : 0 < z.1.1 :=
  ((mem_primitiveDirections_iff M z.1.1 z.1.2).mp z.2).1

/-- 一个本原方向和有理截距对应的实际几何直线。 -/
noncomputable def dyadicParameterLine (M : ℕ)
    (z : DirectionMember M × ℚ) : WeightedLine :=
  primitiveDirectionLine z.1.1.1 z.1.1.2 z.2 (directionPositive M z.1)

/-- 几何直线相等可恢复全部方向及截距参数。 -/
theorem dyadicParameterLine_injective (M : ℕ) :
    Function.Injective (dyadicParameterLine M) := by
  intro z z' heq
  obtain ⟨hp, hq, hr⟩ :=
    primitiveDirectionLine_parameters_unique
      z.1.1.1 z.1.1.2 z'.1.1.1 z'.1.1.2 z.2 z'.2
      (directionPositive M z.1) (directionPositive M z'.1)
      ((mem_primitiveDirections_iff M z.1.1.1 z.1.1.2).mp z.1.2).2.1
      ((mem_primitiveDirections_iff M z'.1.1.1 z'.1.1.2).mp z'.1.2).2.1
      ((mem_primitiveDirections_iff M z.1.1.1 z.1.1.2).mp z.1.2).2.2.1
      ((mem_primitiveDirections_iff M z'.1.1.1 z'.1.1.2).mp z'.1.2).2.2.1
      heq
  cases z with
  | mk z r =>
    cases z' with
    | mk z' r' =>
      have hd : z = z' := Subtype.ext (Prod.ext hp hq)
      cases hd
      simp only at hr
      exact Prod.ext rfl hr

/-- 有限参数集，由二进方向与截距作笛卡尔积。 -/
noncomputable def dyadicParameters (M : ℕ) (V : Finset ℕ) (H D : ℕ) :
    Finset (DirectionMember M × ℚ) :=
  (primitiveDirections M).attach.product (rationalIntercepts V H D)

/-- 上述参数的几何直线集。 -/
noncomputable def dyadicLineSet (M : ℕ) (V : Finset ℕ) (H D : ℕ) :
    Finset WeightedLine :=
  (dyadicParameters M V H D).image (dyadicParameterLine M)

/-- 几何线的权重由唯一截距参数取得；不在本层的直线权重为零。 -/
noncomputable def dyadicLineWeight (M : ℕ) (V : Finset ℕ) (H D : ℕ)
    (ℓ : WeightedLine) : ℕ :=
  if h : ∃ z ∈ dyadicParameters M V H D, dyadicParameterLine M z = ℓ then
    interceptWeight V H D (Classical.choose h).2
  else 0

/-- 直线参数的权重确实是该截距的既有权重。 -/
theorem dyadicLineWeight_apply (M : ℕ) (V : Finset ℕ) (H D : ℕ)
    (z : DirectionMember M × ℚ) (hz : z ∈ dyadicParameters M V H D) :
    dyadicLineWeight M V H D (dyadicParameterLine M z) =
      interceptWeight V H D z.2 := by
  classical
  let h : ∃ z' ∈ dyadicParameters M V H D,
      dyadicParameterLine M z' = dyadicParameterLine M z := ⟨z, hz, rfl⟩
  simp only [dyadicLineWeight, dite_eq_left h]
  have heq : Classical.choose h = z :=
    (dyadicParameterLine_injective M) (Classical.choose_spec h).2
  rw [heq]

/-- 方向层所有线的权重均为正；由截距集合成员性推出。 -/
theorem dyadicLineWeight_pos (M : ℕ) (V : Finset ℕ) (H D : ℕ)
    (ℓ : WeightedLine) (hℓ : ℓ ∈ dyadicLineSet M V H D) :
    0 < dyadicLineWeight M V H D ℓ := by
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hℓ
  rw [dyadicLineWeight_apply M V H D z hz]
  exact interceptWeight_pos V H D z.2 (Finset.mem_product.mp hz).2

/-- 方向层的平方权重和恰是方向数乘截距能量。 -/
theorem dyadic_weightSquareSum_eq (M : ℕ) (V : Finset ℕ) (H D : ℕ) :
    weightSquareSum (dyadicLineSet M V H D) (dyadicLineWeight M V H D) =
      ((primitiveDirections M).card : ℝ) *
        (∑ r ∈ rationalIntercepts V H D, (interceptWeight V H D r : ℝ) ^ 2) := by
  classical
  unfold weightSquareSum dyadicLineSet
  rw [Finset.sum_image (dyadicParameterLine_injective M).injOn]
  calc
    (∑ z ∈ dyadicParameters M V H D,
        ((dyadicLineWeight M V H D (dyadicParameterLine M z) : ℝ) ^ 2)) =
      (∑ z ∈ dyadicParameters M V H D,
        ((interceptWeight V H D z.2 : ℝ) ^ 2)) := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [dyadicLineWeight_apply M V H D z hz]
    _ = _ := by
      unfold dyadicParameters
      refine (Finset.sum_product _ _ _).trans ?_
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [Finset.card_attach]

/-- 方向层总权重恰是方向数乘截距总权重。 -/
theorem dyadic_weightSum_eq (M : ℕ) (V : Finset ℕ) (H D : ℕ) :
    weightSum (dyadicLineSet M V H D) (dyadicLineWeight M V H D) =
      ((primitiveDirections M).card : ℝ) *
        (∑ r ∈ rationalIntercepts V H D, (interceptWeight V H D r : ℝ)) := by
  classical
  unfold weightSum dyadicLineSet
  rw [Finset.sum_image (dyadicParameterLine_injective M).injOn]
  calc
    (∑ z ∈ dyadicParameters M V H D,
        (dyadicLineWeight M V H D (dyadicParameterLine M z) : ℝ)) =
      (∑ z ∈ dyadicParameters M V H D,
        (interceptWeight V H D z.2 : ℝ)) := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [dyadicLineWeight_apply M V H D z hz]
    _ = _ := by
      unfold dyadicParameters
      refine (Finset.sum_product _ _ _).trans ?_
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [Finset.card_attach]

/-- 每层最大线权重不超过 `2HD`，空线集的约定也包含在内。 -/
theorem dyadic_maxWeight_le (M : ℕ) (V : Finset ℕ) (H D : ℕ) :
    maxWeight (dyadicLineSet M V H D) (dyadicLineWeight M V H D) ≤
      2 * H * D := by
  classical
  unfold maxWeight
  apply Finset.sup_le_iff.mpr
  intro ℓ hℓ
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hℓ
  rw [dyadicLineWeight_apply M V H D z hz]
  exact interceptWeight_le V H D z.2

/-- 二进方向层的平方权重上界。 -/
theorem dyadic_weightSquareSum_le (M : ℕ) (hM : 1 ≤ M)
    (V : Finset ℕ) (H D : ℕ) :
    weightSquareSum (dyadicLineSet M V H D) (dyadicLineWeight M V H D) ≤
      (16 * M ^ 2 : ℝ) *
        (∑ r ∈ rationalIntercepts V H D, (interceptWeight V H D r : ℝ) ^ 2) := by
  rw [dyadic_weightSquareSum_eq]
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast primitiveDirections_card_le M hM
  · positivity

/-- 二进方向层的总权重上界。 -/
theorem dyadic_weightSum_le (M : ℕ) (hM : 1 ≤ M)
    (V : Finset ℕ) (H D : ℕ) :
    weightSum (dyadicLineSet M V H D) (dyadicLineWeight M V H D) ≤
      (32 * V.card * H * D * M ^ 2 : ℝ) := by
  rw [dyadic_weightSum_eq]
  have hc : ((primitiveDirections M).card : ℝ) ≤ (16 * M ^ 2 : ℝ) := by
    exact_mod_cast primitiveDirections_card_le M hM
  have hw : (∑ r ∈ rationalIntercepts V H D,
      (interceptWeight V H D r : ℝ)) ≤ (2 * V.card * H * D : ℝ) := by
    exact_mod_cast interceptWeight_sum_le V H D
  have hc0 : 0 ≤ ((primitiveDirections M).card : ℝ) := by positivity
  have hw0 : 0 ≤ (∑ r ∈ rationalIntercepts V H D,
      (interceptWeight V H D r : ℝ)) := by positivity
  calc
    _ ≤ (16 * M ^ 2 : ℝ) * (2 * V.card * H * D : ℝ) :=
      mul_le_mul hc hw hw0 (by positivity)
    _ = (32 * V.card * H * D * M ^ 2 : ℝ) := by ring

/-- 每条参数直线的几何关联数与有理等式的速度对计数相同。 -/
theorem dyadic_line_incidence_card (M : ℕ) (V : Finset ℕ)
    (z : DirectionMember M × ℚ) :
    ((velocityPairPoints V).filter fun x =>
      x ∈ (dyadicParameterLine M z : AffineSubspace ℝ _)).card =
      ((V.product V).filter fun ab =>
        (z.1.1.1 : ℚ) * (ab.1 : ℚ) + (z.1.1.2 : ℚ) * (ab.2 : ℚ) = z.2).card := by
  classical
  unfold velocityPairPoints
  rw [Finset.filter_image]
  rw [Finset.card_image_of_injective _ velocityPairPoint_injective]
  congr 1
  ext ab
  simp only [Finset.mem_filter]
  exact and_congr_right fun _ =>
    velocityPairPoint_mem_primitiveDirectionLine_iff
      z.1.1.1 z.1.1.2 z.2 (directionPositive M z.1) ab.1 ab.2

/-- 论文短关系计数：几何加权关联数精确等于方向、截距参数的有理方程计数。 -/
theorem dyadic_weightedIncidences_eq (M : ℕ) (V : Finset ℕ) (H D : ℕ) :
    weightedIncidences (velocityPairPoints V)
      (dyadicLineSet M V H D) (dyadicLineWeight M V H D) =
      ∑ d ∈ primitiveDirections M, ∑ r ∈ rationalIntercepts V H D,
        (interceptWeight V H D r : ℝ) *
          (((V.product V).filter fun ab =>
            (d.1 : ℚ) * (ab.1 : ℚ) + (d.2 : ℚ) * (ab.2 : ℚ) = r).card : ℝ) := by
  classical
  unfold weightedIncidences dyadicLineSet
  rw [Finset.sum_image (dyadicParameterLine_injective M).injOn]
  calc
    (∑ z ∈ dyadicParameters M V H D,
        (dyadicLineWeight M V H D (dyadicParameterLine M z) : ℝ) *
          (((velocityPairPoints V).filter fun x =>
            x ∈ (dyadicParameterLine M z : AffineSubspace ℝ _)).card : ℝ)) =
      (∑ z ∈ dyadicParameters M V H D,
        (interceptWeight V H D z.2 : ℝ) *
          (((V.product V).filter fun ab =>
            (z.1.1.1 : ℚ) * (ab.1 : ℚ) +
              (z.1.1.2 : ℚ) * (ab.2 : ℚ) = z.2).card : ℝ)) := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [dyadicLineWeight_apply M V H D z hz,
          dyadic_line_incidence_card M V z]
    _ = _ := by
      unfold dyadicParameters
      refine (Finset.sum_product _ _ _).trans ?_
      simpa only using
        (Finset.sum_attach (primitiveDirections M)
          (fun d : ℤ × ℤ => ∑ r ∈ rationalIntercepts V H D,
            (interceptWeight V H D r : ℝ) *
              (((V.product V).filter fun ab =>
                (d.1 : ℚ) * (ab.1 : ℚ) +
                  (d.2 : ℚ) * (ab.2 : ℚ) = r).card : ℝ)))

/-- 速度对点集的 ST 点数项：`(|V|²)^(2/3)=|V|^(4/3)`。 -/
private theorem dyadic_point_power (V : Finset ℕ) :
    ((velocityPairPoints V).card : ℝ) ^ ((2 : ℝ) / 3) =
      (V.card : ℝ) ^ ((4 : ℝ) / 3) := by
  rw [velocityPairPoints_card]
  push_cast
  calc
    ((V.card : ℝ) ^ 2) ^ ((2 : ℝ) / 3) =
        ((V.card : ℝ) ^ (2 : ℝ)) ^ ((2 : ℝ) / 3) := by
          exact congrArg (fun x : ℝ => x ^ ((2 : ℝ) / 3))
            (Real.rpow_natCast (V.card : ℝ) 2).symm
    _ = (V.card : ℝ) ^ ((2 : ℝ) * ((2 : ℝ) / 3)) := by
          rw [Real.rpow_mul (by positivity)]
    _ = (V.card : ℝ) ^ ((4 : ℝ) / 3) := by ring

set_option maxHeartbeats 1000000

/-- 论文短关系计数的二进方向 ST 步骤。常数来自已证 `weightedST`，
    截距能量保持为已定义的有限平方和；空点集和空方向集均包含在内。 -/
theorem dyadic_direction_incidence_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ℕ) (_hM : 1 ≤ M) (V : Finset ℕ) (H D : ℕ),
        (∑ d ∈ primitiveDirections M, ∑ r ∈ rationalIntercepts V H D,
          (interceptWeight V H D r : ℝ) *
            (((V.product V).filter fun ab =>
              (d.1 : ℚ) * (ab.1 : ℚ) + (d.2 : ℚ) * (ab.2 : ℚ) = r).card : ℝ)) ≤
          C * ((V.card : ℝ) ^ ((4 : ℝ) / 3) *
              ((16 : ℝ) * (M : ℝ) ^ 2 *
                (∑ r ∈ rationalIntercepts V H D,
                  (interceptWeight V H D r : ℝ) ^ 2)) ^ ((2 : ℝ) / 3) +
            (2 : ℝ) * (V.card : ℝ) ^ 2 * (H : ℝ) * (D : ℝ) +
            (32 : ℝ) * (V.card : ℝ) * (H : ℝ) * (D : ℝ) * (M : ℝ) ^ 2) := by
  obtain ⟨C, hC, hST⟩ := weightedST
  refine ⟨C, hC, ?_⟩
  intro M hM V H D
  let P := velocityPairPoints V
  let L := dyadicLineSet M V H D
  let w := dyadicLineWeight M V H D
  have hQ : weightSquareSum L w ≤
      (16 : ℝ) * (M : ℝ) ^ 2 *
        (∑ r ∈ rationalIntercepts V H D,
          (interceptWeight V H D r : ℝ) ^ 2) := by
    simpa only [P, L, w, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_assoc] using
      dyadic_weightSquareSum_le M hM V H D
  have hQ0 : 0 ≤ weightSquareSum L w := by
    simp only [weightSquareSum]
    positivity
  have hQpow := Real.rpow_le_rpow hQ0 hQ (by norm_num : 0 ≤ (2 : ℝ) / 3)
  have hmax : (maxWeight L w : ℝ) ≤ (2 : ℝ) * (H : ℝ) * (D : ℝ) := by
    exact_mod_cast dyadic_maxWeight_le M V H D
  have hsum : weightSum L w ≤
      (32 : ℝ) * (V.card : ℝ) * (H : ℝ) * (D : ℝ) * (M : ℝ) ^ 2 := by
    simpa only [P, L, w, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      dyadic_weightSum_le M hM V H D
  have hfirst : ((P.card : ℝ) ^ ((2 : ℝ) / 3)) *
      (weightSquareSum L w) ^ ((2 : ℝ) / 3) ≤
      (V.card : ℝ) ^ ((4 : ℝ) / 3) *
        ((16 : ℝ) * (M : ℝ) ^ 2 *
          (∑ r ∈ rationalIntercepts V H D,
            (interceptWeight V H D r : ℝ) ^ 2)) ^ ((2 : ℝ) / 3) := by
    rw [show ((P.card : ℝ) ^ ((2 : ℝ) / 3)) =
      (V.card : ℝ) ^ ((4 : ℝ) / 3) from dyadic_point_power V]
    exact mul_le_mul_of_nonneg_left hQpow (by positivity)
  have hsecond : (P.card : ℝ) * (maxWeight L w : ℝ) ≤
      (2 : ℝ) * (V.card : ℝ) ^ 2 * (H : ℝ) * (D : ℝ) := by
    rw [show (P.card : ℝ) = (V.card : ℝ) ^ 2 from by
      exact_mod_cast velocityPairPoints_card V]
    nlinarith [mul_le_mul_of_nonneg_left hmax (sq_nonneg (V.card : ℝ))]
  have htotal :
      ((P.card : ℝ) ^ ((2 : ℝ) / 3)) *
          (weightSquareSum L w) ^ ((2 : ℝ) / 3) +
        (P.card : ℝ) * (maxWeight L w : ℝ) + weightSum L w ≤
      (V.card : ℝ) ^ ((4 : ℝ) / 3) *
          ((16 : ℝ) * (M : ℝ) ^ 2 *
            (∑ r ∈ rationalIntercepts V H D,
              (interceptWeight V H D r : ℝ) ^ 2)) ^ ((2 : ℝ) / 3) +
        (2 : ℝ) * (V.card : ℝ) ^ 2 * (H : ℝ) * (D : ℝ) +
          (32 : ℝ) * (V.card : ℝ) * (H : ℝ) * (D : ℝ) * (M : ℝ) ^ 2 := by
    linarith
  calc
    _ = weightedIncidences P L w := (dyadic_weightedIncidences_eq M V H D).symm
    _ ≤ C * (((P.card : ℝ) ^ ((2 : ℝ) / 3)) *
          (weightSquareSum L w) ^ ((2 : ℝ) / 3) +
        (P.card : ℝ) * (maxWeight L w : ℝ) + weightSum L w) :=
      hST P L w (dyadicLineWeight_pos M V H D)
    _ ≤ _ := mul_le_mul_of_nonneg_left htotal (le_of_lt hC)

end LonelyRunner
