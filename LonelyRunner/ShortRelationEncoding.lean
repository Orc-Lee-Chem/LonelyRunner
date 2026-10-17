import LonelyRunner.DyadicDirectionIncidence
import LonelyRunner.CoverMomentTriple
import Mathlib.Data.Nat.Log

/-!
# 三个系数均非零的短关系编码

对应 `paper/lonely_runner_zh.tex` 的 `lem:relations` 证明第 170–189 行。
每个递增三元组只选一次整数关系；零系数情形仍须另行处理。
-/

open Classical

namespace LonelyRunner

/-- 一个三元组的已规范化短整数关系：首系数正，三个系数均非零。 -/
structure NonzeroShortRelation (H : ℕ) (t : (ℕ × ℕ) × ℕ) where
  α : ℤ
  β : ℤ
  γ : ℤ
  α_pos : 0 < α
  β_ne : β ≠ 0
  γ_ne : γ ≠ 0
  α_le : α.natAbs ≤ H
  β_le : β.natAbs ≤ H
  γ_le : γ.natAbs ≤ H
  equation : α * (t.1.1 : ℤ) + β * (t.1.2 : ℤ) + γ * (t.2 : ℤ) = 0

/-- 论文的整体变号步骤：非零关系存在当且仅当首系数为正的非零关系存在。 -/
theorem nonzeroRelation_iff_normalized (H : ℕ) (t : (ℕ × ℕ) × ℕ) :
    (∃ α β γ : ℤ, α ≠ 0 ∧ β ≠ 0 ∧ γ ≠ 0 ∧
      α.natAbs ≤ H ∧ β.natAbs ≤ H ∧ γ.natAbs ≤ H ∧
      α * (t.1.1 : ℤ) + β * (t.1.2 : ℤ) + γ * (t.2 : ℤ) = 0) ↔
      Nonempty (NonzeroShortRelation H t) := by
  constructor
  · rintro ⟨α, β, γ, hα, hβ, hγ, hαH, hβH, hγH, heq⟩
    by_cases hpos : 0 < α
    · exact ⟨⟨α, β, γ, hpos, hβ, hγ, hαH, hβH, hγH, heq⟩⟩
    · have hneg : 0 < -α := by omega
      refine ⟨⟨-α, -β, -γ, hneg, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
      · exact neg_ne_zero.mpr hβ
      · exact neg_ne_zero.mpr hγ
      · simpa only [Int.natAbs_neg] using hαH
      · simpa only [Int.natAbs_neg] using hβH
      · simpa only [Int.natAbs_neg] using hγH
      · nlinarith [heq]
  · rintro ⟨R⟩
    exact ⟨R.α, R.β, R.γ, ne_of_gt R.α_pos, R.β_ne, R.γ_ne,
      R.α_le, R.β_le, R.γ_le, R.equation⟩

/-- 三个系数均非零且存在长度不超过 `H` 的关系的递增三元组。 -/
noncomputable def nonzeroShortTriples (V : Finset ℕ) (H : ℕ) :
    Finset ((ℕ × ℕ) × ℕ) :=
  (increasingTriples V).filter fun t => Nonempty (NonzeroShortRelation H t)

theorem mem_nonzeroShortTriples_iff (V : Finset ℕ) (H : ℕ)
    (t : (ℕ × ℕ) × ℕ) :
    t ∈ nonzeroShortTriples V H ↔
      t ∈ increasingTriples V ∧ Nonempty (NonzeroShortRelation H t) := by
  simp [nonzeroShortTriples]

/-- 对每个三元组固定一次关系，后面的所有方向层均复用这一选择。 -/
noncomputable def chosenNonzeroRelation (V : Finset ℕ) (H : ℕ)
    (t : {t : (ℕ × ℕ) × ℕ // t ∈ nonzeroShortTriples V H}) :
    NonzeroShortRelation H t.1 :=
  Classical.choice ((mem_nonzeroShortTriples_iff V H t.1).mp t.2).2

/-- 选定关系首两个系数的最大公因数。 -/
def shortRelationD {H : ℕ} {t : (ℕ × ℕ) × ℕ}
    (R : NonzeroShortRelation H t) : ℕ := Int.gcd R.α R.β

/-- 本原方向的正首坐标。 -/
def shortRelationP {H : ℕ} {t : (ℕ × ℕ) × ℕ}
    (R : NonzeroShortRelation H t) : ℤ := R.α / (shortRelationD R : ℤ)

/-- 本原方向的非零次坐标。 -/
def shortRelationQ {H : ℕ} {t : (ℕ × ℕ) × ℕ}
    (R : NonzeroShortRelation H t) : ℤ := R.β / (shortRelationD R : ℤ)

/-- 本原方向的最大坐标，以及包含它的二进尺度。 -/
def shortRelationHeight {H : ℕ} {t : (ℕ × ℕ) × ℕ}
    (R : NonzeroShortRelation H t) : ℕ :=
  max (shortRelationP R).natAbs (shortRelationQ R).natAbs

def shortRelationIndex {H : ℕ} {t : (ℕ × ℕ) × ℕ}
    (R : NonzeroShortRelation H t) : ℕ := Nat.log 2 (shortRelationHeight R)

def shortRelationScale {H : ℕ} {t : (ℕ × ℕ) × ℕ}
    (R : NonzeroShortRelation H t) : ℕ := 2 ^ shortRelationIndex R

/-- `d=gcd(|α|,|β|)` 为正，且原系数精确分解为 `α=dp, β=dq`。 -/
theorem shortRelation_factorization {H : ℕ} {t : (ℕ × ℕ) × ℕ}
    (R : NonzeroShortRelation H t) :
    0 < shortRelationD R ∧
      R.α = (shortRelationD R : ℤ) * shortRelationP R ∧
      R.β = (shortRelationD R : ℤ) * shortRelationQ R := by
  have hα : R.α ≠ 0 := ne_of_gt R.α_pos
  have hd : 0 < shortRelationD R := by
    unfold shortRelationD
    exact Nat.gcd_pos_of_pos_left _ (Int.natAbs_pos.mpr hα)
  refine ⟨hd, ?_, ?_⟩
  · change R.α = (Int.gcd R.α R.β : ℤ) *
        (R.α / (Int.gcd R.α R.β : ℤ))
    simpa only [mul_comm] using
      (Int.ediv_mul_cancel (Int.gcd_dvd_left R.α R.β)).symm
  · change R.β = (Int.gcd R.α R.β : ℤ) *
        (R.β / (Int.gcd R.α R.β : ℤ))
    simpa only [mul_comm] using
      (Int.ediv_mul_cancel (Int.gcd_dvd_right R.α R.β)).symm

/-- 分解方向满足首坐标正、次坐标非零和本原性。 -/
theorem shortRelation_primitive {H : ℕ} {t : (ℕ × ℕ) × ℕ}
    (R : NonzeroShortRelation H t) :
    0 < shortRelationP R ∧ shortRelationQ R ≠ 0 ∧
      Nat.gcd (shortRelationP R).natAbs (shortRelationQ R).natAbs = 1 := by
  obtain ⟨hd, hα, hβ⟩ := shortRelation_factorization R
  have hp : 0 < shortRelationP R := by
    have hd' : (0 : ℤ) < (shortRelationD R : ℤ) := by exact_mod_cast hd
    nlinarith [R.α_pos]
  have hq : shortRelationQ R ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hβ
    exact R.β_ne hβ
  have hg : Nat.gcd (shortRelationP R).natAbs
      (shortRelationQ R).natAbs = 1 := by
    change Int.gcd (shortRelationP R) (shortRelationQ R) = 1
    exact Int.gcd_div_gcd_div_gcd hd
  exact ⟨hp, hq, hg⟩

/-- 本原方向的高度处于 `[1,H]`，且 `d·height≤H`。 -/
theorem shortRelation_height_bounds {H : ℕ} {t : (ℕ × ℕ) × ℕ}
    (R : NonzeroShortRelation H t) :
    1 ≤ shortRelationHeight R ∧
      shortRelationHeight R ≤ H ∧
      shortRelationD R * shortRelationHeight R ≤ H := by
  obtain ⟨hd, hα, hβ⟩ := shortRelation_factorization R
  have hp0 : 0 < (shortRelationP R).natAbs :=
    Int.natAbs_pos.mpr (ne_of_gt (shortRelation_primitive R).1)
  have hαabs : R.α.natAbs = shortRelationD R * (shortRelationP R).natAbs := by
    rw [hα, Int.natAbs_mul]
    simp
  have hβabs : R.β.natAbs = shortRelationD R * (shortRelationQ R).natAbs := by
    rw [hβ, Int.natAbs_mul]
    simp
  have hmul : shortRelationD R * shortRelationHeight R ≤ H := by
    unfold shortRelationHeight
    rcases le_total (shortRelationP R).natAbs (shortRelationQ R).natAbs with h | h
    · rw [max_eq_right h]
      simpa only [hβabs] using R.β_le
    · rw [max_eq_left h]
      simpa only [hαabs] using R.α_le
  have hheight : shortRelationHeight R ≤ H := by
    have hd1 : 1 ≤ shortRelationD R := hd
    nlinarith [hmul]
  exact ⟨by unfold shortRelationHeight; omega, hheight, hmul⟩

/-- `M=2^⌊log₂ height⌋` 的严格二进定位。 -/
theorem shortRelation_dyadic_bounds {H : ℕ} {t : (ℕ × ℕ) × ℕ}
    (R : NonzeroShortRelation H t) :
    1 ≤ shortRelationScale R ∧
      shortRelationScale R ≤ shortRelationHeight R ∧
      shortRelationHeight R < 2 * shortRelationScale R ∧
      shortRelationScale R ≤ H ∧
      1 ≤ shortRelationD R ∧
      shortRelationD R ≤ H / shortRelationScale R ∧
      shortRelationIndex R ≤ Nat.log 2 H := by
  obtain ⟨hheight0, hheightH, hmul⟩ := shortRelation_height_bounds R
  let M := shortRelationScale R
  have hM0 : 1 ≤ M := by
    have hpow : 0 < 2 ^ shortRelationIndex R := pow_pos (by omega) _
    exact hpow
  have hMheight : M ≤ shortRelationHeight R := by
    exact Nat.pow_log_le_self 2 (by omega)
  have hheight2M : shortRelationHeight R < 2 * M := by
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2)
      (shortRelationHeight R)
    simpa only [pow_succ, M, shortRelationScale, shortRelationIndex,
      Nat.mul_comm] using h
  have hMH : M ≤ H := le_trans hMheight hheightH
  have hd : 1 ≤ shortRelationD R := (shortRelation_factorization R).1
  have hdM : shortRelationD R * M ≤ H :=
    le_trans (Nat.mul_le_mul_left _ hMheight) hmul
  have hdD : shortRelationD R ≤ H / M :=
    (Nat.le_div_iff_mul_le hM0).2 hdM
  have hj : shortRelationIndex R ≤ Nat.log 2 H := by
    apply Nat.le_log_of_pow_le (by norm_num : 1 < 2)
    exact hMH
  exact ⟨hM0, hMheight, hheight2M, hMH, hd, hdD, hj⟩

/-- 规范化方向确实属于已有的二进本原方向集。 -/
theorem shortRelation_mem_primitiveDirections {H : ℕ} {t : (ℕ × ℕ) × ℕ}
    (R : NonzeroShortRelation H t) :
    (shortRelationP R, shortRelationQ R) ∈
      primitiveDirections (shortRelationScale R) := by
  obtain ⟨hp, hq, hg⟩ := shortRelation_primitive R
  obtain ⟨_, hlow, hhigh, _, _, _, _⟩ := shortRelation_dyadic_bounds R
  exact (mem_primitiveDirections_iff _ _ _).mpr
    ⟨hp, hq, hg, hlow, hhigh⟩

/-- 论文第 180 行的截距 `r=-γc/d`，按已有有理数截距定义书写。 -/
def shortRelationIntercept {H : ℕ} {t : (ℕ × ℕ) × ℕ}
    (R : NonzeroShortRelation H t) : ℚ :=
  rationalIntercept (-R.γ) t.2 (shortRelationD R)

theorem shortRelationIntercept_eq {H : ℕ} {t : (ℕ × ℕ) × ℕ}
    (R : NonzeroShortRelation H t) :
    shortRelationIntercept R =
      -(R.γ : ℚ) * (t.2 : ℚ) / (shortRelationD R : ℚ) := by
  simp [shortRelationIntercept, rationalIntercept]

/-- 原关系式除以正整数 `d` 后，速度对 `(a,b)` 落在参数直线上。 -/
theorem shortRelation_incidence_equation {H : ℕ} {t : (ℕ × ℕ) × ℕ}
    (R : NonzeroShortRelation H t) :
    (shortRelationP R : ℚ) * (t.1.1 : ℚ) +
      (shortRelationQ R : ℚ) * (t.1.2 : ℚ) =
        shortRelationIntercept R := by
  obtain ⟨hd, hα, hβ⟩ := shortRelation_factorization R
  have hdz : (shortRelationD R : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hdq : (shortRelationD R : ℚ) ≠ 0 := by exact_mod_cast hdz
  have heqZ : (shortRelationD R : ℤ) *
      (shortRelationP R * (t.1.1 : ℤ) +
        shortRelationQ R * (t.1.2 : ℤ)) = -R.γ * (t.2 : ℤ) := by
    nlinarith [R.equation]
  have heqQ : (shortRelationD R : ℚ) *
      ((shortRelationP R : ℚ) * (t.1.1 : ℚ) +
        (shortRelationQ R : ℚ) * (t.1.2 : ℚ)) =
          -(R.γ : ℚ) * (t.2 : ℚ) := by exact_mod_cast heqZ
  unfold shortRelationIntercept rationalIntercept
  apply (eq_div_iff hdq).2
  calc
    _ = (shortRelationD R : ℚ) *
        ((shortRelationP R : ℚ) * (t.1.1 : ℚ) +
          (shortRelationQ R : ℚ) * (t.1.2 : ℚ)) := by ring
    _ = -(R.γ : ℚ) * (t.2 : ℚ) := heqQ
    _ = ((-R.γ : ℤ) : ℚ) * (t.2 : ℚ) := by norm_num

/-- 第 180–187 行：选定截距属于原截距集，且第三个速度属于 `C_r`。 -/
theorem shortRelation_intercept_membership {H : ℕ}
    {t : (ℕ × ℕ) × ℕ} (R : NonzeroShortRelation H t)
    (V : Finset ℕ) (hc : t.2 ∈ V) :
    shortRelationIntercept R ∈
      rationalIntercepts V H (H / shortRelationScale R) ∧
    t.2 ∈ interceptCore V H (H / shortRelationScale R)
      (shortRelationIntercept R) := by
  have hγ : -R.γ ∈ interceptNumerators H := by
    apply (mem_interceptNumerators_iff H (-R.γ)).2
    simpa only [Int.natAbs_neg] using
      (show 0 < R.γ.natAbs ∧ R.γ.natAbs ≤ H from
        ⟨Int.natAbs_pos.mpr R.γ_ne, R.γ_le⟩)
  have hd : shortRelationD R ∈ interceptDenominators
      (H / shortRelationScale R) := by
    exact Finset.mem_Icc.mpr
      ⟨(shortRelation_dyadic_bounds R).2.2.2.2.1,
        (shortRelation_dyadic_bounds R).2.2.2.2.2.1⟩
  have hcore : t.2 ∈ interceptCore V H (H / shortRelationScale R)
      (shortRelationIntercept R) :=
    (interceptCore_mem_iff V H _ _ _).2
      ⟨hc, -R.γ, hγ, shortRelationD R, hd, rfl⟩
  exact ⟨interceptCore_mem_rationalIntercepts V H _ _ _ hcore, hcore⟩

/-- 单个二进层的真实关联数据：方向、截距、关联速度对，以及可选第三速度。 -/
noncomputable def shortRelationLayerCodes (M : ℕ) (V : Finset ℕ) (H D : ℕ) :
    Finset (Σ z : (ℤ × ℤ) × ℚ, (ℕ × ℕ) × ℕ) :=
  ((primitiveDirections M).product (rationalIntercepts V H D)).sigma fun z =>
    (((V.product V).filter fun ab =>
      (z.1.1 : ℚ) * (ab.1 : ℚ) + (z.1.2 : ℚ) * (ab.2 : ℚ) = z.2).product
      (interceptCore V H D z.2))

/-- 所有 `M=2^j` 层的关联数据，`0≤j≤⌊log₂ H⌋`。 -/
noncomputable def shortRelationAllCodes (V : Finset ℕ) (H : ℕ) :
    Finset (Σ j : ℕ, Σ z : (ℤ × ℤ) × ℚ, (ℕ × ℕ) × ℕ) :=
  (Finset.Icc 0 (Nat.log 2 H)).sigma fun j =>
    shortRelationLayerCodes (2 ^ j) V H (H / 2 ^ j)

/-- 每个合格三元组用其一次性选定关系编码；数据最后分量仍是原三元组。 -/
noncomputable def chosenShortRelationCode (V : Finset ℕ) (H : ℕ)
    (t : {t : (ℕ × ℕ) × ℕ // t ∈ nonzeroShortTriples V H}) :
    Σ j : ℕ, Σ z : (ℤ × ℤ) × ℚ, (ℕ × ℕ) × ℕ :=
  let R := chosenNonzeroRelation V H t
  ⟨shortRelationIndex R,
    ⟨((shortRelationP R, shortRelationQ R), shortRelationIntercept R), t.1⟩⟩

/-- 编码保留 `(a,b,c)`，所以对三元组单射；选定关系本身无须单射。 -/
theorem chosenShortRelationCode_injective (V : Finset ℕ) (H : ℕ) :
    Function.Injective (chosenShortRelationCode V H) := by
  intro t u heq
  apply Subtype.ext
  exact congrArg (fun z : Σ j : ℕ, Σ d : (ℤ × ℤ) × ℚ, (ℕ × ℕ) × ℕ => z.2.2) heq

/-- 编码确实落在对应的方向、截距、点线关联和第三速度构成的有限数据集。 -/
theorem chosenShortRelationCode_mem (V : Finset ℕ) (H : ℕ)
    (t : {t : (ℕ × ℕ) × ℕ // t ∈ nonzeroShortTriples V H}) :
    chosenShortRelationCode V H t ∈ shortRelationAllCodes V H := by
  let R := chosenNonzeroRelation V H t
  have htriple : t.1 ∈ increasingTriples V :=
    ((mem_nonzeroShortTriples_iff V H t.1).mp t.2).1
  obtain ⟨ha, hb, hc, _, _⟩ := (mem_increasingTriples_iff V t.1).mp htriple
  have hbounds := shortRelation_dyadic_bounds R
  have hmemD := shortRelation_mem_primitiveDirections R
  obtain ⟨hr, hcore⟩ := shortRelation_intercept_membership R V hc
  have hab : t.1.1 ∈ V.product V := Finset.mem_product.mpr ⟨ha, hb⟩
  have hinc : t.1.1 ∈
      (V.product V).filter (fun ab =>
        (shortRelationP R : ℚ) * (ab.1 : ℚ) +
          (shortRelationQ R : ℚ) * (ab.2 : ℚ) = shortRelationIntercept R) :=
    Finset.mem_filter.mpr ⟨hab, shortRelation_incidence_equation R⟩
  change (⟨shortRelationIndex R,
      ⟨((shortRelationP R, shortRelationQ R), shortRelationIntercept R), t.1⟩⟩ :
      Σ j : ℕ, Σ z : (ℤ × ℤ) × ℚ, (ℕ × ℕ) × ℕ) ∈ shortRelationAllCodes V H
  apply Finset.mem_sigma.mpr
  constructor
  · exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, hbounds.2.2.2.2.2.2⟩
  · apply Finset.mem_sigma.mpr
    constructor
    · exact Finset.mem_product.mpr ⟨hmemD, hr⟩
    · exact Finset.mem_product.mpr ⟨hinc, hcore⟩

/-- 逐层数据的基数恰为参数关联数：每个关联速度对可配 `w(r)` 个第三速度。 -/
theorem shortRelationLayerCodes_card (M : ℕ) (V : Finset ℕ) (H D : ℕ) :
    (shortRelationLayerCodes M V H D).card =
      ∑ d ∈ primitiveDirections M, ∑ r ∈ rationalIntercepts V H D,
        interceptWeight V H D r *
          ((V.product V).filter fun ab =>
            (d.1 : ℚ) * (ab.1 : ℚ) + (d.2 : ℚ) * (ab.2 : ℚ) = r).card := by
  classical
  unfold shortRelationLayerCodes
  rw [Finset.card_sigma]
  calc
    (∑ z ∈ (primitiveDirections M).product (rationalIntercepts V H D),
        (((V.product V).filter fun ab =>
          (z.1.1 : ℚ) * (ab.1 : ℚ) + (z.1.2 : ℚ) * (ab.2 : ℚ) = z.2).product
            (interceptCore V H D z.2)).card) =
      (∑ z ∈ (primitiveDirections M).product (rationalIntercepts V H D),
        interceptWeight V H D z.2 *
          ((V.product V).filter fun ab =>
            (z.1.1 : ℚ) * (ab.1 : ℚ) +
              (z.1.2 : ℚ) * (ab.2 : ℚ) = z.2).card) := by
        apply Finset.sum_congr rfl
        intro z hz
        exact (Finset.card_product _ _).trans (by simp [interceptWeight, Nat.mul_comm])
    _ = _ := by
      exact (Finset.sum_product _ _ _).trans (by rfl)

/-- 全部二进层的数据基数精确等于各层加权关联和的自然数版本。 -/
theorem shortRelationAllCodes_card (V : Finset ℕ) (H : ℕ) :
    (shortRelationAllCodes V H).card =
      ∑ j ∈ Finset.Icc 0 (Nat.log 2 H),
        ∑ d ∈ primitiveDirections (2 ^ j),
          ∑ r ∈ rationalIntercepts V H (H / 2 ^ j),
            interceptWeight V H (H / 2 ^ j) r *
              ((V.product V).filter fun ab =>
                (d.1 : ℚ) * (ab.1 : ℚ) + (d.2 : ℚ) * (ab.2 : ℚ) = r).card := by
  classical
  unfold shortRelationAllCodes
  rw [Finset.card_sigma]
  apply Finset.sum_congr rfl
  intro j hj
  exact shortRelationLayerCodes_card (2 ^ j) V H (H / 2 ^ j)

/-- 全部实际关联数据的基数转为实数后，恰是 `dyadic_direction_incidence_bound`
    左侧沿 `j` 的有限和，没有把计数界作为输入假设。 -/
theorem shortRelationAllCodes_card_real (V : Finset ℕ) (H : ℕ) :
    ((shortRelationAllCodes V H).card : ℝ) =
      ∑ j ∈ Finset.Icc 0 (Nat.log 2 H),
        ∑ d ∈ primitiveDirections (2 ^ j),
          ∑ r ∈ rationalIntercepts V H (H / 2 ^ j),
            (interceptWeight V H (H / 2 ^ j) r : ℝ) *
              (((V.product V).filter fun ab =>
                (d.1 : ℚ) * (ab.1 : ℚ) + (d.2 : ℚ) * (ab.2 : ℚ) = r).card : ℝ) := by
  rw [shortRelationAllCodes_card]
  simp only [Nat.cast_sum, Nat.cast_mul]

/-- 第 185–189 行的非零系数编码计数：合格三元组数至多为各二进层的
    真实参数加权关联数之和，空速度集也包含在内。 -/
theorem nonzeroShortTriples_card_le_dyadic_incidence (V : Finset ℕ) (H : ℕ)
    (_hH : 1 ≤ H) :
    ((nonzeroShortTriples V H).card : ℝ) ≤
      ∑ j ∈ Finset.Icc 0 (Nat.log 2 H),
        ∑ d ∈ primitiveDirections (2 ^ j),
          ∑ r ∈ rationalIntercepts V H (H / 2 ^ j),
            (interceptWeight V H (H / 2 ^ j) r : ℝ) *
              (((V.product V).filter fun ab =>
                (d.1 : ℚ) * (ab.1 : ℚ) + (d.2 : ℚ) * (ab.2 : ℚ) = r).card : ℝ) := by
  classical
  have hinj := chosenShortRelationCode_injective V H
  have hsubset :
      ((nonzeroShortTriples V H).attach.image (chosenShortRelationCode V H)) ⊆
        shortRelationAllCodes V H := by
    intro z hz
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
    exact chosenShortRelationCode_mem V H t
  have hcard : (nonzeroShortTriples V H).card ≤
      (shortRelationAllCodes V H).card := by
    calc
      _ = (nonzeroShortTriples V H).attach.card := (Finset.card_attach).symm
      _ = ((nonzeroShortTriples V H).attach.image
          (chosenShortRelationCode V H)).card :=
        (Finset.card_image_of_injective _ hinj).symm
      _ ≤ (shortRelationAllCodes V H).card := Finset.card_le_card hsubset
  rw [← shortRelationAllCodes_card_real V H]
  exact_mod_cast hcard

end LonelyRunner
