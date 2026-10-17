import LonelyRunner.ShortRelationEncoding
import LonelyRunner.RelationLatticeCount

/-!
# 零系数短关系的有限计数

对应 `paper/lonely_runner_zh.tex` 的 `lem:relations` 证明第 170–176 行。
本文件仅给出零系数部分的有限计数和 `λ` 所定义集合的覆盖分解。
-/

open Classical

namespace LonelyRunner

/-- 三元组的非平凡短整数关系，至少一个系数为零。 -/
structure ZeroShortRelation (H : ℕ) (t : (ℕ × ℕ) × ℕ) where
  α : ℤ
  β : ℤ
  γ : ℤ
  nontrivial : α ≠ 0 ∨ β ≠ 0 ∨ γ ≠ 0
  hasZero : α = 0 ∨ β = 0 ∨ γ = 0
  α_le : α.natAbs ≤ H
  β_le : β.natAbs ≤ H
  γ_le : γ.natAbs ≤ H
  equation : α * (t.1.1 : ℤ) + β * (t.1.2 : ℤ) + γ * (t.2 : ℤ) = 0

/-- 结构中的三个逐项界与原文 `max(|α|,|β|,|γ|)≤H` 完全等价。 -/
theorem zeroShortRelation_iff_original (H : ℕ) (t : (ℕ × ℕ) × ℕ) :
    Nonempty (ZeroShortRelation H t) ↔
      ∃ α β γ : ℤ,
        (α ≠ 0 ∨ β ≠ 0 ∨ γ ≠ 0) ∧
        (α = 0 ∨ β = 0 ∨ γ = 0) ∧
        max α.natAbs (max β.natAbs γ.natAbs) ≤ H ∧
        α * (t.1.1 : ℤ) + β * (t.1.2 : ℤ) + γ * (t.2 : ℤ) = 0 := by
  constructor
  · rintro ⟨R⟩
    exact ⟨R.α, R.β, R.γ, R.nontrivial, R.hasZero,
      max_le R.α_le (max_le R.β_le R.γ_le), R.equation⟩
  · rintro ⟨α, β, γ, hne, hz, hmax, heq⟩
    exact ⟨⟨α, β, γ, hne, hz, by omega, by omega, by omega, heq⟩⟩

/-- 论文第 176 行的零系数短关系三元组集合，直接使用原整数关系定义。 -/
noncomputable def zeroShortTriples (V : Finset ℕ) (H : ℕ) :
    Finset ((ℕ × ℕ) × ℕ) :=
  (increasingTriples V).filter fun t => Nonempty (ZeroShortRelation H t)

theorem mem_zeroShortTriples_iff (V : Finset ℕ) (H : ℕ)
    (t : (ℕ × ℕ) × ℕ) :
    t ∈ zeroShortTriples V H ↔
      t ∈ increasingTriples V ∧ Nonempty (ZeroShortRelation H t) := by
  simp [zeroShortTriples]

/-- 同一三元组的零系数关系也只选一次。 -/
noncomputable def chosenZeroRelation (V : Finset ℕ) (H : ℕ)
    (t : {t : (ℕ × ℕ) × ℕ // t ∈ zeroShortTriples V H}) :
    ZeroShortRelation H t.1 :=
  Classical.choice ((mem_zeroShortTriples_iff V H t.1).mp t.2).2

/-- 正整数速度下，两项非零关系的系数必异号，绝对值满足等比例关系。 -/
theorem twoSpeedRelation_sign_and_abs (x y : ℕ) (hx : 0 < x) (hy : 0 < y)
    (u v : ℤ) (hu : u ≠ 0) (hv : v ≠ 0)
    (hrel : u * (x : ℤ) + v * (y : ℤ) = 0) :
    ((0 < u ∧ v < 0) ∨ (u < 0 ∧ 0 < v)) ∧
      u.natAbs * x = v.natAbs * y := by
  have hxZ : (0 : ℤ) < x := by exact_mod_cast hx
  have hyZ : (0 : ℤ) < y := by exact_mod_cast hy
  have hsign : (0 < u ∧ v < 0) ∨ (u < 0 ∧ 0 < v) := by
    by_cases hup : 0 < u
    · left
      refine ⟨hup, ?_⟩
      by_contra hnot
      have hv0 : 0 ≤ v := by omega
      nlinarith [mul_pos hup hxZ, mul_nonneg hv0 hyZ.le]
    · right
      have hun : u < 0 := by omega
      refine ⟨hun, ?_⟩
      by_contra hnot
      have hv0 : v ≤ 0 := by omega
      nlinarith [mul_pos (show 0 < -u by omega) hxZ,
        mul_nonneg (show 0 ≤ -v by omega) hyZ.le]
  have heq : u * (x : ℤ) = -(v * (y : ℤ)) := by omega
  have habs := congrArg Int.natAbs heq
  simp only [Int.natAbs_mul, Int.natAbs_neg] at habs
  simpa using ⟨hsign, habs⟩

/-- 正速度下，非平凡零系数关系恰有一个零系数。 -/
theorem zeroShortRelation_exactly_one_zero {H : ℕ} {t : (ℕ × ℕ) × ℕ}
    (ha : 0 < t.1.1) (hb : 0 < t.1.2) (hc : 0 < t.2)
    (R : ZeroShortRelation H t) :
    (R.α = 0 ∧ R.β ≠ 0 ∧ R.γ ≠ 0) ∨
      (R.α ≠ 0 ∧ R.β = 0 ∧ R.γ ≠ 0) ∨
      (R.α ≠ 0 ∧ R.β ≠ 0 ∧ R.γ = 0) := by
  have haZ : (t.1.1 : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ha)
  have hbZ : (t.1.2 : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  have hcZ : (t.2 : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hc)
  rcases R.hasZero with hα | hβ | hγ
  · have hβ : R.β ≠ 0 := by
      intro hβ
      have hγ : R.γ = 0 := by
        have hprod : R.γ * (t.2 : ℤ) = 0 := by simpa [hα, hβ] using R.equation
        exact (mul_eq_zero.mp hprod).resolve_right hcZ
      rcases R.nontrivial with hn | hn | hn <;> contradiction
    have hγ : R.γ ≠ 0 := by
      intro hγ
      have hprod : R.β * (t.1.2 : ℤ) = 0 := by simpa [hα, hγ] using R.equation
      exact hβ ((mul_eq_zero.mp hprod).resolve_right hbZ)
    exact Or.inl ⟨hα, hβ, hγ⟩
  · have hα : R.α ≠ 0 := by
      intro hα
      have hprod : R.γ * (t.2 : ℤ) = 0 := by simpa [hα, hβ] using R.equation
      have hγ := (mul_eq_zero.mp hprod).resolve_right hcZ
      rcases R.nontrivial with hn | hn | hn <;> contradiction
    have hγ : R.γ ≠ 0 := by
      intro hγ
      have hprod : R.α * (t.1.1 : ℤ) = 0 := by simpa [hβ, hγ] using R.equation
      exact hα ((mul_eq_zero.mp hprod).resolve_right haZ)
    exact Or.inr (Or.inl ⟨hα, hβ, hγ⟩)
  · have hα : R.α ≠ 0 := by
      intro hα
      have hprod : R.β * (t.1.2 : ℤ) = 0 := by simpa [hα, hγ] using R.equation
      have hβ := (mul_eq_zero.mp hprod).resolve_right hbZ
      rcases R.nontrivial with hn | hn | hn <;> contradiction
    have hβ : R.β ≠ 0 := by
      intro hβ
      have hprod : R.α * (t.1.1 : ℤ) = 0 := by simpa [hβ, hγ] using R.equation
      exact hα ((mul_eq_zero.mp hprod).resolve_right haZ)
    exact Or.inr (Or.inr ⟨hα, hβ, hγ⟩)

/-- 零系数的三个位置中，另外两系数严格异号且绝对值都在 `1..H`。 -/
theorem zeroShortRelation_remaining_signs {H : ℕ} {t : (ℕ × ℕ) × ℕ}
    (ha : 0 < t.1.1) (hb : 0 < t.1.2) (hc : 0 < t.2)
    (R : ZeroShortRelation H t) :
    (R.α = 0 ∧
      ((0 < R.β ∧ R.γ < 0) ∨ (R.β < 0 ∧ 0 < R.γ)) ∧
      R.β.natAbs ∈ Finset.Icc 1 H ∧ R.γ.natAbs ∈ Finset.Icc 1 H) ∨
    (R.β = 0 ∧
      ((0 < R.α ∧ R.γ < 0) ∨ (R.α < 0 ∧ 0 < R.γ)) ∧
      R.α.natAbs ∈ Finset.Icc 1 H ∧ R.γ.natAbs ∈ Finset.Icc 1 H) ∨
    (R.γ = 0 ∧
      ((0 < R.α ∧ R.β < 0) ∨ (R.α < 0 ∧ 0 < R.β)) ∧
      R.α.natAbs ∈ Finset.Icc 1 H ∧ R.β.natAbs ∈ Finset.Icc 1 H) := by
  rcases zeroShortRelation_exactly_one_zero ha hb hc R with
      ⟨hα, hβ, hγ⟩ | ⟨hα, hβ, hγ⟩ | ⟨hα, hβ, hγ⟩
  · have hrel : R.β * (t.1.2 : ℤ) + R.γ * (t.2 : ℤ) = 0 := by
      simpa [hα] using R.equation
    left
    exact ⟨hα, (twoSpeedRelation_sign_and_abs t.1.2 t.2 hb hc
      R.β R.γ hβ hγ hrel).1,
      Finset.mem_Icc.mpr ⟨Int.natAbs_pos.mpr hβ, R.β_le⟩,
      Finset.mem_Icc.mpr ⟨Int.natAbs_pos.mpr hγ, R.γ_le⟩⟩
  · have hrel : R.α * (t.1.1 : ℤ) + R.γ * (t.2 : ℤ) = 0 := by
      simpa [hβ] using R.equation
    right; left
    exact ⟨hβ, (twoSpeedRelation_sign_and_abs t.1.1 t.2 ha hc
      R.α R.γ hα hγ hrel).1,
      Finset.mem_Icc.mpr ⟨Int.natAbs_pos.mpr hα, R.α_le⟩,
      Finset.mem_Icc.mpr ⟨Int.natAbs_pos.mpr hγ, R.γ_le⟩⟩
  · have hrel : R.α * (t.1.1 : ℤ) + R.β * (t.1.2 : ℤ) = 0 := by
      simpa [hγ] using R.equation
    right; right
    exact ⟨hγ, (twoSpeedRelation_sign_and_abs t.1.1 t.1.2 ha hb
      R.α R.β hα hβ hrel).1,
      Finset.mem_Icc.mpr ⟨Int.natAbs_pos.mpr hα, R.α_le⟩,
      Finset.mem_Icc.mpr ⟨Int.natAbs_pos.mpr hβ, R.β_le⟩⟩

/-- 零位置、固定速度、自由速度、两个正系数绝对值的编码类型。 -/
private abbrev ZeroRelationCode := Fin 3 × ((ℕ × ℕ) × (ℕ × ℕ))

/-- 从一次性选定的零系数关系得到有限参数编码。 -/
private def zeroRelationCode {H : ℕ} {t : (ℕ × ℕ) × ℕ}
    (R : ZeroShortRelation H t) : ZeroRelationCode :=
  if R.α = 0 then
    (0, ((t.1.2, t.1.1), (R.β.natAbs, R.γ.natAbs)))
  else if R.β = 0 then
    (1, ((t.1.1, t.1.2), (R.α.natAbs, R.γ.natAbs)))
  else
    (2, ((t.1.1, t.2), (R.α.natAbs, R.β.natAbs)))

/-- 固定一个速度及两个绝对值后，另一速度由整数除法唯一恢复。 -/
private def decodeZeroRelationCode (z : ZeroRelationCode) : (ℕ × ℕ) × ℕ :=
  if z.1 = 0 then
    ((z.2.1.2, z.2.1.1), z.2.2.1 * z.2.1.1 / z.2.2.2)
  else if z.1 = 1 then
    ((z.2.1.1, z.2.1.2), z.2.2.1 * z.2.1.1 / z.2.2.2)
  else
    ((z.2.1.1, z.2.2.1 * z.2.1.1 / z.2.2.2), z.2.1.2)

/-- 对正速度，编码的解码结果恰是原三元组；证明了固定数据唯一确定剩余速度。 -/
private theorem decode_zeroRelationCode {H : ℕ} {t : (ℕ × ℕ) × ℕ}
    (ha : 0 < t.1.1) (hb : 0 < t.1.2) (hc : 0 < t.2)
    (R : ZeroShortRelation H t) : decodeZeroRelationCode (zeroRelationCode R) = t := by
  rcases zeroShortRelation_exactly_one_zero ha hb hc R with
      ⟨hα, hβ, hγ⟩ | ⟨hα, hβ, hγ⟩ | ⟨hα, hβ, hγ⟩
  · have hrel : R.β * (t.1.2 : ℤ) + R.γ * (t.2 : ℤ) = 0 := by
      simpa [hα] using R.equation
    have habs := (twoSpeedRelation_sign_and_abs t.1.2 t.2 hb hc
      R.β R.γ hβ hγ hrel).2
    have hv : 0 < R.γ.natAbs := Int.natAbs_pos.mpr hγ
    have hdiv : R.β.natAbs * t.1.2 / R.γ.natAbs = t.2 := by
      rw [habs, Nat.mul_div_cancel_left _ hv]
    simp [zeroRelationCode, decodeZeroRelationCode, hα, hdiv]
  · have hrel : R.α * (t.1.1 : ℤ) + R.γ * (t.2 : ℤ) = 0 := by
      simpa [hβ] using R.equation
    have habs := (twoSpeedRelation_sign_and_abs t.1.1 t.2 ha hc
      R.α R.γ hα hγ hrel).2
    have hv : 0 < R.γ.natAbs := Int.natAbs_pos.mpr hγ
    have hdiv : R.α.natAbs * t.1.1 / R.γ.natAbs = t.2 := by
      rw [habs, Nat.mul_div_cancel_left _ hv]
    simp [zeroRelationCode, decodeZeroRelationCode, hα, hβ, hdiv]
  · have hrel : R.α * (t.1.1 : ℤ) + R.β * (t.1.2 : ℤ) = 0 := by
      simpa [hγ] using R.equation
    have habs := (twoSpeedRelation_sign_and_abs t.1.1 t.1.2 ha hb
      R.α R.β hα hβ hrel).2
    have hv : 0 < R.β.natAbs := Int.natAbs_pos.mpr hβ
    have hdiv : R.α.natAbs * t.1.1 / R.β.natAbs = t.1.2 := by
      rw [habs, Nat.mul_div_cancel_left _ hv]
    simp [zeroRelationCode, decodeZeroRelationCode, hα, hβ, hdiv]

/-- 三个零位置、两个速度及两个 `1..H` 的正系数构成的有限编码全集。 -/
private def zeroRelationCodeSet (V : Finset ℕ) (H : ℕ) : Finset ZeroRelationCode :=
  (Finset.univ : Finset (Fin 3)).product
    ((V.product V).product ((Finset.Icc 1 H).product (Finset.Icc 1 H)))

/-- 每个三元组从其固定关系产生的唯一编码。 -/
private noncomputable def chosenZeroCode (V : Finset ℕ) (H : ℕ)
    (t : {t : (ℕ × ℕ) × ℕ // t ∈ zeroShortTriples V H}) : ZeroRelationCode :=
  zeroRelationCode (chosenZeroRelation V H t)

/-- 选定关系产生的编码确实使用 `V` 中两个速度及 `1..H` 中两个绝对值。 -/
private theorem chosenZeroCode_mem (V : Finset ℕ) (H : ℕ)
    (hV : ∀ v ∈ V, 0 < v)
    (t : {t : (ℕ × ℕ) × ℕ // t ∈ zeroShortTriples V H}) :
    chosenZeroCode V H t ∈ zeroRelationCodeSet V H := by
  let R := chosenZeroRelation V H t
  have ht : t.1 ∈ increasingTriples V :=
    ((mem_zeroShortTriples_iff V H t.1).mp t.2).1
  obtain ⟨haV, hbV, hcV, _, _⟩ := (mem_increasingTriples_iff V t.1).mp ht
  have ha := hV _ haV
  have hb := hV _ hbV
  have hc := hV _ hcV
  change zeroRelationCode R ∈ zeroRelationCodeSet V H
  rcases zeroShortRelation_exactly_one_zero ha hb hc R with
      ⟨hα, hβ, hγ⟩ | ⟨hα, hβ, hγ⟩ | ⟨hα, hβ, hγ⟩
  · have hβI : R.β.natAbs ∈ Finset.Icc 1 H :=
      Finset.mem_Icc.mpr ⟨Int.natAbs_pos.mpr hβ, R.β_le⟩
    have hγI : R.γ.natAbs ∈ Finset.Icc 1 H :=
      Finset.mem_Icc.mpr ⟨Int.natAbs_pos.mpr hγ, R.γ_le⟩
    simp [zeroRelationCode, zeroRelationCodeSet,
      hα, haV, hbV, hβI, hγI]
  · have hαI : R.α.natAbs ∈ Finset.Icc 1 H :=
      Finset.mem_Icc.mpr ⟨Int.natAbs_pos.mpr hα, R.α_le⟩
    have hγI : R.γ.natAbs ∈ Finset.Icc 1 H :=
      Finset.mem_Icc.mpr ⟨Int.natAbs_pos.mpr hγ, R.γ_le⟩
    simp [zeroRelationCode, zeroRelationCodeSet,
      hα, hβ, haV, hbV, hαI, hγI]
  · have hαI : R.α.natAbs ∈ Finset.Icc 1 H :=
      Finset.mem_Icc.mpr ⟨Int.natAbs_pos.mpr hα, R.α_le⟩
    have hβI : R.β.natAbs ∈ Finset.Icc 1 H :=
      Finset.mem_Icc.mpr ⟨Int.natAbs_pos.mpr hβ, R.β_le⟩
    simp [zeroRelationCode, zeroRelationCodeSet,
      hα, hβ, haV, hcV, hαI, hβI]

/-- 解码恒等式给出选定编码的单射，而不是把唯一性作为假设。 -/
private theorem chosenZeroCode_injective (V : Finset ℕ) (H : ℕ)
    (hV : ∀ v ∈ V, 0 < v) : Function.Injective (chosenZeroCode V H) := by
  intro t u heq
  have ht : t.1 ∈ increasingTriples V :=
    ((mem_zeroShortTriples_iff V H t.1).mp t.2).1
  have hu : u.1 ∈ increasingTriples V :=
    ((mem_zeroShortTriples_iff V H u.1).mp u.2).1
  obtain ⟨hta, htb, htc, _, _⟩ := (mem_increasingTriples_iff V t.1).mp ht
  obtain ⟨hua, hub, huc, _, _⟩ := (mem_increasingTriples_iff V u.1).mp hu
  have hdecodeT := decode_zeroRelationCode (hV _ hta) (hV _ htb) (hV _ htc)
    (chosenZeroRelation V H t)
  have hdecodeU := decode_zeroRelationCode (hV _ hua) (hV _ hub) (hV _ huc)
    (chosenZeroRelation V H u)
  apply Subtype.ext
  calc
    t.1 = decodeZeroRelationCode (chosenZeroCode V H t) := hdecodeT.symm
    _ = decodeZeroRelationCode (chosenZeroCode V H u) := by rw [heq]
    _ = u.1 := hdecodeU

/-- 编码全集恰有 `3 |V|² H²` 个元素，空速度集也满足该式。 -/
private theorem zeroRelationCodeSet_card (V : Finset ℕ) (H : ℕ) :
    (zeroRelationCodeSet V H).card = 3 * V.card ^ 2 * H ^ 2 := by
  classical
  unfold zeroRelationCodeSet
  simp [Finset.card_product, pow_two]
  ring

/-- 论文第 176 行的零系数三元组显式计数；证明给出更强的系数 `3`。 -/
theorem zeroShortTriples_card_le (V : Finset ℕ) (H : ℕ)
    (hV : ∀ v ∈ V, 0 < v) (_hH : 1 ≤ H) :
    (zeroShortTriples V H).card ≤ 12 * V.card ^ 2 * H ^ 2 := by
  classical
  have hsubset :
      (zeroShortTriples V H).attach.image (chosenZeroCode V H) ⊆
        zeroRelationCodeSet V H := by
    intro z hz
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
    exact chosenZeroCode_mem V H hV t
  have hcard : (zeroShortTriples V H).card ≤ (zeroRelationCodeSet V H).card := by
    calc
      _ = (zeroShortTriples V H).attach.card := (Finset.card_attach).symm
      _ = ((zeroShortTriples V H).attach.image (chosenZeroCode V H)).card :=
        (Finset.card_image_of_injective _ (chosenZeroCode_injective V H hV)).symm
      _ ≤ _ := Finset.card_le_card hsubset
  rw [zeroRelationCodeSet_card] at hcard
  nlinarith

/-- 按论文的最小最大范数 `λ(a,b,c)` 定义全部短关系三元组。 -/
noncomputable def shortTriples (V : Finset ℕ) (H : ℕ) :
    Finset ((ℕ × ℕ) × ℕ) :=
  (increasingTriples V).filter fun t =>
    relationLambda t.1.1 t.1.2 t.2 ≤ H

theorem mem_shortTriples_iff (V : Finset ℕ) (H : ℕ)
    (t : (ℕ × ℕ) × ℕ) :
    t ∈ shortTriples V H ↔
      t ∈ increasingTriples V ∧ relationLambda t.1.1 t.1.2 t.2 ≤ H := by
  simp [shortTriples]

/-- 最短关系实际取到，因此每个 `λ≤H` 的三元组属于零系数或全非零类；
    这里只证明并集覆盖，不把两类未经证明地视为不交。 -/
theorem shortTriples_subset_zero_union_nonzero (V : Finset ℕ) (H : ℕ)
    (hV : ∀ v ∈ V, 0 < v) :
    shortTriples V H ⊆ zeroShortTriples V H ∪ nonzeroShortTriples V H := by
  intro t ht
  obtain ⟨htV, hLamH⟩ := (mem_shortTriples_iff V H t).mp ht
  obtain ⟨haV, hbV, hcV, _, _⟩ := (mem_increasingTriples_iff V t).mp htV
  obtain ⟨w, hw, hwne, hmax⟩ :=
    (relationLambda_pos_and_attained t.1.1 t.1.2 t.2 (hV _ hbV)).2
  have hmaxH : relationMaxAbs w ≤ H := by omega
  have hαH : (w 0).natAbs ≤ H := by unfold relationMaxAbs at hmaxH; omega
  have hβH : (w 1).natAbs ≤ H := by unfold relationMaxAbs at hmaxH; omega
  have hγH : (w 2).natAbs ≤ H := by unfold relationMaxAbs at hmaxH; omega
  have heq : (w 0) * (t.1.1 : ℤ) + (w 1) * (t.1.2 : ℤ) +
      (w 2) * (t.2 : ℤ) = 0 := by
    change (t.1.1 : ℤ) * w 0 + (t.1.2 : ℤ) * w 1 +
      (t.2 : ℤ) * w 2 = 0 at hw
    nlinarith [hw]
  have hnontrivial : w 0 ≠ 0 ∨ w 1 ≠ 0 ∨ w 2 ≠ 0 := by
    by_contra h
    push Not at h
    apply hwne
    funext i
    fin_cases i <;> simp [h.1, h.2.1, h.2.2]
  by_cases hz : w 0 = 0 ∨ w 1 = 0 ∨ w 2 = 0
  · apply Finset.mem_union.mpr
    left
    apply (mem_zeroShortTriples_iff V H t).2
    refine ⟨htV, ⟨{
      α := w 0
      β := w 1
      γ := w 2
      nontrivial := hnontrivial
      hasZero := hz
      α_le := hαH
      β_le := hβH
      γ_le := hγH
      equation := heq
    }⟩⟩
  · have hα : w 0 ≠ 0 := by tauto
    have hβ : w 1 ≠ 0 := by tauto
    have hγ : w 2 ≠ 0 := by tauto
    have hnormal : Nonempty (NonzeroShortRelation H t) :=
      (nonzeroRelation_iff_normalized H t).1
        ⟨w 0, w 1, w 2, hα, hβ, hγ, hαH, hβH, hγH, heq⟩
    apply Finset.mem_union.mpr
    right
    exact (mem_nonzeroShortTriples_iff V H t).2 ⟨htV, hnormal⟩

/-- 并集覆盖给出无需不交性的自然数基数界。 -/
theorem shortTriples_card_le_sum (V : Finset ℕ) (H : ℕ)
    (hV : ∀ v ∈ V, 0 < v) :
    (shortTriples V H).card ≤
      (zeroShortTriples V H).card + (nonzeroShortTriples V H).card := by
  calc
    _ ≤ (zeroShortTriples V H ∪ nonzeroShortTriples V H).card :=
      Finset.card_le_card (shortTriples_subset_zero_union_nonzero V H hV)
    _ ≤ _ := Finset.card_union_le _ _

/-- 本轮合并后的显式界；右侧保留已证明的非零系数二进关联和。 -/
theorem shortTriples_card_le_zero_and_dyadic (V : Finset ℕ) (H : ℕ)
    (hV : ∀ v ∈ V, 0 < v) (hH : 1 ≤ H) :
    ((shortTriples V H).card : ℝ) ≤
      (12 * V.card ^ 2 * H ^ 2 : ℕ) +
        ∑ j ∈ Finset.Icc 0 (Nat.log 2 H),
          ∑ d ∈ primitiveDirections (2 ^ j),
            ∑ r ∈ rationalIntercepts V H (H / 2 ^ j),
              (interceptWeight V H (H / 2 ^ j) r : ℝ) *
                (((V.product V).filter fun ab =>
                  (d.1 : ℚ) * (ab.1 : ℚ) + (d.2 : ℚ) * (ab.2 : ℚ) = r).card : ℝ) := by
  have hcard := shortTriples_card_le_sum V H hV
  have hzero := zeroShortTriples_card_le V H hV hH
  have hnonzero := nonzeroShortTriples_card_le_dyadic_incidence V H hH
  have hcardR : ((shortTriples V H).card : ℝ) ≤
      ((zeroShortTriples V H).card : ℝ) +
        ((nonzeroShortTriples V H).card : ℝ) := by exact_mod_cast hcard
  have hzeroR : ((zeroShortTriples V H).card : ℝ) ≤
      (12 * V.card ^ 2 * H ^ 2 : ℕ) := by exact_mod_cast hzero
  linarith

end LonelyRunner
