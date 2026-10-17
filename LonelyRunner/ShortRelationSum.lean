import LonelyRunner.ShortRelationCount
import Mathlib.Data.Nat.Sqrt

/-!
# 短关系倒数总和

对应 `paper/lonely_runner_zh.tex` 的 `lem:relations`。本文件的无条件界保留
`S₂(V)=inversePairGcdSum V`；最后的论文型幂次界明确以 GCD 和界为参数。
-/

open Classical
open scoped Real

namespace LonelyRunner

/-- 整数截断所需的有限望远镜求和。 -/
private theorem shortRelation_kernel_sum (i j : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) :
    (∑ h ∈ Finset.Ico i j, (1 : ℝ) / ((h : ℝ) * (h + 1))) =
      1 / (i : ℝ) - 1 / (j : ℝ) := by
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hj ih =>
      rw [Finset.sum_Ico_succ_top (by omega), ih]
      have hj0 : (0 : ℝ) < j := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < i) hj)
      have hj1 : (0 : ℝ) < j + 1 := by positivity
      push_cast
      field_simp
      ring

/-- 对任意正整数 λ，倒数可由有限层计数核及尾项控制。 -/
private theorem shortRelation_inverse_layer (lam k : ℕ) (hlam : 1 ≤ lam) :
    (1 : ℝ) / lam ≤ 1 / ((k + 1 : ℕ) : ℝ) +
      ∑ h ∈ Finset.Icc 1 k,
        if lam ≤ h then (1 : ℝ) / ((h : ℝ) * (h + 1)) else 0 := by
  by_cases hle : lam ≤ k + 1
  · have hfilter :
        (Finset.Icc 1 k).filter (fun h => lam ≤ h) = Finset.Ico lam (k + 1) := by
      ext h
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
      omega
    have hsum :
        (∑ h ∈ Finset.Icc 1 k,
          if lam ≤ h then (1 : ℝ) / ((h : ℝ) * (h + 1)) else 0) =
          1 / (lam : ℝ) - 1 / ((k + 1 : ℕ) : ℝ) := by
      rw [← Finset.sum_filter, hfilter]
      exact shortRelation_kernel_sum lam (k + 1) hlam hle
    rw [hsum]
    ring
    exact le_rfl
  · have hgt : k + 1 ≤ lam := by omega
    have hpos : 0 < (k + 1 : ℝ) := by exact_mod_cast (by omega : 0 < k + 1)
    have hinv : (1 : ℝ) / lam ≤ 1 / ((k + 1 : ℕ) : ℝ) := by
      have hcast : ((k + 1 : ℕ) : ℝ) ≤ (lam : ℝ) := by exact_mod_cast hgt
      have hcast' : (k : ℝ) + 1 ≤ (lam : ℝ) := by simpa using hcast
      simpa using (one_div_le_one_div_of_le hpos hcast')
    have hsum : 0 ≤ ∑ h ∈ Finset.Icc 1 k,
        if lam ≤ h then (1 : ℝ) / ((h : ℝ) * (h + 1)) else 0 := by
      apply Finset.sum_nonneg
      intro h hh
      split_ifs <;> positivity
    linarith

/-- 有限版分部求和；每一层的集合是 `lam ≤ h` 的过滤集。 -/
private theorem shortRelation_sum_inverse_layers {α : Type*} [DecidableEq α]
    (T : Finset α) (lam : α → ℕ) (hlam : ∀ t ∈ T, 1 ≤ lam t) (k : ℕ) :
    (∑ t ∈ T, (1 : ℝ) / lam t) ≤
      (T.card : ℝ) / ((k + 1 : ℕ) : ℝ) +
        ∑ h ∈ Finset.Icc 1 k,
          (((T.filter fun t => lam t ≤ h).card : ℝ) /
            ((h : ℝ) * (h + 1))) := by
  calc
    _ ≤ ∑ t ∈ T, ((1 : ℝ) / ((k + 1 : ℕ) : ℝ) +
          ∑ h ∈ Finset.Icc 1 k,
            if lam t ≤ h then (1 : ℝ) / ((h : ℝ) * (h + 1)) else 0) := by
      apply Finset.sum_le_sum
      intro t ht
      exact shortRelation_inverse_layer (lam t) k (hlam t ht)
    _ = (T.card : ℝ) / ((k + 1 : ℕ) : ℝ) +
          ∑ h ∈ Finset.Icc 1 k,
            (((T.filter fun t => lam t ≤ h).card : ℝ) /
              ((h : ℝ) * (h + 1))) := by
      rw [Finset.sum_add_distrib, Finset.sum_comm]
      simp only [Finset.sum_const, nsmul_eq_mul]
      congr 1
      · ring
      · apply Finset.sum_congr rfl
        intro h hh
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring

/-- 若每一层的累积个数至多为 `B h²`，则小层总贡献至多为 `Bk`。 -/
private theorem shortRelation_sum_inverse_bound {α : Type*} [DecidableEq α]
    (T : Finset α) (lam : α → ℕ) (hlam : ∀ t ∈ T, 1 ≤ lam t)
    (k : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hcount : ∀ h : ℕ, 1 ≤ h → h ≤ k →
      ((T.filter fun t => lam t ≤ h).card : ℝ) ≤ B * (h : ℝ) ^ 2) :
    (∑ t ∈ T, (1 : ℝ) / lam t) ≤
      (T.card : ℝ) / ((k + 1 : ℕ) : ℝ) + B * (k : ℝ) := by
  have hterm : ∀ h ∈ Finset.Icc 1 k,
      (((T.filter fun t => lam t ≤ h).card : ℝ) /
        ((h : ℝ) * (h + 1))) ≤ B := by
    intro h hh
    obtain ⟨hh1, hhk⟩ := Finset.mem_Icc.mp hh
    have hc := hcount h hh1 hhk
    have hhr : (0 : ℝ) < h := by exact_mod_cast hh1
    have hden : (0 : ℝ) < (h : ℝ) * (h + 1) := by positivity
    apply (div_le_iff₀ hden).2
    have hs : (h : ℝ) ^ 2 ≤ (h : ℝ) * (h + 1) := by nlinarith
    nlinarith [mul_nonneg hB (sub_nonneg.mpr hs)]
  have hsum : (∑ h ∈ Finset.Icc 1 k,
      (((T.filter fun t => lam t ≤ h).card : ℝ) /
        ((h : ℝ) * (h + 1)))) ≤ B * (k : ℝ) := by
    calc
      _ ≤ ∑ _h ∈ Finset.Icc 1 k, B := Finset.sum_le_sum hterm
      _ = B * (k : ℝ) := by simp; ring
  linarith [shortRelation_sum_inverse_layers T lam hlam k]

/-- `⌊√m⌋` 的两侧边界，包括 `m=1`。 -/
private theorem shortRelation_sqrt_cutoff (m : ℕ) (hm : 1 ≤ m) :
    1 ≤ Nat.sqrt m ∧ Nat.sqrt m ≤ m ∧
      (Nat.sqrt m : ℝ) ≤ (m : ℝ) ^ ((1 : ℝ) / 2) ∧
      (m : ℝ) ^ ((1 : ℝ) / 2) < ((Nat.sqrt m + 1 : ℕ) : ℝ) := by
  let k := Nat.sqrt m
  have hk1 : 1 ≤ k := (Nat.le_sqrt).2 (by simpa [k] using hm)
  have hkm : k ≤ m := Nat.sqrt_le_self m
  have hslo : k ^ 2 ≤ m := by simpa [k] using Nat.sqrt_le' m
  have hshi : m < (k + 1) ^ 2 := by simpa [k] using Nat.lt_succ_sqrt' m
  have hsloR : (k : ℝ) ^ 2 ≤ (m : ℝ) := by exact_mod_cast hslo
  have hshiR : (m : ℝ) < ((k + 1 : ℕ) : ℝ) ^ 2 := by exact_mod_cast hshi
  have hroot0 : 0 ≤ Real.sqrt (m : ℝ) := Real.sqrt_nonneg _
  have hrootSq : (Real.sqrt (m : ℝ)) ^ 2 = (m : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hkR : (0 : ℝ) ≤ k := by positivity
  have hlow : (k : ℝ) ≤ Real.sqrt (m : ℝ) := by nlinarith
  have hhigh : Real.sqrt (m : ℝ) < ((k + 1 : ℕ) : ℝ) := by
    have hk1R : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by positivity
    nlinarith
  have hlow' : (Nat.sqrt m : ℝ) ≤ (m : ℝ) ^ ((1 : ℝ) / 2) := by
    simpa [k, Real.sqrt_eq_rpow] using hlow
  have hhigh' : (m : ℝ) ^ ((1 : ℝ) / 2) < ((Nat.sqrt m + 1 : ℕ) : ℝ) := by
    simpa [k, Real.sqrt_eq_rpow] using hhigh
  exact ⟨hk1, hkm, hlow', hhigh'⟩

private theorem shortRelation_cube_div_sqrt (m : ℕ) (hm : 1 ≤ m) :
    (m : ℝ) ^ 3 / ((Nat.sqrt m + 1 : ℕ) : ℝ) ≤
      (m : ℝ) ^ ((5 : ℝ) / 2) := by
  obtain ⟨_, _, _, hhigh⟩ := shortRelation_sqrt_cutoff m hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hroot : (0 : ℝ) < (m : ℝ) ^ ((1 : ℝ) / 2) := by positivity
  have hle : (m : ℝ) ^ 3 / ((Nat.sqrt m + 1 : ℕ) : ℝ) ≤
      (m : ℝ) ^ 3 / ((m : ℝ) ^ ((1 : ℝ) / 2)) := by
    apply div_le_div_of_nonneg_left (by positivity) hroot hhigh.le
  rw [← Real.rpow_natCast, ← Real.rpow_sub hmR] at hle
  convert hle using 1 <;> norm_num

/-- 论文 `lem:relations` 的左侧：所有递增三元组的最短关系倒数和。 -/
noncomputable def shortRelationInverseSum (V : Finset ℕ) : ℝ :=
  ∑ t ∈ increasingTriples V,
    (1 : ℝ) / relationLambda t.1.1 t.1.2 t.2

/-- 不使用 Bondarenko–Seip 的短关系总和界。`S₂(V)` 保留为已定义的 GCD 对和。 -/
theorem shortRelationInverseSum_bound (θ : ℝ) (hθ : 0 < θ) :
    ∃ Cθ : ℝ, 0 < Cθ ∧
      ∀ (V : Finset ℕ) (hV : ∀ v ∈ V, 0 < v) (hm : 1 ≤ V.card),
        shortRelationInverseSum V ≤
          Cθ * ((V.card : ℝ) ^ ((11 : ℝ) / 6 + 8 * θ / 3) *
              (inversePairGcdSum V) ^ ((2 : ℝ) / 3) +
            (V.card : ℝ) ^ ((5 : ℝ) / 2)) := by
  obtain ⟨C, hC, hcount⟩ := shortRelationCount_bound θ hθ
  let Cθ : ℝ := 2 * C + 1
  have hCθ : 0 < Cθ := by dsimp [Cθ]; positivity
  refine ⟨Cθ, hCθ, ?_⟩
  intro V hV hm
  let m := V.card
  let k := Nat.sqrt m
  let T := increasingTriples V
  let lam : ((ℕ × ℕ) × ℕ) → ℕ := fun t => relationLambda t.1.1 t.1.2 t.2
  let A : ℝ := (m : ℝ) ^ ((4 : ℝ) / 3 + 8 * θ / 3) *
      (inversePairGcdSum V) ^ ((2 : ℝ) / 3)
  let B : ℝ := C * (A + 2 * (m : ℝ) ^ 2)
  have hm1 : 1 ≤ m := hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hS : 0 ≤ inversePairGcdSum V := by unfold inversePairGcdSum; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg hC.le (add_nonneg hA (by positivity))
  obtain ⟨hk1, hkm, hkle, hkhi⟩ := shortRelation_sqrt_cutoff m hm1
  have hlam : ∀ t ∈ T, 1 ≤ lam t := by
    intro t ht
    obtain ⟨_, hb, _, _, _⟩ := (mem_increasingTriples_iff V t).mp ht
    exact (relationLambda_pos_and_attained _ _ _ (hV _ hb)).1
  have hcountLayer : ∀ h : ℕ, 1 ≤ h → h ≤ k →
      ((T.filter fun t => lam t ≤ h).card : ℝ) ≤ B * (h : ℝ) ^ 2 := by
    intro h hh hhk
    have hhm : h ≤ m := hhk.trans hkm
    have hraw := hcount V hV h hm hh hhm
    have heq : T.filter (fun t => lam t ≤ h) = shortTriples V h := rfl
    rw [heq]
    have hhR : (0 : ℝ) ≤ h := by positivity
    have hhmR : (h : ℝ) ≤ (m : ℝ) := by exact_mod_cast hhm
    have habsorb : (m : ℝ) * (h : ℝ) ^ 3 ≤
        (m : ℝ) ^ 2 * (h : ℝ) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hhmR)
        (mul_nonneg hmR.le (sq_nonneg (h : ℝ)))]
    have hraw' : ((shortTriples V h).card : ℝ) ≤
        C * (A * (h : ℝ) ^ 2 + (m : ℝ) ^ 2 * (h : ℝ) ^ 2 +
          (m : ℝ) * (h : ℝ) ^ 3) := by
      simpa [A, m] using hraw
    dsimp [B]
    nlinarith [mul_nonneg hC.le (sub_nonneg.mpr habsorb)]
  have hmain := shortRelation_sum_inverse_bound T lam hlam k B hB hcountLayer
  have hCardNat : T.card ≤ m ^ 3 := increasingTriples_card_le_cube V
  have hCard : (T.card : ℝ) ≤ (m : ℝ) ^ 3 := by exact_mod_cast hCardNat
  have hkden : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by positivity
  have htail : (T.card : ℝ) / ((k + 1 : ℕ) : ℝ) ≤
      (m : ℝ) ^ ((5 : ℝ) / 2) := by
    calc
      _ ≤ (m : ℝ) ^ 3 / ((k + 1 : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right hCard hkden
      _ ≤ _ := by simpa [k] using shortRelation_cube_div_sqrt m hm1
  have hlead : A * (m : ℝ) ^ ((1 : ℝ) / 2) =
      (m : ℝ) ^ ((11 : ℝ) / 6 + 8 * θ / 3) *
        (inversePairGcdSum V) ^ ((2 : ℝ) / 3) := by
    dsimp [A]
    calc
      _ = ((m : ℝ) ^ ((4 : ℝ) / 3 + 8 * θ / 3) *
          (m : ℝ) ^ ((1 : ℝ) / 2)) *
          (inversePairGcdSum V) ^ ((2 : ℝ) / 3) := by ring
      _ = _ := by
        rw [← Real.rpow_add hmR]
        congr 1
        ring
  have hmiddle : (m : ℝ) ^ 2 * (m : ℝ) ^ ((1 : ℝ) / 2) =
      (m : ℝ) ^ ((5 : ℝ) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hmR]
    congr 1
    ring
  have hkbound : B * (k : ℝ) ≤
      C * ((m : ℝ) ^ ((11 : ℝ) / 6 + 8 * θ / 3) *
          (inversePairGcdSum V) ^ ((2 : ℝ) / 3) +
        2 * (m : ℝ) ^ ((5 : ℝ) / 2)) := by
    have hh := mul_le_mul_of_nonneg_left hkle hB
    calc
      _ ≤ B * (m : ℝ) ^ ((1 : ℝ) / 2) := hh
      _ = C * (A * (m : ℝ) ^ ((1 : ℝ) / 2) +
          2 * ((m : ℝ) ^ 2 * (m : ℝ) ^ ((1 : ℝ) / 2))) := by
            dsimp [B]; ring
      _ = _ := by rw [hlead, hmiddle]
  have hX : 0 ≤ (m : ℝ) ^ ((11 : ℝ) / 6 + 8 * θ / 3) *
      (inversePairGcdSum V) ^ ((2 : ℝ) / 3) := by positivity
  have hY : 0 ≤ (m : ℝ) ^ ((5 : ℝ) / 2) := by positivity
  have hcombine :
      (m : ℝ) ^ ((5 : ℝ) / 2) +
        C * ((m : ℝ) ^ ((11 : ℝ) / 6 + 8 * θ / 3) *
          (inversePairGcdSum V) ^ ((2 : ℝ) / 3) +
          2 * (m : ℝ) ^ ((5 : ℝ) / 2)) ≤
        Cθ * ((m : ℝ) ^ ((11 : ℝ) / 6 + 8 * θ / 3) *
          (inversePairGcdSum V) ^ ((2 : ℝ) / 3) +
          (m : ℝ) ^ ((5 : ℝ) / 2)) := by
    dsimp [Cθ]
    nlinarith [mul_nonneg hC.le hX, mul_nonneg hC.le hY]
  change (∑ t ∈ T, (1 : ℝ) / lam t) ≤ _
  have hsum : (∑ t ∈ T, (1 : ℝ) / lam t) ≤
      (m : ℝ) ^ ((5 : ℝ) / 2) +
        C * ((m : ℝ) ^ ((11 : ℝ) / 6 + 8 * θ / 3) *
          (inversePairGcdSum V) ^ ((2 : ℝ) / 3) +
          2 * (m : ℝ) ^ ((5 : ℝ) / 2)) := by
    linarith
  exact hsum.trans hcombine

/-- 条件式推论：若外部提供论文所需的 GCD 对和界，则得到 `m^(5/2+η)`。
    `gcdBound` 是普通定理参数；本项目此处并未证明它。 -/
theorem shortRelationInverseSum_bound_of_gcd
    (gcdBound : ∀ ε : ℝ, 0 < ε →
      ∃ Kε : ℝ, 0 < Kε ∧
        ∀ (W : Finset ℕ), (∀ w ∈ W, 0 < w) →
          inversePairGcdSum W ≤ Kε * (W.card : ℝ) ^ (1 + ε))
    (η : ℝ) (hη : 0 < η) :
    ∃ Cη : ℝ, 0 < Cη ∧
      ∀ (V : Finset ℕ) (hV : ∀ v ∈ V, 0 < v) (hm : 1 ≤ V.card),
        shortRelationInverseSum V ≤
          Cη * (V.card : ℝ) ^ ((5 : ℝ) / 2 + η) := by
  have hθ : 0 < η / 4 := by positivity
  obtain ⟨C, hC, hmain⟩ := shortRelationInverseSum_bound (η / 4) hθ
  have hε : 0 < η / 2 := by positivity
  obtain ⟨K, hK, hgcd⟩ := gcdBound (η / 2) hε
  let Cη : ℝ := C * (K ^ ((2 : ℝ) / 3) + 1)
  have hCη : 0 < Cη := by dsimp [Cη]; positivity
  refine ⟨Cη, hCη, ?_⟩
  intro V hV hm
  let m := V.card
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmOne : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hS : 0 ≤ inversePairGcdSum V := by unfold inversePairGcdSum; positivity
  have hSpow : (inversePairGcdSum V) ^ ((2 : ℝ) / 3) ≤
      K ^ ((2 : ℝ) / 3) *
        (m : ℝ) ^ ((1 + η / 2) * ((2 : ℝ) / 3)) := by
    calc
      _ ≤ (K * (m : ℝ) ^ (1 + η / 2)) ^ ((2 : ℝ) / 3) :=
        Real.rpow_le_rpow hS (by simpa [m] using hgcd V hV) (by norm_num)
      _ = K ^ ((2 : ℝ) / 3) *
          (m : ℝ) ^ ((1 + η / 2) * ((2 : ℝ) / 3)) := by
        rw [Real.mul_rpow hK.le (by positivity), ← Real.rpow_mul hmR.le]
  have hExp :
      (m : ℝ) ^ ((11 : ℝ) / 6 + 8 * (η / 4) / 3) *
        (m : ℝ) ^ ((1 + η / 2) * ((2 : ℝ) / 3)) =
          (m : ℝ) ^ ((5 : ℝ) / 2 + η) := by
    rw [← Real.rpow_add hmR]
    congr 1
    ring
  have hsmall : (m : ℝ) ^ ((5 : ℝ) / 2) ≤
      (m : ℝ) ^ ((5 : ℝ) / 2 + η) :=
    Real.rpow_le_rpow_of_exponent_le hmOne (by linarith)
  have hmain' := hmain V hV hm
  have hfac : (m : ℝ) ^ ((11 : ℝ) / 6 + 8 * (η / 4) / 3) *
        (inversePairGcdSum V) ^ ((2 : ℝ) / 3) ≤
      K ^ ((2 : ℝ) / 3) * (m : ℝ) ^ ((5 : ℝ) / 2 + η) := by
    have hh := mul_le_mul_of_nonneg_left hSpow (by positivity :
      0 ≤ (m : ℝ) ^ ((11 : ℝ) / 6 + 8 * (η / 4) / 3))
    calc
      _ ≤ (m : ℝ) ^ ((11 : ℝ) / 6 + 8 * (η / 4) / 3) *
          (K ^ ((2 : ℝ) / 3) *
            (m : ℝ) ^ ((1 + η / 2) * ((2 : ℝ) / 3))) := hh
      _ = K ^ ((2 : ℝ) / 3) * (m : ℝ) ^ ((5 : ℝ) / 2 + η) := by
        rw [← hExp]
        ring
  change shortRelationInverseSum V ≤ _ at hmain' ⊢
  dsimp [Cη]
  nlinarith [mul_nonneg hC.le (sub_nonneg.mpr hfac),
    mul_nonneg hC.le (sub_nonneg.mpr hsmall)]

end LonelyRunner
