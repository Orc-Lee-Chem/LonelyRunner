import LonelyRunner.ShortRelationZero
import LonelyRunner.RationalInterceptEnergy
import LonelyRunner.DyadicDirectionIncidence
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# 短关系计数的二进求和

对应 `paper/lonely_runner_zh.tex` 的 `lem:relations` 证明第 172–221 行。
本文件保留 `S₂(V)=inversePairGcdSum V`，不调用未形式化的 Bondarenko–Seip 估计。
-/

open Classical
open scoped Real

namespace LonelyRunner

/-- 固定二进层 `M=2^j≤H≤m` 时，`D=H/M` 为正，且 `HD≤m²`。 -/
theorem shortRelation_dyadic_denominator_bounds (m H j : ℕ)
    (hm : 1 ≤ m) (hH : 1 ≤ H) (hHm : H ≤ m)
    (hj : j ≤ Nat.log 2 H) :
    1 ≤ H / 2 ^ j ∧ H * (H / 2 ^ j) ≤ m ^ 2 := by
  have hM : 0 < 2 ^ j := pow_pos (by omega : 0 < 2) _
  have hMle : 2 ^ j ≤ H :=
    (Nat.le_log_iff_pow_le (by norm_num : 1 < 2) (by omega)).mp hj
  have hD : 1 ≤ H / 2 ^ j := (Nat.le_div_iff_mul_le hM).2 (by simpa using hMle)
  have hDle : H / 2 ^ j ≤ H := Nat.div_le_self _ _
  have hHD : H * (H / 2 ^ j) ≤ H * H := Nat.mul_le_mul_left _ hDle
  exact ⟨hD, by nlinarith⟩

private theorem shortRelation_Icc_zero_eq_range (n : ℕ) :
    Finset.Icc 0 n = Finset.range (n + 1) := by
  ext j
  simp only [Finset.mem_Icc, Finset.mem_range]
  omega

private theorem shortRelation_sum_two_powers (n : ℕ) :
    (∑ j ∈ Finset.range n, 2 ^ j) + 1 = 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    omega

/-- 论文第 215–219 行的有限几何和：`Σ 2^j ≤ 2H`。 -/
theorem shortRelation_sum_scales_le (H : ℕ) (hH : 1 ≤ H) :
    (∑ j ∈ Finset.Icc 0 (Nat.log 2 H), (2 ^ j : ℕ)) ≤ 2 * H := by
  rw [shortRelation_Icc_zero_eq_range]
  have hs := shortRelation_sum_two_powers (Nat.log 2 H + 1)
  have hpow := Nat.pow_log_le_self 2 (by omega : H ≠ 0)
  rw [pow_succ] at hs
  omega

/-- 论文第 215–219 行的有限几何和：`Σ (2^j)⁻¹ ≤ 2`。 -/
theorem shortRelation_sum_inverse_scales_le (H : ℕ) :
    (∑ j ∈ Finset.Icc 0 (Nat.log 2 H),
      ((2 ^ j : ℕ) : ℝ)⁻¹) ≤ 2 := by
  rw [shortRelation_Icc_zero_eq_range]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  simpa only [inv_pow, one_div] using sum_geometric_two_le (Nat.log 2 H + 1)

private theorem shortRelation_two_rpow_ge :
    (3 / 2 : ℝ) ≤ (2 : ℝ) ^ ((2 : ℝ) / 3) := by
  let A : ℝ := (2 : ℝ) ^ ((2 : ℝ) / 3)
  have hA3 : A ^ 3 = 4 := by
    dsimp [A]
    calc
      ((2 : ℝ) ^ ((2 : ℝ) / 3)) ^ (3 : ℕ) =
          ((2 : ℝ) ^ ((2 : ℝ) / 3)) ^ (3 : ℝ) :=
        (Real.rpow_natCast _ 3).symm
      _ = (2 : ℝ) ^ (((2 : ℝ) / 3) * 3) :=
        (Real.rpow_mul (by norm_num) _ _).symm
      _ = 4 := by norm_num
  by_contra h
  have hlt : A < 3 / 2 := lt_of_not_ge h
  have hcube := pow_lt_pow_left₀ hlt (by positivity : (0 : ℝ) ≤ A)
    (by norm_num : (3 : ℕ) ≠ 0)
  norm_num [hA3] at hcube

private theorem shortRelation_rpow_two_pow (j : ℕ) :
    (((2 ^ j : ℕ) : ℝ) ^ ((2 : ℝ) / 3)) =
      ((2 : ℝ) ^ ((2 : ℝ) / 3)) ^ j := by
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  calc
    ((2 : ℝ) ^ j) ^ ((2 : ℝ) / 3) =
        (2 : ℝ) ^ ((j : ℝ) * ((2 : ℝ) / 3)) := by
          rw [← Real.rpow_natCast, Real.rpow_mul (by norm_num)]
    _ = (2 : ℝ) ^ (((2 : ℝ) / 3) * (j : ℝ)) := by ring
    _ = ((2 : ℝ) ^ ((2 : ℝ) / 3)) ^ j := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]

private theorem shortRelation_geom_rpow_bound (A : ℝ) (hA : 3 / 2 ≤ A)
    (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), A ^ j) ≤ 4 * A ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hn : 0 ≤ A ^ n := by positivity
    have hcoef : 0 ≤ 3 * A - 4 := by linarith
    have hmul := mul_nonneg hcoef hn
    calc
      _ ≤ 4 * A ^ n + A ^ (n + 1) := by linarith
      _ ≤ 4 * A ^ (n + 1) := by rw [pow_succ]; nlinarith

/-- 论文第 215–219 行的有限几何和：`Σ (2^j)^(2/3) ≤ 4H^(2/3)`。 -/
theorem shortRelation_sum_rpow_scales_le (H : ℕ) (hH : 1 ≤ H) :
    (∑ j ∈ Finset.Icc 0 (Nat.log 2 H),
      (((2 ^ j : ℕ) : ℝ) ^ ((2 : ℝ) / 3))) ≤
      4 * (H : ℝ) ^ ((2 : ℝ) / 3) := by
  rw [shortRelation_Icc_zero_eq_range]
  simp_rw [shortRelation_rpow_two_pow]
  let A : ℝ := (2 : ℝ) ^ ((2 : ℝ) / 3)
  have hgeom := shortRelation_geom_rpow_bound A shortRelation_two_rpow_ge
    (Nat.log 2 H)
  have hM : (2 ^ Nat.log 2 H : ℕ) ≤ H :=
    Nat.pow_log_le_self 2 (by omega)
  have hMr : (((2 ^ Nat.log 2 H : ℕ) : ℝ) ^ ((2 : ℝ) / 3)) ≤
      (H : ℝ) ^ ((2 : ℝ) / 3) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hM) (by norm_num)
  have hpow := shortRelation_rpow_two_pow (Nat.log 2 H)
  calc
    _ ≤ 4 * A ^ Nat.log 2 H := hgeom
    _ = 4 * (((2 ^ Nat.log 2 H : ℕ) : ℝ) ^ ((2 : ℝ) / 3)) := by rw [hpow]
    _ ≤ _ := mul_le_mul_of_nonneg_left hMr (by norm_num)

/-- 自然数除法 `D=H/M` 的实数形式，分母 `M` 明确为正。 -/
theorem shortRelation_dyadic_div_real (H M : ℕ) (hM : 0 < M) :
    ((H / M : ℕ) : ℝ) ≤ (H : ℝ) / (M : ℝ) := by
  have hDM : (H / M) * M ≤ H := Nat.div_mul_le_self H M
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  apply (le_div_iff₀ hMr).2
  exact_mod_cast hDM

/-- 二进层的核心算术不等式 `M²·H·⌊H/M⌋≤H²M`。 -/
theorem shortRelation_dyadic_product_bound (H M : ℕ) :
    (M : ℝ) ^ 2 * ((H * (H / M) : ℕ) : ℝ) ≤
      (H : ℝ) ^ 2 * (M : ℝ) := by
  have hDM : (H / M) * M ≤ H := Nat.div_mul_le_self H M
  have hnat : M ^ 2 * (H * (H / M)) ≤ H ^ 2 * M := by
    nlinarith [Nat.mul_le_mul_left (H * M) hDM]
  exact_mod_cast hnat

private theorem inversePairGcdSum_nonneg (V : Finset ℕ) :
    0 ≤ inversePairGcdSum V := by
  unfold inversePairGcdSum
  positivity

private theorem shortRelation_power_factorization
    (m H M C S θ : ℝ) (hm : 0 < m) (hH : 0 < H)
    (hM : 0 < M) (hC : 0 ≤ C) (hS : 0 ≤ S) :
    m ^ ((4 : ℝ) / 3) *
      ((16 * C) * m ^ (4 * θ) * H ^ 2 * M * S) ^ ((2 : ℝ) / 3) =
      (16 * C) ^ ((2 : ℝ) / 3) *
        (m ^ ((4 : ℝ) / 3 + 8 * θ / 3) * S ^ ((2 : ℝ) / 3) *
          H ^ ((4 : ℝ) / 3) * M ^ ((2 : ℝ) / 3)) := by
  have hmexp : (m ^ (4 * θ)) ^ ((2 : ℝ) / 3) = m ^ (8 * θ / 3) := by
    rw [← Real.rpow_mul hm.le]
    congr 1
    ring
  have hHexp : (H ^ (2 : ℕ)) ^ ((2 : ℝ) / 3) = H ^ ((4 : ℝ) / 3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hH.le]
    congr 1
    ring
  rw [Real.mul_rpow (by positivity) hS]
  rw [Real.mul_rpow (by positivity) hM.le]
  rw [Real.mul_rpow (by positivity) (by positivity)]
  rw [Real.mul_rpow (by positivity) (by positivity)]
  rw [hmexp, hHexp]
  rw [Real.rpow_add hm]
  ring

/-- `dyadic_direction_incidence_bound` 左侧的现有参数和，作为本文件的记号。 -/
noncomputable def shortRelationLayerIncidence (M : ℕ) (V : Finset ℕ)
    (H D : ℕ) : ℝ :=
  ∑ d ∈ primitiveDirections M, ∑ r ∈ rationalIntercepts V H D,
    (interceptWeight V H D r : ℝ) *
      (((V.product V).filter fun ab =>
        (d.1 : ℚ) * (ab.1 : ℚ) + (d.2 : ℚ) * (ab.2 : ℚ) = r).card : ℝ)

private noncomputable def shortRelationLayerEnergy (V : Finset ℕ)
    (H D : ℕ) : ℝ :=
  ∑ r ∈ rationalIntercepts V H D, (interceptWeight V H D r : ℝ) ^ 2

/-- 单层二进估计：实际把截距能量界和加权 ST 连接起来。
    `Ce,Cs` 分别由已证定理给出，只依赖 `θ` 或为绝对常数。 -/
theorem shortRelation_layer_bound (θ : ℝ) (hθ : 0 < θ) :
    ∃ Ce Cs : ℝ, 0 < Ce ∧ 0 < Cs ∧
      ∀ (V : Finset ℕ) (hV : ∀ v ∈ V, 0 < v)
        (H M : ℕ) (hm : 1 ≤ V.card) (hH : 1 ≤ H)
        (hHM : H ≤ V.card) (hM : 1 ≤ M) (hMH : M ≤ H),
        shortRelationLayerIncidence M V H (H / M) ≤
          Cs * (((16 * Ce : ℝ) ^ ((2 : ℝ) / 3)) *
              ((V.card : ℝ) ^ ((4 : ℝ) / 3 + 8 * θ / 3) *
                (inversePairGcdSum V) ^ ((2 : ℝ) / 3) *
                (H : ℝ) ^ ((4 : ℝ) / 3) * (M : ℝ) ^ ((2 : ℝ) / 3)) +
            (2 : ℝ) * (V.card : ℝ) ^ 2 * (H : ℝ) ^ 2 / (M : ℝ) +
            (32 : ℝ) * (V.card : ℝ) * (H : ℝ) ^ 2 * (M : ℝ)) := by
  obtain ⟨Ce, hCe, hEnergy⟩ := rationalInterceptEnergy_power_bound θ hθ
  obtain ⟨Cs, hCs, hST⟩ := dyadic_direction_incidence_bound
  refine ⟨Ce, Cs, hCe, hCs, ?_⟩
  intro V hV H M hm hH hHM hM hMH
  let D := H / M
  have hD : 0 < D := by
    apply (Nat.le_div_iff_mul_le hM).2
    simpa using hMH
  have hHD : H * D ≤ V.card ^ 2 := by
    have hDle : D ≤ H := Nat.div_le_self _ _
    nlinarith [Nat.mul_le_mul_left H hDle]
  have hE : shortRelationLayerEnergy V H D ≤
      Ce * (V.card : ℝ) ^ (4 * θ) * ((H * D : ℕ) : ℝ) *
        inversePairGcdSum V := by
    exact hEnergy V H D V.card hV hH hD hm hHD
  have hE0 : 0 ≤ shortRelationLayerEnergy V H D := by
    unfold shortRelationLayerEnergy
    positivity
  have hS0 : 0 ≤ inversePairGcdSum V := inversePairGcdSum_nonneg V
  have hProd : (M : ℝ) ^ 2 * ((H * D : ℕ) : ℝ) ≤
      (H : ℝ) ^ 2 * (M : ℝ) := shortRelation_dyadic_product_bound H M
  have hbase : (16 : ℝ) * (M : ℝ) ^ 2 *
      shortRelationLayerEnergy V H D ≤
        (16 * Ce) * (V.card : ℝ) ^ (4 * θ) *
          (H : ℝ) ^ 2 * (M : ℝ) * inversePairGcdSum V := by
    calc
      _ ≤ (16 : ℝ) * (M : ℝ) ^ 2 *
          (Ce * (V.card : ℝ) ^ (4 * θ) * ((H * D : ℕ) : ℝ) *
            inversePairGcdSum V) :=
        mul_le_mul_of_nonneg_left hE (by positivity)
      _ = ((16 * Ce) * (V.card : ℝ) ^ (4 * θ) *
          inversePairGcdSum V) *
            ((M : ℝ) ^ 2 * ((H * D : ℕ) : ℝ)) := by ring
      _ ≤ ((16 * Ce) * (V.card : ℝ) ^ (4 * θ) *
          inversePairGcdSum V) * ((H : ℝ) ^ 2 * (M : ℝ)) :=
        mul_le_mul_of_nonneg_left hProd (by positivity)
      _ = _ := by ring
  have hfirst : (V.card : ℝ) ^ ((4 : ℝ) / 3) *
      ((16 : ℝ) * (M : ℝ) ^ 2 * shortRelationLayerEnergy V H D) ^
        ((2 : ℝ) / 3) ≤
      (16 * Ce : ℝ) ^ ((2 : ℝ) / 3) *
        ((V.card : ℝ) ^ ((4 : ℝ) / 3 + 8 * θ / 3) *
          (inversePairGcdSum V) ^ ((2 : ℝ) / 3) *
          (H : ℝ) ^ ((4 : ℝ) / 3) * (M : ℝ) ^ ((2 : ℝ) / 3)) := by
    have hpow := Real.rpow_le_rpow
      (by positivity : 0 ≤ (16 : ℝ) * (M : ℝ) ^ 2 *
        shortRelationLayerEnergy V H D) hbase
      (by norm_num : 0 ≤ (2 : ℝ) / 3)
    have hmR : (0 : ℝ) < V.card := by exact_mod_cast hm
    have hHR : (0 : ℝ) < H := by exact_mod_cast hH
    have hMR : (0 : ℝ) < M := by exact_mod_cast hM
    calc
      _ ≤ (V.card : ℝ) ^ ((4 : ℝ) / 3) *
        ((16 * Ce) * (V.card : ℝ) ^ (4 * θ) *
          (H : ℝ) ^ 2 * (M : ℝ) * inversePairGcdSum V) ^
            ((2 : ℝ) / 3) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = _ := shortRelation_power_factorization _ _ _ _ _ _
        hmR hHR hMR hCe.le hS0
  have hDR : (D : ℝ) ≤ (H : ℝ) / (M : ℝ) :=
    shortRelation_dyadic_div_real H M hM
  have hsecond : (2 : ℝ) * (V.card : ℝ) ^ 2 * (H : ℝ) * (D : ℝ) ≤
      (2 : ℝ) * (V.card : ℝ) ^ 2 * (H : ℝ) ^ 2 / (M : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hDR
      (by positivity : 0 ≤ (2 : ℝ) * (V.card : ℝ) ^ 2 * (H : ℝ))
    convert hmul using 1 <;> ring
  have hthird : (32 : ℝ) * (V.card : ℝ) * (H : ℝ) * (D : ℝ) *
      (M : ℝ) ^ 2 ≤
      (32 : ℝ) * (V.card : ℝ) * (H : ℝ) ^ 2 * (M : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hProd
      (by positivity : 0 ≤ (32 : ℝ) * (V.card : ℝ))
    convert hmul using 1 <;> push_cast <;> ring
  have hst := hST M hM V H D
  change shortRelationLayerIncidence M V H D ≤ Cs *
    ((V.card : ℝ) ^ ((4 : ℝ) / 3) *
      ((16 : ℝ) * (M : ℝ) ^ 2 * shortRelationLayerEnergy V H D) ^
        ((2 : ℝ) / 3) +
      (2 : ℝ) * (V.card : ℝ) ^ 2 * (H : ℝ) * (D : ℝ) +
      (32 : ℝ) * (V.card : ℝ) * (H : ℝ) * (D : ℝ) * (M : ℝ) ^ 2) at hst
  have hsum :
      (V.card : ℝ) ^ ((4 : ℝ) / 3) *
          ((16 : ℝ) * (M : ℝ) ^ 2 * shortRelationLayerEnergy V H D) ^
            ((2 : ℝ) / 3) +
        (2 : ℝ) * (V.card : ℝ) ^ 2 * (H : ℝ) * (D : ℝ) +
        (32 : ℝ) * (V.card : ℝ) * (H : ℝ) * (D : ℝ) * (M : ℝ) ^ 2 ≤
      (16 * Ce : ℝ) ^ ((2 : ℝ) / 3) *
          ((V.card : ℝ) ^ ((4 : ℝ) / 3 + 8 * θ / 3) *
            (inversePairGcdSum V) ^ ((2 : ℝ) / 3) *
            (H : ℝ) ^ ((4 : ℝ) / 3) * (M : ℝ) ^ ((2 : ℝ) / 3)) +
        (2 : ℝ) * (V.card : ℝ) ^ 2 * (H : ℝ) ^ 2 / (M : ℝ) +
        (32 : ℝ) * (V.card : ℝ) * (H : ℝ) ^ 2 * (M : ℝ) := by
    linarith
  exact hst.trans (mul_le_mul_of_nonneg_left hsum hCs.le)

private theorem shortRelation_H_powers (H : ℕ) (hH : 1 ≤ H) :
    (H : ℝ) ^ ((4 : ℝ) / 3) * (H : ℝ) ^ ((2 : ℝ) / 3) =
      (H : ℝ) ^ 2 := by
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  rw [← Real.rpow_add hHR]
  convert (Real.rpow_natCast (H : ℝ) 2) using 1 <;> norm_num

/-- 论文 `lem:relations` 的有限 `N_V(H)` 估计，保留已证的 `S₂(V)`。
    常数仅依赖 `θ`，并未使用 Bondarenko–Seip 估计。 -/
theorem shortRelationCount_bound (θ : ℝ) (hθ : 0 < θ) :
    ∃ Cθ : ℝ, 0 < Cθ ∧
      ∀ (V : Finset ℕ) (hV : ∀ v ∈ V, 0 < v)
        (H : ℕ) (hm : 1 ≤ V.card) (hH : 1 ≤ H) (hHm : H ≤ V.card),
        ((shortTriples V H).card : ℝ) ≤
          Cθ * ((V.card : ℝ) ^ ((4 : ℝ) / 3 + 8 * θ / 3) *
              (inversePairGcdSum V) ^ ((2 : ℝ) / 3) * (H : ℝ) ^ 2 +
            (V.card : ℝ) ^ 2 * (H : ℝ) ^ 2 +
            (V.card : ℝ) * (H : ℝ) ^ 3) := by
  obtain ⟨Ce, Cs, hCe, hCs, hLayer⟩ := shortRelation_layer_bound θ hθ
  let K : ℝ := (16 * Ce) ^ ((2 : ℝ) / 3)
  let Cθ : ℝ := 12 + Cs * (4 * K + 64)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hCθ : 0 < Cθ := by dsimp [Cθ]; positivity
  refine ⟨Cθ, hCθ, ?_⟩
  intro V hV H hm hH hHm
  let J := Finset.Icc 0 (Nat.log 2 H)
  let A : ℝ := (V.card : ℝ) ^ ((4 : ℝ) / 3 + 8 * θ / 3) *
    (inversePairGcdSum V) ^ ((2 : ℝ) / 3)
  let B : ℝ := (V.card : ℝ) ^ 2
  let C : ℝ := (V.card : ℝ)
  have hS : 0 ≤ inversePairGcdSum V := inversePairGcdSum_nonneg V
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hM_j (j : ℕ) (hj : j ∈ J) :
      1 ≤ 2 ^ j ∧ 2 ^ j ≤ H := by
    have hjlog : j ≤ Nat.log 2 H := (Finset.mem_Icc.mp hj).2
    exact ⟨pow_pos (by omega : 0 < 2) _,
      (Nat.le_log_iff_pow_le (by norm_num : 1 < 2) (by omega)).mp hjlog⟩
  have hLayerSum :
      (∑ j ∈ J, shortRelationLayerIncidence (2 ^ j) V H (H / 2 ^ j)) ≤
      ∑ j ∈ J, Cs *
        (K * (A * (H : ℝ) ^ ((4 : ℝ) / 3) *
            ((2 ^ j : ℕ) : ℝ) ^ ((2 : ℝ) / 3)) +
          2 * B * (H : ℝ) ^ 2 * ((2 ^ j : ℕ) : ℝ)⁻¹ +
          32 * C * (H : ℝ) ^ 2 * ((2 ^ j : ℕ) : ℝ)) := by
    apply Finset.sum_le_sum
    intro j hj
    obtain ⟨hM, hMH⟩ := hM_j j hj
    have h := hLayer V hV H (2 ^ j) hm hH hHm hM hMH
    convert h using 1 <;> dsimp [K, A, B, C] <;> ring
  have hSumForm :
      (∑ j ∈ J, Cs *
        (K * (A * (H : ℝ) ^ ((4 : ℝ) / 3) *
            ((2 ^ j : ℕ) : ℝ) ^ ((2 : ℝ) / 3)) +
          2 * B * (H : ℝ) ^ 2 * ((2 ^ j : ℕ) : ℝ)⁻¹ +
          32 * C * (H : ℝ) ^ 2 * ((2 ^ j : ℕ) : ℝ))) =
        Cs * (K * A * (H : ℝ) ^ ((4 : ℝ) / 3) *
            (∑ j ∈ J, (((2 ^ j : ℕ) : ℝ) ^ ((2 : ℝ) / 3))) +
          2 * B * (H : ℝ) ^ 2 *
            (∑ j ∈ J, ((2 ^ j : ℕ) : ℝ)⁻¹) +
          32 * C * (H : ℝ) ^ 2 *
            (∑ j ∈ J, ((2 ^ j : ℕ) : ℝ))) := by
    calc
      _ = ∑ j ∈ J,
          (Cs * K * A * (H : ℝ) ^ ((4 : ℝ) / 3) *
              ((2 ^ j : ℕ) : ℝ) ^ ((2 : ℝ) / 3) +
            Cs * 2 * B * (H : ℝ) ^ 2 * ((2 ^ j : ℕ) : ℝ)⁻¹ +
            Cs * 32 * C * (H : ℝ) ^ 2 * ((2 ^ j : ℕ) : ℝ)) := by
              apply Finset.sum_congr rfl
              intro j hj
              ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        ring
  have hS1 : (∑ j ∈ J,
      (((2 ^ j : ℕ) : ℝ) ^ ((2 : ℝ) / 3))) ≤
        4 * (H : ℝ) ^ ((2 : ℝ) / 3) :=
    shortRelation_sum_rpow_scales_le H hH
  have hS2 : (∑ j ∈ J, ((2 ^ j : ℕ) : ℝ)⁻¹) ≤ 2 :=
    shortRelation_sum_inverse_scales_le H
  have hS3 : (∑ j ∈ J, ((2 ^ j : ℕ) : ℝ)) ≤ 2 * (H : ℝ) := by
    exact_mod_cast shortRelation_sum_scales_le H hH
  have hTotal :
      (∑ j ∈ J, shortRelationLayerIncidence (2 ^ j) V H (H / 2 ^ j)) ≤
      Cs * (4 * K * A * (H : ℝ) ^ 2 +
        4 * B * (H : ℝ) ^ 2 +
        64 * C * (H : ℝ) ^ 3) := by
    calc
      _ ≤ Cs * (K * A * (H : ℝ) ^ ((4 : ℝ) / 3) *
            (∑ j ∈ J, (((2 ^ j : ℕ) : ℝ) ^ ((2 : ℝ) / 3))) +
          2 * B * (H : ℝ) ^ 2 *
            (∑ j ∈ J, ((2 ^ j : ℕ) : ℝ)⁻¹) +
          32 * C * (H : ℝ) ^ 2 *
            (∑ j ∈ J, ((2 ^ j : ℕ) : ℝ))) := by
              rw [← hSumForm]
              exact hLayerSum
      _ ≤ Cs * (K * A * (H : ℝ) ^ ((4 : ℝ) / 3) *
            (4 * (H : ℝ) ^ ((2 : ℝ) / 3)) +
          2 * B * (H : ℝ) ^ 2 * 2 +
          32 * C * (H : ℝ) ^ 2 * (2 * (H : ℝ))) := by
            apply mul_le_mul_of_nonneg_left _ hCs.le
            have h1 := mul_le_mul_of_nonneg_left hS1
              (by positivity : 0 ≤ K * A * (H : ℝ) ^ ((4 : ℝ) / 3))
            have h2 := mul_le_mul_of_nonneg_left hS2
              (by positivity : 0 ≤ 2 * B * (H : ℝ) ^ 2)
            have h3 := mul_le_mul_of_nonneg_left hS3
              (by positivity : 0 ≤ 32 * C * (H : ℝ) ^ 2)
            linarith
      _ = Cs * (4 * K * A *
          ((H : ℝ) ^ ((4 : ℝ) / 3) * (H : ℝ) ^ ((2 : ℝ) / 3)) +
          4 * B * (H : ℝ) ^ 2 + 64 * C * (H : ℝ) ^ 3) := by ring
      _ = _ := by rw [shortRelation_H_powers H hH]
  have hbase := shortTriples_card_le_zero_and_dyadic V H hV hH
  have hbase' : ((shortTriples V H).card : ℝ) ≤
      12 * B * (H : ℝ) ^ 2 +
        ∑ j ∈ J, shortRelationLayerIncidence (2 ^ j) V H (H / 2 ^ j) := by
    convert hbase using 1 <;> dsimp [B, J, shortRelationLayerIncidence] <;> push_cast <;> ring
  have hA2 : 0 ≤ A * (H : ℝ) ^ 2 := by positivity
  have hB2 : 0 ≤ B * (H : ℝ) ^ 2 := by positivity
  have hC3 : 0 ≤ C * (H : ℝ) ^ 3 := by positivity
  have hCA : 4 * Cs * K ≤ Cθ := by dsimp [Cθ]; nlinarith [mul_nonneg hCs.le hK]
  have hCB : 12 + 4 * Cs ≤ Cθ := by
    dsimp [Cθ]
    nlinarith [mul_nonneg hCs.le hK]
  have hCC : 64 * Cs ≤ Cθ := by
    dsimp [Cθ]
    nlinarith [mul_nonneg hCs.le hK]
  have hfinal :
      12 * B * (H : ℝ) ^ 2 +
        Cs * (4 * K * A * (H : ℝ) ^ 2 +
          4 * B * (H : ℝ) ^ 2 + 64 * C * (H : ℝ) ^ 3) ≤
        Cθ * (A * (H : ℝ) ^ 2 + B * (H : ℝ) ^ 2 + C * (H : ℝ) ^ 3) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hCA) hA2,
      mul_nonneg (sub_nonneg.mpr hCB) hB2,
      mul_nonneg (sub_nonneg.mpr hCC) hC3]
  have hcombine : ((shortTriples V H).card : ℝ) ≤
      12 * B * (H : ℝ) ^ 2 +
        Cs * (4 * K * A * (H : ℝ) ^ 2 +
          4 * B * (H : ℝ) ^ 2 + 64 * C * (H : ℝ) ^ 3) := by
    linarith [hbase', hTotal]
  exact hcombine.trans hfinal

end LonelyRunner
