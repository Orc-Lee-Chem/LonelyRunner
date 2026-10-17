import LonelyRunner.STIncidence

open scoped Real
open Classical

namespace LonelyRunner

/-- 带权 ST 中的直线仍是实二维空间的一维仿射子空间。 -/
abbrev WeightedLine :=
  {ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) // IsAffineLine ℓ}

/-- 论文 `lem:weighted` 左侧：每条直线的权重乘以它与点集的关联数。 -/
noncomputable def weightedIncidences
    (P : Finset (EuclideanSpace ℝ (Fin 2)))
    (L : Finset WeightedLine) (w : WeightedLine → ℕ) : ℝ :=
  ∑ ℓ ∈ L, (w ℓ : ℝ) * ((P.filter fun p => p ∈ (ℓ : AffineSubspace ℝ _)).card : ℝ)

@[simp] theorem weightedIncidences_empty_points
    (L : Finset WeightedLine) (w : WeightedLine → ℕ) :
    weightedIncidences ∅ L w = 0 := by
  simp [weightedIncidences]

@[simp] theorem weightedIncidences_empty_lines
    (P : Finset (EuclideanSpace ℝ (Fin 2))) (w : WeightedLine → ℕ) :
    weightedIncidences P ∅ w = 0 := by
  simp [weightedIncidences]

/-- 论文 `lem:weighted` 的平方权重和 `Q`。 -/
noncomputable def weightSquareSum (L : Finset WeightedLine) (w : WeightedLine → ℕ) : ℝ :=
  ∑ ℓ ∈ L, ((w ℓ : ℝ) ^ 2)

/-- 论文 `lem:weighted` 的总权重 `W₁`。 -/
noncomputable def weightSum (L : Finset WeightedLine) (w : WeightedLine → ℕ) : ℝ :=
  ∑ ℓ ∈ L, (w ℓ : ℝ)

/-- 论文 `lem:weighted` 的最大权重；空直线集时为零。 -/
noncomputable def maxWeight (L : Finset WeightedLine) (w : WeightedLine → ℕ) : ℕ :=
  L.sup w

@[simp] theorem maxWeight_empty (w : WeightedLine → ℕ) : maxWeight ∅ w = 0 := by
  simp [maxWeight]

noncomputable def dyadicLines (L : Finset WeightedLine) (w : WeightedLine → ℕ) (j : ℕ) :
    Finset WeightedLine :=
  L.filter fun ℓ => Nat.log 2 (w ℓ) = j

private lemma lineIncidences_eq_sum
    (P : Finset (EuclideanSpace ℝ (Fin 2))) (L : Finset WeightedLine) :
    (LineIncidences P L : ℝ) =
      ∑ ℓ ∈ L, ((P.filter fun p => p ∈ (ℓ : AffineSubspace ℝ _)).card : ℝ) := by
  have hnat : LineIncidences P L =
      ∑ ℓ ∈ L, (P.filter fun p => p ∈ (ℓ : AffineSubspace ℝ _)).card := by
    unfold LineIncidences
    rw [Finset.card_filter]
    change (∑ x ∈ P.product L, if x.1 ∈ (x.2 : AffineSubspace ℝ _) then 1 else 0) = _
    calc
      (∑ x ∈ P.product L, if x.1 ∈ (x.2 : AffineSubspace ℝ _) then 1 else 0) =
          ∑ p ∈ P, ∑ ℓ ∈ L, if p ∈ (ℓ : AffineSubspace ℝ _) then 1 else 0 := by
        exact Finset.sum_product P L _
      _ = ∑ ℓ ∈ L, (P.filter fun p => p ∈ (ℓ : AffineSubspace ℝ _)).card := by
        rw [Finset.sum_comm]
        simp only [Finset.card_filter]
  exact_mod_cast hnat

private lemma dyadicLines_subset (L : Finset WeightedLine) (w : WeightedLine → ℕ)
    (j : ℕ) : dyadicLines L w j ⊆ L := Finset.filter_subset _ _

private lemma dyadic_lower (L : Finset WeightedLine) (w : WeightedLine → ℕ)
    (hw : ∀ ℓ ∈ L, 0 < w ℓ) (j : ℕ) {ℓ : WeightedLine}
    (hℓ : ℓ ∈ dyadicLines L w j) : 2 ^ j ≤ w ℓ := by
  have hmem := (Finset.mem_filter.mp hℓ).1
  have hlog := (Finset.mem_filter.mp hℓ).2
  simpa [hlog] using Nat.pow_log_le_self 2 (Nat.ne_of_gt (hw ℓ hmem))

private lemma dyadic_upper (L : Finset WeightedLine) (w : WeightedLine → ℕ)
    (j : ℕ) {ℓ : WeightedLine} (hℓ : ℓ ∈ dyadicLines L w j) :
    w ℓ < 2 ^ (j + 1) := by
  have hlog := (Finset.mem_filter.mp hℓ).2
  simpa [hlog] using Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (w ℓ)

private lemma dyadic_square_bound (L : Finset WeightedLine) (w : WeightedLine → ℕ)
    (hw : ∀ ℓ ∈ L, 0 < w ℓ) (j : ℕ) :
    ((2 ^ j : ℕ) : ℝ) ^ 2 * (dyadicLines L w j).card ≤ weightSquareSum L w := by
  let Lj := dyadicLines L w j
  calc
    ((2 ^ j : ℕ) : ℝ) ^ 2 * (Lj.card : ℝ) =
        ∑ ℓ ∈ Lj, ((2 ^ j : ℕ) : ℝ) ^ 2 := by simp [mul_comm]
    _ ≤ ∑ ℓ ∈ Lj, ((w ℓ : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro ℓ hℓ
      have h := dyadic_lower L w hw j hℓ
      exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast h) _
    _ ≤ weightSquareSum L w := by
      unfold weightSquareSum
      exact Finset.sum_le_sum_of_subset_of_nonneg (dyadicLines_subset L w j)
        (by intro ℓ _ _; positivity)

private lemma dyadic_incidence_bound
    (P : Finset (EuclideanSpace ℝ (Fin 2)))
    (L : Finset WeightedLine) (w : WeightedLine → ℕ) (j : ℕ) :
    weightedIncidences P (dyadicLines L w j) w ≤
      ((2 ^ (j + 1) : ℕ) : ℝ) * (LineIncidences P (dyadicLines L w j) : ℝ) := by
  rw [weightedIncidences, lineIncidences_eq_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ℓ hℓ
  have h := dyadic_upper L w j hℓ
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast (le_of_lt h)) (Nat.cast_nonneg _)

private lemma dyadic_main_bound (n k q t : ℝ) (hn : 0 ≤ n) (hk : 0 ≤ k)
    (ht : 0 < t) (hq : t ^ 2 * k ≤ q) :
    t * (n * k) ^ ((2 : ℝ) / 3) ≤
      (n * q) ^ ((2 : ℝ) / 3) * t ^ (-(1 : ℝ) / 3) := by
  have hnk : 0 ≤ n * k := mul_nonneg hn hk
  have htd : (t ^ 2) ^ ((2 : ℝ) / 3) * t ^ (-(1 : ℝ) / 3) = t := by
    rw [← Real.rpow_natCast t 2, ← Real.rpow_mul (le_of_lt ht)]
    rw [← Real.rpow_add ht]
    norm_num
  have hmq : n * (t ^ 2 * k) ≤ n * q := mul_le_mul_of_nonneg_left hq hn
  have hpow := Real.rpow_le_rpow (mul_nonneg hn (mul_nonneg (sq_nonneg t) hk)) hmq
    (by norm_num : 0 ≤ (2 : ℝ) / 3)
  calc
    t * (n * k) ^ ((2 : ℝ) / 3) =
        (n * (t ^ 2 * k)) ^ ((2 : ℝ) / 3) * t ^ (-(1 : ℝ) / 3) := by
      rw [show n * (t ^ 2 * k) = (n * k) * t ^ 2 by ring,
        Real.mul_rpow hnk (sq_nonneg t)]
      rw [mul_assoc, htd]
      ring
    _ ≤ (n * q) ^ ((2 : ℝ) / 3) * t ^ (-(1 : ℝ) / 3) :=
      mul_le_mul_of_nonneg_right hpow (by positivity)

private lemma dyadic_partition (L : Finset WeightedLine) (w : WeightedLine → ℕ)
    (f : WeightedLine → ℝ) :
    ∑ j ∈ Finset.range (Nat.log 2 (maxWeight L w) + 1),
      ∑ ℓ ∈ dyadicLines L w j, f ℓ = ∑ ℓ ∈ L, f ℓ := by
  let J := Nat.log 2 (maxWeight L w) + 1
  have hlog (ℓ : WeightedLine) (hℓ : ℓ ∈ L) : Nat.log 2 (w ℓ) < J := by
    have hmax : w ℓ ≤ maxWeight L w := Finset.le_sup hℓ
    exact Nat.lt_succ_of_le (Nat.log_monotone hmax)
  calc
    ∑ j ∈ Finset.range J, ∑ ℓ ∈ dyadicLines L w j, f ℓ =
        ∑ ℓ ∈ L, ∑ j ∈ Finset.range J, if Nat.log 2 (w ℓ) = j then f ℓ else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ℓ hℓ
      simp [dyadicLines, Finset.sum_filter]
    _ = ∑ ℓ ∈ L, f ℓ := by
      apply Finset.sum_congr rfl
      intro ℓ hℓ
      simp [hlog ℓ hℓ]

private lemma geom_bound (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    ∑ j ∈ Finset.range N, r ^ j ≤ 1 / (1 - r) := by
  have hident : (1 - r) * (∑ j ∈ Finset.range N, r ^ j) = 1 - r ^ N := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
      ring
  have hpow : 0 ≤ r ^ N := pow_nonneg hr0 _
  apply (le_div_iff₀ (by linarith : 0 < 1 - r)).2
  nlinarith

private lemma dyadic_weight_bound (L : Finset WeightedLine) (w : WeightedLine → ℕ)
    (hw : ∀ ℓ ∈ L, 0 < w ℓ) (j : ℕ) :
    ((2 ^ j : ℕ) : ℝ) * (dyadicLines L w j).card ≤
      weightSum (dyadicLines L w j) w := by
  unfold weightSum
  calc
    ((2 ^ j : ℕ) : ℝ) * (dyadicLines L w j).card =
        ∑ ℓ ∈ dyadicLines L w j, ((2 ^ j : ℕ) : ℝ) := by simp [mul_comm]
    _ ≤ ∑ ℓ ∈ dyadicLines L w j, (w ℓ : ℝ) := by
      apply Finset.sum_le_sum
      intro ℓ hℓ
      exact_mod_cast dyadic_lower L w hw j hℓ

private lemma dyadic_rpow (j : ℕ) :
    (((2 ^ j : ℕ) : ℝ) ^ (-(1 : ℝ) / 3)) =
      ((2 : ℝ) ^ (-(1 : ℝ) / 3)) ^ j := by
  have h : ((2 : ℝ) ^ j) ^ (-(1 : ℝ) / 3) =
      ((2 : ℝ) ^ (-(1 : ℝ) / 3)) ^ j := by
    calc
      ((2 : ℝ) ^ j) ^ (-(1 : ℝ) / 3) =
          (2 : ℝ) ^ ((j : ℝ) * (-(1 : ℝ) / 3)) := by
        rw [← Real.rpow_natCast (2 : ℝ) j, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ = (2 : ℝ) ^ ((-(1 : ℝ) / 3) * (j : ℝ)) := by ring_nf
      _ = ((2 : ℝ) ^ (-(1 : ℝ) / 3)) ^ j := by
        rw [← Real.rpow_natCast ((2 : ℝ) ^ (-(1 : ℝ) / 3)) j,
          Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using h

private lemma dyadic_group_bound
    (C : ℝ) (hC : 0 ≤ C)
    (hST : ∀ (P : Finset (EuclideanSpace ℝ (Fin 2)))
        (L : Finset WeightedLine),
        (LineIncidences P L : ℝ) ≤
          C * (((P.card : ℝ) * (L.card : ℝ)) ^ ((2 : ℝ) / 3) +
            (P.card : ℝ) + (L.card : ℝ)))
    (P : Finset (EuclideanSpace ℝ (Fin 2)))
    (L : Finset WeightedLine) (w : WeightedLine → ℕ)
    (hw : ∀ ℓ ∈ L, 0 < w ℓ) (j : ℕ) :
    weightedIncidences P (dyadicLines L w j) w ≤
      2 * C *
        (((P.card : ℝ) * weightSquareSum L w) ^ ((2 : ℝ) / 3) *
          ((2 ^ j : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) +
         (P.card : ℝ) * ((2 ^ j : ℕ) : ℝ) +
         weightSum (dyadicLines L w j) w) := by
  let Lj := dyadicLines L w j
  let t : ℝ := ((2 ^ j : ℕ) : ℝ)
  let n : ℝ := P.card
  let k : ℝ := Lj.card
  let q : ℝ := weightSquareSum L w
  have ht : 0 < t := by dsimp [t]; positivity
  have hn : 0 ≤ n := by dsimp [n]; positivity
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hq : t ^ 2 * k ≤ q := dyadic_square_bound L w hw j
  have hmain := dyadic_main_bound n k q t hn hk ht hq
  have hweight : t * k ≤ weightSum Lj w := dyadic_weight_bound L w hw j
  have hinc := dyadic_incidence_bound P L w j
  have hst := hST P Lj
  have hpow : 0 ≤ (n * k) ^ ((2 : ℝ) / 3) := by positivity
  have hline : 0 ≤ (LineIncidences P Lj : ℝ) := by positivity
  have hst' : (LineIncidences P Lj : ℝ) ≤ C * ((n * k) ^ ((2 : ℝ) / 3) + n + k) := hst
  have hinc' : weightedIncidences P Lj w ≤ 2 * t * (LineIncidences P Lj : ℝ) := by
    convert hinc using 1
    dsimp [t]
    push_cast
    ring
  have hprod := mul_le_mul_of_nonneg_left hst' (by positivity : 0 ≤ 2 * t)
  change weightedIncidences P Lj w ≤
    2 * C * ((n * q) ^ ((2 : ℝ) / 3) * t ^ (-(1 : ℝ) / 3) +
      n * t + weightSum Lj w)
  nlinarith [mul_le_mul_of_nonneg_left hmain (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC),
    mul_le_mul_of_nonneg_left hweight (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC)]

/-- 论文 `lem:weighted`：有限点集、不同直线及正整数权重的加权关联上界。
空直线集的最大权重定义为零。 -/
theorem weightedST :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : Finset (EuclideanSpace ℝ (Fin 2)))
        (L : Finset WeightedLine) (w : WeightedLine → ℕ),
        (∀ ℓ ∈ L, 0 < w ℓ) →
        weightedIncidences P L w ≤ C *
          (((P.card : ℝ) ^ ((2 : ℝ) / 3)) *
             (weightSquareSum L w) ^ ((2 : ℝ) / 3) +
           (P.card : ℝ) * (maxWeight L w : ℝ) + weightSum L w) := by
  obtain ⟨C₀, hC₀, hST⟩ := stIncidence
  let r : ℝ := (2 : ℝ) ^ (-(1 : ℝ) / 3)
  have hr0 : 0 ≤ r := le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  let C : ℝ := 2 * C₀ * (1 / (1 - r) + 2)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro P L w hw
  by_cases hL : L = ∅
  · subst L
    simp [weightedIncidences, weightSquareSum, weightSum, maxWeight]
  let J := Nat.log 2 (maxWeight L w) + 1
  have hmax : 0 < maxWeight L w := by
    obtain ⟨ℓ, hℓ⟩ : L.Nonempty := Finset.nonempty_iff_ne_empty.mpr hL
    exact lt_of_lt_of_le (hw ℓ hℓ) (Finset.le_sup hℓ)
  have hpowNat : 2 ^ J ≤ 2 * maxWeight L w := by
    dsimp [J]
    rw [pow_succ]
    simpa [mul_comm] using
      Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 (Nat.ne_of_gt hmax))
  have hpowReal : (2 : ℝ) ^ J ≤ 2 * (maxWeight L w : ℝ) := by
    exact_mod_cast hpowNat
  have hsumPow : (∑ j ∈ Finset.range J, ((2 ^ j : ℕ) : ℝ)) =
      (2 : ℝ) ^ J - 1 := by
    have hs := geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1) J
    norm_num at hs
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hs
  have hsumWeight :
      (∑ j ∈ Finset.range J, weightSum (dyadicLines L w j) w) =
        weightSum L w := by
    simpa only [weightSum] using dyadic_partition L w (fun ℓ => (w ℓ : ℝ))
  have hsumInc :
      (∑ j ∈ Finset.range J, weightedIncidences P (dyadicLines L w j) w) =
        weightedIncidences P L w := by
    simpa only [weightedIncidences] using
      dyadic_partition L w
        (fun ℓ => (w ℓ : ℝ) * ((P.filter fun p => p ∈ (ℓ : AffineSubspace ℝ _)).card : ℝ))
  have hgeom := geom_bound r hr0 hr1 J
  let A : ℝ := ((P.card : ℝ) * weightSquareSum L w) ^ ((2 : ℝ) / 3)
  have hqNonneg : 0 ≤ weightSquareSum L w := by unfold weightSquareSum; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hn : 0 ≤ (P.card : ℝ) := by positivity
  have hW : 0 ≤ weightSum L w := by unfold weightSum; positivity
  have hsum : weightedIncidences P L w ≤
      2 * C₀ * (A * (∑ j ∈ Finset.range J, r ^ j) +
        (P.card : ℝ) * (∑ j ∈ Finset.range J, ((2 ^ j : ℕ) : ℝ)) +
        weightSum L w) := by
    rw [← hsumInc]
    have hgroup := Finset.sum_le_sum
      (fun j (hj : j ∈ Finset.range J) => dyadic_group_bound C₀ (le_of_lt hC₀) hST P L w hw j)
    convert hgroup using 1
    simp only [Finset.sum_add_distrib,
      ← Finset.mul_sum, dyadic_rpow, ← hsumWeight]
    ring
  have hmain : A * (∑ j ∈ Finset.range J, r ^ j) ≤ A / (1 - r) := by
    have := mul_le_mul_of_nonneg_left hgeom hA
    simpa [div_eq_mul_inv] using this
  have hpoint : (∑ j ∈ Finset.range J, ((2 ^ j : ℕ) : ℝ)) ≤
      2 * (maxWeight L w : ℝ) := by
    rw [hsumPow]
    linarith
  have htotal : weightedIncidences P L w ≤
      2 * C₀ * (A / (1 - r) + 2 * (P.card : ℝ) * (maxWeight L w : ℝ) +
        weightSum L w) := by
    have hp := mul_le_mul_of_nonneg_left hpoint hn
    nlinarith [mul_le_mul_of_nonneg_left hmain (by positivity : (0 : ℝ) ≤ 2 * C₀),
      mul_le_mul_of_nonneg_left hp (by positivity : (0 : ℝ) ≤ 2 * C₀)]
  have hfactor : A = ((P.card : ℝ) ^ ((2 : ℝ) / 3)) *
      (weightSquareSum L w) ^ ((2 : ℝ) / 3) := by
    dsimp [A]
    rw [Real.mul_rpow hn (by unfold weightSquareSum; positivity)]
  rw [hfactor] at htotal
  have haux : 0 ≤ 1 / (1 - r) := by positivity
  have hB : 0 ≤ (P.card : ℝ) ^ ((2 : ℝ) / 3) *
      weightSquareSum L w ^ ((2 : ℝ) / 3) := by positivity
  have hnm : 0 ≤ (P.card : ℝ) * (maxWeight L w : ℝ) := by positivity
  have hinner :
      (P.card : ℝ) ^ ((2 : ℝ) / 3) *
        weightSquareSum L w ^ ((2 : ℝ) / 3) / (1 - r) +
        2 * (P.card : ℝ) * (maxWeight L w : ℝ) + weightSum L w ≤
      (1 / (1 - r) + 2) *
        ((P.card : ℝ) ^ ((2 : ℝ) / 3) *
          weightSquareSum L w ^ ((2 : ℝ) / 3) +
          (P.card : ℝ) * (maxWeight L w : ℝ) + weightSum L w) := by
    have hdiv : ((P.card : ℝ) ^ ((2 : ℝ) / 3) *
        weightSquareSum L w ^ ((2 : ℝ) / 3)) / (1 - r) =
        (1 / (1 - r)) * ((P.card : ℝ) ^ ((2 : ℝ) / 3) *
          weightSquareSum L w ^ ((2 : ℝ) / 3)) := by ring
    rw [hdiv]
    have hnon := mul_nonneg haux (add_nonneg hnm hW)
    nlinarith
  calc
    weightedIncidences P L w ≤
        2 * C₀ * ((P.card : ℝ) ^ ((2 : ℝ) / 3) *
          weightSquareSum L w ^ ((2 : ℝ) / 3) / (1 - r) +
          2 * (P.card : ℝ) * (maxWeight L w : ℝ) + weightSum L w) := htotal
    _ ≤ C * ((P.card : ℝ) ^ ((2 : ℝ) / 3) *
          weightSquareSum L w ^ ((2 : ℝ) / 3) +
          (P.card : ℝ) * (maxWeight L w : ℝ) + weightSum L w) := by
      dsimp [C]
      convert mul_le_mul_of_nonneg_left hinner
        (by positivity : (0 : ℝ) ≤ 2 * C₀) using 1
      ring

end LonelyRunner
