import LonelyRunnerNew.Definitions
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

noncomputable section
open scoped BigOperators

namespace LonelyRunnerNew.LargePrime

def rectangleMass (E : Finset (ℕ × ℕ)) (mu : ℕ × ℕ → ℝ) (A B : Finset ℕ) : ℝ :=
  ∑ e ∈ E.filter (fun e => e.1 ∈ A ∧ e.2 ∈ B), mu e

def lowerMass (E : Finset (ℕ × ℕ)) (mu : ℕ × ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ e ∈ E.filter (fun e => e.1 < k ∧ e.2 < k), mu e

def upperMass (E : Finset (ℕ × ℕ)) (mu : ℕ × ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ e ∈ E.filter (fun e => k < e.1 ∧ k < e.2), mu e

def exceptionMass (E : Finset (ℕ × ℕ)) (mu : ℕ × ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ e ∈ E.filter (fun e => ¬ (min e.1 e.2 ≤ k ∧ k ≤ max e.1 e.2)), mu e

theorem exceptionMass_eq_tails (E : Finset (ℕ × ℕ)) (mu : ℕ × ℕ → ℝ) (k : ℕ) :
    exceptionMass E mu k = lowerMass E mu k + upperMass E mu k := by
  unfold exceptionMass lowerMass upperMass
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hlo : e.1 < k ∧ e.2 < k
  · have hhi : ¬ (k < e.1 ∧ k < e.2) := by omega
    simp [hlo, hhi]
  · by_cases hhi : k < e.1 ∧ k < e.2
    · simp [hlo, hhi]
    · have hgood : min e.1 e.2 ≤ k ∧ k ≤ max e.1 e.2 := by omega
      simp [hlo, hhi, hgood]

theorem lowerMass_eq_rectangle (I J : Finset ℕ) (E : Finset (ℕ × ℕ))
    (hE : E ⊆ I.product J) (mu : ℕ × ℕ → ℝ) (k : ℕ) :
    lowerMass E mu k = rectangleMass E mu (I.filter (· < k)) (J.filter (· < k)) := by
  unfold lowerMass rectangleMass
  have hfilter : E.filter (fun e => e.1 < k ∧ e.2 < k) =
      E.filter (fun e => e.1 ∈ I.filter (· < k) ∧ e.2 ∈ J.filter (· < k)) := by
    apply Finset.filter_congr
    intro e he
    have hm := Finset.mem_product.mp (hE he)
    simp only [Finset.mem_filter, hm.1, hm.2, true_and]
  rw [hfilter]

theorem upperMass_eq_rectangle (I J : Finset ℕ) (E : Finset (ℕ × ℕ))
    (hE : E ⊆ I.product J) (mu : ℕ × ℕ → ℝ) (k : ℕ) :
    upperMass E mu k = rectangleMass E mu (I.filter (k < ·)) (J.filter (k < ·)) := by
  unfold upperMass rectangleMass
  have hfilter : E.filter (fun e => k < e.1 ∧ k < e.2) =
      E.filter (fun e => e.1 ∈ I.filter (k < ·) ∧ e.2 ∈ J.filter (k < ·)) := by
    apply Finset.filter_congr
    intro e he
    have hm := Finset.mem_product.mp (hE he)
    simp only [Finset.mem_filter, hm.1, hm.2, true_and]
  rw [hfilter]

theorem product_rpow_le_mean {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a * b) ^ (3 / 4 : ℝ) ≤ ((a + b) / 2) ^ (3 / 2 : ℝ) := by
  have hmean : 0 ≤ (a + b) / 2 := by positivity
  have hprod : a * b ≤ ((a + b) / 2) ^ 2 := by nlinarith [sq_nonneg (a - b)]
  calc
    (a * b) ^ (3 / 4 : ℝ) ≤ (((a + b) / 2) ^ 2) ^ (3 / 4 : ℝ) :=
      Real.rpow_le_rpow (mul_nonneg ha hb) hprod (by norm_num)
    _ = ((a + b) / 2) ^ (3 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hmean]
      norm_num

/-- The exact same-direction tail estimate, for a given center. This theorem
does not assert that a center with a small tail exists. -/
theorem exceptionMass_le_tail_means (I J : Finset ℕ) (E : Finset (ℕ × ℕ))
    (hE : E ⊆ I.product J) (mu : ℕ × ℕ → ℝ) (alpha beta : ℕ → ℝ)
    (ha : ∀ i ∈ I, 0 ≤ alpha i) (hb : ∀ j ∈ J, 0 ≤ beta j)
    (hrect : ∀ A ⊆ I, ∀ B ⊆ J, rectangleMass E mu A B ≤
      ((∑ i ∈ A, alpha i) * (∑ j ∈ B, beta j)) ^ (3 / 4 : ℝ)) (k : ℕ) :
    exceptionMass E mu k ≤
      (((∑ i ∈ I.filter (· < k), alpha i) +
        (∑ j ∈ J.filter (· < k), beta j)) / 2) ^ (3 / 2 : ℝ) +
      (((∑ i ∈ I.filter (k < ·), alpha i) +
        (∑ j ∈ J.filter (k < ·), beta j)) / 2) ^ (3 / 2 : ℝ) := by
  rw [exceptionMass_eq_tails, lowerMass_eq_rectangle I J E hE,
    upperMass_eq_rectangle I J E hE]
  apply add_le_add
  · exact (hrect _ (Finset.filter_subset _ _) _ (Finset.filter_subset _ _)).trans
      (product_rpow_le_mean
        (Finset.sum_nonneg (fun i hi => ha i (Finset.mem_filter.mp hi).1))
        (Finset.sum_nonneg (fun j hj => hb j (Finset.mem_filter.mp hj).1)))
  · exact (hrect _ (Finset.filter_subset _ _) _ (Finset.filter_subset _ _)).trans
      (product_rpow_le_mean
        (Finset.sum_nonneg (fun i hi => ha i (Finset.mem_filter.mp hi).1))
        (Finset.sum_nonneg (fun j hj => hb j (Finset.mem_filter.mp hj).1)))

/-- The modal-center extraction needed after a diagonal lower bound is proved.
The diagonal lower bound is an explicit premise, not supplied by this theorem. -/
theorem center_of_diagonal_lower_bound (F : Finset ℕ) (alpha beta : ℕ → ℝ)
    (ha : ∀ i ∈ F, 0 ≤ alpha i) (hb : ∀ i ∈ F, 0 ≤ beta i)
    (hasum : (∑ i ∈ F, alpha i) = 1) (hbsum : (∑ i ∈ F, beta i) = 1)
    (d : ℝ) (hd : 0 ≤ d)
    (hdiag : d ≤ ∑ i ∈ F, (alpha i * beta i) ^ (3 / 4 : ℝ)) :
    ∃ k ∈ F, d ^ 2 ≤ (alpha k + beta k) / 2 := by
  let m : ℕ → ℝ := fun i => (alpha i + beta i) / 2
  have hF : F.Nonempty := Finset.nonempty_of_ne_empty (by
    intro h
    simp [h] at hasum)
  obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image F m hF
  have hm : ∀ i ∈ F, 0 ≤ m i := by
    intro i hi
    have hai := ha i hi
    have hbi := hb i hi
    dsimp [m]
    positivity
  have hsum : (∑ i ∈ F, m i) = 1 := by
    dsimp [m]
    rw [← Finset.sum_div, Finset.sum_add_distrib, hasum, hbsum]
    norm_num
  have hpoint : ∀ i ∈ F,
      (alpha i * beta i) ^ (3 / 4 : ℝ) ≤ m i * Real.sqrt (m k) := by
    intro i hi
    calc
      (alpha i * beta i) ^ (3 / 4 : ℝ) ≤ m i ^ (3 / 2 : ℝ) :=
        product_rpow_le_mean (ha i hi) (hb i hi)
      _ = m i * Real.sqrt (m i) := by
        rw [show (3 / 2 : ℝ) = 1 + (1 / 2 : ℝ) by norm_num,
          Real.rpow_one_add' (hm i hi) (by norm_num), ← Real.sqrt_eq_rpow]
      _ ≤ m i * Real.sqrt (m k) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hmax i hi)) (hm i hi)
  have hroot : d ≤ Real.sqrt (m k) := by
    calc
      d ≤ ∑ i ∈ F, (alpha i * beta i) ^ (3 / 4 : ℝ) := hdiag
      _ ≤ ∑ i ∈ F, m i * Real.sqrt (m k) := Finset.sum_le_sum hpoint
      _ = Real.sqrt (m k) := by rw [← Finset.sum_mul, hsum, one_mul]
  have hsq := pow_le_pow_left₀ hd hroot 2
  rw [Real.sq_sqrt (hm k hk)] at hsq
  exact ⟨k, hk, hsq⟩

end LonelyRunnerNew.LargePrime
