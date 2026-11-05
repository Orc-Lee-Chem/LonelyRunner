import LonelyRunnerNew.ValuationDistribution
import Mathlib.Analysis.MeanInequalities
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Data.Int.NatAbs

noncomputable section
open scoped BigOperators
namespace LonelyRunnerNew.BootstrapGeometry

theorem finite_geometric_tail (F : Finset ℕ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hF : ∀ d ∈ F, 1 ≤ d) : (∑ d ∈ F, r^d) ≤ r/(1-r) := by
  have hsub : F ⊆ Finset.Ico 1 (F.sup id+1) := by
    intro d hd
    exact Finset.mem_Ico.mpr ⟨hF d hd, Nat.lt_succ_of_le (Finset.le_sup (f := id) hd)⟩
  calc
    _ ≤ ∑ d ∈ Finset.Ico 1 (F.sup id+1), r^d :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => pow_nonneg hr _)
    _ ≤ r/(1-r) := by simpa using geom_sum_Ico_le_of_lt_one (m := 1) (n := F.sup id+1) hr hr1

theorem lower_geometric_tail (F : Finset ℕ) (k : ℕ) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) (hF : ∀ j ∈ F, j < k) :
    (∑ j ∈ F, r^((k:ℤ)-(j:ℤ)).natAbs) ≤ r/(1-r) := by
  have hinj : Set.InjOn (fun j => k-j) F := by
    intro i hi j hj heq
    dsimp only at heq
    have := hF i hi
    have := hF j hj
    omega
  calc
    _ = ∑ j ∈ F, r^(k-j) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Int.natAbs_natCast_sub_natCast_of_ge (hF j hj).le]
    _ = ∑ d ∈ F.image (fun j => k-j), r^d := (Finset.sum_image hinj).symm
    _ ≤ r/(1-r) := finite_geometric_tail _ hr hr1 (by
      intro d hd
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hd
      have := hF j hj
      omega)

theorem upper_geometric_tail (F : Finset ℕ) (k : ℕ) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) (hF : ∀ j ∈ F, k < j) :
    (∑ j ∈ F, r^((k:ℤ)-(j:ℤ)).natAbs) ≤ r/(1-r) := by
  have hinj : Set.InjOn (fun j => j-k) F := by
    intro i hi j hj heq
    dsimp only at heq
    have := hF i hi
    have := hF j hj
    omega
  calc
    _ = ∑ j ∈ F, r^(j-k) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Int.natAbs_natCast_sub_natCast_of_le (hF j hj).le]
    _ = ∑ d ∈ F.image (fun j => j-k), r^d := (Finset.sum_image hinj).symm
    _ ≤ r/(1-r) := finite_geometric_tail _ hr hr1 (by
      intro d hd
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hd
      have := hF j hj
      omega)

/-- Both sides are bounded separately. At k=0 the lower side is empty. -/
theorem away_geometric_tail (F : Finset ℕ) (k : ℕ) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) :
    (∑ j ∈ F.erase k, r^((k:ℤ)-(j:ℤ)).natAbs) ≤ 2*r/(1-r) := by
  have he : (∑ j ∈ F.erase k, r^((k:ℤ)-(j:ℤ)).natAbs) =
      (∑ j ∈ (F.erase k).filter (· < k), r^((k:ℤ)-(j:ℤ)).natAbs)+
      (∑ j ∈ (F.erase k).filter (k < ·), r^((k:ℤ)-(j:ℤ)).natAbs) := by
    simp only [Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hne := (Finset.mem_erase.mp hj).1
    by_cases h : j < k
    · have : ¬ k < j := by omega
      simp [h,this]
    · have : k < j := by omega
      simp [h,this]
  rw [he]
  have hl := lower_geometric_tail ((F.erase k).filter (· < k)) k hr hr1
    (fun _ h => (Finset.mem_filter.mp h).2)
  have hu := upper_geometric_tail ((F.erase k).filter (k < ·)) k hr hr1
    (fun _ h => (Finset.mem_filter.mp h).2)
  calc
    _ ≤ r/(1-r)+r/(1-r) := add_le_add hl hu
    _ = _ := by ring

theorem holder_row (F : Finset ℕ) (k : ℕ) (beta : ℕ → ℝ)
    (hb : ∀ j ∈ F.erase k, 0 ≤ beta j) {lam : ℝ} (hl0 : 0 ≤ lam) (hl1 : lam < 1) :
    (∑ j ∈ F.erase k, lam^((k:ℤ)-(j:ℤ)).natAbs*(beta j)^(3/4:ℝ)) ≤
      (2*lam^4/(1-lam^4))^(1/4:ℝ)*(∑ j ∈ F.erase k, beta j)^(3/4:ℝ) := by
  have hpq : Real.HolderConjugate 4 (4/3) := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hh := Real.inner_le_Lp_mul_Lq_of_nonneg (s := F.erase k)
    (f := fun j => lam^((k:ℤ)-(j:ℤ)).natAbs) (g := fun j => (beta j)^(3/4:ℝ)) hpq
    (fun _ _ => pow_nonneg hl0 _) (fun j hj => Real.rpow_nonneg (hb j hj) _)
  have he : (∑ j ∈ F.erase k, (lam^((k:ℤ)-(j:ℤ)).natAbs)^(4:ℝ)) =
      ∑ j ∈ F.erase k, (lam^4)^((k:ℤ)-(j:ℤ)).natAbs := by
    apply Finset.sum_congr rfl
    intro j hj
    norm_num only [Real.rpow_ofNat]
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  have hg : (∑ j ∈ F.erase k, ((beta j)^(3/4:ℝ))^(4/3:ℝ)) = ∑ j ∈ F.erase k, beta j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [← Real.rpow_mul (hb j hj)]
    norm_num
  rw [he,hg] at hh
  norm_num only [one_div_div, one_div_one, div_one] at hh
  have hl4 : lam^4 < 1 := by simpa using pow_lt_pow_left₀ hl1 hl0 (by decide : (4:ℕ)≠0)
  exact hh.trans (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (Finset.sum_nonneg (fun _ _ => pow_nonneg (pow_nonneg hl0 4) _))
      (away_geometric_tail F k (pow_nonneg hl0 4) hl4) (by norm_num))
    (Real.rpow_nonneg (Finset.sum_nonneg hb) _))

end LonelyRunnerNew.BootstrapGeometry
