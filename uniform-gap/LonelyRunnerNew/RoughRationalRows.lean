import LonelyRunnerNew.RoughRowGlobal
import LonelyRunnerNew.RoughRationalSmall

noncomputable section
open scoped BigOperators
namespace LonelyRunnerNew.RoughRational

def countedSet (S : Finset ℚ) (T : ℝ) : Finset ℚ := S.filter (fun r => (product r:ℝ) ≤ T)
def rowCount (S : Finset ℚ) (T : ℝ) (i : ℕ) : ℕ :=
  ((countedSet S T).filter (fun r => r.den = i+1)).card

theorem denominator_le_floor {R T : ℝ} (hR : 0 < R) (hT : 0 < T)
    (r : ℚ) (hr : 0 < r) (hl : R ≤ (r:ℝ)) (hprod : (product r:ℝ) ≤ T) :
    r.den ≤ ⌊Real.sqrt (T/R)⌋₊ := by
  have hd : (0:ℝ)<r.den := by exact_mod_cast r.pos
  rw [cast_eq_abs_num_div_den r hr] at hl
  have hnum := (le_div_iff₀ hd).mp hl
  have hsq : (r.den:ℝ)^2 ≤ T/R := by
    apply (le_div_iff₀ hR).2
    have hmul := mul_le_mul_of_nonneg_right hnum hd.le
    simp only [product, Nat.cast_mul] at hprod
    nlinarith
  exact (Nat.le_floor_iff (Real.sqrt_nonneg _)).2
    ((Real.le_sqrt hd.le (div_pos hT hR).le).2 hsq)

theorem count_eq_sum_rows (S : Finset ℚ) (T : ℝ) (m : ℕ)
    (hden : ∀ r ∈ countedSet S T, r.den ≤ m) :
    count S T = ∑ i ∈ Finset.range m, rowCount S T i := by
  have hp := Finset.card_eq_sum_card_fiberwise
    (s := countedSet S T) (t := Finset.range m) (f := fun r : ℚ => r.den-1)
    (fun r hr => Finset.mem_range.mpr (by
      dsimp only
      have h := hden r hr
      have hh := r.pos
      omega))
  change (countedSet S T).card = _
  conv_lhs => rw [hp]
  apply Finset.sum_congr rfl
  intro i hi
  unfold rowCount
  congr 1
  ext r
  have hh := r.pos
  simp only [Finset.mem_filter]
  constructor <;> intro h <;> exact ⟨h.1, by omega⟩

/-- The all-range row sums are applied to actual denominator fibres of S.
Only the row counting inequality still has to be supplied by sieve/packing. -/
theorem count_bound_of_row_bounds (S : Finset ℚ) (R T L Z Y : ℝ)
    (hR : 0 < R) (hT : 0 < T) (hL : 0 < L) (hZ : 0 < Z) (hY : 0 < Y+1)
    (hpos : ∀ r ∈ S, 0 < r) (hsector : ∀ r ∈ S, R ≤ (r:ℝ))
    (hrows : ∀ i < ⌊Real.sqrt (T/R)⌋₊, (rowCount S T i:ℝ) ≤ 1+
      ((569/1000:ℝ)*min (2*R*(i+1:ℝ)) (T/(i+1:ℝ))-(499/1000:ℝ)*R*(i+1:ℝ)+
        (569/1000:ℝ)*min (2*R*(i+1:ℝ)) (T/(i+1:ℝ))/(Y+1))/L+
      min (2*R*(i+1:ℝ)) (T/(i+1:ℝ))/Z) :
    (count S T:ℝ) ≤ (⌊Real.sqrt (T/R)⌋₊:ℝ)+
      ((639/2000:ℝ)*T+(1707/2000:ℝ)*T/(Y+1))/L+(3/2:ℝ)*T/Z := by
  have hp := count_eq_sum_rows S T ⌊Real.sqrt (T/R)⌋₊ (fun r hr =>
    denominator_le_floor hR hT r (hpos r (Finset.mem_filter.mp hr).1)
      (hsector r (Finset.mem_filter.mp hr).1) (Finset.mem_filter.mp hr).2)
  have hsum : (count S T:ℝ) = ∑ i ∈ Finset.range ⌊Real.sqrt (T/R)⌋₊, (rowCount S T i:ℝ) := by
    exact_mod_cast hp
  rw [hsum]
  exact RoughRow.aggregate_rows _ R T L Z Y hR hT (RoughRow.floor_physical hR hT)
    hL hZ hY (fun i => (rowCount S T i:ℝ)) hrows

end LonelyRunnerNew.RoughRational
