import LonelyRunnerNew.RoughRowPacking

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew.RoughRational

def rowUpper (R T : ℝ) (i : ℕ) : ℝ := min (2*R*(i+1:ℝ)) (T/(i+1:ℝ))
def rowMajorant (R T L Z Y : ℝ) (i : ℕ) : ℝ := 1+
  ((569/1000:ℝ)*rowUpper R T i-(499/1000:ℝ)*R*(i+1:ℝ)+
    (569/1000:ℝ)*rowUpper R T i/(Y+1))/L+rowUpper R T i/Z

theorem rowUpper_lower (R T : ℝ) (hR : 0<R) (hT : 0<T)
    {i : ℕ} (hi : i<⌊Real.sqrt (T/R)⌋₊) : R*(i+1:ℝ)≤rowUpper R T i := by
  have hb : (i+1:ℝ)≤(⌊Real.sqrt (T/R)⌋₊:ℝ) := by exact_mod_cast (show i+1≤⌊Real.sqrt (T/R)⌋₊ by omega)
  have hs := pow_le_pow_left₀ (by positivity : (0:ℝ)≤(i+1:ℝ)) hb 2
  have hf := RoughRow.floor_physical hR hT
  have hp := (mul_le_mul_of_nonneg_right hs hR.le).trans hf
  apply le_min
  · nlinarith [mul_pos hR (by positivity : (0:ℝ)<(i+1:ℝ))]
  · apply (le_div_iff₀ (by positivity : (0:ℝ)<(i+1:ℝ))).mpr
    nlinarith only [hp]

theorem rowMajorant_ge_one (R T L Z Y : ℝ) (hR : 0<R) (hT : 0<T)
    (hL : 0<L) (hZ : 0<Z) (hY : 0<Y+1) {i : ℕ} (hi : i<⌊Real.sqrt (T/R)⌋₊) :
    (1:ℝ)≤rowMajorant R T L Z Y i := by
  have hb := rowUpper_lower R T hR hT hi
  have hu : 0≤rowUpper R T i := (mul_nonneg hR.le (by positivity)).trans hb
  have hn : 0≤(569/1000:ℝ)*rowUpper R T i-(499/1000:ℝ)*R*(i+1:ℝ) := by
    nlinarith [mul_nonneg hR.le (by positivity : (0:ℝ)≤(i+1:ℝ))]
  have ht := div_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤569/1000) hu) hY.le
  have hp := div_nonneg (add_nonneg hn ht) hL.le
  have hz := div_nonneg hu hZ.le
  unfold rowMajorant
  linarith

/-- The old full-row aggregation only needs sieve input for rows whose actual
numerator upper bound exceeds exp ell. Every other row is discharged here. -/
theorem count_bound_of_residual_rows (S : Finset ℚ) (ell R T L Z Y : ℝ)
    (hR : 0<R) (hT : 0<T) (hL : 0<L) (hZ : 0<Z) (hY : 0<Y+1)
    (hrough : ∀ r∈S,roughPoint 142 r)
    (hsector : ∀ r∈S,R≤(r:ℝ) ∧ (r:ℝ)<2*R) (hsep : separated (Real.exp ell) S)
    (hrows : ∀ i<⌊Real.sqrt (T/R)⌋₊,Real.exp ell<rowUpper R T i →
      (rowCount S T i:ℝ)≤rowMajorant R T L Z Y i) :
    (count S T:ℝ)≤(⌊Real.sqrt (T/R)⌋₊:ℝ)+
      ((639/2000:ℝ)*T+(1707/2000:ℝ)*T/(Y+1))/L+(3/2:ℝ)*T/Z := by
  apply count_bound_of_row_bounds S R T L Z Y hR hT hL hZ hY
    (fun r hr => (hrough r hr).1) (fun r hr => (hsector r hr).1)
  intro i hi
  change (rowCount S T i:ℝ)≤rowMajorant R T L Z Y i
  by_cases hu : Real.exp ell<rowUpper R T i
  · exact hrows i hi hu
  · have hs := row_singleton_of_small_upper S hR i (fun r hr => (hrough r hr).1) hsector hsep (le_of_not_gt hu)
    have hsR : (rowCount S T i:ℝ)≤1 := by exact_mod_cast hs
    exact hsR.trans (rowMajorant_ge_one R T L Z Y hR hT hL hZ hY hi)

end LonelyRunnerNew.RoughRational
