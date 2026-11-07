import LonelyRunnerNew.SelbergWeightNorm
import LonelyRunnerNew.SelbergInterval

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew.FiniteSelberg

/-- The actual closed-interval finite Selberg sieve. All weights, G bounds,
diagonalization, and interval error estimates are internally proved. -/
theorem finite_interval_sieve (X : ℕ) (hX : 2≤X) {U A : ℝ} (hU : 0<U) (hUA : U≤A) :
    ((RoughRational.roughIntegerInterval X U A).card:ℝ)≤
      (A-U)/Real.log (X+1:ℝ)+16*(X:ℝ)^2/(Real.log (X+1:ℝ))^2 := by
  have hx0 : 0<X := by omega
  have hG := G_pos hx0
  have hlog : 0<Real.log (X+1:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1<X+1))
  have hLG := log_le_G X
  have hc := (rough_card_le_square hx0 hU hUA).trans (square_sum_upper X (weight X) hU hUA)
  rw [weight_quadratic hx0] at hc
  have hW0 : 0≤∑d∈Finset.Icc 1 X,|weight X d| := Finset.sum_nonneg (fun d hd => abs_nonneg _)
  have hW := weight_abs_sum_le hX
  have hWsq := (sq_le_sq₀ hW0 (by positivity : (0:ℝ)≤4*(X:ℝ)/G X)).mpr hW
  have hmain : (A-U)/G X≤(A-U)/Real.log (X+1:ℝ) :=
    div_le_div_of_nonneg_left (by linarith) hlog hLG
  have herr : 16*(X:ℝ)^2/(G X)^2≤16*(X:ℝ)^2/(Real.log (X+1:ℝ))^2 :=
    div_le_div_of_nonneg_left (by positivity) (pow_pos hlog 2)
      ((sq_le_sq₀ hlog.le hG.le).mpr hLG)
  have he1 : (A-U)*(1/G X)=(A-U)/G X := by ring
  have he2 : (4*(X:ℝ)/G X)^2=16*(X:ℝ)^2/(G X)^2 := by ring
  rw [he1] at hc
  rw [he2] at hWsq
  linarith

end LonelyRunnerNew.FiniteSelberg
