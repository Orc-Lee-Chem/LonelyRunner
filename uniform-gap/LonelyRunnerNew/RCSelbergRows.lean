import LonelyRunnerNew.FiniteIntervalSieve
import LonelyRunnerNew.RoughRowReduction

noncomputable section
set_option autoImplicit false
namespace LonelyRunnerNew.RoughRational
attribute [local instance] Classical.propDecidable

theorem cutoff_log_succ (ell alpha : ℝ) : alpha*ell<Real.log (Asymmetric.cutoff ell alpha+1:ℝ) := by
  have hh := Nat.lt_floor_add_one (Real.exp (alpha*ell))
  have hl := Real.log_lt_log (Real.exp_pos _) hh
  rw [Real.log_exp] at hl
  exact hl

theorem initial_rough_sieve (X : ℕ) (hX : 2≤X) {A : ℝ} (hA : 0≤A) :
    ((roughIntegerInterval X 1 A).card:ℝ)≤A/Real.log (X+1:ℝ)+
      16*(X:ℝ)^2/(Real.log (X+1:ℝ))^2 := by
  have hL : 0<Real.log (X+1:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1<X+1))
  by_cases h : 1≤A
  · have hb := FiniteSelberg.finite_interval_sieve X hX (by norm_num : (0:ℝ)<1) h
    have hh := div_le_div_of_nonneg_right (by linarith : A-1≤A) hL.le
    linarith
  · have he : roughIntegerInterval X 1 A=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hn
      have hh := Finset.mem_filter.mp hn
      have hb : (n:ℝ)≤A := by
        have hi := Finset.mem_range.mp hh.1
        exact (by exact_mod_cast (by omega : n≤⌊A⌋₊) : (n:ℝ)≤⌊A⌋₊).trans (Nat.floor_le hA)
      linarith [hh.2.2]
    rw [he,Finset.card_empty,Nat.cast_zero]
    positivity

theorem two_interval_sieve (X : ℕ) (hX : 2≤X) {U A : ℝ} (hU : 0<U) (hUA : U≤A) :
    ((roughIntegerInterval X U A).card:ℝ)+(roughIntegerInterval X 1 (A/143)).card≤
      (A-U+A/143)/Real.log (X+1:ℝ)+32*(X:ℝ)^2/(Real.log (X+1:ℝ))^2 := by
  have hA : 0≤A := hU.le.trans hUA
  have h1 := FiniteSelberg.finite_interval_sieve X hX hU hUA
  have h2 := initial_rough_sieve X hX (div_nonneg hA (by norm_num : (0:ℝ)≤143))
  have he : (A-U+A/143)/Real.log (X+1:ℝ)=
      (A-U)/Real.log (X+1:ℝ)+(A/143)/Real.log (X+1:ℝ) := by ring
  rw [he]
  simp only [div_eq_mul_inv] at h1 h2 ⊢
  linarith

theorem two_interval_power_sieve {ell alpha U A : ℝ} (hell : 4096≤ell)
    (hal : (1/5:ℝ)≤alpha) (hau : alpha≤9/10) (hU : 0<U) (hUA : U≤A) :
    ((roughIntegerInterval (Asymmetric.cutoff ell alpha) U A).card:ℝ)+
      (roughIntegerInterval (Asymmetric.cutoff ell alpha) 1 (A/143)).card≤
      (A-U+A/143)/(alpha*ell)+32*Real.exp (2*alpha*ell)/(alpha*ell)^2 := by
  let X := Asymmetric.cutoff ell alpha
  let L := Real.log (X+1:ℝ)
  have hc := Asymmetric.parameter_conditions hell hal hau
  have hx : 2≤X := by omega
  have hL0 : 0<alpha*ell := by
    have he : 0<ell := by linarith
    have ha : 0<alpha := by linarith
    positivity
  have hL : alpha*ell≤L := (cutoff_log_succ ell alpha).le
  have hX : (X:ℝ)≤Real.exp (alpha*ell) := Nat.floor_le (Real.exp_nonneg _)
  have hx2 : (X:ℝ)^2≤Real.exp (2*alpha*ell) := by
    have he : Real.exp (alpha*ell)^2=Real.exp (2*alpha*ell) := by rw [pow_two,←Real.exp_add];congr 1;ring
    rw [←he]
    gcongr
  have herr : 32*(X:ℝ)^2/L^2≤32*Real.exp (2*alpha*ell)/(alpha*ell)^2 := by
    have hn := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hx2 (by norm_num : (0:ℝ)≤32)) (sq_nonneg L)
    have hd := div_le_div_of_nonneg_left (by positivity : (0:ℝ)≤32*Real.exp (2*alpha*ell))
      (pow_pos hL0 2) ((sq_le_sq₀ hL0.le (hL0.le.trans hL)).mpr hL)
    exact hn.trans hd
  have hp := two_interval_sieve X hx hU hUA
  change ((roughIntegerInterval X U A).card:ℝ)+(roughIntegerInterval X 1 (A/143)).card≤_
  have hm : (A-U+A/143)/L≤(A-U+A/143)/(alpha*ell) := by
    apply div_le_div_of_nonneg_left _ hL0 hL
    have hA : 0≤A := hU.le.trans hUA
    linarith
  linarith

/-- Actual rational row, not an abstract independent count. -/
theorem row_selberg_bound (S : Finset ℚ) {R T ell alpha : ℝ} (hR : 0<R) (hT : 0<T)
    (hell : 4096≤ell) (hal : (1/5:ℝ)≤alpha) (hau : alpha≤9/10)
    {i : ℕ} (hi : i<⌊Real.sqrt (T/R)⌋₊)
    (hrough : ∀r∈S,roughPoint 142 r)
    (hsector : ∀r∈S,R≤(r:ℝ) ∧ (r:ℝ)<2*R) (hsep : separated (Real.exp ell) S) :
    (rowCount S T i:ℝ)≤(rowUpper R T i-R*(i+1:ℝ)+rowUpper R T i/143)/(alpha*ell)+
      32*Real.exp (2*alpha*ell)/(alpha*ell)^2+2*rowUpper R T i*Real.exp (-ell/10) := by
  have hrow := Asymmetric.row_power_packing S hR hT hell hal hau i hrough hsector hsep
  have hs := two_interval_power_sieve hell hal hau (by positivity : (0:ℝ)<R*(i+1:ℝ))
    (rowUpper_lower R T hR hT hi)
  change (rowCount S T i:ℝ)≤(roughIntegerInterval (Asymmetric.cutoff ell alpha) (R*(i+1:ℝ)) (rowUpper R T i)).card+
    (roughIntegerInterval (Asymmetric.cutoff ell alpha) 1 (rowUpper R T i/143)).card+
    2*rowUpper R T i*Real.exp (-ell/10) at hrow
  linarith

end LonelyRunnerNew.RoughRational
