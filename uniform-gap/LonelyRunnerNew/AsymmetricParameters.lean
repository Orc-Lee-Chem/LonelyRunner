import LonelyRunnerNew.AsymmetricRows

noncomputable section
set_option autoImplicit false
namespace LonelyRunnerNew.RoughRational.Asymmetric

def cutoff (ell alpha : ℝ) : ℕ := ⌊Real.exp (alpha*ell)⌋₊
def multiplier (ell : ℝ) : ℕ := ⌊Real.exp (ell/10)⌋₊

/-- All three cutoffs 9/10,4/5,1/5 meet the exact asymmetric arithmetic
conditions on the whole infinite ell range. Floors are not ignored. -/
theorem parameter_conditions {ell alpha : ℝ} (hell : 4096≤ell)
    (hal : (1/5:ℝ)≤alpha) (hau : alpha≤9/10) :
    142≤cutoff ell alpha ∧ 0<multiplier ell ∧
      (multiplier ell)^2≤cutoff ell alpha ∧
      ((cutoff ell alpha*multiplier ell:ℕ):ℝ)≤Real.exp ell ∧
      Real.exp (ell/10)/2≤(multiplier ell:ℝ) ∧
      alpha*ell-1<Real.log (cutoff ell alpha+1:ℝ) := by
  have hp : 0<ell := by linarith
  have ha : 0<alpha := by linarith
  have he := Real.add_one_le_exp (alpha*ell)
  have ht := Real.add_one_le_exp (ell/10)
  have hcut : (cutoff ell alpha:ℝ)≤Real.exp (alpha*ell) := Nat.floor_le (Real.exp_nonneg _)
  have hmult : (multiplier ell:ℝ)≤Real.exp (ell/10) := Nat.floor_le (Real.exp_nonneg _)
  have hmultlo : Real.exp (ell/10)-1<(multiplier ell:ℝ) := Nat.sub_one_lt_floor _
  have hx142 : 142≤cutoff ell alpha := (Nat.le_floor_iff (Real.exp_nonneg _)).mpr (by
    norm_num
    have hm : (1/5:ℝ)*ell≤alpha*ell := mul_le_mul_of_nonneg_right hal hp.le
    linarith)
  have hz : 0<multiplier ell := by
    have hr : (0:ℝ)<multiplier ell := by linarith
    exact_mod_cast hr
  have hsquare : (multiplier ell)^2≤cutoff ell alpha := by
    apply (Nat.le_floor_iff (Real.exp_nonneg _)).mpr
    rw [Nat.cast_pow]
    calc
      (multiplier ell:ℝ)^2≤(Real.exp (ell/10))^2 := by gcongr
      _ =Real.exp (ell/5) := by rw [pow_two,←Real.exp_add];congr 1;ring
      _ ≤Real.exp (alpha*ell) := Real.exp_le_exp.mpr (by nlinarith)
  have hprod : ((cutoff ell alpha*multiplier ell:ℕ):ℝ)≤Real.exp ell := by
    rw [Nat.cast_mul]
    calc
      _ ≤Real.exp (alpha*ell)*Real.exp (ell/10) := mul_le_mul hcut hmult (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ =Real.exp (alpha*ell+ell/10) := (Real.exp_add _ _).symm
      _ ≤Real.exp ell := Real.exp_le_exp.mpr (by nlinarith)
  have hfhalf : Real.exp (ell/10)/2≤(multiplier ell:ℝ) := by
    have hf : (multiplier ell:ℝ)+1≤2*(multiplier ell:ℝ) := by exact_mod_cast (by omega : multiplier ell+1≤2*multiplier ell)
    have hh := Nat.lt_floor_add_one (Real.exp (ell/10))
    change Real.exp (ell/10)<(multiplier ell:ℝ)+1 at hh
    linarith
  have hlog : alpha*ell-1<Real.log (cutoff ell alpha+1:ℝ) := by
    have hh := Nat.lt_floor_add_one (Real.exp (alpha*ell))
    change Real.exp (alpha*ell)<(cutoff ell alpha:ℝ)+1 at hh
    have hl := Real.log_lt_log (Real.exp_pos _) hh
    rw [Real.log_exp] at hl
    norm_num only [Nat.cast_add,Nat.cast_one]
    linarith
  exact ⟨hx142,hz,hsquare,hprod,hfhalf,hlog⟩

theorem packing_error {ell A : ℝ} (hell : 4096≤ell) (hA : 0≤A) :
    A/(multiplier ell:ℝ)≤2*A*Real.exp (-ell/10) := by
  have hc := parameter_conditions hell (alpha:=1/5) (by norm_num) (by norm_num)
  have hz : (0:ℝ)<multiplier ell := by exact_mod_cast hc.2.1
  have hh := hc.2.2.2.2.1
  have he : Real.exp (-ell/10)=1/Real.exp (ell/10) := by
    rw [show -ell/10=-(ell/10) by ring,Real.exp_neg,one_div]
  rw [he]
  calc
    _ ≤ A/(Real.exp (ell/10)/2) := div_le_div_of_nonneg_left hA (by positivity) hh
    _ = _ := by ring

theorem row_power_packing (S : Finset ℚ) {R T ell alpha : ℝ} (hR : 0<R) (hT : 0<T)
    (hell : 4096≤ell) (hal : (1/5:ℝ)≤alpha) (hau : alpha≤9/10) (i : ℕ)
    (hrough : ∀r∈S,roughPoint 142 r)
    (hsector : ∀r∈S,R≤(r:ℝ) ∧ (r:ℝ)<2*R) (hsep : separated (Real.exp ell) S) :
    (rowCount S T i:ℝ)≤
      (roughIntegerInterval (cutoff ell alpha) (R*(i+1:ℝ))
        (min (2*R*(i+1:ℝ)) (T/(i+1:ℝ)))).card+
      (roughIntegerInterval (cutoff ell alpha) 1
        ((min (2*R*(i+1:ℝ)) (T/(i+1:ℝ)))/143)).card+
      2*(min (2*R*(i+1:ℝ)) (T/(i+1:ℝ)))*Real.exp (-ell/10) := by
  have hc := parameter_conditions hell hal hau
  have hp := row_asymmetric_packing S hR hT i (cutoff ell alpha) (multiplier ell)
    hc.2.1 hc.2.2.1 hc.2.2.2.1 hrough hsector hsep
  have he := packing_error (A:=min (2*R*(i+1:ℝ)) (T/(i+1:ℝ))) hell (by positivity)
  linarith

theorem small_B_power_packing (S : Finset ℚ) {R T ell alpha : ℝ} (hR : 0<R) (hT : 0<T)
    (hell : 4096≤ell) (hal : (1/5:ℝ)≤alpha) (hau : alpha≤9/10)
    (hB : Real.sqrt (T/R)<128) (hrough : ∀r∈S,roughPoint 142 r)
    (hsector : ∀r∈S,R≤(r:ℝ) ∧ (r:ℝ)<2*R) (hsep : separated (Real.exp ell) S) :
    (count S T:ℝ)≤
      (roughIntegerInterval (cutoff ell alpha) R (min (2*R) T)).card+
      (roughIntegerInterval (cutoff ell alpha) 1 ((min (2*R) T)/143)).card+
      2*(min (2*R) T)*Real.exp (-ell/10) := by
  rw [small_B_count_one_row S hR hT hB hrough (fun r hr => (hsector r hr).1)]
  simpa only [Nat.cast_zero,zero_add,mul_one,div_one] using
    row_power_packing S hR hT hell hal hau 0 hrough hsector hsep

theorem cutoff_log_lower {ell alpha : ℝ} (hell : 4096≤ell)
    (hal : (1/5:ℝ)≤alpha) (hau : alpha≤9/10) :
    alpha*ell-1<Real.log (cutoff ell alpha:ℝ) := by
  have hc := parameter_conditions hell hal hau
  have hX : (1:ℝ)≤cutoff ell alpha := by exact_mod_cast (by omega : 1≤cutoff ell alpha)
  have hh := Nat.lt_floor_add_one (Real.exp (alpha*ell))
  change Real.exp (alpha*ell)<(cutoff ell alpha:ℝ)+1 at hh
  have hl := Real.log_lt_log (Real.exp_pos _) (hh.trans_le (by linarith : (cutoff ell alpha:ℝ)+1≤2*(cutoff ell alpha:ℝ)))
  rw [Real.log_exp,Real.log_mul (by norm_num : (2:ℝ)≠0) (by linarith : (cutoff ell alpha:ℝ)≠0)] at hl
  have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  norm_num at hlog2
  linarith

theorem moderate_cutoff_square {ell A : ℝ} (hell : 4096≤ell)
    (hA : A≤Real.exp ((17/10:ℝ)*ell)) : A<(cutoff ell (9/10):ℝ)^2 := by
  have hc := parameter_conditions hell (alpha:=9/10) (by norm_num) (le_refl _)
  have hX : (0:ℝ)<cutoff ell (9/10) := by exact_mod_cast (by omega : 0<cutoff ell (9/10))
  have hl := cutoff_log_lower hell (alpha:=9/10) (by norm_num) (le_refl _)
  have he : (17/10:ℝ)*ell<2*Real.log (cutoff ell (9/10):ℝ) := by linarith
  have hex := Real.exp_lt_exp.mpr he
  have hh : Real.exp (2*Real.log (cutoff ell (9/10):ℝ))=(cutoff ell (9/10):ℝ)^2 := by
    rw [show (2:ℝ)*Real.log (cutoff ell (9/10):ℝ)=Real.log (cutoff ell (9/10):ℝ)+Real.log (cutoff ell (9/10):ℝ) by ring,
      Real.exp_add,Real.exp_log hX,pow_two]
  rw [hh] at hex
  exact hA.trans_lt hex

end LonelyRunnerNew.RoughRational.Asymmetric
