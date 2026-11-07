import LonelyRunnerNew.KernelInputProved
import LonelyRunnerNew.FrozenRootRows
import Mathlib.Tactic.GCongr

noncomputable section
open scoped BigOperators
namespace LonelyRunnerNew.Certificate

def logLowerQ (y : ℚ) (m : ℕ) : ℚ :=
  2*∑ k∈Finset.range m,((y-1)/(y+1))^(2*k+1)/((2*k+1:ℕ):ℚ)
def logUpperQ (y : ℚ) (m : ℕ) : ℚ :=
  logLowerQ y m+2*((y-1)/(y+1))^(2*m+1)/(1-((y-1)/(y+1))^2)

theorem cast_logLowerQ (y : ℚ) (m : ℕ) :
    (logLowerQ y m:ℝ)=RationalAnalysis.logSeriesLower (y:ℝ) m := by
  unfold logLowerQ RationalAnalysis.logSeriesLower
  push_cast
  rfl
theorem cast_logUpperQ (y : ℚ) (m : ℕ) :
    (logUpperQ y m:ℝ)=RationalAnalysis.logSeriesUpper (y:ℝ) m := by
  unfold logUpperQ RationalAnalysis.logSeriesUpper
  push_cast
  rw [cast_logLowerQ]

theorem rational_log_enclosure (y : ℚ) (hy : 1≤y) (m : ℕ) :
    (logLowerQ y m:ℝ)≤Real.log (y:ℝ) ∧ Real.log (y:ℝ)≤(logUpperQ y m:ℝ) := by
  rw [cast_logLowerQ,cast_logUpperQ]
  exact RationalAnalysis.log_series_enclosure (by exact_mod_cast hy) m

def sqrt3Upper : ℚ := 1732050807568877293527447/1000000000000000000000000
theorem sqrt_three_upper : Real.sqrt 3≤(sqrt3Upper:ℝ) := by
  apply Real.sqrt_le_iff.mpr
  norm_num [sqrt3Upper]

structure AnalyticWitness where
  lo : ℚ
  hi : ℚ
  sqrtUpper : ℚ
  shift : ℕ
  deriving Inhabited,DecidableEq

def rowNormUpper (r : PrimeRow) (w : AnalyticWitness) : ℚ :=
  (sqrt3Upper/2)*r.lambdaUpper*w.hi*w.sqrtUpper/(1-r.lambdaUpper)^2+
    1-2*r.lambdaUpper*(w.lo-1+r.lambdaUpper)/(1-r.lambdaUpper)^2

def AnalyticWitness.Valid (r : PrimeRow) (w : AnalyticWitness) : Prop :=
  0≤w.lo ∧ 0≤w.hi ∧ 0≤w.sqrtUpper ∧
  w.lo≤logLowerQ (1/r.lambdaUpper) 24 ∧ logUpperQ (1/r.lambdaUpper) 24≤w.hi ∧
  w.hi≤w.sqrtUpper^2 ∧ rowNormUpper r w≤r.normUpper ∧ 0<r.tau ∧
  1≤r.normUpper ∧ 1≤r.normUpper/(2:ℚ)^w.shift ∧
  (w.shift:ℚ)*logUpperQ 2 24+logUpperQ (r.normUpper/(2:ℚ)^w.shift) 24≤r.tau*r.edgeUpper

instance (r : PrimeRow) (w : AnalyticWitness) : Decidable (w.Valid r) := by
  unfold AnalyticWitness.Valid; infer_instance

theorem AnalyticWitness.kernel_bound (r : PrimeRow) (w : AnalyticWitness)
    (hl0 : 0<r.lambdaUpper) (hl1 : r.lambdaUpper<1) (hw : w.Valid r) :
    kernelN (r.lambdaUpper:ℝ)≤(r.normUpper:ℝ) := by
  rcases hw with ⟨hlo0,hhi0,hs0,hlo,hhi,hsq,hcert,_⟩
  have hlR : (0:ℝ)<r.lambdaUpper := by exact_mod_cast hl0
  have hlR1 : (r.lambdaUpper:ℝ)<1 := by exact_mod_cast hl1
  have hrecip : (1:ℚ)≤1/r.lambdaUpper := (le_div_iff₀ hl0).mpr (by linarith)
  have he := rational_log_enclosure (1/r.lambdaUpper) hrecip 24
  have hlog : Real.log ((1/r.lambdaUpper:ℚ):ℝ) = -Real.log (r.lambdaUpper:ℝ) := by
    push_cast
    rw [one_div,Real.log_inv]
  rw [hlog] at he
  have hL : (w.lo:ℝ)≤-Real.log (r.lambdaUpper:ℝ) := (by exact_mod_cast hlo : (w.lo:ℝ)≤logLowerQ (1/r.lambdaUpper) 24).trans he.1
  have hH : -Real.log (r.lambdaUpper:ℝ)≤(w.hi:ℝ) := he.2.trans (by exact_mod_cast hhi)
  have hroot : Real.sqrt (-Real.log (r.lambdaUpper:ℝ))≤(w.sqrtUpper:ℝ) := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by exact_mod_cast hs0,hH.trans (by exact_mod_cast hsq)⟩
  have ha : 0 < -Real.log (r.lambdaUpper:ℝ) := neg_pos.mpr (Real.log_neg hlR hlR1)
  have har : (-Real.log (r.lambdaUpper:ℝ))^(3/2:ℝ)=
      (-Real.log (r.lambdaUpper:ℝ))*Real.sqrt (-Real.log (r.lambdaUpper:ℝ)) := by
    rw [show (3/2:ℝ)=1+1/2 by norm_num,Real.rpow_one_add' ha.le (by norm_num),← Real.sqrt_eq_rpow]
  have hnum : (Real.sqrt 3/2)*(r.lambdaUpper:ℝ)*(-Real.log (r.lambdaUpper:ℝ))*Real.sqrt (-Real.log (r.lambdaUpper:ℝ)) ≤
      ((sqrt3Upper:ℝ)/2)*(r.lambdaUpper:ℝ)*(w.hi:ℝ)*(w.sqrtUpper:ℝ) := by
    have hs3 : (0:ℝ)≤sqrt3Upper := by norm_num [sqrt3Upper]
    have hHiR : (0:ℝ)≤w.hi := by exact_mod_cast hhi0
    gcongr <;> first | exact sqrt_three_upper | exact hH | exact hroot | positivity
  have hC := div_le_div_of_nonneg_right hnum (sq_nonneg (1-(r.lambdaUpper:ℝ)))
  have hneg := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (show (w.lo:ℝ)-1+(r.lambdaUpper:ℝ)≤-Real.log (r.lambdaUpper:ℝ)-1+(r.lambdaUpper:ℝ) by linarith)
      (by positivity : (0:ℝ)≤2*(r.lambdaUpper:ℝ))) (sq_nonneg (1-(r.lambdaUpper:ℝ)))
  have hq : (rowNormUpper r w:ℝ)≤(r.normUpper:ℝ) := by exact_mod_cast hcert
  unfold rowNormUpper at hq
  push_cast at hq
  unfold kernelN
  change (Real.sqrt 3/2)*(r.lambdaUpper:ℝ)*(-Real.log (r.lambdaUpper:ℝ))^(3/2:ℝ)/(1-(r.lambdaUpper:ℝ))^2+1-
    2*(r.lambdaUpper:ℝ)*(-Real.log (r.lambdaUpper:ℝ)-1+(r.lambdaUpper:ℝ))/(1-(r.lambdaUpper:ℝ))^2≤(r.normUpper:ℝ)
  rw [har,← mul_assoc]
  linarith only [hC,hneg,hq]

theorem AnalyticWitness.edge_bound (r : PrimeRow) (w : AnalyticWitness) (hw : w.Valid r) :
    Real.log (r.normUpper:ℝ)/(r.tau:ℝ)≤(r.edgeUpper:ℝ) := by
  rcases hw with ⟨_,_,_,_,_,_,_,ht,hN,hred,hcert⟩
  have hu := (rational_log_enclosure (r.normUpper/(2:ℚ)^w.shift) hred 24).2
  have htwo := (rational_log_enclosure 2 (by norm_num) 24).2
  have hp : (0:ℝ)<((r.normUpper/(2:ℚ)^w.shift:ℚ):ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0:ℚ)<1) hred)
  have he := RationalAnalysis.log_two_pow_mul hp w.shift
  have heq : (2:ℝ)^w.shift*((r.normUpper/(2:ℚ)^w.shift:ℚ):ℝ)=(r.normUpper:ℝ) := by
    push_cast
    field_simp
  rw [heq] at he
  have hm := mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg w.shift : (0:ℝ)≤w.shift)
  norm_num only [Rat.cast_ofNat] at hm
  have hc : (w.shift:ℝ)*(logUpperQ 2 24:ℝ)+(logUpperQ (r.normUpper/(2:ℚ)^w.shift) 24:ℝ)≤(r.tau:ℝ)*(r.edgeUpper:ℝ) := by exact_mod_cast hcert
  apply (div_le_iff₀ (show (0:ℝ)<r.tau by exact_mod_cast ht)).mpr
  linarith

end LonelyRunnerNew.Certificate
