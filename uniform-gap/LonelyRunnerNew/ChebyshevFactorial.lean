import LonelyRunnerNew.ChebyshevThirty
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew.RCThirty

def mainTerm (x : ℝ) : ℝ := x*Real.log x-x
def F (x : ℝ) : ℝ := Real.log ((⌊x⌋₊).factorial:ℝ)
def constantC : ℝ := Real.log 2/2+Real.log 3/3+Real.log 5/5-Real.log 30/30

theorem log_factorial_sum (n : ℕ) : Real.log (n.factorial:ℝ)=
    ∑i∈Finset.range n,Real.log (i+1:ℝ) := by
  rw [Nat.factorial_eq_prod_range_add_one,Nat.cast_prod,Real.log_prod]
  · simp only [Nat.cast_add,Nat.cast_one]
  · intro i hi;positivity

theorem factorial_integral_bounds (n : ℕ) :
    mainTerm (n:ℝ)≤Real.log (n.factorial:ℝ) ∧
      Real.log (n.factorial:ℝ)≤mainTerm ((n:ℝ)+1)+1 := by
  have hmono0 : MonotoneOn Real.log (Set.Ioc (0:ℝ) (0+(n:ℝ))) := by
    intro x hx y hy hxy
    exact Real.log_le_log hx.1 hxy
  have hint : MeasureTheory.IntegrableOn Real.log (Set.Icc (0:ℝ) (0+(n:ℝ))) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by positivity)).mp intervalIntegral.intervalIntegrable_log'
  have hlo := hmono0.integral_le_sum_of_integrableOn hint
  have hmono1 : MonotoneOn Real.log (Set.Icc (1:ℝ) (1+(n:ℝ))) := by
    intro x hx y hy hxy
    exact Real.log_le_log (by linarith [hx.1]) hxy
  have hhi := hmono1.sum_le_integral
  rw [integral_log] at hlo hhi
  have hs1 : (∑i∈Finset.range n,Real.log (1+(i:ℝ)))=Real.log (n.factorial:ℝ) := by
    rw [log_factorial_sum]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1;ring
  simp only [zero_add,zero_mul,sub_zero,add_zero,Nat.cast_add,Nat.cast_one] at hlo
  rw [←log_factorial_sum] at hlo
  rw [hs1] at hhi
  simp only [Real.log_one,mul_zero,sub_zero] at hhi
  constructor
  · exact hlo
  · simpa only [mainTerm,add_comm (1:ℝ) (n:ℝ)] using hhi

theorem main_difference {a b : ℝ} (ha : 0<a) (hb : 0<b) :
    mainTerm b-mainTerm a≤(b-a)*Real.log b := by
  have h := Real.log_le_sub_one_of_pos (div_pos hb ha)
  have hm := mul_le_mul_of_nonneg_left h ha.le
  rw [Real.log_div hb.ne' ha.ne'] at hm
  have he : a*(b/a-1)=b-a := by field_simp
  rw [he] at hm
  unfold mainTerm
  nlinarith

theorem factorial_main_error {x : ℝ} (hx : 1≤x) :
    |F x-mainTerm x|≤1+Real.log (x+1) := by
  let n := ⌊x⌋₊
  have hn1 : 1≤n := (Nat.le_floor_iff (by linarith)).mpr (by simpa using hx)
  have hnpos : (0:ℝ)<n := by exact_mod_cast hn1
  have hnle : (n:ℝ)≤x := Nat.floor_le (by linarith)
  have hnlt : x<(n:ℝ)+1 := Nat.lt_floor_add_one x
  have hlogx : 0≤Real.log x := Real.log_nonneg hx
  have hlogn : 0≤Real.log ((n:ℝ)+1) := Real.log_nonneg (by linarith)
  have hb := factorial_integral_bounds n
  have hlo := main_difference hnpos (by linarith : 0<x)
  have hhi := main_difference (by linarith : 0<x) (by linarith : (0:ℝ)<n+1)
  have hlog : Real.log x≤Real.log (x+1) := Real.log_le_log (by linarith) (by linarith)
  have hlog' : Real.log ((n:ℝ)+1)≤Real.log (x+1) := Real.log_le_log (by linarith) (by linarith)
  have h1 : (x-(n:ℝ))*Real.log x≤Real.log x := by
    nlinarith [mul_le_mul_of_nonneg_right (by linarith : x-(n:ℝ)≤1) hlogx]
  have h2 : ((n:ℝ)+1-x)*Real.log ((n:ℝ)+1)≤Real.log ((n:ℝ)+1) := by
    nlinarith [mul_le_mul_of_nonneg_right (by linarith : (n:ℝ)+1-x≤1) hlogn]
  apply abs_le.mpr
  change -(1+Real.log (x+1))≤Real.log (n.factorial:ℝ)-mainTerm x ∧
    Real.log (n.factorial:ℝ)-mainTerm x≤1+Real.log (x+1)
  constructor <;> linarith

theorem J_main_identity {x : ℝ} (hx : 0<x) :
    mainTerm x-mainTerm (x/2)-mainTerm (x/3)-mainTerm (x/5)+mainTerm (x/30)=constantC*x := by
  unfold mainTerm constantC
  rw [Real.log_div hx.ne' (by norm_num : (2:ℝ)≠0),
    Real.log_div hx.ne' (by norm_num : (3:ℝ)≠0),
    Real.log_div hx.ne' (by norm_num : (5:ℝ)≠0),
    Real.log_div hx.ne' (by norm_num : (30:ℝ)≠0)]
  ring

theorem J_main_error {x : ℝ} (hx : 30≤x) : |J x-constantC*x|≤5+10*Real.log x := by
  have he (y : ℝ) (hy : 1≤y) (hyx : y≤x) : |F y-mainTerm y|≤1+2*Real.log x := by
    have h := factorial_main_error hy
    have hl : Real.log (y+1)≤2*Real.log x := by
      have hi : y+1≤x^2 := by nlinarith
      have hh := Real.log_le_log (by linarith : 0<y+1) hi
      rw [Real.log_pow] at hh
      norm_num at hh
      exact hh
    linarith
  have h0 := abs_le.mp (he x (by linarith) (le_refl _))
  have h2 := abs_le.mp (he (x/2) (by linarith) (by linarith))
  have h3 := abs_le.mp (he (x/3) (by linarith) (by linarith))
  have h5 := abs_le.mp (he (x/5) (by linarith) (by linarith))
  have h30 := abs_le.mp (he (x/30) (by linarith) (by linarith))
  have hid := J_main_identity (by linarith : 0<x)
  apply abs_le.mpr
  change -(5+10*Real.log x)≤F x-F (x/2)-F (x/3)-F (x/5)+F (x/30)-constantC*x ∧
    F x-F (x/2)-F (x/3)-F (x/5)+F (x/30)-constantC*x≤5+10*Real.log x
  constructor <;> linarith

end LonelyRunnerNew.RCThirty
