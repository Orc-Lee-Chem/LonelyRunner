import LonelyRunnerNew.PeelingArithmetic
import Mathlib.Data.Nat.Dist

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew.SmallPrimePeeling

def smallDistance (x y : ℕ) : ℝ :=
  ∑ p∈Certificate.smallPrimes,|(padicValNat p x:ℝ)-(padicValNat p y:ℝ)| * Real.log (p:ℝ)
def distanceProduct (x y : ℕ) : ℕ :=
  ∏ p∈Certificate.smallPrimes,p^(Nat.dist (padicValNat p x) (padicValNat p y))

theorem exponent_balance (a b : ℕ) : 2*min a b+Nat.dist a b=a+b := by
  by_cases h : a≤b
  · rw [min_eq_left h,Nat.dist_eq_sub_of_le h];omega
  · have hh : b≤a := by omega
    rw [min_eq_right hh,Nat.dist_eq_sub_of_le_right hh];omega

theorem smooth_product_identity (x y : ℕ) :
    smoothPart x*smoothPart y=(Nat.gcd (smoothPart x) (smoothPart y))^2*distanceProduct x y := by
  rw [smooth_gcd_product,smoothPart_product x,smoothPart_product y]
  unfold distanceProduct
  rw [← Finset.prod_mul_distrib,← Finset.prod_pow,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  rw [← pow_add,← pow_mul,← pow_add]
  congr 1
  have h := exponent_balance (padicValNat p x) (padicValNat p y)
  omega

theorem abs_cast_sub_eq_dist (a b : ℕ) : |(a:ℝ)-(b:ℝ)|=(Nat.dist a b:ℝ) := by
  by_cases h : a≤b
  · rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast h)),Nat.dist_eq_sub_of_le h,Nat.cast_sub h]
    ring
  · have hh : b≤a := by omega
    rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hh)),Nat.dist_eq_sub_of_le_right hh,Nat.cast_sub hh]

theorem exp_smallDistance_product (x y : ℕ) : Real.exp (smallDistance x y)=(distanceProduct x y:ℝ) := by
  unfold smallDistance distanceProduct
  rw [Real.exp_sum]
  push_cast
  apply Finset.prod_congr rfl
  intro p hp
  rw [abs_cast_sub_eq_dist,Real.exp_nat_mul,Real.exp_log (by exact_mod_cast (Certificate.smallPrimes_mem.mp hp).1.pos)]

theorem exp_smallDistance_ratio (x y : ℕ) :
    Real.exp (smallDistance x y)=
      ((smoothPart x:ℝ)*(smoothPart y:ℝ))/(Nat.gcd (smoothPart x) (smoothPart y):ℝ)^2 := by
  have hg : (0:ℝ)<Nat.gcd (smoothPart x) (smoothPart y) := by
    exact_mod_cast Nat.gcd_pos_of_pos_left (smoothPart y) (smoothPart_pos x)
  apply (eq_div_iff (pow_ne_zero 2 hg.ne')).mpr
  rw [exp_smallDistance_product]
  have h : (smoothPart x:ℝ)*(smoothPart y:ℝ)=
      (Nat.gcd (smoothPart x) (smoothPart y):ℝ)^2*(distanceProduct x y:ℝ) := by
    exact_mod_cast smooth_product_identity x y
  nlinarith only [h]

end LonelyRunnerNew.SmallPrimePeeling
