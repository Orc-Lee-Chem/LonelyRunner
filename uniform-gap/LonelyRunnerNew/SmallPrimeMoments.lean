import LonelyRunnerNew.SmallPrimeAnalytic
import LonelyRunnerNew.UniversalDescent
import LonelyRunnerNew.ValuationKernelSteps
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen

noncomputable section
open scoped BigOperators
namespace LonelyRunnerNew

theorem finite_mean_le_log_moment {ι : Type*} (F : Finset ι) (w X : ι → ℝ)
    (hw : ∀ i∈F,0≤w i) (hs : (∑ i∈F,w i)=1) {tau N : ℝ} (ht : 0<tau)
    (hN : (∑ i∈F,w i*Real.exp (tau*X i))≤N) :
    (∑ i∈F,w i*X i)≤Real.log N/tau := by
  have hj := convexOn_exp.map_sum_le hw hs (fun _ _ => Set.mem_univ _)
    (p := fun i => tau*X i)
  simp only [smul_eq_mul] at hj
  have he : (∑ i∈F,w i*(tau*X i))=tau*(∑ i∈F,w i*X i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he] at hj
  have hexp := hj.trans hN
  have hn : 0<N := (Real.exp_pos _).trans_le hexp
  have hh := Real.log_le_log (Real.exp_pos _) hexp
  rw [Real.log_exp] at hh
  exact (le_div_iff₀ ht).mpr (by nlinarith only [hh])

namespace KernelProbability
theorem nat_kernel_bound {lam : ℝ} (hl0 : 0<lam) (hl1 : lam<1)
    (F : Finset ℕ) (f g : ℕ → ℝ) (hf : ∀ i∈F,0≤f i) (hg : ∀ i∈F,0≤g i)
    (hsf : (∑ i∈F,f i)=1) (hsg : (∑ i∈F,g i)=1) :
    (∑ i∈F,∑ j∈F,lam^((i:ℤ)-(j:ℤ)).natAbs*(f i*g j)^(3/4:ℝ))≤kernelN lam := by
  have hfn : (∑ i∈KernelSteps.natSupport F,f i.toNat)=1 := by
    unfold KernelSteps.natSupport
    rw [Finset.sum_image KernelSteps.nat_injective.injOn]
    simpa only [Int.toNat_natCast] using hsf
  have hgn : (∑ i∈KernelSteps.natSupport F,g i.toNat)=1 := by
    unfold KernelSteps.natSupport
    rw [Finset.sum_image KernelSteps.nat_injective.injOn]
    simpa only [Int.toNat_natCast] using hsg
  have hfpos : ∀ i∈KernelSteps.natSupport F,0≤f i.toNat := by
    intro i hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
    simpa only [Int.toNat_natCast] using hf j hj
  have hgpos : ∀ i∈KernelSteps.natSupport F,0≤g i.toNat := by
    intro i hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
    simpa only [Int.toNat_natCast] using hg j hj
  have hk := kernelInput_proved lam hl0 hl1 (KernelSteps.natSupport F) (KernelSteps.natSupport F)
    (fun i => f i.toNat) (fun j => g j.toNat) hfpos hgpos hfn hgn
  change (∑ i∈KernelSteps.natSupport F,∑ j∈KernelSteps.natSupport F,
    lam^(i-j).natAbs*(f i.toNat)^(3/4:ℝ)*(g j.toNat)^(3/4:ℝ))≤_ at hk
  simp_rw [KernelSteps.natSupport,Finset.sum_image KernelSteps.nat_injective.injOn] at hk
  simp only [Int.toNat_natCast] at hk
  have he : (∑ i∈F,∑ j∈F,lam^((i:ℤ)-(j:ℤ)).natAbs*(f i*g j)^(3/4:ℝ)) =
      ∑ i∈F,∑ j∈F,lam^((i:ℤ)-(j:ℤ)).natAbs*(f i)^(3/4:ℝ)*(g j)^(3/4:ℝ) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [Real.mul_rpow (hf i hi) (hg j hj),mul_assoc]
  rw [he]
  exact hk
end KernelProbability

namespace TaggedState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

/-- Includes log p: this is the logarithmic distance, not the bare valuation gap. -/
def primeLogDistance (p : ℕ) (ij : ℕ × ℕ) : ℝ :=
  (((ij.1:ℤ)-(ij.2:ℤ)).natAbs:ℝ)*Real.log (p:ℝ)
def primeMeanLogDistance (s : TaggedState Label n) (p : ℕ) : ℝ :=
  ∑ ij∈(s.valuationSupport p).product (s.valuationSupport p),s.mu p ij*primeLogDistance p ij
def primeExpMoment (s : TaggedState Label n) (p : ℕ) (tau : ℝ) : ℝ :=
  ∑ ij∈(s.valuationSupport p).product (s.valuationSupport p),s.mu p ij*Real.exp (tau*primeLogDistance p ij)

theorem shifted_kernel_factor {p : ℕ} (hp : Nat.Prime p) (tau : ℝ) (d : ℕ) :
    (p:ℝ)^(-(d:ℝ)/q)*Real.exp (tau*((d:ℝ)*Real.log (p:ℝ))) =
      ((p:ℝ)^(-1/q+tau))^d := by
  rw [Real.rpow_def_of_pos (by exact_mod_cast hp.pos),Real.rpow_def_of_pos (by exact_mod_cast hp.pos),← Real.exp_add,← Real.exp_nat_mul]
  congr 1
  ring

/-- Generic layer estimate: callers below supply their OWN proved L05. -/
theorem exp_moment_of_layers (s : TaggedState Label n) (p : ℕ) (hp : Nat.Prime p)
    (hL : ∀ i j,s.mu p (i,j)≤(p:ℝ)^(-(((i:ℤ)-(j:ℤ)).natAbs:ℝ)/q)*(s.alpha p i*s.beta p j)^(3/4:ℝ))
    {tau lam : ℝ} (hl0 : 0<lam) (hl1 : lam<1) (hshift : (p:ℝ)^(-1/q+tau)≤lam) :
    s.primeExpMoment p tau≤kernelN lam := by
  have hpoint (i j : ℕ) : s.mu p (i,j)*Real.exp (tau*primeLogDistance p (i,j)) ≤
      lam^((i:ℤ)-(j:ℤ)).natAbs*(s.alpha p i*s.beta p j)^(3/4:ℝ) := by
    have h := mul_le_mul_of_nonneg_right (hL i j) (Real.exp_pos (tau*primeLogDistance p (i,j))).le
    have he : ((p:ℝ)^(-(((i:ℤ)-(j:ℤ)).natAbs:ℝ)/q)*(s.alpha p i*s.beta p j)^(3/4:ℝ))*
        Real.exp (tau*primeLogDistance p (i,j)) =
        ((p:ℝ)^(-1/q+tau))^((i:ℤ)-(j:ℤ)).natAbs*(s.alpha p i*s.beta p j)^(3/4:ℝ) := by
      rw [mul_right_comm]
      rw [primeLogDistance,shifted_kernel_factor hp]
    rw [he] at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Real.rpow_nonneg (by exact_mod_cast hp.pos.le) _) hshift _)
      (Real.rpow_nonneg (mul_nonneg (s.alpha_nonneg p i) (s.beta_nonneg p j)) _))
  have hsum : s.primeExpMoment p tau≤ ∑ i∈s.valuationSupport p,∑ j∈s.valuationSupport p,
      lam^((i:ℤ)-(j:ℤ)).natAbs*(s.alpha p i*s.beta p j)^(3/4:ℝ) := by
    unfold primeExpMoment
    rw [Finset.product_eq_sprod,Finset.sum_product]
    exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hpoint i j))
  exact hsum.trans (KernelProbability.nat_kernel_bound hl0 hl1 (s.valuationSupport p) _ _
    (fun i _ => s.alpha_nonneg p i) (fun j _ => s.beta_nonneg p j)
    (s.alpha_sum_common_support p) (s.beta_sum_common_support p))

theorem mean_log_distance_of_moment (s : TaggedState Label n) (hM : 0<s.edgeMass)
    (p : ℕ) {tau N : ℝ} (ht : 0<tau) (hm : s.primeExpMoment p tau≤N) :
    s.primeMeanLogDistance p≤Real.log N/tau :=
  finite_mean_le_log_moment _ _ _ (fun ij _ => s.mu_nonneg hM p ij) (s.mu_sum_common_support hM p) ht hm

end TaggedState
end LonelyRunnerNew
