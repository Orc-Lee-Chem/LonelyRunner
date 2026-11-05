import LonelyRunnerNew.KernelStepFunctions
import LonelyRunnerNew.ValuationDistribution
import LonelyRunnerNew.BootstrapInterval

noncomputable section
open scoped BigOperators
open MeasureTheory
namespace LonelyRunnerNew.KernelSteps

def natSupport (F : Finset ℕ) : Finset ℤ := F.image (fun i : ℕ => (i:ℤ))
def liftArray (F : Finset ℕ) (f : ℕ → ℝ) (i : ℤ) : ℝ :=
  if i ∈ natSupport F then (f i.toNat)^(3/4:ℝ) else 0
def probabilityStep (F : Finset ℕ) (f : ℕ → ℝ) : ℝ → ℝ :=
  step (natSupport F) (liftArray F f)

theorem nat_injective : Function.Injective (fun i : ℕ => (i:ℤ)) := by
  intro i j h
  dsimp only at h
  exact_mod_cast h

theorem liftArray_nat (F : Finset ℕ) (f : ℕ → ℝ) {i : ℕ} (hi : i ∈ F) :
    liftArray F f (i:ℤ) = (f i)^(3/4:ℝ) := by
  simp [liftArray, natSupport, Finset.mem_image_of_mem _ hi]

theorem liftArray_nonneg (F : Finset ℕ) (f : ℕ → ℝ) (hf : ∀ i ∈ F, 0 ≤ f i) (i : ℤ) :
    0 ≤ liftArray F f i := by
  by_cases hi : i ∈ natSupport F
  · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
    rw [liftArray_nat F f hj]
    exact Real.rpow_nonneg (hf j hj) _
  · simp [liftArray,hi]

theorem probabilityStep_nonneg (F : Finset ℕ) (f : ℕ → ℝ)
    (hf : ∀ i ∈ F, 0 ≤ f i) (u : ℝ) : 0 ≤ probabilityStep F f u := by
  unfold probabilityStep step
  apply Finset.sum_nonneg
  intro i hi
  by_cases hu : u ∈ cell i
  · simpa [hu] using liftArray_nonneg F f hf i
  · simp [hu]

theorem probabilityStep_norm (F : Finset ℕ) (f : ℕ → ℝ)
    (hf : ∀ i ∈ F, 0 ≤ f i) (hsum : (∑ i ∈ F, f i)=1) :
    (∫ u, |probabilityStep F f u|^(4/3:ℝ)) = 1 := by
  unfold probabilityStep
  rw [norm_power_integral]
  unfold natSupport
  rw [Finset.sum_image nat_injective.injOn]
  calc
    _ = ∑ i ∈ F, f i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [liftArray_nat F f hi, abs_of_nonneg (Real.rpow_nonneg (hf i hi) _),
        ← Real.rpow_mul (hf i hi)]
      norm_num
    _ = 1 := hsum

end LonelyRunnerNew.KernelSteps

namespace LonelyRunnerNew.TaggedState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

def kernelParameter (p : ℕ) : ℝ := Real.log (p:ℝ)/q

/-- Actual valuation kernel at an arbitrary real scale. No primality is needed
for this definition or for the cell identity below. -/
def scaleKernel (s : TaggedState Label n) (p : ℕ) (a : ℝ) : ℝ :=
  ∑ i ∈ s.valuationSupport p,∑ j ∈ s.valuationSupport p,
    Real.exp (-a)^((i:ℤ)-(j:ℤ)).natAbs*(s.alpha p i*s.beta p j)^(3/4:ℝ)

theorem kernelParameter_pos {p : ℕ} (hp : Nat.Prime p) : 0 < kernelParameter p :=
  div_pos (Real.log_pos (by exact_mod_cast hp.one_lt)) (by norm_num [q])

theorem prime_exp_kernel (p : ℕ) (hp : Nat.Prime p) (d : ℕ) :
    Real.exp (-kernelParameter p)^d=(p:ℝ)^(-(d:ℝ)/q) := by
  rw [← Real.exp_nat_mul, Real.rpow_def_of_pos (by exact_mod_cast hp.pos)]
  congr 1
  unfold kernelParameter
  ring

theorem actual_step_norms (s : TaggedState Label n) (p : ℕ) :
    (∫ u, |KernelSteps.probabilityStep (s.valuationSupport p) (s.alpha p) u|^(4/3:ℝ))=1 ∧
    (∫ u, |KernelSteps.probabilityStep (s.valuationSupport p) (s.beta p) u|^(4/3:ℝ))=1 :=
  ⟨KernelSteps.probabilityStep_norm _ _ (fun i _ => s.alpha_nonneg p i) (s.alpha_sum_common_support p),
    KernelSteps.probabilityStep_norm _ _ (fun i _ => s.beta_nonneg p i) (s.beta_sum_common_support p)⟩

theorem actual_cell_integral_identity_scale (s : TaggedState Label n) (p : ℕ)
    (a : ℝ) (ha : 0 < a) :
    (∫ u, KernelSteps.probabilityStep (s.valuationSupport p) (s.alpha p) u*
      (∫ v, KernelSteps.probabilityStep (s.valuationSupport p) (s.beta p) v*
        Real.exp (-a*|u-v|))) =
      KernelCells.A a*s.scaleKernel p a+
        (KernelCells.D a-KernelCells.A a)*
          (∑ i ∈ s.valuationSupport p,(s.alpha p i*s.beta p i)^(3/4:ℝ)) := by
  unfold KernelSteps.probabilityStep
  rw [KernelSteps.bilinear_cell_identity,
    KernelCells.bilinear_cell_identity _ ha]
  have hK : (∑ i ∈ KernelSteps.natSupport (s.valuationSupport p),
      ∑ j ∈ KernelSteps.natSupport (s.valuationSupport p),
        Real.exp (-a)^(i-j).natAbs*
          KernelSteps.liftArray (s.valuationSupport p) (s.alpha p) i*
          KernelSteps.liftArray (s.valuationSupport p) (s.beta p) j) = s.scaleKernel p a := by
    unfold KernelSteps.natSupport
    rw [Finset.sum_image KernelSteps.nat_injective.injOn]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_image KernelSteps.nat_injective.injOn]
    apply Finset.sum_congr rfl
    intro j hj
    rw [KernelSteps.liftArray_nat _ _ hi, KernelSteps.liftArray_nat _ _ hj,
      Real.mul_rpow (s.alpha_nonneg p i) (s.beta_nonneg p j)]
    ring
  have hD : (∑ i ∈ KernelSteps.natSupport (s.valuationSupport p),
      KernelSteps.liftArray (s.valuationSupport p) (s.alpha p) i*
        KernelSteps.liftArray (s.valuationSupport p) (s.beta p) i) =
        ∑ i ∈ s.valuationSupport p,(s.alpha p i*s.beta p i)^(3/4:ℝ) := by
    unfold KernelSteps.natSupport
    rw [Finset.sum_image KernelSteps.nat_injective.injOn]
    apply Finset.sum_congr rfl
    intro i hi
    rw [KernelSteps.liftArray_nat _ _ hi, KernelSteps.liftArray_nat _ _ hi,
      Real.mul_rpow (s.alpha_nonneg p i) (s.beta_nonneg p i)]
  rw [hK,hD]

theorem scaleKernel_prime (s : TaggedState Label n) (p : ℕ) (hp : Nat.Prime p) :
    s.scaleKernel p (kernelParameter p)=s.valuationKernel p := by
  unfold scaleKernel valuationKernel
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [prime_exp_kernel p hp]

/-- Preserved prime-scale API, now obtained from the arbitrary-scale identity. -/
theorem actual_cell_integral_identity (s : TaggedState Label n) (p : ℕ) (hp : Nat.Prime p) :
    (∫ u, KernelSteps.probabilityStep (s.valuationSupport p) (s.alpha p) u*
      (∫ v, KernelSteps.probabilityStep (s.valuationSupport p) (s.beta p) v*
        Real.exp (-kernelParameter p*|u-v|))) =
      KernelCells.A (kernelParameter p)*s.valuationKernel p+
        (KernelCells.D (kernelParameter p)-KernelCells.A (kernelParameter p))*
          (∑ i ∈ s.valuationSupport p,(s.alpha p i*s.beta p i)^(3/4:ℝ)) := by
  simpa only [s.scaleKernel_prime p hp] using
    s.actual_cell_integral_identity_scale p (kernelParameter p) (kernelParameter_pos hp)

end LonelyRunnerNew.TaggedState
