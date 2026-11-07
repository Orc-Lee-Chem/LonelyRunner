import LonelyRunnerNew.GreenBilinear
import LonelyRunnerNew.ValuationKernelSteps

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LonelyRunnerNew.GreenPotential

theorem step_zero_of_coefficients (F : Finset ℤ) (f : ℤ → ℝ) (hf : ∀ i ∈ F,f i=0) :
    KernelSteps.step F f=(fun _ => 0) := by
  funext x
  unfold KernelSteps.step
  apply Finset.sum_eq_zero
  intro i hi
  simp [hf i hi]

theorem sharp_kernel_bound {a : ℝ} (ha : 0<a) (F G : Finset ℤ) (f g : ℤ → ℝ)
    (hf : ∀ i ∈ F,0≤f i) (hg : ∀ j ∈ G,0≤g j) :
    (∫ x,KernelSteps.step F f x*(∫ y,KernelSteps.step G g y*Real.exp (-a*|x-y|))) ≤
      (Real.sqrt 3/(2*Real.sqrt a))*N F f*N G g := by
  have hNf0 := N_nonneg F f
  have hNg0 := N_nonneg G g
  by_cases hfn : ∃ i ∈ F,0<f i
  · by_cases hgn : ∃ j ∈ G,0<g j
    · let B := mixedEnergy a F G f g
      let A := energyFactor a
      have hA : 0≤A := by dsimp [A,energyFactor]; positivity
      have hNf := N_nonneg F f
      have hNg := N_nonneg G g
      have hB0 : 0≤B := by
        rw [show B=mixedEnergy a F G f g from rfl,mixed_energy_identity ha F G f g hf hg]
        exact integral_nonneg (fun x => mul_nonneg (step_nonneg F f hf x) (U_nonneg ha G g hg x))
      have hprod := mul_le_mul (energy_upper ha F f hf hfn) (energy_upper ha G g hg hgn)
        (energy_nonneg a G g) (mul_nonneg hA (sq_nonneg (N F f)))
      have hBs : B^2≤(A*N F f*N G g)^2 := by
        apply (mixed_energy_sq_le ha F G f g hf hg).trans
        convert hprod using 1 <;> ring
      have hB : B≤A*N F f*N G g :=
        (pow_le_pow_iff_left₀ hB0 (by positivity) (by decide : (2:ℕ)≠0)).mp hBs
      have hJ : (∫ x,KernelSteps.step F f x*(∫ y,KernelSteps.step G g y*Real.exp (-a*|x-y|)))=2*a*B := by
        rw [show B=mixedEnergy a F G f g from rfl,mixed_energy_identity ha F G f g hf hg,← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with x
        rw [U_eq_green]
        change KernelSteps.step F f x*KernelSteps.potential a G g x=
          2*a*(KernelSteps.step F f x*(KernelSteps.potential a G g x/(2*a)))
        field_simp
      have har : a^(3/2:ℝ)=a*Real.sqrt a := by
        rw [show (3/2:ℝ)=1+1/2 by norm_num,Real.rpow_one_add' ha.le (by norm_num),← Real.sqrt_eq_rpow]
      have hcoef : 2*a*A=Real.sqrt 3/(2*Real.sqrt a) := by
        dsimp [A,energyFactor]
        rw [har]
        field_simp
        norm_num
      rw [hJ]
      calc
        _ ≤ 2*a*(A*N F f*N G g) := mul_le_mul_of_nonneg_left hB (by positivity)
        _ = _ := by rw [← mul_assoc,← mul_assoc,hcoef]
    · have hz : ∀ j ∈ G,g j=0 := by
        intro j hj
        have hle : g j≤0 := le_of_not_gt (fun h => hgn ⟨j,hj,h⟩)
        exact le_antisymm hle (hg j hj)
      rw [step_zero_of_coefficients G g hz]
      simp only [zero_mul,integral_zero,mul_zero]
      positivity
  · have hz : ∀ i ∈ F,f i=0 := by
      intro i hi
      have hle : f i≤0 := le_of_not_gt (fun h => hfn ⟨i,hi,h⟩)
      exact le_antisymm hle (hf i hi)
    rw [step_zero_of_coefficients F f hz]
    simp only [zero_mul,integral_zero]
    positivity

theorem sharp_cell_bound {a : ℝ} (ha : 0<a) (F : Finset ℤ) (f g : ℤ → ℝ)
    (hf : ∀ i ∈ F,0≤f i) (hg : ∀ j ∈ F,0≤g j) :
    (∑ i ∈ F,∑ j ∈ F,KernelCells.cellIntegral a ((i-j).natAbs:ℝ)*f i*g j) ≤
      (Real.sqrt 3/(2*Real.sqrt a))*N F f*N F g := by
  rw [← KernelSteps.bilinear_cell_identity]
  exact sharp_kernel_bound ha F F f g hf hg

theorem constant_eq {a : ℝ} (ha : 0<a) :
    Real.sqrt 3/(2*Real.sqrt a)=(Real.sqrt 3/2)*a^(-1/2:ℝ) := by
  rw [show (-1/2:ℝ)= -(1/2:ℝ) by norm_num,Real.rpow_neg ha.le,← Real.sqrt_eq_rpow]
  ring

theorem lifted_norm (F : Finset ℕ) (f : ℕ → ℝ) (hf : ∀ i ∈ F,0≤f i)
    (hs : (∑ i ∈ F,f i)=1) : N (KernelSteps.natSupport F) (KernelSteps.liftArray F f)=1 := by
  unfold N
  rw [← KernelSteps.norm_power_integral]
  change (∫ x,|KernelSteps.probabilityStep F f x|^(4/3:ℝ))^(3/4:ℝ)=1
  rw [KernelSteps.probabilityStep_norm F f hf hs]
  norm_num

theorem actual_probability_cell_bound {a : ℝ} (ha : 0<a) (F : Finset ℕ) (f g : ℕ → ℝ)
    (hf : ∀ i ∈ F,0≤f i) (hg : ∀ j ∈ F,0≤g j)
    (hsf : (∑ i ∈ F,f i)=1) (hsg : (∑ i ∈ F,g i)=1) :
    (∑ i ∈ KernelSteps.natSupport F,∑ j ∈ KernelSteps.natSupport F,
      KernelCells.cellIntegral a ((i-j).natAbs:ℝ)*KernelSteps.liftArray F f i*KernelSteps.liftArray F g j) ≤
      (Real.sqrt 3/2)*a^(-1/2:ℝ) := by
  have h := sharp_cell_bound ha (KernelSteps.natSupport F) _ _
    (fun i _ => KernelSteps.liftArray_nonneg F f hf i)
    (fun j _ => KernelSteps.liftArray_nonneg F g hg j)
  rw [lifted_norm F f hf hsf,lifted_norm F g hg hsg,mul_one,mul_one,constant_eq ha] at h
  exact h

end LonelyRunnerNew.GreenPotential
