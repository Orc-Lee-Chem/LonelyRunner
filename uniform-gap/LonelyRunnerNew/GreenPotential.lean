import LonelyRunnerNew.GreenEnergy
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace LonelyRunnerNew.GreenPotential

def kernel (a t : ℝ) : ℝ := Real.exp (-a*|t|)
def primitive (a t : ℝ) : ℝ := ∫ r in (0:ℝ)..t,kernel a r
def U (a : ℝ) (F : Finset ℤ) (f : ℤ → ℝ) (x : ℝ) : ℝ :=
  ∑ i ∈ F,f i*((primitive a (x-i)-primitive a (x-((i:ℝ)+1)))/(2*a))
def V (a : ℝ) (F : Finset ℤ) (f : ℤ → ℝ) (x : ℝ) : ℝ :=
  ∑ i ∈ F,f i*((kernel a (x-i)-kernel a (x-((i:ℝ)+1)))/(2*a))

theorem kernel_continuous (a : ℝ) : Continuous (kernel a) := by unfold kernel; fun_prop

theorem primitive_deriv (a t : ℝ) : HasDerivAt (primitive a) (kernel a t) t :=
  intervalIntegral.integral_hasDerivAt_right ((kernel_continuous a).intervalIntegrable _ _)
    (kernel_continuous a).aestronglyMeasurable.stronglyMeasurableAtFilter (kernel_continuous a).continuousAt

theorem cell_primitive_identity (a x : ℝ) (i : ℤ) :
    (∫ y in KernelSteps.cell i,Real.exp (-a*|x-y|)) =
      primitive a (x-i)-primitive a (x-((i:ℝ)+1)) := by
  unfold KernelSteps.cell
  rw [integral_Ico_eq_integral_Ioc,← intervalIntegral.integral_of_le (by linarith : (i:ℝ)≤(i:ℝ)+1)]
  change (∫ y in (i:ℝ)..(i:ℝ)+1,kernel a (x-y)) = _
  rw [intervalIntegral.integral_comp_sub_left]
  have h := intervalIntegral.integral_add_adjacent_intervals
    ((kernel_continuous a).intervalIntegrable (μ := volume) 0 (x-((i:ℝ)+1)))
    ((kernel_continuous a).intervalIntegrable (μ := volume) (x-((i:ℝ)+1)) (x-i))
  dsimp [primitive]
  linarith

theorem U_eq_green (a : ℝ) (F : Finset ℤ) (f : ℤ → ℝ) (x : ℝ) :
    U a F f x=KernelSteps.potential a F f x/(2*a) := by
  rw [KernelSteps.potential_eq_sum,Finset.sum_div]
  unfold U
  apply Finset.sum_congr rfl
  intro i hi
  rw [cell_primitive_identity]
  ring

theorem U_deriv (a : ℝ) (F : Finset ℤ) (f : ℤ → ℝ) (x : ℝ) :
    HasDerivAt (U a F f) (V a F f x) x := by
  apply HasDerivAt.fun_sum
  intro i hi
  have hr := (primitive_deriv a (x-i)).comp x ((hasDerivAt_id x).sub_const (i:ℝ))
  have hl := (primitive_deriv a (x-((i:ℝ)+1))).comp x ((hasDerivAt_id x).sub_const ((i:ℝ)+1))
  convert (((hr.sub hl).div_const (2*a)).const_mul (f i)) using 1 <;> (try simp only [mul_one]) <;> rfl

theorem U_continuous (a : ℝ) (F : Finset ℤ) (f : ℤ → ℝ) : Continuous (U a F f) :=
  continuous_iff_continuousAt.mpr (fun x => (U_deriv a F f x).continuousAt)

theorem V_continuous (a : ℝ) (F : Finset ℤ) (f : ℤ → ℝ) : Continuous (V a F f) := by
  unfold V kernel
  fun_prop

theorem step_nonneg (F : Finset ℤ) (f : ℤ → ℝ) (hf : ∀ i ∈ F,0≤f i) (x : ℝ) :
    0≤KernelSteps.step F f x := by
  unfold KernelSteps.step
  apply Finset.sum_nonneg
  intro i hi
  by_cases hx : x ∈ KernelSteps.cell i <;> simp [hx,hf i hi]

theorem U_nonneg {a : ℝ} (ha : 0<a) (F : Finset ℤ) (f : ℤ → ℝ) (hf : ∀ i ∈ F,0≤f i) (x : ℝ) :
    0≤U a F f x := by
  rw [U_eq_green]
  apply div_nonneg _ (by positivity)
  exact integral_nonneg (fun y => mul_nonneg (step_nonneg F f hf y) (Real.exp_pos _).le)

theorem cell_positive (a x : ℝ) (i : ℤ) :
    0<(∫ y in KernelSteps.cell i,Real.exp (-a*|x-y|)) := by
  unfold KernelSteps.cell
  rw [integral_Ico_eq_integral_Ioc,← intervalIntegral.integral_of_le (by linarith : (i:ℝ)≤(i:ℝ)+1)]
  apply intervalIntegral.integral_pos (by linarith : (i:ℝ)<(i:ℝ)+1) (by fun_prop)
    (fun y _ => (Real.exp_pos _).le)
  exact ⟨(i:ℝ),⟨le_rfl,by linarith⟩,Real.exp_pos _⟩

theorem U_pos {a : ℝ} (ha : 0<a) (F : Finset ℤ) (f : ℤ → ℝ)
    (hf : ∀ i ∈ F,0≤f i) (hne : ∃ i ∈ F,0<f i) (x : ℝ) : 0<U a F f x := by
  rw [U_eq_green]
  apply div_pos _ (by positivity)
  rw [KernelSteps.potential_eq_sum]
  obtain ⟨i,hi,hfi⟩ := hne
  apply (mul_pos hfi (cell_positive a x i)).trans_le
  exact Finset.single_le_sum (fun j hj => mul_nonneg (hf j hj) (cell_positive a x j).le) hi

end LonelyRunnerNew.GreenPotential
