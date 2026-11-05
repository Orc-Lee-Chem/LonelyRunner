import LonelyRunnerNew.GreenDecay
import Mathlib.Analysis.Calculus.Deriv.Abs

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace LonelyRunnerNew.GreenPotential

theorem exp_primitive {c : ℝ} (hc : c≠0) (x : ℝ) :
    (∫ t in (0:ℝ)..x,Real.exp (c*t))=(Real.exp (c*x)-1)/c := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => Real.exp (c*t)/c) (Real.exp (c*t)) t := by
    convert (((hasDerivAt_id t).const_mul c).exp.div_const c) using 1 <;>
      (try simp only [mul_one,id_eq]) <;> (try field_simp [hc]) <;> rfl
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    ((by fun_prop : Continuous (fun t : ℝ => Real.exp (c*t))).intervalIntegrable (μ := volume) 0 x)
  simpa only [mul_zero,Real.exp_zero,sub_div] using hh

theorem primitive_nonneg {a t : ℝ} (ha : 0<a) (ht : 0≤t) :
    primitive a t=(1-kernel a t)/a := by
  have he : primitive a t=∫ x in (0:ℝ)..t,Real.exp (-a*x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le ht] at hx
    simp only [kernel,abs_of_nonneg hx.1]
  rw [he,exp_primitive (neg_ne_zero.mpr ha.ne')]
  unfold kernel
  rw [abs_of_nonneg ht]
  ring

theorem primitive_nonpos {a t : ℝ} (ha : 0<a) (ht : t≤0) :
    primitive a t=(kernel a t-1)/a := by
  have he : primitive a t=∫ x in (0:ℝ)..t,Real.exp (a*x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_ge ht] at hx
    unfold kernel
    rw [abs_of_nonpos hx.2]
    congr 1
    ring
  rw [he,exp_primitive ha.ne']
  unfold kernel
  rw [abs_of_nonpos ht]
  congr 2
  ring

def kernelRight (a t : ℝ) : ℝ := if t<0 then a*kernel a t else -a*kernel a t

theorem kernel_right_deriv (a t : ℝ) :
    HasDerivWithinAt (kernel a) (kernelRight a t) (Set.Ici t) t := by
  by_cases ht : t<0
  · have hh := (((hasDerivAt_abs_neg ht).const_mul (-a)).exp).hasDerivWithinAt (s := Set.Ici t)
    change HasDerivWithinAt (kernel a) (kernel a t*((-a)*(-1))) (Set.Ici t) t at hh
    simpa [kernelRight,ht,mul_comm] using hh
  · have ht0 : 0≤t := le_of_not_gt ht
    have hh := (((hasDerivAt_id t).const_mul (-a)).exp).hasDerivWithinAt (s := Set.Ici t)
    simp only [id_eq,mul_one] at hh
    have hhc := hh.congr_of_mem (f₁ := kernel a)
      (fun x hx => by simp [kernel,abs_of_nonneg (ht0.trans hx)]) Set.self_mem_Ici
    convert hhc using 1
    unfold kernelRight
    rw [if_neg ht]
    simp only [kernel,abs_of_nonneg ht0]
    ring

theorem kernelRight_primitive {a : ℝ} (ha : 0<a) (t : ℝ) :
    kernelRight a t=a^2*primitive a t+a-2*a*(if 0≤t then 1 else 0) := by
  by_cases ht : t<0
  · rw [kernelRight,if_pos ht,if_neg (by linarith : ¬0≤t),primitive_nonpos ha ht.le]
    field_simp <;> ring
  · have ht0 : 0≤t := le_of_not_gt ht
    rw [kernelRight,if_neg ht,if_pos ht0,primitive_nonneg ha ht0]
    field_simp
    ring

theorem cell_difference (i : ℤ) (x : ℝ) :
    (if 0≤x-(i:ℝ) then (1:ℝ) else 0)-(if 0≤x-((i:ℝ)+1) then 1 else 0) =
      (KernelSteps.cell i).indicator (fun _ => (1:ℝ)) x := by
  unfold KernelSteps.cell
  by_cases hl : (i:ℝ)≤x
  · by_cases hu : x<(i:ℝ)+1
    · simp [Set.mem_Ico,hl,hu,show 0≤x-(i:ℝ) by linarith,show ¬0≤x-((i:ℝ)+1) by linarith]
    · simp [Set.mem_Ico,hl,hu,show 0≤x-(i:ℝ) by linarith,show 0≤x-((i:ℝ)+1) by linarith]
  · simp [Set.mem_Ico,hl,show ¬0≤x-(i:ℝ) by linarith,show ¬0≤x-((i:ℝ)+1) by linarith]

theorem cell_equation {a : ℝ} (ha : 0<a) (i : ℤ) (x : ℝ) :
    (kernelRight a (x-i)-kernelRight a (x-((i:ℝ)+1)))/(2*a) =
      a^2*((primitive a (x-i)-primitive a (x-((i:ℝ)+1)))/(2*a))-
        (KernelSteps.cell i).indicator (fun _ => (1:ℝ)) x := by
  rw [kernelRight_primitive ha,kernelRight_primitive ha,← cell_difference]
  field_simp
  ring

/-- The right second derivative exists even at the finitely many source jumps.
It agrees with the Ico convention, avoiding a false classical C2 assertion. -/
theorem V_right_equation {a : ℝ} (ha : 0<a) (F : Finset ℤ) (f : ℤ → ℝ) (x : ℝ) :
    HasDerivWithinAt (V a F f) (a^2*U a F f x-KernelSteps.step F f x) (Set.Ici x) x := by
  have hh : HasDerivWithinAt (V a F f)
      (∑ i ∈ F,f i*((kernelRight a (x-i)-kernelRight a (x-((i:ℝ)+1)))/(2*a))) (Set.Ici x) x := by
    apply HasDerivWithinAt.fun_sum
    intro i hi
    have hr := (kernel_right_deriv a (x-i)).comp x
      (((hasDerivAt_id x).sub_const (i:ℝ)).hasDerivWithinAt (s := Set.Ici x))
      (fun y hy => by dsimp; exact sub_le_sub_right (show x≤y from hy) _)
    have hl := (kernel_right_deriv a (x-((i:ℝ)+1))).comp x
      (((hasDerivAt_id x).sub_const ((i:ℝ)+1)).hasDerivWithinAt (s := Set.Ici x))
      (fun y hy => by dsimp; exact sub_le_sub_right (show x≤y from hy) _)
    convert (((hr.sub hl).div_const (2*a)).const_mul (f i)) using 1 <;>
      (try simp only [mul_one]) <;> rfl
  have he : (∑ i ∈ F,f i*((kernelRight a (x-i)-kernelRight a (x-((i:ℝ)+1)))/(2*a))) =
      a^2*U a F f x-KernelSteps.step F f x := by
    unfold U KernelSteps.step
    rw [Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [cell_equation ha]
    by_cases hx : x ∈ KernelSteps.cell i <;> simp [hx] <;> ring
  rw [he] at hh
  exact hh

end LonelyRunnerNew.GreenPotential
