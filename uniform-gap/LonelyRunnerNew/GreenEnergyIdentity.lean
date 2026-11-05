import LonelyRunnerNew.GreenEquation

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace LonelyRunnerNew.GreenPotential

/-- FTC on the whole line with right derivatives, proved by the two actual
improper-integral limits. This permits the source jumps of finite step data. -/
theorem integral_right_derivative_zero (H R : ℝ → ℝ) (hH : Continuous H)
    (hd : ∀ x,HasDerivWithinAt H (R x) (Set.Ici x) x) (hR : Integrable R)
    (hbot : Tendsto H atBot (𝓝 0)) (htop : Tendsto H atTop (𝓝 0)) : (∫ x,R x)=0 := by
  have hleft : (∫ x in Set.Iic (0:ℝ),R x)=H 0 := by
    have hh := intervalIntegral_tendsto_integral_Iic (0:ℝ) hR.integrableOn tendsto_id
    have hl : Tendsto (fun b => H 0-H b) atBot (𝓝 (H 0)) := by simpa using hbot.const_sub (H 0)
    apply tendsto_nhds_unique_of_eventuallyEq hh hl
    filter_upwards [eventually_le_atBot (0:ℝ)] with b hb
    exact intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hb hH.continuousOn
      (fun x _ => (hd x).mono Set.Ioi_subset_Ici_self) hR.intervalIntegrable
  have hright : (∫ x in Set.Ioi (0:ℝ),R x)= -H 0 := by
    have hh := intervalIntegral_tendsto_integral_Ioi (0:ℝ) hR.integrableOn tendsto_id
    have hl : Tendsto (fun b => H b-H 0) atTop (𝓝 (-H 0)) := by simpa using htop.sub_const (H 0)
    apply tendsto_nhds_unique_of_eventuallyEq hh hl
    filter_upwards [eventually_ge_atTop (0:ℝ)] with b hb
    exact intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hb hH.continuousOn
      (fun x _ => (hd x).mono Set.Ioi_subset_Ici_self) hR.intervalIntegrable
  have hs := integral_add_compl (s := Set.Iic (0:ℝ)) measurableSet_Iic hR
  rw [Set.compl_Iic,hleft,hright] at hs
  linarith

theorem energy_identity {a : ℝ} (ha : 0<a) (F : Finset ℤ) (f : ℤ → ℝ) (hf : ∀ i ∈ F,0≤f i) :
    (∫ x,(V a F f x)^2+a^2*(U a F f x)^2) = ∫ x,KernelSteps.step F f x*U a F f x := by
  let e := fun x => (V a F f x)^2+a^2*(U a F f x)^2
  let R := fun x => e x-KernelSteps.step F f x*U a F f x
  have hei : Integrable e := (V_square_integrable ha F f hf).add ((U_square_integrable ha F f hf).const_mul (a^2))
  have hfi := KernelSteps.step_mul_integrable F f (U a F f) (U_continuous a F f)
  have hRi : Integrable R := hei.sub hfi
  have hd (x : ℝ) : HasDerivWithinAt (fun x => U a F f x*V a F f x) (R x) (Set.Ici x) x := by
    have hh := (U_deriv a F f x).hasDerivWithinAt.mul (V_right_equation ha F f x)
    apply hh.congr_deriv
    dsimp [R,e]
    ring
  have hb : Tendsto (fun x => U a F f x*V a F f x) atBot (𝓝 0) := by
    simpa using (U_limits ha F f hf).1.mul (V_limits ha F f hf).1
  have ht : Tendsto (fun x => U a F f x*V a F f x) atTop (𝓝 0) := by
    simpa using (U_limits ha F f hf).2.mul (V_limits ha F f hf).2
  have hz := integral_right_derivative_zero _ R ((U_continuous a F f).mul (V_continuous a F f)) hd hRi hb ht
  dsimp [R] at hz
  rw [integral_sub hei hfi] at hz
  exact sub_eq_zero.mp hz

end LonelyRunnerNew.GreenPotential
