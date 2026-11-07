import LonelyRunnerNew.GreenKernel

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace LonelyRunnerNew.KernelSteps

/-- Normalized Green potential. `potential` itself remains the unnormalized P. -/
def normalizedPotential (a : ℝ) (F : Finset ℤ) (f : ℤ → ℝ) (x : ℝ) : ℝ :=
  potential a F f x/(2*a)

theorem normalizedPotential_eq_green (a : ℝ) (F : Finset ℤ) (f : ℤ → ℝ) :
    normalizedPotential a F f=GreenPotential.U a F f := by
  funext x
  exact (GreenPotential.U_eq_green a F f x).symm

theorem potential_eq_two_mul_normalized {a : ℝ} (ha : 0<a)
    (F : Finset ℤ) (f : ℤ → ℝ) (x : ℝ) :
    potential a F f x=2*a*normalizedPotential a F f x := by
  unfold normalizedPotential
  field_simp

theorem normalizedPotential_deriv (a : ℝ) (F : Finset ℤ) (f : ℤ → ℝ) (x : ℝ) :
    HasDerivAt (normalizedPotential a F f) (GreenPotential.V a F f x) x := by
  rw [normalizedPotential_eq_green]
  exact GreenPotential.U_deriv a F f x

theorem normalizedPotential_equation {a : ℝ} (ha : 0<a)
    (F : Finset ℤ) (f : ℤ → ℝ) (x : ℝ) :
    HasDerivWithinAt (GreenPotential.V a F f)
      (a^2*normalizedPotential a F f x-step F f x) (Set.Ici x) x := by
  rw [normalizedPotential_eq_green]
  exact GreenPotential.V_right_equation ha F f x

theorem potential_deriv {a : ℝ} (ha : 0<a) (F : Finset ℤ) (f : ℤ → ℝ) (x : ℝ) :
    HasDerivAt (potential a F f) (2*a*GreenPotential.V a F f x) x := by
  have he : potential a F f=(fun x => 2*a*GreenPotential.U a F f x) := by
    funext x
    rw [potential_eq_two_mul_normalized ha,normalizedPotential_eq_green]
  rw [he]
  exact (GreenPotential.U_deriv a F f x).const_mul (2*a)

/-- In unnormalized variables the source is 2*a*f, not f. Right derivatives
retain the established Ico convention at source jumps. -/
theorem potential_equation {a : ℝ} (ha : 0<a) (F : Finset ℤ) (f : ℤ → ℝ) (x : ℝ) :
    HasDerivWithinAt (fun x => 2*a*GreenPotential.V a F f x)
      (a^2*potential a F f x-2*a*step F f x) (Set.Ici x) x := by
  have hh := (GreenPotential.V_right_equation ha F f x).const_mul (2*a)
  have he : 2*a*(a^2*GreenPotential.U a F f x-step F f x)=
      a^2*potential a F f x-2*a*step F f x := by
    rw [potential_eq_two_mul_normalized ha,normalizedPotential_eq_green]
    ring
  simpa only [he] using hh

theorem normalized_energy_identity {a : ℝ} (ha : 0<a) (F : Finset ℤ) (f : ℤ → ℝ)
    (hf : ∀ i ∈ F,0≤f i) :
    GreenPotential.energy a F f=∫ x,step F f x*normalizedPotential a F f x := by
  rw [normalizedPotential_eq_green]
  exact GreenPotential.energy_identity ha F f hf

theorem potential_energy_scale {a : ℝ} (ha : 0<a) (F : Finset ℤ) (f : ℤ → ℝ) :
    (∫ x,(2*a*GreenPotential.V a F f x)^2+a^2*(potential a F f x)^2)=
      (2*a)^2*GreenPotential.energy a F f := by
  unfold GreenPotential.energy
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  rw [potential_eq_two_mul_normalized ha,normalizedPotential_eq_green]
  ring

theorem potential_energy_identity {a : ℝ} (ha : 0<a) (F : Finset ℤ) (f : ℤ → ℝ)
    (hf : ∀ i ∈ F,0≤f i) :
    (∫ x,(2*a*GreenPotential.V a F f x)^2+a^2*(potential a F f x)^2)=
      2*a*(∫ x,step F f x*potential a F f x) := by
  rw [potential_energy_scale ha,normalized_energy_identity ha F f hf,← integral_const_mul,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  rw [potential_eq_two_mul_normalized ha]
  ring

theorem bilinear_eq_two_mul_mixedEnergy {a : ℝ} (ha : 0<a)
    (F G : Finset ℤ) (f g : ℤ → ℝ) (hf : ∀ i ∈ F,0≤f i) (hg : ∀ j ∈ G,0≤g j) :
    (∫ x,step F f x*potential a G g x)=2*a*GreenPotential.mixedEnergy a F G f g := by
  rw [GreenPotential.mixed_energy_identity ha F G f g hf hg,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  rw [potential_eq_two_mul_normalized ha,normalizedPotential_eq_green]
  ring

end LonelyRunnerNew.KernelSteps

namespace LonelyRunnerNew.TaggedState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

/-- An arbitrary positive scale, using actual cardinal probabilities, the
proved Green bound, and the actual-scale cell identity. No hcell premise. -/
theorem actual_enhanced_scale (s : TaggedState Label n) (p : ℕ) (a : ℝ) (ha : 0<a) :
    s.scaleKernel p a ≤ (Real.sqrt 3/2)*Real.exp (-a)*a^(3/2:ℝ)/(1-Real.exp (-a))^2+
      (1-2*Real.exp (-a)*(a-1+Real.exp (-a))/(1-Real.exp (-a))^2)*
        (∑ i ∈ s.valuationSupport p,(s.alpha p i*s.beta p i)^(3/4:ℝ)) := by
  have hc := GreenPotential.actual_probability_cell_bound ha (s.valuationSupport p) (s.alpha p) (s.beta p)
    (fun i _ => s.alpha_nonneg p i) (fun j _ => s.beta_nonneg p j)
    (s.alpha_sum_common_support p) (s.beta_sum_common_support p)
  have hJ : (∫ u,KernelSteps.probabilityStep (s.valuationSupport p) (s.alpha p) u*
      (∫ v,KernelSteps.probabilityStep (s.valuationSupport p) (s.beta p) v*Real.exp (-a*|u-v|))) ≤
      (Real.sqrt 3/2)*a^(-1/2:ℝ) := by
    unfold KernelSteps.probabilityStep
    rw [KernelSteps.bilinear_cell_identity]
    exact hc
  rw [s.actual_cell_integral_identity_scale p a ha] at hJ
  let Dg := ∑ i ∈ s.valuationSupport p,(s.alpha p i*s.beta p i)^(3/4:ℝ)
  let B := (Real.sqrt 3/2)*a^(-1/2:ℝ)
  change KernelCells.A a*s.scaleKernel p a+(KernelCells.D a-KernelCells.A a)*Dg ≤ B at hJ
  have hA := KernelCells.A_pos a ha
  have hh : s.scaleKernel p a ≤ (B+(KernelCells.A a-KernelCells.D a)*Dg)/KernelCells.A a := by
    apply (le_div_iff₀ hA).mpr
    nlinarith only [hJ]
  have he : (B+(KernelCells.A a-KernelCells.D a)*Dg)/KernelCells.A a =
      B/KernelCells.A a+(1-KernelCells.D a/KernelCells.A a)*Dg := by
    field_simp [hA.ne']
  rw [he] at hh
  dsimp [B] at hh
  rw [KernelCells.continuous_constant_div_A a ha,KernelCells.correction_coefficient a ha] at hh
  exact hh

theorem actual_normalized_cell_identity_scale (s : TaggedState Label n) (p : ℕ)
    (a : ℝ) (ha : 0<a) :
    2*a*(∫ u,KernelSteps.probabilityStep (s.valuationSupport p) (s.alpha p) u*
      KernelSteps.normalizedPotential a (KernelSteps.natSupport (s.valuationSupport p))
        (KernelSteps.liftArray (s.valuationSupport p) (s.beta p)) u) =
      KernelCells.A a*s.scaleKernel p a+(KernelCells.D a-KernelCells.A a)*
        (∑ i ∈ s.valuationSupport p,(s.alpha p i*s.beta p i)^(3/4:ℝ)) := by
  have hh := s.actual_cell_integral_identity_scale p a ha
  have he : (∫ u,KernelSteps.probabilityStep (s.valuationSupport p) (s.alpha p) u*
      (∫ v,KernelSteps.probabilityStep (s.valuationSupport p) (s.beta p) v*Real.exp (-a*|u-v|))) =
      2*a*(∫ u,KernelSteps.probabilityStep (s.valuationSupport p) (s.alpha p) u*
        KernelSteps.normalizedPotential a (KernelSteps.natSupport (s.valuationSupport p))
          (KernelSteps.liftArray (s.valuationSupport p) (s.beta p)) u) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with u
    change KernelSteps.probabilityStep (s.valuationSupport p) (s.alpha p) u*
        KernelSteps.potential a (KernelSteps.natSupport (s.valuationSupport p))
          (KernelSteps.liftArray (s.valuationSupport p) (s.beta p)) u = _
    rw [KernelSteps.potential_eq_two_mul_normalized ha]
    ring
  rw [he] at hh
  exact hh

end LonelyRunnerNew.TaggedState
