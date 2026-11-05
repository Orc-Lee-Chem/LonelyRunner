import LonelyRunnerNew.GreenEnergyIdentity
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace LonelyRunnerNew.GreenPotential

def energy (a : ℝ) (F : Finset ℤ) (f : ℤ → ℝ) : ℝ := ∫ x,(V a F f x)^2+a^2*(U a F f x)^2
def mixedEnergy (a : ℝ) (F G : Finset ℤ) (f g : ℤ → ℝ) : ℝ :=
  ∫ x,V a F f x*V a G g x+a^2*(U a F f x*U a G g x)
def N (F : Finset ℤ) (f : ℤ → ℝ) : ℝ := (∑ i ∈ F,|f i|^(4/3:ℝ))^(3/4:ℝ)
def energyFactor (a : ℝ) : ℝ := Real.sqrt 3/(4*a^(3/2:ℝ))

theorem energy_nonneg (a : ℝ) (F : Finset ℤ) (f : ℤ → ℝ) : 0≤energy a F f :=
  integral_nonneg (fun x => by positivity)

theorem N_nonneg (F : Finset ℤ) (f : ℤ → ℝ) : 0≤N F f := by unfold N; positivity

theorem quartic_green_integrable {a : ℝ} (ha : 0<a) (F : Finset ℤ) (f : ℤ → ℝ)
    (hf : ∀ i ∈ F,0≤f i) (hne : ∃ i ∈ F,0<f i) : Integrable (fun x => (U a F f x)^4) := by
  obtain ⟨c,hM,hmax⟩ := positive_maximum ha F f hf hne
  exact GreenEnergy.quartic_integrable _ _ hM.le (U_continuous a F f) (U_nonneg ha F f hf) hmax (U_square_integrable ha F f hf)

theorem holder_energy {a : ℝ} (ha : 0<a) (F : Finset ℤ) (f : ℤ → ℝ)
    (hf : ∀ i ∈ F,0≤f i) (hne : ∃ i ∈ F,0<f i) :
    energy a F f ≤ N F f*(∫ x,(U a F f x)^4)^(1/4:ℝ) := by
  have hfmeas : AEStronglyMeasurable (KernelSteps.step F f) volume := by
    simpa only [mul_one] using (KernelSteps.step_mul_integrable F f (fun _ => 1) continuous_const).aestronglyMeasurable
  have hfp : MemLp (KernelSteps.step F f) (ENNReal.ofReal (4/3:ℝ)) volume := by
    apply (integrable_norm_rpow_iff hfmeas (by norm_num) (by finiteness)).mp
    simpa only [ENNReal.toReal_ofReal (by norm_num : (0:ℝ)≤4/3),Real.norm_eq_abs] using KernelSteps.norm_power_integrable F f
  have hUp : MemLp (U a F f) (ENNReal.ofReal (4:ℝ)) volume := by
    apply (integrable_norm_rpow_iff (U_continuous a F f).aestronglyMeasurable (by norm_num) (by finiteness)).mp
    have habs (x : ℝ) : |U a F f x|=U a F f x := abs_of_nonneg (U_nonneg ha F f hf x)
    simpa [Real.norm_eq_abs,habs] using quartic_green_integrable ha F f hf hne
  have hpq : Real.HolderConjugate (4/3) 4 := by rw [Real.holderConjugate_iff]; norm_num
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (ae_of_all _ (step_nonneg F f hf)) (ae_of_all _ (U_nonneg ha F f hf)) hfp hUp
  have hfi : (∫ x,(KernelSteps.step F f x)^(4/3:ℝ))=∑ i ∈ F,|f i|^(4/3:ℝ) := by
    rw [← KernelSteps.norm_power_integral]
    apply integral_congr_ae
    filter_upwards with x
    rw [abs_of_nonneg (step_nonneg F f hf x)]
  rw [hfi] at hh
  norm_num only [one_div_div,div_one,Real.rpow_ofNat] at hh
  simpa only [energy,N,energy_identity ha F f hf] using hh

theorem energy_upper {a : ℝ} (ha : 0<a) (F : Finset ℤ) (f : ℤ → ℝ)
    (hf : ∀ i ∈ F,0≤f i) (hne : ∃ i ∈ F,0<f i) :
    energy a F f ≤ energyFactor a*(N F f)^2 := by
  let L := ∫ x,(U a F f x)^4
  let R := L^(1/4:ℝ)
  let C := 4*a^(3/2:ℝ)/Real.sqrt 3
  have hL : 0≤L := integral_nonneg (fun _ => by positivity)
  have hR : 0≤R := Real.rpow_nonneg hL _
  have hC : 0<C := by dsimp [C]; positivity
  have hA : 0≤energyFactor a := by unfold energyFactor; positivity
  have hR2 : R^2=Real.sqrt L := by
    dsimp [R]
    rw [← Real.rpow_natCast,← Real.rpow_mul hL]
    norm_num [Real.sqrt_eq_rpow]
  have hs : C*R^2 ≤ energy a F f := by
    rw [hR2]
    exact actual_energy_sharp ha F f hf hne
  have hh : energy a F f ≤ N F f*R := holder_energy ha F f hf hne
  by_cases hz : R=0
  · rw [hz,mul_zero] at hh
    exact hh.trans (mul_nonneg hA (sq_nonneg _))
  · have hRp : 0<R := lt_of_le_of_ne hR (Ne.symm hz)
    have hcR : C*R≤N F f := by
      apply (mul_le_mul_iff_left₀ hRp).mp
      convert hs.trans hh using 1 <;> ring
    have hRb : R≤N F f/C := (le_div_iff₀ hC).mpr (by simpa only [mul_comm] using hcR)
    calc
      energy a F f ≤ N F f*R := hh
      _ ≤ N F f*(N F f/C) := mul_le_mul_of_nonneg_left hRb (N_nonneg F f)
      _ = energyFactor a*(N F f)^2 := by dsimp [C,energyFactor]; field_simp

theorem square_product_integrable (X Y : ℝ → ℝ) (hX : Continuous X) (hY : Continuous Y)
    (hXi : Integrable (fun x => (X x)^2)) (hYi : Integrable (fun x => (Y x)^2)) :
    Integrable (fun x => X x*Y x) := by
  apply Integrable.mono' ((hXi.add hYi).div_const 2) (hX.mul hY).aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs]
  change |X x*Y x|≤((X x)^2+(Y x)^2)/2
  rw [abs_mul]
  nlinarith only [sq_nonneg (|X x|-|Y x|),sq_abs (X x),sq_abs (Y x)]

theorem mixed_integrable {a : ℝ} (ha : 0<a) (F G : Finset ℤ) (f g : ℤ → ℝ)
    (hf : ∀ i ∈ F,0≤f i) (hg : ∀ j ∈ G,0≤g j) :
    Integrable (fun x => V a F f x*V a G g x+a^2*(U a F f x*U a G g x)) :=
  (square_product_integrable _ _ (V_continuous a F f) (V_continuous a G g)
    (V_square_integrable ha F f hf) (V_square_integrable ha G g hg)).add
  ((square_product_integrable _ _ (U_continuous a F f) (U_continuous a G g)
    (U_square_integrable ha F f hf) (U_square_integrable ha G g hg)).const_mul (a^2))

theorem mixed_energy_identity {a : ℝ} (ha : 0<a) (F G : Finset ℤ) (f g : ℤ → ℝ)
    (hf : ∀ i ∈ F,0≤f i) (hg : ∀ j ∈ G,0≤g j) :
    mixedEnergy a F G f g=∫ x,KernelSteps.step F f x*U a G g x := by
  let e := fun x => V a F f x*V a G g x+a^2*(U a F f x*U a G g x)
  let R := fun x => e x-KernelSteps.step F f x*U a G g x
  have hei := mixed_integrable ha F G f g hf hg
  have hfi := KernelSteps.step_mul_integrable F f (U a G g) (U_continuous a G g)
  have hd (x : ℝ) : HasDerivWithinAt (fun x => U a G g x*V a F f x) (R x) (Set.Ici x) x := by
    have hh := (U_deriv a G g x).hasDerivWithinAt.mul (V_right_equation ha F f x)
    apply hh.congr_deriv
    dsimp [R,e]
    ring
  have hb : Tendsto (fun x => U a G g x*V a F f x) atBot (𝓝 0) := by simpa using (U_limits ha G g hg).1.mul (V_limits ha F f hf).1
  have ht : Tendsto (fun x => U a G g x*V a F f x) atTop (𝓝 0) := by simpa using (U_limits ha G g hg).2.mul (V_limits ha F f hf).2
  have hz := integral_right_derivative_zero _ R ((U_continuous a G g).mul (V_continuous a F f)) hd (hei.sub hfi) hb ht
  dsimp [R] at hz
  rw [integral_sub hei hfi] at hz
  exact sub_eq_zero.mp hz

theorem mixed_energy_sq_le {a : ℝ} (ha : 0<a) (F G : Finset ℤ) (f g : ℤ → ℝ)
    (hf : ∀ i ∈ F,0≤f i) (hg : ∀ j ∈ G,0≤g j) :
    (mixedEnergy a F G f g)^2≤energy a F f*energy a G g := by
  let E := energy a F f
  let D := energy a G g
  let B := mixedEnergy a F G f g
  have hEi : Integrable (fun x => (V a F f x)^2+a^2*(U a F f x)^2) :=
    (V_square_integrable ha F f hf).add ((U_square_integrable ha F f hf).const_mul (a^2))
  have hDi : Integrable (fun x => (V a G g x)^2+a^2*(U a G g x)^2) :=
    (V_square_integrable ha G g hg).add ((U_square_integrable ha G g hg).const_mul (a^2))
  have hBi := mixed_integrable ha F G f g hf hg
  have hquad (t : ℝ) : 0≤t^2*E-2*t*B+D := by
    have hh : 0≤∫ x,(t*V a F f x-V a G g x)^2+a^2*(t*U a F f x-U a G g x)^2 :=
      integral_nonneg (fun _ => by positivity)
    have he : (fun x => (t*V a F f x-V a G g x)^2+a^2*(t*U a F f x-U a G g x)^2) =
        fun x => t^2*((V a F f x)^2+a^2*(U a F f x)^2)-2*t*(V a F f x*V a G g x+a^2*(U a F f x*U a G g x))+
          ((V a G g x)^2+a^2*(U a G g x)^2) := by funext x; ring
    have hAt : Integrable (fun x => t^2*((V a F f x)^2+a^2*(U a F f x)^2)-
        2*t*(V a F f x*V a G g x+a^2*(U a F f x*U a G g x))) :=
      (hEi.const_mul (t^2)).sub (hBi.const_mul (2*t))
    rw [he,integral_add hAt hDi,
      integral_sub (hEi.const_mul (t^2)) (hBi.const_mul (2*t)),integral_const_mul,integral_const_mul] at hh
    exact hh
  have hE : 0≤E := energy_nonneg a F f
  by_cases hE0 : E=0
  · by_cases hB0 : B=0
    · change B^2≤E*D
      simp [hB0,hE0]
    · have hh := hquad ((D+1)/(2*B))
      rw [hE0,mul_zero] at hh
      have he : 2*((D+1)/(2*B))*B=D+1 := by field_simp
      rw [he] at hh
      linarith
  · have hEp : 0<E := lt_of_le_of_ne hE (Ne.symm hE0)
    have hh := mul_nonneg hE (hquad (B/E))
    have he : E*((B/E)^2*E-2*(B/E)*B+D)=E*D-B^2 := by field_simp; ring
    change B^2≤E*D
    rw [he] at hh
    linarith

end LonelyRunnerNew.GreenPotential
