import LonelyRunnerNew.PhysicalSaturatedWeight
import LonelyRunnerNew.SaturatedPlusSum

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew.PhysicalState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

def sumParameter (s : PhysicalState Label n) (kappa : ℝ) : ℝ :=
  2*Real.sqrt s.Q0*kappa/Real.sqrt s.geometry.area

theorem sumParameter_pos (s : PhysicalState Label n) {kappa : ℝ} (hk : 0<kappa) :
    0<s.sumParameter kappa :=
  div_pos (mul_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr s.Q0_pos)) hk)
    (Real.sqrt_pos.mpr s.geometry.area_pos)

theorem sumParameter_square (s : PhysicalState Label n) (kappa : ℝ) :
    (s.sumParameter kappa)^2=4*s.Q0*kappa^2/s.geometry.area := by
  simp only [sumParameter,div_pow,mul_pow,Real.sq_sqrt s.Q0_pos.le,
    Real.sq_sqrt s.geometry.area_pos.le]
  ring

theorem mass_eq_density_area (s : PhysicalState Label n) :
    s.edgeMass=s.density*s.geometry.area := by
  unfold density
  rw [div_mul_cancel₀ _ s.geometry.area_pos.ne']

theorem fourth_score_of_terminal (s : PhysicalState Label n) {kappa : ℝ} (hk : 0<kappa)
    (hret : (27/50:ℝ)*(1-1/1000)*s.density≤Saturated.Psi (s.sumParameter kappa)) :
    s.quality 4 0≤4*kappa^2/Saturated.t0^2 := by
  have ht := s.sumParameter_pos hk
  have hb := Saturated.fourth_power_bound s.density_nonneg s.density_le_one ht hret
  have hs : (s.sumParameter kappa)^2*s.geometry.area/s.Q0=4*kappa^2 := by
    rw [sumParameter_square]
    field_simp [s.Q0_pos.ne',s.geometry.area_pos.ne']
  have he : s.quality 4 0=(s.density^4/(s.sumParameter kappa)^2)*(4*kappa^2) := by
    rw [universal_quality_formula,←hs]
    field_simp
  rw [he]
  have hm := mul_le_mul_of_nonneg_right hb (by positivity : (0:ℝ)≤4*kappa^2)
  convert hm using 1 <;> ring

theorem stable_universal_physical_bound (s : PhysicalState Label n)
    (hs : ∀ t,Step s t → t.quality 4 0≤s.quality 4 0) (hM : 0<s.edgeMass)
    (hr : s.InRange)
    (hL : ∀ x∈s.geometry.left,rough 142 (s.geometry.leftValue x))
    (hR : ∀ y∈s.geometry.right,rough 142 (s.geometry.rightValue y)) :
    s.quality 4 0≤8/Saturated.t0^2 := by
  obtain ⟨centers,G,hoff,hG,hkeep,hall⟩ := s.universal_all_prime_retention hs hM hL hR
  have hcount := s.universal_label_counts centers hr
  have hc : 0<2*Real.sqrt s.Q0 := mul_pos (by norm_num) (Real.sqrt_pos.mpr s.Q0_pos)
  have hk : 0<Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsum := Saturated.label_sum_no_plus s.geometry.left s.geometry.right
    s.geometry.left_nonempty s.geometry.right_nonempty (s.leftProduct centers) (s.rightProduct centers)
    hc hk (fun _ hx => s.leftProduct_pos centers hx) (fun _ hy => s.rightProduct_pos centers hy)
    hcount.1 hcount.2
  have hchain := hkeep.trans ((s.retained_mass_le_full_cap centers hr hoff G hG hall).trans hsum)
  change (27/50:ℝ)*s.edgeMass≤s.geometry.area*Saturated.Psi (s.sumParameter (Real.sqrt 2)) at hchain
  rw [mass_eq_density_area] at hchain
  have hraw : ((27/50:ℝ)*s.density)*s.geometry.area≤
      Saturated.Psi (s.sumParameter (Real.sqrt 2))*s.geometry.area := by nlinarith only [hchain]
  have hret := (mul_le_mul_iff_left₀ s.geometry.area_pos).mp hraw
  have hweak : (27/50:ℝ)*(1-1/1000)*s.density≤Saturated.Psi (s.sumParameter (Real.sqrt 2)) := by
    nlinarith only [hret,s.density_nonneg]
  have hb := s.fourth_score_of_terminal hk hweak
  norm_num only [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),show (4:ℝ)*2=8 by norm_num] at hb
  exact hb

/-- All physical rough states, with no separation or stability assumption.
Its stable state is obtained using its OWN fourth-power physical score. -/
theorem universal_physical_bound (s : PhysicalState Label n) (hr : s.InRange)
    (hL : ∀ x∈s.geometry.left,rough 142 (s.geometry.leftValue x))
    (hR : ∀ y∈s.geometry.right,rough 142 (s.geometry.rightValue y)) :
    s.quality 4 0≤8/Saturated.t0^2 := by
  by_cases hM : 0<s.edgeMass
  · obtain ⟨t,ht,hq,hs,hpos⟩ := s.stable_positive_state_exists 4 0 (by norm_num) hM
    have hrough := TaggedState.reachable_preserves_rough (reachable_geometry ht) hL hR
    exact hq.trans (t.stable_universal_physical_bound hs hpos
      (reachable_preserves_range ht hr) hrough.1 hrough.2)
  · have hz := le_antisymm (le_of_not_gt hM) s.edgeMass_nonneg
    simp [quality,density,hz,Saturated.t0]
    norm_num

end LonelyRunnerNew.PhysicalState
