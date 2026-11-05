import LonelyRunnerNew.BohrPairMoments

noncomputable section
set_option autoImplicit false
namespace LonelyRunnerNew

/-- Conditional intermediate assembly only. The two endpoint pair-count bounds
remain unproved; this theorem is not a proof of `spilloverInput`. -/
theorem spillover_of_actual_pair_mass_bounds (V : Finset ℕ) (hV : valid V)
    (hlower : 1-1/(V.card:ℝ)-W V≤bohrDifferentMass V (1/(2*(V.card:ℝ))))
    (hupper : bohrDifferentMass V ((7/5:ℝ)*(1/(2*(V.card:ℝ))))≤
      (7/5:ℝ)^2*(1-1/(V.card:ℝ))) :
    3/35-W V/2+1/(5*(V.card:ℝ))≤gap V := by
  have hn : (2:ℝ)≤V.card := by exact_mod_cast hV.2
  have hn0 : (0:ℝ)<V.card := by linarith
  let r := 1/(2*(V.card:ℝ))
  have hr : 0<r := by dsimp [r];positivity
  have hsmall : (7/5:ℝ)*r<1/2 := by
    dsimp [r]
    rw [show (7/5:ℝ)*(1/(2*(V.card:ℝ)))=(7/10:ℝ)/(V.card:ℝ) by ring]
    apply (div_lt_iff₀ hn0).mpr
    nlinarith only [hn]
  have hd := bohrDifferentMass_dilation V hV.1 hr (by norm_num : (1:ℝ)≤7/5) hsmall
  have hEg : forbiddenExcess V r=gap V := forbiddenExcess_eq_gap V hV
  have hE := bohr_tail_integral_lower V hV.1 (mul_pos (by norm_num : (0:ℝ)<7/5) hr).le hsmall.le
  rw [bohr_tail_integral_eq_excess V hV.1] at hE
  have he : 2*((7/5:ℝ)*r)*(V.card:ℝ)-1=2/5 := by dsimp [r];field_simp;ring
  rw [he] at hE
  rw [hEg] at hd
  change 1-1/(V.card:ℝ)-W V≤bohrDifferentMass V r at hlower
  change bohrDifferentMass V ((7/5:ℝ)*r)≤(7/5:ℝ)^2*(1-1/(V.card:ℝ)) at hupper
  have hi : 1/(5*(V.card:ℝ))=(1/5:ℝ)*(1/(V.card:ℝ)) := by ring
  rw [hi]
  nlinarith only [hd,hE,hlower,hupper]

end LonelyRunnerNew
