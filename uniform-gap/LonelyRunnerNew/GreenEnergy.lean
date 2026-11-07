import LonelyRunnerNew.GreenVariation

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace LonelyRunnerNew.GreenEnergy

theorem quartic_integrable (U : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hc : Continuous U) (hU : ∀ x, 0 ≤ U x) (hUM : ∀ x, U x ≤ M)
    (h2 : Integrable (fun x => (U x)^2)) : Integrable (fun x => (U x)^4) := by
  apply Integrable.mono' (h2.const_mul (M^2)) (hc.pow 4).aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs]
  change |(U x)^4| ≤ M^2*(U x)^2
  rw [abs_of_nonneg (by positivity : 0 ≤ (U x)^4)]
  have hh := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hU x) (hUM x) 2) (sq_nonneg (U x))
  nlinarith only [hh]

theorem energy_maximum_bound (U V : ℝ → ℝ) (a M c : ℝ) (ha : 0 < a) (hM : 0 < M)
    (hd : ∀ x, HasDerivAt U (V x) x) (hV : Continuous V)
    (hU : ∀ x, 0 ≤ U x) (hUM : ∀ x, U x ≤ M) (hmax : U c=M)
    (hbot : Tendsto U atBot (𝓝 0)) (htop : Tendsto U atTop (𝓝 0))
    (hU2 : Integrable (fun x => (U x)^2)) (hV2 : Integrable (fun x => (V x)^2)) :
    a^2*(∫ x,(U x)^4)/M^2+4*a*M^2/3 ≤ ∫ x,(V x)^2+a^2*(U x)^2 := by
  have hc : Continuous U := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  have hU4 := quartic_integrable U M hM.le hc hU hUM hU2
  let W := fun x => |V x| *U x*Real.sqrt (1-(U x)^2/M^2)
  let e := fun x => (V x)^2+a^2*(U x)^2
  have hei : Integrable e := hV2.add (hU2.const_mul (a^2))
  have hwc : Continuous W := by dsimp [W]; fun_prop
  have hW0 (x : ℝ) : 0 ≤ W x := by have hu := hU x; dsimp [W]; positivity
  have hpoint (x : ℝ) : 2*a*W x ≤ (V x)^2+a^2*(U x)^2*(1-(U x)^2/M^2) := by
    simpa only [W,mul_assoc] using GreenVariation.square_bound ha.le hM (hU x) (hUM x) (v := V x)
  have hdrop (x : ℝ) : (V x)^2+a^2*(U x)^2*(1-(U x)^2/M^2) ≤ e x := by
    have hh := mul_le_mul_of_nonneg_left
      (show 1-(U x)^2/M^2 ≤ (1:ℝ) by have h := div_nonneg (sq_nonneg (U x)) (sq_nonneg M); linarith)
      (show 0 ≤ a^2*(U x)^2 by positivity)
    dsimp [e]
    linarith
  have hWi : Integrable W := Integrable.mono' (hei.div_const (2*a)) hwc.aestronglyMeasurable (by
    filter_upwards with x
    rw [Real.norm_eq_abs,abs_of_nonneg (hW0 x)]
    exact (le_div_iff₀ (by positivity : 0<2*a)).mpr (by
      simpa only [mul_comm] using (hpoint x).trans (hdrop x)))
  have hv := GreenVariation.two_sided_variation U V M c hM hd hV hU hmax hbot htop hWi
  change 2*M^2/3 ≤ ∫ x,W x at hv
  have hpi : Integrable (fun x => (V x)^2+a^2*(U x)^2*(1-(U x)^2/M^2)) := by
    have he : (fun x => (V x)^2+a^2*(U x)^2*(1-(U x)^2/M^2)) =
        fun x => (V x)^2+a^2*(U x)^2-(a^2/M^2)*(U x)^4 := by funext x; ring
    rw [he]
    exact hei.sub (hU4.const_mul _)
  have hh := integral_mono (hWi.const_mul (2*a)) hpi hpoint
  rw [integral_const_mul] at hh
  have he : (∫ x,(V x)^2+a^2*(U x)^2*(1-(U x)^2/M^2)) =
      (∫ x,e x)-(a^2/M^2)*(∫ x,(U x)^4) := by
    have hf : (fun x => (V x)^2+a^2*(U x)^2*(1-(U x)^2/M^2)) =
        fun x => e x-(a^2/M^2)*(U x)^4 := by funext x; dsimp [e]; ring
    rw [hf,integral_sub hei (hU4.const_mul _),integral_const_mul]
  rw [he] at hh
  rw [div_mul_eq_mul_div] at hh
  have hv' := mul_le_mul_of_nonneg_left hv (by positivity : 0≤2*a)
  change a^2*(∫ x,(U x)^4)/M^2+4*a*M^2/3 ≤ ∫ x,e x
  nlinarith only [hh,hv']

theorem energy_sharp (U V : ℝ → ℝ) (a M c : ℝ) (ha : 0 < a) (hM : 0 < M)
    (hd : ∀ x, HasDerivAt U (V x) x) (hV : Continuous V)
    (hU : ∀ x, 0 ≤ U x) (hUM : ∀ x, U x ≤ M) (hmax : U c=M)
    (hbot : Tendsto U atBot (𝓝 0)) (htop : Tendsto U atTop (𝓝 0))
    (hU2 : Integrable (fun x => (U x)^2)) (hV2 : Integrable (fun x => (V x)^2)) :
    (4*a^(3/2:ℝ)/Real.sqrt 3)*Real.sqrt (∫ x,(U x)^4) ≤ ∫ x,(V x)^2+a^2*(U x)^2 := by
  let L := ∫ x,(U x)^4
  let E := ∫ x,(V x)^2+a^2*(U x)^2
  let X := a^2*L/M^2
  let Y := 4*a*M^2/3
  have hL : 0 ≤ L := integral_nonneg (fun _ => by positivity)
  have hE : 0 ≤ E := integral_nonneg (fun _ => by positivity)
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have hsum : X+Y ≤ E := energy_maximum_bound U V a M c ha hM hd hV hU hUM hmax hbot htop hU2 hV2
  have hsq := pow_le_pow_left₀ (add_nonneg hX hY) hsum 2
  have hprod : X*Y=4*a^3*L/3 := by dsimp [X,Y]; field_simp
  have hEsq : 16*a^3*L ≤ 3*E^2 := by nlinarith only [hsq,sq_nonneg (X-Y),hprod]
  have har : (a^(3/2:ℝ))^2=a^3 := by
    rw [← Real.rpow_natCast,← Real.rpow_mul ha.le]
    norm_num
  have hleft : (4*a^(3/2:ℝ)*Real.sqrt L)^2=16*a^3*L := by
    rw [mul_pow,mul_pow,Real.sq_sqrt hL,har]
    ring
  have hright : (Real.sqrt 3*E)^2=3*E^2 := by rw [mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤3)]
  have hroot : 4*a^(3/2:ℝ)*Real.sqrt L ≤ Real.sqrt 3*E :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by decide : (2:ℕ)≠0)).mp (by rw [hleft,hright]; exact hEsq)
  change (4*a^(3/2:ℝ)/Real.sqrt 3)*Real.sqrt L ≤ E
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<3))).mpr
  simpa only [mul_comm] using hroot

end LonelyRunnerNew.GreenEnergy
