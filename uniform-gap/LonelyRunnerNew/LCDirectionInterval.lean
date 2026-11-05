import LonelyRunnerNew.LCNormalizedDirection
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
namespace LonelyRunnerNew.LCDirection

def A (z : ℝ) : ℝ := (1-(1-z)^(3/2:ℝ))/z
def C (z : ℝ) : ℝ := (1+(1-2*z)^3)^(1/4:ℝ)
def denominator (v z : ℝ) : ℝ := A z-v*Real.sqrt z

theorem A_identity {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    A z=Real.sqrt (1-z)+1/(1+Real.sqrt (1-z)) := by
  have hr := Real.sq_sqrt (show 0 ≤ 1-z by linarith)
  have hd : 1+Real.sqrt (1-z) ≠ 0 := by positivity
  unfold A
  rw [BootstrapInterval.three_halves _ (by linarith : 0 ≤ 1-z)]
  field_simp [hz.ne',hd]
  nlinarith only [hr,congrArg (fun t : ℝ => t*Real.sqrt (1-z)) hr]

theorem A_bounds {z : ℝ} (hz : 0 < z) (hz1 : z < 1) : 1 ≤ A z ∧ A z ≤ 3/2 := by
  have hr0 := Real.sqrt_nonneg (1-z)
  have hr1 : Real.sqrt (1-z) ≤ 1 := by
    exact (Real.sqrt_le_iff).mpr ⟨by norm_num,by linarith⟩
  have hd : 0 < 1+Real.sqrt (1-z) := by positivity
  rw [A_identity hz hz1]
  constructor
  · apply (mul_le_mul_iff_right₀ hd).mp
    field_simp [hd.ne']
    nlinarith [sq_nonneg (Real.sqrt (1-z))]
  · apply (mul_le_mul_iff_right₀ hd).mp
    field_simp [hd.ne']
    nlinarith [mul_nonneg (sub_nonneg.mpr hr1) (show 0 ≤ Real.sqrt (1-z)+1/2 by positivity)]

theorem A_hasDeriv {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    HasDerivAt A (-(Real.sqrt (1-z)+2)/(2*(1+Real.sqrt (1-z))^2)) z := by
  have hpos : 0 < 1-z := by linarith
  have hr0 : 0 < Real.sqrt (1-z) := Real.sqrt_pos.mpr hpos
  have hd : 1+Real.sqrt (1-z) ≠ 0 := by positivity
  have hr := (Real.hasDerivAt_sqrt hpos.ne').comp z
    ((hasDerivAt_const z (1:ℝ)).sub (hasDerivAt_id z))
  have hh := hr.add ((hasDerivAt_const z (1:ℝ)).div
    ((hasDerivAt_const z (1:ℝ)).add hr) hd)
  have he : A =ᶠ[nhds z] (fun x : ℝ => Real.sqrt (1-x)+1/(1+Real.sqrt (1-x))) := by
    filter_upwards [isOpen_Ioo.mem_nhds (show z ∈ Set.Ioo (0:ℝ) 1 from ⟨hz,hz1⟩)] with x hx
    exact A_identity hx.1 hx.2
  convert hh.congr_of_eventuallyEq he using 1
  dsimp only [Pi.add_apply,Pi.div_apply,Function.comp_def]
  field_simp [hr0.ne',hd]
  ring

theorem A_deriv_upper {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    -(Real.sqrt (1-z)+2)/(2*(1+Real.sqrt (1-z))^2) ≤ -(3/8:ℝ) := by
  have hr0 := Real.sqrt_nonneg (1-z)
  have hr1 : Real.sqrt (1-z) ≤ 1 := (Real.sqrt_le_iff).mpr ⟨by norm_num,by linarith⟩
  apply (div_le_iff₀ (by positivity : 0 < 2*(1+Real.sqrt (1-z))^2)).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hr1) (show 0 ≤ 3*Real.sqrt (1-z)+5 by positivity)]

theorem C_pos {z : ℝ} (hz : z ≤ 1/2) : 0 < C z := by
  unfold C
  have : 0 ≤ 1-2*z := by linarith
  positivity

theorem C_hasDeriv {z : ℝ} (hz : z ≤ 1/2) :
    HasDerivAt C (C z*(-(3/2:ℝ)*(1-2*z)^2/(1+(1-2*z)^3))) z := by
  have ht : 0 ≤ 1-2*z := by linarith
  have hd : 0 < 1+(1-2*z)^3 := by positivity
  have hh := (((hasDerivAt_const z (1:ℝ)).sub ((hasDerivAt_id z).const_mul 2)).pow 3
    |>.const_add 1).rpow_const (p := (1/4:ℝ)) (Or.inl hd.ne')
  convert hh using 1
  · rfl
  · dsimp only [Pi.sub_apply,Pi.pow_apply,id_eq]
    norm_num only [Nat.cast_ofNat,Nat.reduceSub,mul_one,zero_sub]
    rw [show (-(3/4):ℝ)=(1/4)-1 by norm_num,Real.rpow_sub_one hd.ne']
    unfold C
    ring

theorem C_deriv_lower {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1/2) :
    -(3/4:ℝ)*C z ≤ C z*(-(3/2:ℝ)*(1-2*z)^2/(1+(1-2*z)^3)) := by
  have ht : 0 ≤ 1-2*z := by linarith
  have ht1 : 1-2*z ≤ 1 := by linarith
  have hd : 0 < 1+(1-2*z)^3 := by positivity
  have hc : -(3/4:ℝ) ≤ -(3/2:ℝ)*(1-2*z)^2/(1+(1-2*z)^3) := by
    apply (le_div_iff₀ hd).mpr
    have he : 0 ≤ (1-(1-2*z))*(1+(1-2*z)-(1-2*z)^2) := by
      have hs : (1-2*z)^2 ≤ 1-2*z := by nlinarith [mul_nonneg ht (sub_nonneg.mpr ht1)]
      exact mul_nonneg (by linarith) (by linarith)
    nlinarith only [he]
  simpa only [mul_comm (C z)] using mul_le_mul_of_nonneg_left hc (C_pos hz1).le

theorem denominator_pos {v z : ℝ} (hv : 0 ≤ v) (hv2 : v ≤ 2)
    (hz : 0 < z) (hz1 : z ≤ 1/8) : 0 < denominator v z := by
  have hA := (A_bounds hz (by linarith : z < 1)).1
  have hs := Real.sq_sqrt hz.le
  have hs0 := Real.sqrt_nonneg z
  have hs1 : Real.sqrt z < 1/2 := by nlinarith
  unfold denominator
  nlinarith [mul_le_mul_of_nonneg_right hv2 hs0]

theorem denominator_hasDeriv {v z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    HasDerivAt (denominator v)
      (-(Real.sqrt (1-z)+2)/(2*(1+Real.sqrt (1-z))^2)-v/(2*Real.sqrt z)) z := by
  have hh := (A_hasDeriv hz hz1).sub ((Real.hasDerivAt_sqrt hz.ne').const_mul v)
  convert hh using 1
  · rfl
  · ring

theorem denominator_deriv_upper {v z : ℝ} (hv : 0 ≤ v) (hvSq : (1/2:ℝ) ≤ v^2)
    (hz : 0 < z) (hz1 : z ≤ 1/8) :
    -(Real.sqrt (1-z)+2)/(2*(1+Real.sqrt (1-z))^2)-v/(2*Real.sqrt z) ≤ -(11/8:ℝ) := by
  have hs0 := Real.sqrt_nonneg z
  have hs := Real.sq_sqrt hz.le
  have hspos := Real.sqrt_pos.mpr hz
  have hvroot : 2*Real.sqrt z ≤ v := by nlinarith
  have hdiv : 1 ≤ v/(2*Real.sqrt z) := (le_div_iff₀ (by positivity)).mpr (by simpa using hvroot)
  have hA := A_deriv_upper hz (by linarith : z < 1)
  linarith

/-- The endpoint comparison is uniform in z on the entire interval. The
coefficient v is held fixed; it will be instantiated by h(lambda,u). -/
theorem denominator_ratio_antitone {v lo hi : ℝ}
    (hv : 0 ≤ v) (hv2 : v ≤ 2) (hvSq : (1/2:ℝ) ≤ v^2)
    (hlo : 0 < lo) (hhi : hi ≤ 1/8) :
    AntitoneOn (fun z => denominator v z/C z) (Set.Icc lo hi) := by
  let dA := fun z : ℝ => -(Real.sqrt (1-z)+2)/(2*(1+Real.sqrt (1-z))^2)-v/(2*Real.sqrt z)
  let dC := fun z : ℝ => C z*(-(3/2:ℝ)*(1-2*z)^2/(1+(1-2*z)^3))
  let d := fun z : ℝ => (dA z*C z-denominator v z*dC z)/(C z)^2
  have hzpos (z : ℝ) (hz : z ∈ Set.Icc lo hi) : 0 < z := hlo.trans_le hz.1
  have hzupper (z : ℝ) (hz : z ∈ Set.Icc lo hi) : z ≤ 1/8 := hz.2.trans hhi
  have hderiv (z : ℝ) (hz : z ∈ Set.Icc lo hi) :
      HasDerivAt (fun x => denominator v x/C x) (d z) z :=
    (denominator_hasDeriv (hzpos z hz) (by linarith [hzupper z hz])).div
      (C_hasDeriv (by linarith [hzupper z hz])) (C_pos (by linarith [hzupper z hz])).ne'
  apply antitoneOn_of_hasDerivWithinAt_nonpos (f' := d) (convex_Icc lo hi)
  · intro z hz
    exact (hderiv z hz).continuousAt.continuousWithinAt
  · intro z hz
    exact (hderiv z (interior_subset hz)).hasDerivWithinAt
  · intro z hz
    have hzm := interior_subset hz
    have hz0 := hzpos z hzm
    have hz1 := hzupper z hzm
    have hC0 := C_pos (show z ≤ 1/2 by linarith)
    have hD0 := denominator_pos hv hv2 hz0 hz1
    have hD1 : denominator v z ≤ 3/2 := by
      unfold denominator
      exact sub_le_self _ (mul_nonneg hv (Real.sqrt_nonneg _)) |>.trans (A_bounds hz0 (by linarith)).2
    have hdA : dA z ≤ -(11/8:ℝ) := denominator_deriv_upper hv hvSq hz0 hz1
    have hdC : -(3/4:ℝ)*C z ≤ dC z := C_deriv_lower hz0.le (by linarith)
    have hm1 := mul_le_mul_of_nonneg_right hdA hC0.le
    have hm2 := mul_le_mul_of_nonneg_left hdC hD0.le
    have hm3 := mul_le_mul_of_nonneg_right hD1 (mul_nonneg (by norm_num : (0:ℝ) ≤ 3/4) hC0.le)
    dsimp only [d]
    apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    nlinarith only [hm1,hm2,hm3,hC0]

theorem h_upper {lam u : ℝ} (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1/3)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) : h lam u ≤ 2 := by
  have hl4 : lam^4 ≤ 1/81 := by
    convert pow_le_pow_left₀ hl0 hl1 4 using 1 <;> norm_num
  have hd : 0 < 1-lam^4 := by linarith
  let r := (1/(1-lam^4))^(1/4:ℝ)
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by positivity) _
  have hr4 : r^4=1/(1-lam^4) := BootstrapInterval.quarter_fourth _ (by positivity)
  have hr2 : r^2 ≤ 3/2 := by
    apply (pow_le_pow_iff_left₀ (sq_nonneg r) (by norm_num : (0:ℝ) ≤ 3/2) (by decide : (2:ℕ)≠0)).mp
    rw [← pow_mul,show (2:ℕ)*2=4 by decide,hr4]
    apply (div_le_iff₀ hd).mpr
    norm_num
    linarith
  have h4 : (4:ℝ)^(3/4:ℝ) ≤ 3 := by
    apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg (by norm_num) _) (by norm_num : (0:ℝ) ≤ 3)
      (by decide : (4:ℕ)≠0)).mp
    rw [BootstrapInterval.three_quarters_fourth _ (by norm_num)]
    norm_num
  have hl2 : lam^2 ≤ 1/9 := by
    convert pow_le_pow_left₀ hl0 hl1 2 using 1 <;> norm_num
  have hc : 4^(3/4:ℝ)*r^2*lam^2 ≤ 1/2 := by
    have hmul := mul_le_mul h4 hr2 (sq_nonneg r) (by norm_num : (0:ℝ) ≤ 3)
    have hmul' := mul_le_mul hmul hl2 (sq_nonneg lam) (by norm_num : (0:ℝ) ≤ 3*(3/2))
    norm_num at hmul'
    exact hmul'
  have hj : (u*(1-u))^(3/4:ℝ) ≤ 1 := Real.rpow_le_one
    (mul_nonneg hu (by linarith)) (by nlinarith [mul_nonneg hu (by linarith : 0 ≤ 1-u)]) (by norm_num)
  have hh0 : h0 u ≤ 1 := by
    have hx := Real.rpow_le_self_of_le_one hu hu1 (by norm_num : (1:ℝ) ≤ 3/2)
    have hy := Real.rpow_le_self_of_le_one (by linarith : 0 ≤ 1-u) (by linarith : 1-u ≤ 1)
      (by norm_num : (1:ℝ) ≤ 3/2)
    unfold h0
    linarith
  have hm := mul_le_mul hc hj (Real.rpow_nonneg (mul_nonneg hu (by linarith)) _) (by norm_num : (0:ℝ) ≤ 1/2)
  change h0 u+4^(3/4:ℝ)*r^2*lam^2*(u*(1-u))^(3/4:ℝ) ≤ 2
  linarith

def normalizedInequality (lam z u : ℝ) : Prop :=
  1 ≤ (1-z)^(3/2:ℝ)+z^(3/2:ℝ)*h lam u+
    2^(3/4:ℝ)*(1/(1-lam^4))^(1/4:ℝ)*lam*z^(3/4:ℝ)*f u*C z

theorem endpoint_root_bound {lam z S u : ℝ} (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1/3)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hz : 0 < z) (hzS : z ≤ S) (hS : S ≤ 1/8)
    (hit : normalizedInequality lam z u) : z^(1/4:ℝ) ≤ lam*B S lam u := by
  let N := 2^(3/4:ℝ)*(1/(1-lam^4))^(1/4:ℝ)*f u
  have hD0 := denominator_pos (h_nonneg hu hu1) (h_upper hl0 hl1 hu hu1) (hz.trans_le hzS) hS
  have hC0 := C_pos (show S ≤ 1/2 by linarith)
  have hcz0 := C_pos (show z ≤ 1/2 by linarith)
  have heA : z*A z=1-(1-z)^(3/2:ℝ) := by unfold A; field_simp
  have hz15 : z^(3/2:ℝ)=z*Real.sqrt z := by
    rw [BootstrapInterval.three_halves _ hz.le,pow_succ,Real.sq_sqrt hz.le]
  have hzsum : z^(3/4:ℝ)*z^(1/4:ℝ)=z := by
    rw [← Real.rpow_add hz]
    norm_num
  have hb : z*denominator (h lam u) z ≤ N*lam*z^(3/4:ℝ)*C z := by
    unfold normalizedInequality at hit
    rw [hz15] at hit
    dsimp [denominator,N]
    nlinarith only [hit,heA]
  have hroot : z^(1/4:ℝ)*denominator (h lam u) z ≤ N*lam*C z := by
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hz (3/4:ℝ))).mp
    calc
      _ = (z^(3/4:ℝ)*z^(1/4:ℝ))*denominator (h lam u) z := by ring
      _ = z*denominator (h lam u) z := by rw [hzsum]
      _ ≤ N*lam*z^(3/4:ℝ)*C z := hb
      _ = _ := by ring
  have hratio := denominator_ratio_antitone (h_nonneg hu hu1) (h_upper hl0 hl1 hu hu1)
    (h_sq_lower hu hu1) hz hS (show z ∈ Set.Icc z S from ⟨le_rfl,hzS⟩)
    (show S ∈ Set.Icc z S from ⟨hzS,le_rfl⟩) hzS
  have hzcore : z^(1/4:ℝ)*(denominator (h lam u) z/C z) ≤ N*lam := by
    simpa only [mul_div_assoc] using (div_le_iff₀ hcz0).mpr hroot
  have hcore := (mul_le_mul_of_nonneg_left hratio (Real.rpow_nonneg hz.le (1/4:ℝ))).trans hzcore
  have heB : lam*B S lam u = (N*lam*C S)/denominator (h lam u) S := by
    dsimp [B,N,C,denominator,A]
    ring
  rw [heB]
  apply (le_div_iff₀ hD0).mpr
  have hh := (div_le_iff₀ hC0).mp (show
    z^(1/4:ℝ)*denominator (h lam u) S/C S ≤ N*lam by simpa only [mul_div_assoc] using hcore)
  exact hh

theorem endpoint_bound {lam z S u : ℝ} (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1/3)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hz : 0 < z) (hzS : z ≤ S) (hS : S ≤ 1/8)
    (hit : normalizedInequality lam z u) : z ≤ lam^4*(B S lam u)^4 := by
  have hh := pow_le_pow_left₀ (Real.rpow_nonneg hz.le (1/4:ℝ))
    (endpoint_root_bound hl0 hl1 hu hu1 hz hzS hS hit) 4
  rw [BootstrapInterval.quarter_fourth _ hz.le,mul_pow] at hh
  exact hh

theorem endpoint_exception_bound {lam z S u E : ℝ} (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1/3)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hz : 0 < z) (hzS : z ≤ S) (hS : S ≤ 1/8)
    (hit : normalizedInequality lam z u) (hE : E ≤ z^(3/2:ℝ)*h0 u) :
    E ≤ lam^6*(B S lam u)^6*h0 u := by
  have hh := pow_le_pow_left₀ (Real.rpow_nonneg hz.le (1/4:ℝ))
    (endpoint_root_bound hl0 hl1 hu hu1 hz hzS hS hit) 6
  have hp : (z^(1/4:ℝ))^6=z^(3/2:ℝ) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hz.le]
    norm_num
  rw [hp,mul_pow] at hh
  have h0nonneg : 0 ≤ h0 u := by
    exact add_nonneg (Real.rpow_nonneg hu _) (Real.rpow_nonneg (by linarith) _)
  exact hE.trans (mul_le_mul_of_nonneg_right hh h0nonneg)

end LonelyRunnerNew.LCDirection
