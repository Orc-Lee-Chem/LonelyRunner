import LonelyRunnerNew.PhysicalSaturatedWeight

noncomputable section
set_option autoImplicit false
namespace LonelyRunnerNew.PhysicalState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

def normalizedFourth (s : PhysicalState Label n) : ℝ :=
  (s.density^4*s.geometry.area)/(n:ℝ)^2

theorem ordinary_quality_product (s : PhysicalState Label n) (hM : 0<s.edgeMass) :
    s.quality q sigma=s.quality 4 0*(s.normalizedFourth)^sigma := by
  rw [ordinary_quality_formula s hM,universal_quality_formula]
  rfl

theorem area_le_ambient (s : PhysicalState Label n) : s.geometry.area≤(n:ℝ)^2 := by
  have hn := Nat.mul_le_mul s.geometry.left_budget s.geometry.right_budget
  rw [←pow_two] at hn
  unfold TaggedState.area
  exact_mod_cast hn

theorem normalizedFourth_nonneg (s : PhysicalState Label n) : 0≤s.normalizedFourth := by
  exact div_nonneg (mul_nonneg (pow_nonneg s.density_nonneg _) s.geometry.area_pos.le) (sq_nonneg _)

theorem normalizedFourth_le_one (s : PhysicalState Label n) : s.normalizedFourth≤1 := by
  have hr : s.density^4≤1 := by simpa using pow_le_pow_left₀ s.density_nonneg s.density_le_one 4
  apply (div_le_one (sq_pos_of_pos s.geometry.ambient_pos)).mpr
  exact (mul_le_mul_of_nonneg_right hr s.geometry.area_pos.le).trans (by simpa using s.area_le_ambient)

theorem ordinary_quality_le_fourth (s : PhysicalState Label n) (hM : 0<s.edgeMass) :
    s.quality q sigma≤s.quality 4 0 := by
  rw [ordinary_quality_formula s hM,←universal_quality_formula]
  change s.quality 4 0*(s.normalizedFourth)^sigma≤s.quality 4 0
  have hpow := Real.rpow_le_rpow s.normalizedFourth_nonneg s.normalizedFourth_le_one
    (by norm_num [sigma] : (0:ℝ)≤sigma)
  simp only [Real.one_rpow] at hpow
  have hq0 : 0≤s.quality 4 0 := (s.quality_pos_iff_mass (by norm_num : (0:ℝ)<4)).2 hM |>.le
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow hq0

theorem min_size_absorption {rho a b : ℝ} (hr : 0≤rho) (ha : 0<a) (hb : 0<b)
    (hlarge : 2/((27/50:ℝ)*(1/1000))≤min (rho*a) (rho*b)) :
    a+b≤(27/50:ℝ)*(1/1000)*rho*(a*b) := by
  have hl := hlarge.trans (min_le_left _ _)
  have hr' := hlarge.trans (min_le_right _ _)
  norm_num at hl hr' ⊢
  have h1 := mul_le_mul_of_nonneg_right hl hb.le
  have h2 := mul_le_mul_of_nonneg_right hr' ha.le
  nlinarith only [h1,h2]

theorem normalizedFourth_small (s : PhysicalState Label n)
    (hsmall : min (s.density*(s.geometry.left.card:ℝ)) (s.density*(s.geometry.right.card:ℝ))<
      2/((27/50:ℝ)*(1/1000))) :
    s.normalizedFourth≤2/((27/50:ℝ)*(1/1000)*(n:ℝ)) := by
  let H : ℝ := 2/((27/50:ℝ)*(1/1000))
  have hH : 0≤H := by norm_num [H]
  have hr3 : s.density^3≤1 := by simpa using pow_le_pow_left₀ s.density_nonneg s.density_le_one 3
  have hr4 : s.density^4≤s.density := by
    have hh := mul_le_mul_of_nonneg_left hr3 s.density_nonneg
    nlinarith only [hh]
  have hbase := mul_le_mul_of_nonneg_right hr4 s.geometry.area_pos.le
  have hleft : (s.geometry.left.card:ℝ)≤n := by exact_mod_cast s.geometry.left_budget
  have hright : (s.geometry.right.card:ℝ)≤n := by exact_mod_cast s.geometry.right_budget
  have hbound : s.density^4*s.geometry.area≤H*(n:ℝ) := by
    dsimp only [TaggedState.area,H]
    rcases min_lt_iff.mp hsmall with hl | hr
    · have hh := mul_le_mul hl.le hright (Nat.cast_nonneg _) hH
      unfold TaggedState.area at hbase
      nlinarith only [hbase,hh]
    · have hh := mul_le_mul hr.le hleft (Nat.cast_nonneg _) hH
      unfold TaggedState.area at hbase
      nlinarith only [hbase,hh]
  have hn := s.geometry.ambient_pos
  have heq : 2/((27/50:ℝ)*(1/1000)*(n:ℝ))=H/(n:ℝ) := by dsimp [H];ring
  rw [heq]
  unfold normalizedFourth
  apply (div_le_iff₀ (sq_pos_of_pos hn)).mpr
  have hc : (H/(n:ℝ))*(n:ℝ)^2=H*(n:ℝ) := by field_simp
  rwa [hc]

end LonelyRunnerNew.PhysicalState
