import LonelyRunnerNew.PeelingExponential

noncomputable section
set_option autoImplicit false
namespace LonelyRunnerNew.SmallPrimePeeling

theorem smooth_gcd_le_left (x y : ℕ) :
    (Nat.gcd (smoothPart x) (smoothPart y):ℝ)≤(smoothPart x:ℝ) := by
  exact_mod_cast Nat.le_of_dvd (smoothPart_pos x) (Nat.gcd_dvd_left _ _)
theorem smooth_gcd_le_right (x y : ℕ) :
    (Nat.gcd (smoothPart x) (smoothPart y):ℝ)≤(smoothPart y:ℝ) := by
  exact_mod_cast Nat.le_of_dvd (smoothPart_pos y) (Nat.gcd_dvd_right _ _)

theorem smooth_height_le_exp (x y : ℕ) :
    max (smoothPart x:ℝ) (smoothPart y:ℝ)/(Nat.gcd (smoothPart x) (smoothPart y):ℝ)≤
      Real.exp (smallDistance x y) := by
  rw [exp_smallDistance_ratio]
  have hg : (0:ℝ)<Nat.gcd (smoothPart x) (smoothPart y) := by
    exact_mod_cast Nat.gcd_pos_of_pos_left (smoothPart y) (smoothPart_pos x)
  have hm : max (smoothPart x:ℝ) (smoothPart y:ℝ)*(Nat.gcd (smoothPart x) (smoothPart y):ℝ)≤
      (smoothPart x:ℝ)*(smoothPart y:ℝ) := by
    rw [max_mul_of_nonneg _ _ hg.le]
    apply max_le
    · exact mul_le_mul_of_nonneg_left (smooth_gcd_le_right x y) (Nat.cast_nonneg _)
    · have h := mul_le_mul_of_nonneg_left (smooth_gcd_le_left x y) (Nat.cast_nonneg (smoothPart y): (0:ℝ)≤smoothPart y)
      simpa only [mul_comm] using h
  apply (div_le_div_iff₀ hg (sq_pos_of_pos hg)).mpr
  have hh := mul_le_mul_of_nonneg_right hm hg.le
  nlinarith only [hh]

theorem height_split_bound {x y : ℕ} (hx : 0<x) (hy : 0<y) :
    height x y≤(max (smoothPart x:ℝ) (smoothPart y:ℝ)/(Nat.gcd (smoothPart x) (smoothPart y):ℝ))*
      height (roughPart x) (roughPart y) := by
  have hg : (0:ℝ)<Nat.gcd (smoothPart x) (smoothPart y) := by
    exact_mod_cast Nat.gcd_pos_of_pos_left (smoothPart y) (smoothPart_pos x)
  have hr : (0:ℝ)<Nat.gcd (roughPart x) (roughPart y) := by
    exact_mod_cast Nat.gcd_pos_of_pos_left (roughPart y) (roughPart_pos x)
  have hex : (x:ℝ)=(smoothPart x:ℝ)*(roughPart x:ℝ) := by exact_mod_cast (smooth_rough_decomposition hx).symm
  have hey : (y:ℝ)=(smoothPart y:ℝ)*(roughPart y:ℝ) := by exact_mod_cast (smooth_rough_decomposition hy).symm
  have hm : max (x:ℝ) (y:ℝ)≤max (smoothPart x:ℝ) (smoothPart y:ℝ)*max (roughPart x:ℝ) (roughPart y:ℝ) := by
    rw [hex,hey]
    apply max_le
    · exact mul_le_mul (le_max_left _ _) (le_max_left _ _) (Nat.cast_nonneg _) (le_max_of_le_left (Nat.cast_nonneg _))
    · exact mul_le_mul (le_max_right _ _) (le_max_right _ _) (Nat.cast_nonneg _) (le_max_of_le_left (Nat.cast_nonneg _))
  unfold height
  rw [gcd_smooth_rough hx hy,Nat.cast_mul,Nat.cast_max,Nat.cast_max]
  have he : max (smoothPart x:ℝ) (smoothPart y:ℝ)/(Nat.gcd (smoothPart x) (smoothPart y):ℝ)*
      (max (roughPart x:ℝ) (roughPart y:ℝ)/(Nat.gcd (roughPart x) (roughPart y):ℝ))=
      (max (smoothPart x:ℝ) (smoothPart y:ℝ)*max (roughPart x:ℝ) (roughPart y:ℝ))/
        ((Nat.gcd (smoothPart x) (smoothPart y):ℝ)*(Nat.gcd (roughPart x) (roughPart y):ℝ)) := by ring
  rw [he]
  exact div_le_div_of_nonneg_right hm (mul_pos hg hr).le

theorem height_distortion {x y : ℕ} (hx : 0<x) (hy : 0<y) :
    height x y≤Real.exp (smallDistance x y)*height (roughPart x) (roughPart y) :=
  (height_split_bound hx hy).trans (mul_le_mul_of_nonneg_right (smooth_height_le_exp x y)
    (height_pos (roughPart_pos x)).le)

theorem denominator_comparison {a b : ℝ} (ha : 0<a) (hb : 0<b) {x y : ℕ} (hx : 0<x) (hy : 0<y) :
    (Nat.gcd (smoothPart x) (smoothPart y):ℝ)*max (a*(roughPart x:ℝ)) (b*(roughPart y:ℝ))≤
      max (a*(x:ℝ)) (b*(y:ℝ)) := by
  have hg : (0:ℝ)≤Nat.gcd (smoothPart x) (smoothPart y) := Nat.cast_nonneg _
  have hex : (x:ℝ)=(smoothPart x:ℝ)*(roughPart x:ℝ) := by exact_mod_cast (smooth_rough_decomposition hx).symm
  have hey : (y:ℝ)=(smoothPart y:ℝ)*(roughPart y:ℝ) := by exact_mod_cast (smooth_rough_decomposition hy).symm
  rw [mul_max_of_nonneg _ _ hg]
  apply max_le_max
  · calc
      _ ≤ (smoothPart x:ℝ)*(a*(roughPart x:ℝ)) := mul_le_mul_of_nonneg_right (smooth_gcd_le_left x y) (by positivity)
      _ = a*(x:ℝ) := by rw [hex];ring
  · calc
      _ ≤ (smoothPart y:ℝ)*(b*(roughPart y:ℝ)) := mul_le_mul_of_nonneg_right (smooth_gcd_le_right x y) (by positivity)
      _ = b*(y:ℝ) := by rw [hey];ring

theorem weight_le_rough {a b : ℝ} (ha : 0<a) (hb : 0<b) {x y : ℕ} (hx : 0<x) (hy : 0<y) :
    weight a b x y≤weight a b (roughPart x) (roughPart y) := by
  have hd1 : 0<max (a*(x:ℝ)) (b*(y:ℝ)) := lt_max_of_lt_left (mul_pos ha (by exact_mod_cast hx))
  have hd2 : 0<max (a*(roughPart x:ℝ)) (b*(roughPart y:ℝ)) :=
    lt_max_of_lt_left (mul_pos ha (by exact_mod_cast roughPart_pos x))
  have hden := denominator_comparison ha hb hx hy
  have hratio : (Nat.gcd x y:ℝ)/max (a*(x:ℝ)) (b*(y:ℝ))≤
      (Nat.gcd (roughPart x) (roughPart y):ℝ)/max (a*(roughPart x:ℝ)) (b*(roughPart y:ℝ)) := by
    rw [gcd_smooth_rough hx hy,Nat.cast_mul]
    apply (div_le_div_iff₀ hd1 hd2).mpr
    have h := mul_le_mul_of_nonneg_left hden (Nat.cast_nonneg (Nat.gcd (roughPart x) (roughPart y)) : (0:ℝ)≤_)
    simpa only [mul_assoc,mul_left_comm,mul_comm] using h
  exact min_le_min le_rfl hratio

end LonelyRunnerNew.SmallPrimePeeling
