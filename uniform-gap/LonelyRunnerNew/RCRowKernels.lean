import LonelyRunnerNew.UnimodalGrid
import Mathlib.Topology.Order.Lattice

noncomputable section
set_option autoImplicit false
namespace LonelyRunnerNew.RoughRational.RowKernels

def cap (R T x : ℝ) : ℝ := min (2*R*x) (T/x)
def gap (R T x : ℝ) : ℝ := cap R T x-R*x
def switch (B : ℝ) : ℝ := B/Real.sqrt 2

theorem switch_geometry {R T B : ℝ} (hR : 0<R) (hB : 0<B) (hBT : R*B^2=T) :
    0<switch B ∧ switch B≤B ∧ 2*R*(switch B)^2=T := by
  have hs : 0<Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hs1 : (1:ℝ)≤Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg (2:ℝ)]
  refine ⟨div_pos hB hs,?_,?_⟩
  · exact (div_le_self hB.le hs1)
  · unfold switch
    rw [div_pow,hsq]
    nlinarith [hBT]

theorem cap_small {R T B x : ℝ} (hR : 0<R) (hB : 0<B) (hBT : R*B^2=T)
    (hx : 0≤x) (hxc : x≤switch B) : cap R T x=2*R*x := by
  by_cases hz : x=0
  · simp [cap,hz]
  have hx0 : 0<x := lt_of_le_of_ne hx (Ne.symm hz)
  have hg := switch_geometry hR hB hBT
  apply min_eq_left
  apply (le_div_iff₀ hx0).mpr
  have hsq := (sq_le_sq₀ hx hg.1.le).mpr hxc
  nlinarith [mul_le_mul_of_nonneg_left hsq hR.le]

theorem cap_large {R T B x : ℝ} (hR : 0<R) (hB : 0<B) (hBT : R*B^2=T)
    (hcx : switch B≤x) : cap R T x=T/x := by
  have hg := switch_geometry hR hB hBT
  have hx0 : 0<x := hg.1.trans_le hcx
  apply min_eq_right
  apply (div_le_iff₀ hx0).mpr
  have hsq := (sq_le_sq₀ hg.1.le hx0.le).mpr hcx
  nlinarith [mul_le_mul_of_nonneg_left hsq hR.le]

theorem nonneg {R T B x : ℝ} (hR : 0<R) (hB : 0<B) (hBT : R*B^2=T)
    (hx : x∈Set.Icc 0 B) : 0≤cap R T x ∧ 0≤gap R T x := by
  have hT : 0<T := hBT ▸ mul_pos hR (sq_pos_of_pos hB)
  have hc : 0≤cap R T x := le_min (by nlinarith [hx.1]) (div_nonneg hT.le hx.1)
  refine ⟨hc,?_⟩
  by_cases hz : x=0
  · simp [gap,cap,hz]
  have hx0 : 0<x := lt_of_le_of_ne hx.1 (Ne.symm hz)
  unfold gap cap
  apply sub_nonneg.mpr
  apply le_min
  · nlinarith [mul_nonneg hR.le hx.1]
  · apply (le_div_iff₀ hx0).mpr
    have hsq := (sq_le_sq₀ hx.1 hB.le).mpr hx.2
    nlinarith [mul_le_mul_of_nonneg_left hsq hR.le]

theorem upper {R T B x : ℝ} (hR : 0<R) (hB : 0<B) (hBT : R*B^2=T)
    (hx : x∈Set.Icc 0 B) : cap R T x≤2*R*switch B ∧ gap R T x≤R*switch B := by
  have hg := switch_geometry hR hB hBT
  have hT : 0<T := hBT ▸ mul_pos hR (sq_pos_of_pos hB)
  have hTc : T/switch B=2*R*switch B := (div_eq_iff hg.1.ne').mpr (by nlinarith [hg.2.2])
  by_cases hxc : x≤switch B
  · rw [cap_small hR hB hBT hx.1 hxc]
    have hgap : gap R T x=R*x := by rw [gap,cap_small hR hB hBT hx.1 hxc];ring
    rw [hgap]
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hxc hR.le]
  · have hcx := (lt_of_not_ge hxc).le
    have hx0 : 0<x := hg.1.trans_le hcx
    have hdiv : T/x≤T/switch B := div_le_div_of_nonneg_left hT.le hg.1 hcx
    rw [cap_large hR hB hBT hcx]
    have hgap : gap R T x=T/x-R*x := by rw [gap,cap_large hR hB hBT hcx]
    rw [hgap,hTc] at *
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hcx hR.le]

theorem cap_continuous {R T a b : ℝ} (ha : 0<a) : ContinuousOn (cap R T) (Set.Icc a b) := by
  apply ContinuousOn.inf
  · exact (continuous_const.mul continuous_id).continuousOn
  · exact continuousOn_const.div continuousOn_id (fun x hx => (ha.trans_le hx.1).ne')

theorem gap_continuous {R T a b : ℝ} (ha : 0<a) : ContinuousOn (gap R T) (Set.Icc a b) :=
  (cap_continuous ha).sub (continuous_const.mul continuous_id).continuousOn

theorem cap_between {R T B : ℝ} (hR : 0<R) (hB : 0<B) (hBT : R*B^2=T) :
    UnimodalGrid.BetweenLower (cap R T) 0 B := by
  intro x hx z hz y hxy hyz
  have hy : y∈Set.Icc 0 B := ⟨hx.1.trans hxy,hyz.trans hz.2⟩
  by_cases hx0 : x=0
  · have he : cap R T x=0 := by simp [cap,hx0]
    exact (min_le_left _ _).trans (he.le.trans (nonneg hR hB hBT hy).1)
  have hxpos : 0<x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
  have hypos : 0<y := hxpos.trans_le hxy
  have hT : 0<T := hBT ▸ mul_pos hR (sq_pos_of_pos hB)
  apply le_min
  · have hh : cap R T x≤2*R*x := min_le_left _ _
    have hm := mul_le_mul_of_nonneg_left hxy (by positivity : (0:ℝ)≤2*R)
    exact (min_le_left _ _).trans (hh.trans hm)
  · have hh : cap R T z≤T/z := min_le_right _ _
    have hm := div_le_div_of_nonneg_left hT.le hypos hyz
    exact (min_le_right _ _).trans (hh.trans hm)

theorem gap_between {R T B : ℝ} (hR : 0<R) (hB : 0<B) (hBT : R*B^2=T) :
    UnimodalGrid.BetweenLower (gap R T) 0 B := by
  intro x hx z hz y hxy hyz
  have hy : y∈Set.Icc 0 B := ⟨hx.1.trans hxy,hyz.trans hz.2⟩
  by_cases hx0 : x=0
  · have he : gap R T x=0 := by simp [gap,cap,hx0]
    exact (min_le_left _ _).trans (he.le.trans (nonneg hR hB hBT hy).2)
  have hxpos : 0<x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
  have hypos : 0<y := hxpos.trans_le hxy
  have hT : 0<T := hBT ▸ mul_pos hR (sq_pos_of_pos hB)
  have hleft : min (gap R T x) (gap R T z)≤R*y := by
    have hh : gap R T x≤R*x := by
      have hh : cap R T x≤2*R*x := min_le_left _ _
      unfold gap;linarith
    exact (min_le_left _ _).trans (hh.trans (mul_le_mul_of_nonneg_left hxy hR.le))
  have hright : min (gap R T x) (gap R T z)≤T/y-R*y := by
    have hh : gap R T z≤T/z-R*z := sub_le_sub_right (min_le_right _ _) _
    have hm := div_le_div_of_nonneg_left hT.le hypos hyz
    have hr := mul_le_mul_of_nonneg_left hyz hR.le
    exact (min_le_right _ _).trans (hh.trans (by linarith))
  change min (gap R T x) (gap R T z)≤cap R T y-R*y
  apply (le_sub_iff_add_le).mpr
  change min (gap R T x) (gap R T z)+R*y≤min (2*R*y) (T/y)
  exact le_min (by linarith) (by linarith)

end LonelyRunnerNew.RoughRational.RowKernels
