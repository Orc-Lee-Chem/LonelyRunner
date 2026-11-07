import LonelyRunnerNew.SaturatedPsiIntegral
import LonelyRunnerNew.LabelRankCounting

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew.Saturated

theorem grid_average (a : ℕ) (ha : 0<a) (g : ℝ → ℝ)
    (hg : AntitoneOn g (Set.Icc (0:ℝ) 1)) :
    (∑ i∈Finset.range a,g (((i:ℝ)+1)/(a:ℝ)))≤(a:ℝ)*(∫u in (0:ℝ)..1,g u) := by
  have haR : (0:ℝ)<a := by exact_mod_cast ha
  have hh : AntitoneOn (fun u : ℝ => g (u/(a:ℝ))) (Set.Icc (0:ℝ) (0+a)) := by
    intro x hx y hy hxy
    have hmem {z : ℝ} (hz : z∈Set.Icc (0:ℝ) (0+a)) : z/(a:ℝ)∈Set.Icc (0:ℝ) 1 :=
      ⟨div_nonneg hz.1 haR.le,(div_le_one haR).mpr (by simpa using hz.2)⟩
    exact hg (hmem hx) (hmem hy) (div_le_div_of_nonneg_right hxy haR.le)
  have hb := hh.sum_le_integral
  simp only [zero_add] at hb
  have he : (∫u in (0:ℝ)..(a:ℝ),g (u/(a:ℝ)))=
      (a:ℝ)*(∫u in (0:ℝ)..1,g u) := by
    simpa only [zero_div,div_self haR.ne',smul_eq_mul] using
      (intervalIntegral.integral_comp_div (f:=g) (a:=0) (b:=(a:ℝ)) haR.ne')
  rw [he] at hb
  simpa only [Nat.cast_add,Nat.cast_one] using hb

theorem double_grid_bound (a b : ℕ) (ha : 0<a) (hb : 0<b) {t : ℝ} (ht : 0<t) :
    (∑ i∈Finset.range a,∑ j∈Finset.range b,
      cap t ((((i:ℝ)+1)/(a:ℝ))*(((j:ℝ)+1)/(b:ℝ))))≤(a:ℝ)*(b:ℝ)*Psi t := by
  have haR : (0:ℝ)<a := by exact_mod_cast ha
  have hbR : (0:ℝ)<b := by exact_mod_cast hb
  rw [Finset.sum_comm]
  have hrow (j : ℕ) (hj : j∈Finset.range b) :
      (∑ i∈Finset.range a,cap t ((((i:ℝ)+1)/(a:ℝ))*(((j:ℝ)+1)/(b:ℝ))))≤
        (a:ℝ)*inner t (((j:ℝ)+1)/(b:ℝ)) := by
    apply grid_average a ha (fun u : ℝ => cap t (u*(((j:ℝ)+1)/(b:ℝ))))
    intro x hx y hy hxy
    exact cap_antitone ht (mul_le_mul_of_nonneg_right hxy (by positivity))
  have hsum := Finset.sum_le_sum hrow
  rw [←Finset.mul_sum] at hsum
  have hinner := grid_average b hb (inner t) ((inner_antitone ht).mono (fun _ hx => hx.1))
  have hh := mul_le_mul_of_nonneg_left hinner haR.le
  rw [integral_inner ht] at hh
  exact hsum.trans (by convert hh using 1 <;> ring)

theorem cap_rescale {c K : ℝ} (hK : 0<K) (x : ℝ) :
    cap c (K*x)=cap (c/Real.sqrt K) x := by
  have hs : 0<Real.sqrt K := Real.sqrt_pos.mpr hK
  have hs2 := Real.sq_sqrt hK.le
  have hfirst : K*(c/Real.sqrt K)^2=c^2 := by rw [div_pow,hs2];field_simp
  have hmax : max (c^2) (K*x)=K*max ((c/Real.sqrt K)^2) x := by
    rw [mul_max_of_nonneg _ _ hK.le,hfirst]
  simp only [cap]
  rw [hmax,Real.sqrt_mul hK.le]
  ring

end LonelyRunnerNew.Saturated
