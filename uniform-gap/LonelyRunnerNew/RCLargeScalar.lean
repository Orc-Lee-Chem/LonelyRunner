import LonelyRunnerNew.RCPhysicalRows
import LonelyRunnerNew.AsymmetricBudgets

noncomputable section
set_option autoImplicit false
namespace LonelyRunnerNew.RoughRational

theorem large_main_scalar {ell T B : ℝ} (he : 0<ell) (hT : 0<T) (hB : 128≤B) :
    (ell/T)*((T*Real.log 2/6+2*T/(Real.sqrt 2*B)+
      (T*(1+Real.log 2)/6+2*Real.sqrt 2*T/B)/143)/((1/5:ℝ)*ell))≤
      (5/3:ℝ)*(7/20+17/(20*143))+(10/128:ℝ)*(1+3/(2*143)) := by
  have hb0 : 0<B := by linarith
  have hs : 0<Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hs1 : (1:ℝ)≤Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg (2:ℝ)]
  have hs15 : Real.sqrt 2≤(3/2:ℝ) := by nlinarith [Real.sqrt_nonneg (2:ℝ)]
  have hident : (ell/T)*((T*Real.log 2/6+2*T/(Real.sqrt 2*B)+
      (T*(1+Real.log 2)/6+2*Real.sqrt 2*T/B)/143)/((1/5:ℝ)*ell))=
      (5/6:ℝ)*(Real.log 2+(1+Real.log 2)/143)+(10/B)*(1/Real.sqrt 2+Real.sqrt 2/143) := by
    field_simp <;> ring
  rw [hident]
  have hlog := RoughRow.log_two_lt.le
  have hmain : (5/6:ℝ)*(Real.log 2+(1+Real.log 2)/143)≤
      (5/3:ℝ)*(7/20+17/(20*143)) := by nlinarith
  have hInv : 1/Real.sqrt 2≤(1:ℝ) := (div_le_one₀ hs).mpr hs1
  have hK : 1/Real.sqrt 2+Real.sqrt 2/143≤1+3/(2*143:ℝ) := by
    have h := div_le_div_of_nonneg_right hs15 (by norm_num : (0:ℝ)≤143)
    norm_num at h
    linarith
  have h10 : 10/B≤10/(128:ℝ) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hB
  have hm := mul_le_mul h10 hK (by positivity : (0:ℝ)≤1/Real.sqrt 2+Real.sqrt 2/143)
    (by norm_num : (0:ℝ)≤10/128)
  linarith

theorem large_screen_scalar {R T ell : ℝ} (hR : 0<R) (hT : 0<T) (he : 0<ell)
    (hRn : 1/Real.sqrt 2≤R) (hlarge : Real.exp ell<Real.sqrt 2*T) :
    (ell/T)*(Real.sqrt (T/R)*(32*Real.exp ((2/5:ℝ)*ell)/((1/5:ℝ)*ell)^2))≤
      (1200/ell)*Real.exp (-ell/10) := by
  let B := Real.sqrt (T/R)
  have hb := normalized_root_ratio hR hT hRn hlarge
  have hposB : 0<B := (physical_root hR hT).1
  have hs := Real.sqrt_nonneg (2:ℝ)
  have hsq := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hs15 : Real.sqrt 2≤(3/2:ℝ) := by nlinarith
  have hident : (ell/T)*(B*(32*Real.exp ((2/5:ℝ)*ell)/((1/5:ℝ)*ell)^2))=
      (800/ell)*((B/T)*Real.exp ((2/5:ℝ)*ell)) := by field_simp <;> ring
  change (ell/T)*(B*(32*Real.exp ((2/5:ℝ)*ell)/((1/5:ℝ)*ell)^2))≤_
  rw [hident]
  calc
    _ ≤ (800/ell)*((Real.sqrt 2*Real.exp (-ell/2))*Real.exp ((2/5:ℝ)*ell)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb (Real.exp_nonneg _)) (by positivity)
    _ =(800*Real.sqrt 2/ell)*Real.exp (-ell/10) := by
      rw [mul_assoc (Real.sqrt 2),←Real.exp_add,show -ell/2+(2/5:ℝ)*ell=-ell/10 by ring]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      apply div_le_div_of_nonneg_right _ he.le
      nlinarith

end LonelyRunnerNew.RoughRational
