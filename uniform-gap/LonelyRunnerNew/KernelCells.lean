import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace LonelyRunnerNew.KernelCells

def cellIntegral (a d : ℝ) : ℝ :=
  ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, Real.exp (-a*|d+y-x|)

theorem integral_exp_linear (c l r : ℝ) (hc : c ≠ 0) :
    (∫ x in l..r, Real.exp (c*x)) = (Real.exp (c*r)-Real.exp (c*l))/c := by
  rw [intervalIntegral.integral_comp_mul_left Real.exp hc, integral_exp]
  simp only [smul_eq_mul]
  ring

theorem off_diagonal_cell (a d : ℝ) (ha : 0 < a) (hd : 1 ≤ d) :
    cellIntegral a d = Real.exp (-a*d) *
      ((Real.exp a-1)*(1-Real.exp (-a))/a^2) := by
  have hn : -a ≠ 0 := neg_ne_zero.mpr ha.ne'
  have inner (x : ℝ) (hx : x ∈ Set.uIcc (0:ℝ) 1) :
      (∫ y in (0:ℝ)..1, Real.exp (-a*|d+y-x|)) =
      (Real.exp (-a*d)*Real.exp (a*x))*((Real.exp (-a)-1)/(-a)) := by
    have hx' : 0 ≤ x ∧ x ≤ 1 := by simpa using hx
    have hev : (∫ y in (0:ℝ)..1, Real.exp (-a*y)) = (Real.exp (-a)-1)/(-a) := by
      simpa using integral_exp_linear (-a) 0 1 hn
    rw [← hev]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro y hy
    dsimp only
    have hy' : 0 ≤ y ∧ y ≤ 1 := by simpa using hy
    rw [abs_of_nonneg (by linarith : 0 ≤ d+y-x), ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  unfold cellIntegral
  rw [intervalIntegral.integral_congr inner]
  calc
    (∫ x in (0:ℝ)..1, (Real.exp (-a*d)*Real.exp (a*x))*((Real.exp (-a)-1)/(-a))) =
        (Real.exp (-a*d)*((Real.exp (-a)-1)/(-a)))*(∫ x in (0:ℝ)..1, Real.exp (a*x)) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro x hx
      ring
    _ = _ := by rw [integral_exp_linear a 0 1 ha.ne']; simp; field_simp; ring

/-- Exact coefficient conversion; no scalar norm bound is assumed. -/
theorem off_diagonal_coefficient (a : ℝ) :
    (Real.exp a-1)*(1-Real.exp (-a))/a^2 =
      (1-Real.exp (-a))^2/(Real.exp (-a)*a^2) := by
  rw [Real.exp_neg]
  have he := (Real.exp_pos a).ne'
  field_simp

theorem diagonal_cell (a : ℝ) (ha : 0 < a) :
    cellIntegral a 0 = 2*(a-1+Real.exp (-a))/a^2 := by
  have hn : -a ≠ 0 := neg_ne_zero.mpr ha.ne'
  have inner (x : ℝ) (hx : x ∈ Set.uIcc (0:ℝ) 1) :
      (∫ y in (0:ℝ)..1, Real.exp (-a*|y-x|)) =
      (2-Real.exp (-a*x)-Real.exp (-a)*Real.exp (a*x))/a := by
    have hx' : 0 ≤ x ∧ x ≤ 1 := by simpa using hx
    have hc : Continuous (fun y : ℝ => Real.exp (-a*|y-x|)) := by fun_prop
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable 0 x) (hc.intervalIntegrable x 1)]
    have hl : (∫ y in (0:ℝ)..x, Real.exp (-a*|y-x|)) =
        Real.exp (-a*x)*((Real.exp (a*x)-1)/a) := by
      have hev : (∫ y in (0:ℝ)..x, Real.exp (a*y)) = (Real.exp (a*x)-1)/a := by
        simpa using integral_exp_linear a 0 x ha.ne'
      rw [← hev, ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro y hy
      dsimp only
      have hy' : 0 ≤ y ∧ y ≤ x := by simpa [Set.uIcc_of_le hx'.1] using hy
      rw [abs_of_nonpos (by linarith : y-x ≤ 0), ← Real.exp_add]
      congr 1
      ring
    have hr : (∫ y in x..(1:ℝ), Real.exp (-a*|y-x|)) =
        Real.exp (a*x)*((Real.exp (-a)-Real.exp (-a*x))/(-a)) := by
      have hev : (∫ y in x..(1:ℝ), Real.exp (-a*y)) =
          (Real.exp (-a)-Real.exp (-a*x))/(-a) := by
        simpa using integral_exp_linear (-a) x 1 hn
      rw [← hev, ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro y hy
      dsimp only
      have hy' : x ≤ y ∧ y ≤ 1 := by simpa [Set.uIcc_of_le hx'.2] using hy
      rw [abs_of_nonneg (by linarith : 0 ≤ y-x), ← Real.exp_add]
      congr 1
      ring
    rw [hl, hr]
    have hprod : Real.exp (-a*x)*Real.exp (a*x) = 1 := by
      rw [← Real.exp_add, show -a*x+a*x=0 by ring, Real.exp_zero]
    simp only [neg_mul] at hprod
    field_simp
    nlinarith only [hprod]
  unfold cellIntegral
  simp only [zero_add]
  rw [intervalIntegral.integral_congr inner]
  have heval : (∫ x in (0:ℝ)..1,
      (2-Real.exp (-a*x)-Real.exp (-a)*Real.exp (a*x))/a) =
      (2-(∫ x in (0:ℝ)..1, Real.exp (-a*x))-
        Real.exp (-a)*(∫ x in (0:ℝ)..1, Real.exp (a*x)))/a := by
    rw [intervalIntegral.integral_div,
      intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
        (by apply Continuous.intervalIntegrable; fun_prop),
      intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
        (by apply Continuous.intervalIntegrable; fun_prop),
      intervalIntegral.integral_const_mul]
    simp
  rw [heval, integral_exp_linear (-a) 0 1 hn, integral_exp_linear a 0 1 ha.ne']
  simp only [mul_one, mul_zero, Real.exp_zero]
  have hprod : Real.exp (-a)*Real.exp a = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  field_simp
  nlinarith only [hprod]

def A (a : ℝ) : ℝ := (1-Real.exp (-a))^2/(Real.exp (-a)*a^2)
def D (a : ℝ) : ℝ := 2*(a-1+Real.exp (-a))/a^2

theorem A_pos (a : ℝ) (ha : 0 < a) : 0 < A a := by
  have hl : Real.exp (-a) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  exact div_pos (sq_pos_of_pos (by linarith))
    (mul_pos (Real.exp_pos _) (sq_pos_of_pos ha))

theorem cell_entry (a : ℝ) (ha : 0 < a) (d : ℕ) :
    cellIntegral a d = A a*(Real.exp (-a))^d + (if d=0 then D a-A a else 0) := by
  by_cases hd : d=0
  · subst d
    rw [Nat.cast_zero, diagonal_cell a ha]
    simp [D]
  · have hdR : (1:ℝ)≤d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd
    rw [off_diagonal_cell a d ha hdR, off_diagonal_coefficient, ite_eq_right hd, add_zero]
    have he : Real.exp (-a*(d:ℝ)) = Real.exp (-a)^d := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [he]
    unfold A
    ring

/-- Exact unit-cell identity with the diagonal term retained. -/
theorem bilinear_cell_identity (a : ℝ) (ha : 0 < a) (F : Finset ℤ) (x y : ℤ → ℝ) :
    (∑ i ∈ F, ∑ j ∈ F, cellIntegral a ((i-j).natAbs:ℝ)*x i*y j) =
      A a*(∑ i ∈ F, ∑ j ∈ F, Real.exp (-a)^(i-j).natAbs*x i*y j) +
      (D a-A a)*(∑ i ∈ F, x i*y i) := by
  have entry (i j : ℤ) : cellIntegral a ((i-j).natAbs:ℝ)*x i*y j =
      A a*(Real.exp (-a)^(i-j).natAbs*x i*y j)+
        (D a-A a)*(if i=j then x i*y j else 0) := by
    rw [cell_entry a ha]
    by_cases hij : i=j
    · subst j
      simp
      ring
    · have hd : (i-j).natAbs ≠ 0 := by
        intro h
        exact hij (sub_eq_zero.mp (Int.natAbs_eq_zero.mp h))
      simp only [ite_eq_right hd, ite_eq_right hij]
      ring
  simp_rw [entry, Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  apply congrArg ((D a-A a) * ·)
  apply Finset.sum_congr rfl
  intro i hi
  simp [hi]

/-- Discrete correction obtained from a *bilinear cell* bound, not from the
coarse kernelInput. The sharp continuous estimate remains a separate obligation. -/
theorem refined_of_cell_bound (a B : ℝ) (ha : 0 < a) (F : Finset ℤ) (x y : ℤ → ℝ)
    (hcell : (∑ i ∈ F, ∑ j ∈ F,
      cellIntegral a ((i-j).natAbs:ℝ)*x i*y j) ≤ B) :
    (∑ i ∈ F, ∑ j ∈ F, Real.exp (-a)^(i-j).natAbs*x i*y j) ≤
      B/A a + (1-D a/A a)*(∑ i ∈ F, x i*y i) := by
  rw [bilinear_cell_identity a ha F x y] at hcell
  have he : B/A a+(1-D a/A a)*(∑ i ∈ F,x i*y i) =
      (B+(A a-D a)*(∑ i ∈ F,x i*y i))/A a := by
    field_simp [(A_pos a ha).ne']
    <;> ring
  rw [he]
  exact (le_div_iff₀ (A_pos a ha)).mpr (by nlinarith only [hcell])

theorem correction_coefficient (a : ℝ) (ha : 0 < a) :
    1-D a/A a = 1-2*Real.exp (-a)*(a-1+Real.exp (-a))/(1-Real.exp (-a))^2 := by
  have hl : 0 < 1-Real.exp (-a) := by
    have h := Real.exp_lt_one_iff.mpr (neg_neg_of_pos ha)
    linarith
  unfold A D
  field_simp [ha.ne', hl.ne', (Real.exp_pos (-a)).ne']
  <;> ring

theorem continuous_constant_div_A (a : ℝ) (ha : 0 < a) :
    ((Real.sqrt 3/2)*a^(-1/2:ℝ))/A a =
      (Real.sqrt 3/2)*Real.exp (-a)*a^(3/2:ℝ)/(1-Real.exp (-a))^2 := by
  have hl : 0 < 1-Real.exp (-a) := by
    have h := Real.exp_lt_one_iff.mpr (neg_neg_of_pos ha)
    linarith
  have hp : a^(-1/2:ℝ)*a^2=a^(3/2:ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add ha]
    norm_num
  unfold A
  field_simp [ha.ne', hl.ne', (Real.exp_pos (-a)).ne']
  rw [← hp]
  ring

theorem enhanced_kernel_of_cell_bound (a : ℝ) (ha : 0 < a)
    (F : Finset ℤ) (x y : ℤ → ℝ)
    (hcell : (∑ i ∈ F, ∑ j ∈ F,
      cellIntegral a ((i-j).natAbs:ℝ)*x i*y j) ≤ (Real.sqrt 3/2)*a^(-1/2:ℝ)) :
    (∑ i ∈ F, ∑ j ∈ F, Real.exp (-a)^(i-j).natAbs*x i*y j) ≤
      (Real.sqrt 3/2)*Real.exp (-a)*a^(3/2:ℝ)/(1-Real.exp (-a))^2 +
      (1-2*Real.exp (-a)*(a-1+Real.exp (-a))/(1-Real.exp (-a))^2)*
        (∑ i ∈ F,x i*y i) := by
  have h := refined_of_cell_bound a _ ha F x y hcell
  rw [continuous_constant_div_A a ha, correction_coefficient a ha] at h
  exact h

theorem A_sub_D (a : ℝ) (ha : 0 < a) :
    A a-D a = (Real.exp a-Real.exp (-a)-2*a)/a^2 := by
  unfold A D
  rw [← off_diagonal_coefficient]
  have hprod : Real.exp a*Real.exp (-a)=1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  field_simp [ha.ne']
  nlinarith only [hprod]

theorem correction_positive (a : ℝ) (ha : 0 < a) : 0 < 1-D a/A a := by
  have hs := Real.self_lt_sinh_iff.mpr ha
  rw [Real.sinh_eq] at hs
  have hdiff : 0 < A a-D a := by
    rw [A_sub_D a ha]
    exact div_pos (by linarith) (sq_pos_of_pos ha)
  have he : 1-D a/A a = (A a-D a)/A a := by field_simp [(A_pos a ha).ne']
  rw [he]
  exact div_pos hdiff (A_pos a ha)

/-- Reflection of a unit interval, including its actual endpoint convention. -/
theorem unit_reflection (f : ℝ → ℝ) :
    (∫ x in (0:ℝ)..1, f (1-x)) = ∫ x in (0:ℝ)..1, f x := by
  simpa using intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := (1:ℝ)) f 1

theorem cellIntegral_neg (a d : ℝ) : cellIntegral a (-d) = cellIntegral a d := by
  unfold cellIntegral
  calc
    (∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, Real.exp (-a*|-d+y-x|)) =
        ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, Real.exp (-a*|-d+y-(1-x)|) :=
      (unit_reflection _).symm
    _ = ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, Real.exp (-a*|-d+(1-y)-(1-x)|) := by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp only
      exact (unit_reflection _).symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro x hx
      apply intervalIntegral.integral_congr
      intro y hy
      dsimp only
      rw [show -d+(1-y)-(1-x)=-(d+y-x) by ring, abs_neg]

theorem cellIntegral_abs (a d : ℝ) : cellIntegral a |d| = cellIntegral a d := by
  by_cases hd : 0 ≤ d
  · rw [abs_of_nonneg hd]
  · rw [abs_of_neg (lt_of_not_ge hd), cellIntegral_neg]

theorem translated_cell (a i j : ℝ) :
    (∫ x in i..i+1, ∫ y in j..j+1, Real.exp (-a*|x-y|)) = cellIntegral a |j-i| := by
  have shift (f : ℝ → ℝ) (c : ℝ) :
      (∫ x in c..c+1,f x) = ∫ u in (0:ℝ)..1,f (c+u) := by
    simpa using (intervalIntegral.integral_comp_add_left (a := (0:ℝ)) (b := (1:ℝ)) f c).symm
  rw [shift]
  calc
    (∫ x in (0:ℝ)..1, ∫ y in j..j+1, Real.exp (-a*|i+x-y|)) =
        ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, Real.exp (-a*|i+x-(j+y)|) := by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp only
      exact shift _ j
    _ = cellIntegral a (j-i) := by
      unfold cellIntegral
      apply intervalIntegral.integral_congr
      intro x hx
      apply intervalIntegral.integral_congr
      intro y hy
      dsimp only
      rw [show i+x-(j+y) = -(j-i+y-x) by ring, abs_neg]
    _ = _ := (cellIntegral_abs a (j-i)).symm

theorem integer_translated_cell (a : ℝ) (i j : ℤ) :
    (∫ x in (i:ℝ)..(i:ℝ)+1, ∫ y in (j:ℝ)..(j:ℝ)+1,
      Real.exp (-a*|x-y|)) = cellIntegral a ((i-j).natAbs:ℝ) := by
  rw [translated_cell]
  congr 1
  rw [Nat.cast_natAbs, Int.cast_abs, Int.cast_sub, abs_sub_comm]

end LonelyRunnerNew.KernelCells
