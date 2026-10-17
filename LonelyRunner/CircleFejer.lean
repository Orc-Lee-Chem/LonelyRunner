import LonelyRunner.CircleMeasure
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace LonelyRunner

open MeasureTheory

private theorem norm_phase_sub_one (x : ℝ) :
    ‖Complex.exp (Complex.I * (2 * Real.pi * x : ℝ)) - 1‖ =
      2 * |Real.sin (Real.pi * x)| := by
  have h := Complex.norm_exp_I_mul_ofReal_sub_one (2 * Real.pi * x)
  calc
    _ = ‖(2 : ℝ) * Real.sin ((2 * Real.pi * x) / 2)‖ := by
      exact h
    _ = 2 * |Real.sin (Real.pi * x)| := by
      have heq : (2 * Real.pi * x) / 2 = Real.pi * x := by ring
      rw [heq]
      simp [Real.norm_eq_abs]

private theorem circleFourier_nat (j : ℕ) (t : UnitAddCircle) :
    fourier (j : ℤ) t = (fourier 1 t) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Nat.cast_succ, fourier_add, ih, pow_succ]

private theorem circleFourier_one_coe (x : ℝ) :
    fourier 1 (x : UnitAddCircle) =
      Complex.exp (Complex.I * (2 * Real.pi * x : ℝ)) := by
  rw [fourier_coe_apply]
  norm_num
  congr 1
  ring

private theorem sum_range_succ_shift (f : ℕ → ℂ) (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1), f k) =
      f 0 + ∑ j ∈ Finset.range N, f (j + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
      simp only [Finset.sum_range_succ]
      rw [Finset.sum_range_succ] at ih
      rw [ih]
      ring

/-- 论文式 (eq:orthogonality)，第 280–282 行：整数频率字符在归一化圆周 Haar 测度下正交。 -/
theorem integral_circleFourier (k : ℤ) :
    (∫ t : UnitAddCircle, fourier k t ∂circleHaar) = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · subst k
    simp
  · let c : UnitAddCircle := ((1 : ℝ) / 2 / (k : ℝ))
    have htr (t : UnitAddCircle) : fourier k (t + c) = -fourier k t := by
      simpa [c] using fourier_add_half_inv_index hk (by norm_num : (0 : ℝ) < 1) t
    have hi := MeasureTheory.integral_add_right_eq_self
      (μ := circleHaar) (fun t : UnitAddCircle => fourier k t) c
    simp_rw [htr, integral_neg] at hi
    simp only [if_neg hk]
    apply (mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0))
    calc
      (2 : ℂ) * (∫ t : UnitAddCircle, fourier k t ∂circleHaar) = 0 := by
        linear_combination -hi
      _ = (2 : ℂ) * 0 := by ring

/-- 论文引理 `lem:fejer` 第 285–287 行：前 `N` 个圆周 Fourier 字符之和。 -/
noncomputable def fejerCharacterSum (N : ℕ) (t : UnitAddCircle) : ℂ :=
  ∑ j ∈ Finset.range N, fourier (j : ℤ) t

private theorem fejerCharacterSum_coe (N : ℕ) (x : ℝ) :
    fejerCharacterSum N (x : UnitAddCircle) =
      ∑ j ∈ Finset.range N,
        (Complex.exp (Complex.I * (2 * Real.pi * x : ℝ))) ^ j := by
  unfold fejerCharacterSum
  simp_rw [circleFourier_nat, circleFourier_one_coe]

private theorem geomSum_phase_lower (N : ℕ) (x : ℝ) (hx : 0 < |x|)
    (hNx : (N : ℝ) * |x| ≤ 1 / 2) :
    2 * (N : ℝ) / Real.pi ≤
      ‖∑ j ∈ Finset.range N,
        (Complex.exp (Complex.I * (2 * Real.pi * x : ℝ))) ^ j‖ := by
  let z : ℂ := Complex.exp (Complex.I * (2 * Real.pi * x : ℝ))
  let S : ℂ := ∑ j ∈ Finset.range N, z ^ j
  have hgeom : S * (z - 1) = z ^ N - 1 := by
    exact geom_sum_mul z N
  have hnorm : ‖S‖ * ‖z - 1‖ = ‖z ^ N - 1‖ := by
    simpa [norm_mul] using congrArg norm hgeom
  have hden : ‖z - 1‖ ≤ 2 * Real.pi * |x| := by
    change ‖Complex.exp (Complex.I * (2 * Real.pi * x : ℝ)) - 1‖ ≤ _
    rw [norm_phase_sub_one]
    have hs := Real.abs_sin_le_abs (x := Real.pi * x)
    have habs : |Real.pi * x| = Real.pi * |x| := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
    rw [habs] at hs
    nlinarith
  have hexp : z ^ N =
      Complex.exp (Complex.I * (2 * Real.pi * (N : ℝ) * x : ℝ)) := by
    calc
      z ^ N = Complex.exp ((N : ℂ) *
          (Complex.I * (2 * Real.pi * x : ℝ))) := by
            exact (Complex.exp_nat_mul _ N).symm
      _ = _ := by
        congr 1
        push_cast
        ring
  have hangleEq : |Real.pi * (N : ℝ) * x| =
      Real.pi * (N : ℝ) * |x| := by
    rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos,
      abs_of_nonneg (Nat.cast_nonneg N)]
  have hangle : Real.pi * (N : ℝ) * |x| ≤ Real.pi / 2 := by
    have hpi := Real.pi_pos
    nlinarith [mul_le_mul_of_nonneg_left hNx hpi.le]
  have hsin : 2 * (N : ℝ) * |x| ≤
      |Real.sin (Real.pi * (N : ℝ) * x)| := by
    have harg : 0 ≤ Real.pi * (N : ℝ) * |x| := by positivity
    have h := Real.mul_le_sin harg hangle
    have heq : 2 / Real.pi * (Real.pi * (N : ℝ) * |x|) =
        2 * (N : ℝ) * |x| := by
      field_simp
    rw [heq] at h
    have heqsin : |Real.sin (Real.pi * (N : ℝ) * x)| =
        Real.sin (Real.pi * (N : ℝ) * |x|) := by
      rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi
        (by rw [hangleEq]; linarith [Real.pi_pos]), hangleEq]
    rwa [heqsin]
  have hnum : 4 * (N : ℝ) * |x| ≤ ‖z ^ N - 1‖ := by
    have hphase := norm_phase_sub_one ((N : ℝ) * x)
    have harg : 2 * Real.pi * ((N : ℝ) * x) =
        2 * Real.pi * (N : ℝ) * x := by ring
    rw [harg] at hphase
    rw [hexp, hphase]
    have hsinarg : Real.pi * ((N : ℝ) * x) =
        Real.pi * (N : ℝ) * x := by ring
    rw [hsinarg]
    nlinarith
  have hmain : 4 * (N : ℝ) * |x| ≤ ‖S‖ * (2 * Real.pi * |x|) := by
    calc
      _ ≤ ‖z ^ N - 1‖ := hnum
      _ = ‖S‖ * ‖z - 1‖ := hnorm.symm
      _ ≤ ‖S‖ * (2 * Real.pi * |x|) :=
        mul_le_mul_of_nonneg_left hden (norm_nonneg _)
  have hfactor : (2 * (N : ℝ)) * (2 * |x|) ≤
      (Real.pi * ‖S‖) * (2 * |x|) := by
    nlinarith [hmain]
  have hcancel : 2 * (N : ℝ) ≤ Real.pi * ‖S‖ :=
    (mul_le_mul_iff_of_pos_right (by positivity : 0 < 2 * |x|)).mp hfactor
  have hresult : 2 * (N : ℝ) / Real.pi ≤ ‖S‖ :=
    (div_le_iff₀ Real.pi_pos).2 (by simpa only [mul_comm] using hcancel)
  simpa [S, z] using hresult

/-- 论文引理 `lem:fejer` 第 285–287 行：Fejér 核的模平方定义。 -/
noncomputable def circleFejerKernel (N : ℕ) (t : UnitAddCircle) : ℝ :=
  ‖fejerCharacterSum N t‖ ^ 2 / (N : ℝ)

/-- 论文第 299 行：`N≥1` 时 Fejér 核逐点非负。 -/
theorem circleFejerKernel_nonneg (N : ℕ) (hN : 1 ≤ N) (t : UnitAddCircle) :
    0 ≤ circleFejerKernel N t := by
  unfold circleFejerKernel
  positivity

private theorem circleFejerKernel_lower_coe (N : ℕ) (hN : 1 ≤ N)
    (x : ℝ) (hx : 0 < |x|) (hNx : (N : ℝ) * |x| ≤ 1 / 2) :
    4 * (N : ℝ) / Real.pi ^ 2 ≤
      circleFejerKernel N (x : UnitAddCircle) := by
  have hnorm := geomSum_phase_lower N x hx hNx
  rw [← fejerCharacterSum_coe] at hnorm
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hpi := Real.pi_pos
  have hnorm' : 2 * (N : ℝ) ≤
      Real.pi * ‖fejerCharacterSum N (x : UnitAddCircle)‖ :=
    by simpa only [mul_comm] using (div_le_iff₀ hpi).1 hnorm
  have hsq := mul_nonneg (sub_nonneg.mpr hnorm')
    (add_nonneg (mul_nonneg hpi.le
      (norm_nonneg (fejerCharacterSum N (x : UnitAddCircle))))
      (by positivity : 0 ≤ 2 * (N : ℝ)))
  unfold circleFejerKernel
  apply (div_le_div_iff₀ (by positivity : 0 < Real.pi ^ 2) hNpos).2
  nlinarith [hsq]

/-- 论文第 300 行：Fejér 核在圆周原点的取值为 `N`。 -/
theorem circleFejerKernel_zero (N : ℕ) (hN : 1 ≤ N) :
    circleFejerKernel N (0 : UnitAddCircle) = (N : ℝ) := by
  have hsum : fejerCharacterSum N (0 : UnitAddCircle) = (N : ℂ) := by
    simp [fejerCharacterSum]
  unfold circleFejerKernel
  rw [hsum]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  simp
  field_simp

/-- 论文第 300–303 行：若 `dist(t,0)≤δ` 且 `Nδ≤1/2`，Fejér 核逐点至少为
`4N/π²`；证明包含圆周原点和闭区间端点。 -/
theorem circleFejerKernel_lower_on_ball (N : ℕ) (hN : 1 ≤ N)
    (δ : ℝ) (_hδ : 0 < δ) (hNδ : (N : ℝ) * δ ≤ 1 / 2)
    (t : UnitAddCircle) (ht : dist t 0 ≤ δ) :
    4 * (N : ℝ) / Real.pi ^ 2 ≤ circleFejerKernel N t := by
  have hpi2 : (4 : ℝ) ≤ Real.pi ^ 2 := by
    nlinarith [Real.two_le_pi]
  induction t using Quotient.inductionOn with
  | _ z =>
    let y : ℝ := z - (round z : ℝ)
    have hnorm : ‖(z : UnitAddCircle)‖ = |y| := by
      simpa [y] using (AddCircle.norm_eq (1 : ℝ) (x := z))
    have habs : |y| ≤ δ := by
      simpa only [dist_zero_right, hnorm] using ht
    have hcast : (y : UnitAddCircle) = (z : UnitAddCircle) := by
      have hint : (((round z : ℤ) : ℝ) : UnitAddCircle) = 0 := by
        apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).2
        refine ⟨round z, ?_⟩
        simp [zsmul_eq_mul]
      simp [y, hint]
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    by_cases hy : y = 0
    · have ht0 : (z : UnitAddCircle) = 0 := by
        rw [← hcast, hy]
        simp
      change 4 * (N : ℝ) / Real.pi ^ 2 ≤ circleFejerKernel N (z : UnitAddCircle)
      rw [ht0, circleFejerKernel_zero N hN]
      apply (div_le_iff₀ (by positivity : 0 < Real.pi ^ 2)).2
      nlinarith [mul_nonneg hNpos.le (sub_nonneg.mpr hpi2)]
    · have hNx : (N : ℝ) * |y| ≤ 1 / 2 :=
        (mul_le_mul_of_nonneg_left habs hNpos.le).trans hNδ
      change 4 * (N : ℝ) / Real.pi ^ 2 ≤ circleFejerKernel N (z : UnitAddCircle)
      rw [← hcast]
      exact circleFejerKernel_lower_coe N hN y (abs_pos.mpr hy) hNx

/-- 论文第 280–282 行：每个整数频率的圆周字符可积。 -/
theorem circleFourier_integrable (k : ℤ) :
    Integrable (fun t : UnitAddCircle => fourier k t) circleHaar := by
  apply Integrable.of_bound (fourier k).continuous.aestronglyMeasurable 1
  filter_upwards [] with t
  rw [fourier_apply]
  exact le_of_eq (Circle.norm_coe _)

private theorem circleFourier_product (j l : ℕ) (t : UnitAddCircle) :
    fourier (j : ℤ) t * (starRingEnd ℂ) (fourier (l : ℤ) t) =
      fourier ((j : ℤ) - (l : ℤ)) t := by
  rw [sub_eq_add_neg, fourier_add, fourier_neg]

private theorem fejerKernel_complex (N : ℕ) (t : UnitAddCircle) :
    (circleFejerKernel N t : ℂ) =
      (1 / (N : ℂ)) *
        ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N,
          fourier ((j : ℤ) - (l : ℤ)) t := by
  unfold circleFejerKernel fejerCharacterSum
  calc
    (↑(‖∑ j ∈ Finset.range N, fourier (j : ℤ) t‖ ^ 2 / (N : ℝ)) : ℂ) =
        (1 / (N : ℂ)) *
          ((∑ j ∈ Finset.range N, fourier (j : ℤ) t) *
            (starRingEnd ℂ) (∑ l ∈ Finset.range N, fourier (l : ℤ) t)) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    _ = _ := by
      rw [map_sum, Finset.sum_mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro l hl
      exact circleFourier_product j l t

private theorem fejer_cross_positive (N : ℕ) (t : UnitAddCircle) :
    (∑ j ∈ Finset.range N, fourier ((N : ℤ) - (j : ℤ)) t) =
      ∑ j ∈ Finset.range N, fourier ((j + 1 : ℕ) : ℤ) t := by
  calc
    _ = ∑ j ∈ Finset.range N,
        fourier ((N : ℤ) - ((N - 1 - j : ℕ) : ℤ)) t := by
          exact (Finset.sum_range_reflect
            (fun j => fourier ((N : ℤ) - (j : ℤ)) t) N).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      congr 1
      have hj' : j < N := Finset.mem_range.mp hj
      have hle : j + 1 ≤ N := by omega
      have hsub : N - 1 - j = N - (j + 1) := by omega
      rw [hsub, Nat.cast_sub hle]
      push_cast
      ring

private theorem fejer_cross_negative (N : ℕ) (t : UnitAddCircle) :
    (∑ j ∈ Finset.range N, fourier ((j : ℤ) - (N : ℤ)) t) =
      ∑ j ∈ Finset.range N, fourier (-(j + 1 : ℕ) : ℤ) t := by
  calc
    _ = ∑ j ∈ Finset.range N,
        fourier (((N - 1 - j : ℕ) : ℤ) - (N : ℤ)) t := by
          exact (Finset.sum_range_reflect
            (fun j => fourier ((j : ℤ) - (N : ℤ)) t) N).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      congr 1
      have hj' : j < N := Finset.mem_range.mp hj
      have hle : j + 1 ≤ N := by omega
      have hsub : N - 1 - j = N - (j + 1) := by omega
      rw [hsub, Nat.cast_sub hle]
      push_cast
      ring

private noncomputable def fejerDouble (N : ℕ) (t : UnitAddCircle) : ℂ :=
  ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N,
    fourier ((j : ℤ) - (l : ℤ)) t

private theorem fejerDouble_succ (N : ℕ) (t : UnitAddCircle) :
    fejerDouble (N + 1) t = fejerDouble N t +
      (∑ j ∈ Finset.range N, fourier ((N : ℤ) - (j : ℤ)) t) +
      (∑ j ∈ Finset.range N, fourier ((j : ℤ) - (N : ℤ)) t) + 1 := by
  unfold fejerDouble
  simp only [Finset.sum_range_succ, Finset.sum_add_distrib]
  simp [fourier_zero]
  ring

private noncomputable def fejerTriangle (N : ℕ) (t : UnitAddCircle) : ℂ :=
  (∑ k ∈ Finset.range N, ((N - k : ℕ) : ℂ) *
    (fourier (k : ℤ) t + fourier (-(k : ℤ)) t)) - (N : ℂ)

private theorem fejerTriangle_succ (N : ℕ) (t : UnitAddCircle) :
    fejerTriangle (N + 1) t = fejerTriangle N t + 1 +
      ∑ j ∈ Finset.range N,
        (fourier ((j + 1 : ℕ) : ℤ) t + fourier (-(j + 1 : ℕ) : ℤ) t) := by
  have hsum :
      (∑ k ∈ Finset.range N, ((N + 1 - k : ℕ) : ℂ) *
        (fourier (k : ℤ) t + fourier (-(k : ℤ)) t)) =
      (∑ k ∈ Finset.range N, ((N - k : ℕ) : ℂ) *
        (fourier (k : ℤ) t + fourier (-(k : ℤ)) t)) +
      ∑ k ∈ Finset.range N,
        (fourier (k : ℤ) t + fourier (-(k : ℤ)) t) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k < N := Finset.mem_range.mp hk
    have hcoeff : N + 1 - k = N - k + 1 := by omega
    rw [hcoeff]
    push_cast
    ring
  unfold fejerTriangle
  rw [Finset.sum_range_succ, hsum]
  have hlast : N + 1 - N = 1 := by omega
  rw [hlast]
  simp only [Nat.cast_one, one_mul, Nat.cast_add, Nat.cast_one]
  have hshift :
      (∑ k ∈ Finset.range N,
        (fourier (k : ℤ) t + fourier (-(k : ℤ)) t)) +
        (fourier (N : ℤ) t + fourier (-(N : ℤ)) t) =
      2 + ∑ j ∈ Finset.range N,
        (fourier ((j + 1 : ℕ) : ℤ) t + fourier (-(j + 1 : ℕ) : ℤ) t) := by
    let f : ℕ → ℂ := fun k =>
      fourier (k : ℤ) t + fourier (-(k : ℤ)) t
    change (∑ k ∈ Finset.range N, f k) + f N =
      2 + ∑ j ∈ Finset.range N, f (j + 1)
    calc
      _ = ∑ k ∈ Finset.range (N + 1), f k :=
        (Finset.sum_range_succ f N).symm
      _ = f 0 + ∑ j ∈ Finset.range N, f (j + 1) :=
        sum_range_succ_shift f N
      _ = _ := by norm_num [f]
  simp only [Nat.cast_add, Nat.cast_one] at hshift ⊢
  linear_combination hshift

private theorem fejerDouble_eq_triangle (N : ℕ) (t : UnitAddCircle) :
    fejerDouble N t = fejerTriangle N t := by
  induction N with
  | zero => simp [fejerDouble, fejerTriangle]
  | succ N ih =>
      rw [fejerDouble_succ, fejerTriangle_succ, ih,
        fejer_cross_positive, fejer_cross_negative, Finset.sum_add_distrib]
      ring

/-- 论文第 287、299 行：模平方的有限 Fourier 展开，零频率系数为 `1`，
正负频率 `±(j+1)` 的系数均为 `(N-j)/(N+1)`。 -/
theorem circleFejerKernel_finiteExpansion_succ (N : ℕ) (t : UnitAddCircle) :
    (circleFejerKernel (N + 1) t : ℂ) =
      1 + ∑ j ∈ Finset.range N,
        (((N - j : ℕ) : ℂ) / ((N + 1 : ℕ) : ℂ)) *
          (fourier ((j + 1 : ℕ) : ℤ) t + fourier (-(j + 1 : ℕ) : ℤ) t) := by
  have hN0 : (((N + 1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
  rw [fejerKernel_complex, show
    (∑ j ∈ Finset.range (N + 1), ∑ l ∈ Finset.range (N + 1),
      fourier ((j : ℤ) - (l : ℤ)) t) = fejerDouble (N + 1) t from rfl,
    fejerDouble_eq_triangle]
  unfold fejerTriangle
  rw [sum_range_succ_shift]
  simp only [Nat.cast_zero, neg_zero, fourier_zero, Nat.add_sub_cancel_left]
  have hsum :
      (1 / (((N + 1 : ℕ) : ℂ))) *
        (∑ j ∈ Finset.range N,
          ((N - j : ℕ) : ℂ) *
            (fourier ((j + 1 : ℕ) : ℤ) t + fourier (-(j + 1 : ℕ) : ℤ) t)) =
      ∑ j ∈ Finset.range N,
        (((N - j : ℕ) : ℂ) / ((N + 1 : ℕ) : ℂ)) *
          (fourier ((j + 1 : ℕ) : ℤ) t + fourier (-(j + 1 : ℕ) : ℤ) t) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [← hsum]
  have hcoeff (j : ℕ) : N + 1 - (j + 1) = N - j := by omega
  simp_rw [hcoeff]
  simp only [Nat.sub_zero]
  field_simp
  ring

/-- 论文第 299 行：Fejér 核在归一化 Haar 测度下的积分为一。 -/
theorem circleFejerKernel_integral (N : ℕ) (hN : 1 ≤ N) :
    (∫ t : UnitAddCircle, circleFejerKernel N t ∂circleHaar) = 1 := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hpair (j l : ℕ) :
      Integrable (fun t : UnitAddCircle => fourier ((j : ℤ) - (l : ℤ)) t)
        circleHaar := circleFourier_integrable _
  have hint :
      (∫ t : UnitAddCircle, (circleFejerKernel N t : ℂ) ∂circleHaar) = 1 := by
    simp_rw [fejerKernel_complex]
    rw [integral_const_mul]
    rw [integral_finsetSum (Finset.range N) (fun j hj =>
      integrable_finsetSum (Finset.range N) (fun l hl => hpair j l))]
    simp_rw [integral_finsetSum (Finset.range N) (fun l hl => hpair _ l)]
    simp_rw [integral_circleFourier]
    have heq (j l : ℕ) :
        ((j : ℤ) - (l : ℤ) = 0) ↔ j = l := by omega
    simp_rw [heq]
    simp [Finset.sum_ite_eq']
    have hfilter : (Finset.range N).filter (fun x => x < N) = Finset.range N := by
      ext x
      simp
    rw [hfilter, Finset.card_range]
    field_simp
  rw [integral_complex_ofReal] at hint
  exact Complex.ofReal_injective hint

/-- 论文第 290–303 行：`N=⌊1/(2δ)⌋` 的精确取法。 -/
noncomputable def fejerOrder (δ : ℝ) : ℕ := Nat.floor (1 / (2 * δ))

/-- 论文第 303 行：`0<δ≤1/4` 时 `1/(4δ)≤N≤1/(2δ)`，且 `N≥1`。 -/
theorem fejerOrder_bounds (δ : ℝ) (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) :
    1 ≤ fejerOrder δ ∧
      1 / (4 * δ) ≤ (fejerOrder δ : ℝ) ∧
      (fejerOrder δ : ℝ) ≤ 1 / (2 * δ) := by
  let x : ℝ := 1 / (2 * δ)
  have hden : 0 < 2 * δ := by positivity
  have h4 : 0 < 4 * δ := by positivity
  have hx : 2 ≤ x := by
    dsimp [x]
    apply (le_div_iff₀ hden).2
    nlinarith
  have hfloor := Nat.floor_le (show 0 ≤ x by linarith)
  have hfloor' := Nat.lt_floor_add_one x
  have hpos : 1 ≤ fejerOrder δ := by
    unfold fejerOrder
    exact (Nat.floor_pos.mpr (by dsimp [x] at hx ⊢; linarith))
  refine ⟨hpos, ?_, ?_⟩
  · have hh : x / 2 ≤ (fejerOrder δ : ℝ) := by
      dsimp [fejerOrder] at hfloor' ⊢
      linarith
    convert hh using 1 <;> dsimp [x] <;> ring
  · simpa [fejerOrder, x] using hfloor

/-- 论文第 287、294–295 行：频率 `k` 的三角形系数，支撑在 `|k|<N`。 -/
noncomputable def circleFejerCoefficient (N : ℕ) (k : ℤ) : ℝ :=
  if k.natAbs < N then 1 - (k.natAbs : ℝ) / (N : ℝ) else 0

/-- 论文第 290–295 行：论文指定的非负圆周区间控制候选函数。 -/
noncomputable def circleFejerMajorant (δ : ℝ) (t : UnitAddCircle) : ℝ :=
  Real.pi ^ 2 / (4 * (fejerOrder δ : ℝ)) * circleFejerKernel (fejerOrder δ) t

/-- 论文第 295 行：`|k|≥N` 时三角形系数为零；其余系数在 `[0,1]`。 -/
theorem circleFejerCoefficient_bounds (N : ℕ) (hN : 1 ≤ N) (k : ℤ) :
    0 ≤ circleFejerCoefficient N k ∧ circleFejerCoefficient N k ≤ 1 ∧
      (N ≤ k.natAbs → circleFejerCoefficient N k = 0) := by
  unfold circleFejerCoefficient
  by_cases hk : k.natAbs < N
  · simp only [if_pos hk]
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hkreal : (k.natAbs : ℝ) ≤ N := by exact_mod_cast hk.le
    have hratio : (k.natAbs : ℝ) / N ≤ 1 := (div_le_iff₀ hNpos).2 (by linarith)
    have hratio0 : 0 ≤ (k.natAbs : ℝ) / N := by positivity
    refine ⟨by linarith, by linarith, ?_⟩
    intro hbad
    omega
  · simp only [if_neg hk]
    exact ⟨le_refl _, by norm_num, fun _ => trivial⟩

private theorem circleFejerCoefficient_zero (N : ℕ) :
    circleFejerCoefficient (N + 1) 0 = 1 := by
  simp [circleFejerCoefficient]

private theorem circleFejerCoefficient_pos (N j : ℕ) (hj : j < N) :
    circleFejerCoefficient (N + 1) ((j + 1 : ℕ) : ℤ) =
      ((N - j : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ) := by
  have hj' : j + 1 < N + 1 := by omega
  have hjle : j ≤ N := hj.le
  simp only [circleFejerCoefficient, Int.natAbs_natCast, if_pos hj']
  rw [Nat.cast_sub hjle]
  field_simp
  push_cast
  ring

private theorem circleFejerCoefficient_neg (N j : ℕ) (hj : j < N) :
    circleFejerCoefficient (N + 1) (-((j + 1 : ℕ) : ℤ)) =
      ((N - j : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ) := by
  simpa only [circleFejerCoefficient, Int.natAbs_neg] using
    circleFejerCoefficient_pos N j hj

/-- 论文第 294–295 行：`gδ` 的显式 Fourier 系数非负，且每项至多 `π²δ`；
这里 `π²` 是不依赖 `δ,k` 的绝对常数。 -/
theorem circleFejerMajorant_coefficient_bounds (δ : ℝ) (hδ : 0 < δ)
    (hδ4 : δ ≤ 1 / 4) (k : ℤ) :
    let N := fejerOrder δ
    let c := Real.pi ^ 2 / (4 * (N : ℝ)) * circleFejerCoefficient N k
    0 ≤ c ∧ c ≤ Real.pi ^ 2 * δ ∧ (N ≤ k.natAbs → c = 0) := by
  dsimp
  have hB := fejerOrder_bounds δ hδ hδ4
  have hN : (0 : ℝ) < fejerOrder δ := by exact_mod_cast hB.1
  have hp : 0 ≤ Real.pi ^ 2 / (4 * (fejerOrder δ : ℝ)) := by positivity
  have hc := circleFejerCoefficient_bounds (fejerOrder δ) hB.1 k
  have hscale : Real.pi ^ 2 / (4 * (fejerOrder δ : ℝ)) ≤ Real.pi ^ 2 * δ := by
    have h4δ : 0 < 4 * δ := by positivity
    have h4N : 0 < 4 * (fejerOrder δ : ℝ) := by positivity
    apply (div_le_iff₀ h4N).2
    have hlow := hB.2.1
    have hpi : 0 ≤ Real.pi ^ 2 := sq_nonneg _
    have hratio : 1 ≤ 4 * δ * (fejerOrder δ : ℝ) := by
      apply (div_le_iff₀ h4δ).1 at hlow
      nlinarith
    nlinarith [mul_nonneg hpi (sub_nonneg.mpr hratio)]
  refine ⟨mul_nonneg hp hc.1, ?_, ?_⟩
  · calc
      _ ≤ Real.pi ^ 2 / (4 * (fejerOrder δ : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_left hc.2.1 hp
      _ = Real.pi ^ 2 / (4 * (fejerOrder δ : ℝ)) := by ring
      _ ≤ _ := hscale
  · intro hk
    rw [hc.2.2 hk, mul_zero]

/-- 论文第 290–303 行：指定的 Fejér 平滑函数逐点控制半径 `δ` 的闭圆周球；
包括原点与闭区间端点，不借助几乎处处意义。 -/
theorem circleFejerMajorant_ge_indicator (δ : ℝ) (hδ : 0 < δ)
    (hδ4 : δ ≤ 1 / 4) (t : UnitAddCircle) :
    (if dist t 0 ≤ δ then (1 : ℝ) else 0) ≤ circleFejerMajorant δ t := by
  let N := fejerOrder δ
  have hB := fejerOrder_bounds δ hδ hδ4
  have hN : 1 ≤ N := hB.1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hscale : 0 ≤ Real.pi ^ 2 / (4 * (N : ℝ)) := by positivity
  by_cases ht : dist t 0 ≤ δ
  · simp only [if_pos ht]
    have hNδ : (N : ℝ) * δ ≤ 1 / 2 := by
      have hden : 0 < 2 * δ := by positivity
      have hupper := hB.2.2
      have hmul := (le_div_iff₀ hden).1 hupper
      nlinarith
    have hlow := circleFejerKernel_lower_on_ball N hN δ hδ hNδ t ht
    unfold circleFejerMajorant
    change 1 ≤ Real.pi ^ 2 / (4 * (N : ℝ)) * circleFejerKernel N t
    calc
      1 = Real.pi ^ 2 / (4 * (N : ℝ)) *
          (4 * (N : ℝ) / Real.pi ^ 2) := by
            have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
            field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hlow hscale
  · simp only [if_neg ht]
    unfold circleFejerMajorant
    exact mul_nonneg hscale (circleFejerKernel_nonneg N hN t)

/-- 论文第 290–303 行：同一逐点控制写成圆周闭球的真实指示函数。 -/
theorem circleFejerMajorant_ge_closedBall_indicator (δ : ℝ) (hδ : 0 < δ)
    (hδ4 : δ ≤ 1 / 4) (t : UnitAddCircle) :
    (Metric.closedBall (0 : UnitAddCircle) δ).indicator
      (1 : UnitAddCircle → ℝ) t ≤ circleFejerMajorant δ t := by
  by_cases ht : dist t 0 ≤ δ
  · have hmem : t ∈ Metric.closedBall (0 : UnitAddCircle) δ := by
      simpa [Metric.mem_closedBall, dist_comm] using ht
    rw [Set.indicator_of_mem hmem]
    simpa only [if_pos ht, Pi.one_apply] using
      circleFejerMajorant_ge_indicator δ hδ hδ4 t
  · have hnot : t ∉ Metric.closedBall (0 : UnitAddCircle) δ := by
      simpa [Metric.mem_closedBall, dist_comm] using ht
    rw [Set.indicator_of_notMem hnot]
    simpa only [if_neg ht] using circleFejerMajorant_ge_indicator δ hδ hδ4 t

/-- 论文第 287 行：`F_(N+1)` 的零、正、负频率有限展开；每项使用
同一个三角形系数 `circleFejerCoefficient`，对应 `|k|<N+1`。 -/
theorem circleFejerKernel_expansion_coeff_succ (N : ℕ) (t : UnitAddCircle) :
    (circleFejerKernel (N + 1) t : ℂ) =
      1 +
        (∑ j ∈ Finset.range N,
          (circleFejerCoefficient (N + 1) ((j + 1 : ℕ) : ℤ) : ℂ) *
            fourier ((j + 1 : ℕ) : ℤ) t) +
        (∑ j ∈ Finset.range N,
          (circleFejerCoefficient (N + 1) (-((j + 1 : ℕ) : ℤ)) : ℂ) *
            fourier (-((j + 1 : ℕ) : ℤ)) t) := by
  rw [circleFejerKernel_finiteExpansion_succ]
  have hcoeff (j : ℕ) (hj : j ∈ Finset.range N) :
      (((N - j : ℕ) : ℂ) / ((N + 1 : ℕ) : ℂ)) =
        (circleFejerCoefficient (N + 1) ((j + 1 : ℕ) : ℤ) : ℂ) := by
    have hr := circleFejerCoefficient_pos N j (Finset.mem_range.mp hj)
    simpa only [Complex.ofReal_div, Complex.ofReal_natCast] using
      congrArg (fun r : ℝ => (r : ℂ)) hr.symm
  calc
    1 + ∑ j ∈ Finset.range N,
        (((N - j : ℕ) : ℂ) / ((N + 1 : ℕ) : ℂ)) *
          (fourier ((j + 1 : ℕ) : ℤ) t + fourier (-(j + 1 : ℕ) : ℤ) t) =
      1 + ∑ j ∈ Finset.range N,
        ((circleFejerCoefficient (N + 1) ((j + 1 : ℕ) : ℤ) : ℂ) *
            fourier ((j + 1 : ℕ) : ℤ) t +
          (circleFejerCoefficient (N + 1) (-((j + 1 : ℕ) : ℤ)) : ℂ) *
            fourier (-((j + 1 : ℕ) : ℤ)) t) := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [hcoeff j hj]
      have hn := circleFejerCoefficient_neg N j (Finset.mem_range.mp hj)
      have hp := circleFejerCoefficient_pos N j (Finset.mem_range.mp hj)
      rw [hn, ← hp]
      ring
    _ = _ := by rw [Finset.sum_add_distrib]; ring

/-- 论文第 290–295 行：`gδ` 的完整有限 Fourier 展开，正负频率的系数
均由 `circleFejerCoefficient` 与公共因子 `π²/(4N)` 给出。 -/
theorem circleFejerMajorant_expansion (δ : ℝ) (hδ : 0 < δ)
    (hδ4 : δ ≤ 1 / 4) (t : UnitAddCircle) :
    let N := fejerOrder δ
    (circleFejerMajorant δ t : ℂ) =
      (Real.pi ^ 2 / (4 * (N : ℝ)) : ℂ) *
        (1 +
          (∑ j ∈ Finset.range (N - 1),
            (circleFejerCoefficient N ((j + 1 : ℕ) : ℤ) : ℂ) *
              fourier ((j + 1 : ℕ) : ℤ) t) +
          (∑ j ∈ Finset.range (N - 1),
            (circleFejerCoefficient N (-((j + 1 : ℕ) : ℤ)) : ℂ) *
              fourier (-((j + 1 : ℕ) : ℤ)) t)) := by
  dsimp
  have hN := (fejerOrder_bounds δ hδ hδ4).1
  obtain ⟨M, hM⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  unfold circleFejerMajorant
  simp only [hM, Nat.succ_eq_add_one, Nat.add_sub_cancel_right]
  push_cast
  rw [circleFejerKernel_expansion_coeff_succ]
  simp only [fourier_apply, Nat.cast_add, Nat.cast_one]

#print axioms LonelyRunner.integral_circleFourier
#print axioms LonelyRunner.circleFejerKernel_finiteExpansion_succ
#print axioms LonelyRunner.circleFejerKernel_expansion_coeff_succ
#print axioms LonelyRunner.circleFejerKernel_integral
#print axioms LonelyRunner.circleFejerMajorant_ge_indicator
#print axioms LonelyRunner.circleFejerMajorant_ge_closedBall_indicator
#print axioms LonelyRunner.circleFejerMajorant_expansion
#print axioms LonelyRunner.circleFejerMajorant_coefficient_bounds

end LonelyRunner
