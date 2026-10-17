import LonelyRunner.CircleFejerSmoothing
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Fejér 核的点态界与第一距离矩 -/
namespace LonelyRunner
open MeasureTheory

/-- 论文 `lem:smoothing` 第 356 行：Fejér 核的平凡上界。 -/
theorem circleFejerKernel_le_order (R : ℕ) (hR : 1 ≤ R) (t : UnitAddCircle) :
    circleFejerKernel R t ≤ (R : ℝ) := by
  have hsum : ‖fejerCharacterSum R t‖ ≤ (R : ℝ) := by
    calc
      _ ≤ ∑ j ∈ Finset.range R, ‖fourier (j : ℤ) t‖ := by
        unfold fejerCharacterSum
        exact norm_sum_le _ _
      _ = (R : ℝ) := by
        simp [fourier_apply, Circle.norm_coe]
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  unfold circleFejerKernel
  apply (div_le_iff₀ hRpos).2
  nlinarith [norm_nonneg (fejerCharacterSum R t)]

private theorem fejer_character_one_coe (x : ℝ) :
    fourier 1 (x : UnitAddCircle) =
      Complex.exp (Complex.I * (2 * Real.pi * x : ℝ)) := by
  rw [fourier_coe_apply]
  norm_num
  congr 1
  ring

private theorem fejer_phase_lower (x : ℝ) (hx : |x| ≤ 1 / 2) :
    4 * |x| ≤ ‖fourier 1 (x : UnitAddCircle) - 1‖ := by
  rw [fejer_character_one_coe]
  have harg : |Real.pi * x| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hsin := Real.mul_abs_le_abs_sin harg
  have hs : 2 * |x| ≤ |Real.sin (Real.pi * x)| := by
    rw [abs_mul, abs_of_pos Real.pi_pos] at hsin
    have hcalc : (2 / Real.pi) * (Real.pi * |x|) = 2 * |x| := by
      field_simp
    rwa [hcalc] at hsin
  have hphase := Complex.norm_exp_I_mul_ofReal_sub_one (2 * Real.pi * x)
  have hangle : (2 * Real.pi * x) / 2 = Real.pi * x := by ring
  rw [hangle] at hphase
  calc
    4 * |x| ≤ 2 * |Real.sin (Real.pi * x)| := by linarith
    _ = ‖Complex.exp (Complex.I * (2 * Real.pi * x : ℝ)) - 1‖ := by
      rw [hphase]
      simp [Real.norm_eq_abs]

private theorem fejer_phase_lower_circle (t : UnitAddCircle) :
    4 * dist t 0 ≤ ‖fourier 1 t - 1‖ := by
  induction t using Quotient.inductionOn with
  | _ z =>
    let y : ℝ := z - (round z : ℝ)
    have hy : |y| ≤ 1 / 2 := abs_sub_round z
    have hnorm : dist (z : UnitAddCircle) 0 = |y| := by
      simpa [dist_zero_right, y] using (AddCircle.norm_eq (1 : ℝ) (x := z))
    have hcast : (y : UnitAddCircle) = (z : UnitAddCircle) := by
      have hint : (((round z : ℤ) : ℝ) : UnitAddCircle) = 0 := by
        apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).2
        refine ⟨round z, ?_⟩
        simp [zsmul_eq_mul]
      simp [y, hint]
    calc
      4 * dist (z : UnitAddCircle) 0 = 4 * |y| := by rw [hnorm]
      _ ≤ ‖fourier 1 (y : UnitAddCircle) - 1‖ := fejer_phase_lower y hy
      _ = ‖fourier 1 (z : UnitAddCircle) - 1‖ := by rw [hcast]

private theorem fejerCharacterSum_geom (R : ℕ) (t : UnitAddCircle) :
    fejerCharacterSum R t * (fourier 1 t - 1) = (fourier 1 t) ^ R - 1 := by
  have hfour (j : ℕ) : fourier (j : ℤ) t = (fourier 1 t) ^ j := by
    induction j with
    | zero => simp
    | succ j ih =>
        rw [Nat.cast_succ, fourier_add, ih, pow_succ]
  simp_rw [fejerCharacterSum, hfour]
  exact geom_sum_mul (fourier 1 t) R

/-- 论文 `lem:smoothing` 第 356 行：非原点处的平方反距离 Fejér 核上界。 -/
theorem circleFejerKernel_le_inv_dist_sq (R : ℕ) (hR : 1 ≤ R)
    (t : UnitAddCircle) (ht : t ≠ 0) :
    circleFejerKernel R t ≤ 1 / (4 * (R : ℝ) * dist t 0 ^ 2) := by
  let d : ℝ := dist t 0
  have hd : 0 < d := dist_pos.mpr ht
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hphase : 4 * d ≤ ‖fourier 1 t - 1‖ := fejer_phase_lower_circle t
  have hgeom := fejerCharacterSum_geom R t
  have hnorm : ‖fejerCharacterSum R t‖ * ‖fourier 1 t - 1‖ =
      ‖(fourier 1 t) ^ R - 1‖ := by
    simpa only [norm_mul] using congrArg norm hgeom
  have hnum : ‖(fourier 1 t) ^ R - 1‖ ≤ 2 := by
    calc
      _ ≤ ‖(fourier 1 t) ^ R‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by simp [norm_pow]; norm_num
  have hmul : 4 * d * ‖fejerCharacterSum R t‖ ≤ 2 := by
    calc
      _ ≤ ‖fourier 1 t - 1‖ * ‖fejerCharacterSum R t‖ := by
        gcongr
      _ = ‖(fourier 1 t) ^ R - 1‖ := by rw [mul_comm, hnorm]
      _ ≤ 2 := hnum
  have hs : ‖fejerCharacterSum R t‖ ≤ 1 / (2 * d) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * d)).2
    nlinarith
  unfold circleFejerKernel
  have hs2 : ‖fejerCharacterSum R t‖ ^ 2 ≤ (1 / (2 * d)) ^ 2 := by
    gcongr
  calc
    ‖fejerCharacterSum R t‖ ^ 2 / (R : ℝ) ≤
        (1 / (2 * d)) ^ 2 / (R : ℝ) :=
      div_le_div_of_nonneg_right hs2 hRpos.le
    _ = 1 / (4 * (R : ℝ) * d ^ 2) := by
      field_simp
      ring

private theorem circleFejerKernel_even (R : ℕ) (t : UnitAddCircle) :
    circleFejerKernel R (-t) = circleFejerKernel R t := by
  have hfour (j : ℕ) :
      fourier (j : ℤ) (-t) = (starRingEnd ℂ) (fourier (j : ℤ) t) := by
    calc
      fourier (j : ℤ) (-t) = fourier (-((j : ℤ))) t := by
        simp only [fourier_apply, zsmul_neg, neg_zsmul]
      _ = _ := fourier_neg
  have hsum : fejerCharacterSum R (-t) =
      (starRingEnd ℂ) (fejerCharacterSum R t) := by
    simp only [fejerCharacterSum]
    simp_rw [hfour]
    rw [map_sum]
  unfold circleFejerKernel
  rw [hsum, Complex.norm_conj]

private theorem fejer_dist_coe_eq_abs (x : ℝ) (hx : |x| ≤ 1 / 2) :
    dist (x : UnitAddCircle) 0 = |x| := by
  have h := (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).2
    (by simpa using hx)
  simpa only [dist_zero_right] using h

private theorem circleFejerKernel_distance_continuous (R : ℕ) :
    Continuous (fun t : UnitAddCircle => dist t 0 * circleFejerKernel R t) := by
  unfold circleFejerKernel fejerCharacterSum
  fun_prop

private theorem circleFejerKernel_distance_integrable (R : ℕ) :
    Integrable (fun t : UnitAddCircle => dist t 0 * circleFejerKernel R t) circleHaar := by
  exact (circleFejerKernel_distance_continuous R).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- 论文 `lem:smoothing` 第 356–359 行：圆周 Haar 积分转换为一个基本区间的实积分。 -/
theorem circleFejerKernel_distance_interval (R : ℕ) :
    (∫ t : UnitAddCircle, dist t 0 * circleFejerKernel R t ∂circleHaar) =
      ∫ x in (-1 / 2 : ℝ)..1 / 2,
        |x| * circleFejerKernel R (x : UnitAddCircle) := by
  rw [circleHaar_eq_volume]
  have hpre := (UnitAddCircle.intervalIntegral_preimage
    (-1 / 2 : ℝ) (fun t : UnitAddCircle =>
      dist t 0 * circleFejerKernel R t)).symm
  have hend : (-1 / 2 : ℝ) + 1 = 1 / 2 := by ring
  calc
    _ = ∫ x in (-1 / 2 : ℝ)..(-1 / 2 : ℝ) + 1,
        dist (x : UnitAddCircle) 0 * circleFejerKernel R (x : UnitAddCircle) := hpre
    _ = ∫ x in (-1 / 2 : ℝ)..1 / 2,
        |x| * circleFejerKernel R (x : UnitAddCircle) := by
      rw [hend]
      apply intervalIntegral.integral_congr
      intro x hx
      have habs : |x| ≤ 1 / 2 := by
        have hx' : x ∈ Set.uIcc (-1 / 2 : ℝ) (1 / 2) := hx
        simp only [Set.uIcc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2), Set.mem_Icc] at hx'
        exact abs_le.mpr ⟨by linarith [hx'.1], hx'.2⟩
      change dist (x : UnitAddCircle) 0 * circleFejerKernel R (x : UnitAddCircle) =
        |x| * circleFejerKernel R (x : UnitAddCircle)
      rw [fejer_dist_coe_eq_abs x habs]

private theorem circleFejerKernel_distance_even (R : ℕ) (x : ℝ) :
    |(-x)| * circleFejerKernel R ((-x) : UnitAddCircle) =
      |x| * circleFejerKernel R (x : UnitAddCircle) := by
  have hcast : ((-x : ℝ) : UnitAddCircle) = -(x : UnitAddCircle) := by simp
  change |(-x)| * circleFejerKernel R (-(x : UnitAddCircle)) =
    |x| * circleFejerKernel R (x : UnitAddCircle)
  rw [circleFejerKernel_even]
  simp

private theorem circleFejerKernel_distance_interval_pos (R : ℕ) :
    (∫ t : UnitAddCircle, dist t 0 * circleFejerKernel R t ∂circleHaar) =
      2 * ∫ x in (0 : ℝ)..1 / 2,
        x * circleFejerKernel R (x : UnitAddCircle) := by
  rw [circleFejerKernel_distance_interval]
  let f : ℝ → ℝ := fun x => |x| * circleFejerKernel R (x : UnitAddCircle)
  have hf : Continuous f := by
    dsimp [f]
    have hk : Continuous (fun x : ℝ => circleFejerKernel R (x : UnitAddCircle)) := by
      unfold circleFejerKernel fejerCharacterSum
      fun_prop
    exact continuous_abs.mul hk
  have hsplit :
      (∫ x in (-1 / 2 : ℝ)..0, f x) + (∫ x in (0 : ℝ)..1 / 2, f x) =
        ∫ x in (-1 / 2 : ℝ)..1 / 2, f x :=
    intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (-1 / 2) 0) (hf.intervalIntegrable 0 (1 / 2))
  have hneg : (∫ x in (-1 / 2 : ℝ)..0, f x) =
      ∫ x in (0 : ℝ)..1 / 2, f x := by
    calc
      _ = ∫ x in (0 : ℝ)..1 / 2, f (-x) := by
        rw [intervalIntegral.integral_comp_neg]
        norm_num
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact circleFejerKernel_distance_even R x
  have hpos : (∫ x in (0 : ℝ)..1 / 2, f x) =
      ∫ x in (0 : ℝ)..1 / 2,
        x * circleFejerKernel R (x : UnitAddCircle) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : 0 ≤ x := by
      have hx'' : x ∈ Set.uIcc (0 : ℝ) (1 / 2) := hx
      simp only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2), Set.mem_Icc] at hx''
      exact hx''.1
    simp [f, abs_of_nonneg hx']
  calc
    (∫ x in (-1 / 2 : ℝ)..1 / 2, f x) =
        (∫ x in (-1 / 2 : ℝ)..0, f x) + ∫ x in (0 : ℝ)..1 / 2, f x := hsplit.symm
    _ = 2 * ∫ x in (0 : ℝ)..1 / 2,
      x * circleFejerKernel R (x : UnitAddCircle) := by rw [hneg, hpos]; ring

/-- 论文 `lem:smoothing` 第 356–359 行：在 `1/R` 分割积分后的明确估计。 -/
theorem circleFejerKernel_distance_moment_explicit (R : ℕ) (hR : 2 ≤ R) :
    (∫ t : UnitAddCircle, dist t 0 * circleFejerKernel R t ∂circleHaar) ≤
      1 / (R : ℝ) + Real.log ((R : ℝ) / 2) / (2 * (R : ℝ)) := by
  let a : ℝ := 1 / (R : ℝ)
  let f : ℝ → ℝ := fun x => x * circleFejerKernel R (x : UnitAddCircle)
  have hR1 : 1 ≤ R := by omega
  have hRp : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
  have ha : 0 < a := by dsimp [a]; positivity
  have hahalf : a ≤ 1 / 2 := by
    dsimp [a]
    apply (div_le_iff₀ hRp).2
    have hR2 : (2 : ℝ) ≤ R := by exact_mod_cast hR
    nlinarith
  have hf : Continuous f := by
    dsimp [f]
    have hk : Continuous (fun x : ℝ => circleFejerKernel R (x : UnitAddCircle)) := by
      unfold circleFejerKernel fejerCharacterSum
      fun_prop
    exact continuous_id.mul hk
  have hsmall : (∫ x in (0 : ℝ)..a, f x) ≤
      ∫ x in (0 : ℝ)..a, (R : ℝ) * x := by
    apply intervalIntegral.integral_mono_on ha.le
      (hf.intervalIntegrable 0 a)
      ((continuous_const.mul continuous_id).intervalIntegrable 0 a)
    intro x hx
    have hx0 : 0 ≤ x := hx.1
    dsimp [f]
    calc
      x * circleFejerKernel R (x : UnitAddCircle) ≤ x * (R : ℝ) :=
        mul_le_mul_of_nonneg_left (circleFejerKernel_le_order R hR1 _) hx0
      _ = (R : ℝ) * x := by ring
  have htailInt : IntervalIntegrable (fun x : ℝ => x⁻¹) volume a (1 / 2) := by
    apply intervalIntegral.intervalIntegrable_inv
    · intro x hx
      have hx' : x ∈ Set.Icc a (1 / 2) := by
        simpa only [Set.uIcc_of_le hahalf] using hx
      exact ne_of_gt (lt_of_lt_of_le ha hx'.1)
    · exact continuous_id.continuousOn
  have hlarge : (∫ x in a..1 / 2, f x) ≤
      ∫ x in a..1 / 2, (1 / (4 * (R : ℝ))) * x⁻¹ := by
    apply intervalIntegral.integral_mono_on hahalf
      (hf.intervalIntegrable a (1 / 2))
      (htailInt.const_mul _)
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le ha hx.1
    have hxabs : |x| ≤ 1 / 2 := by
      rw [abs_of_pos hxpos]
      exact hx.2
    have hdist := fejer_dist_coe_eq_abs x hxabs
    rw [abs_of_pos hxpos] at hdist
    have hne : (x : UnitAddCircle) ≠ 0 := by
      intro heq
      rw [heq, dist_self] at hdist
      linarith
    have hk := circleFejerKernel_le_inv_dist_sq R hR1 (x : UnitAddCircle) hne
    rw [hdist] at hk
    have hmul := mul_le_mul_of_nonneg_left hk hxpos.le
    dsimp [f]
    calc
      x * circleFejerKernel R (x : UnitAddCircle) ≤
          x * (1 / (4 * (R : ℝ) * x ^ 2)) := hmul
      _ = (1 / (4 * (R : ℝ))) * x⁻¹ := by
        field_simp
  have hsplit :
      (∫ x in (0 : ℝ)..a, f x) + (∫ x in a..1 / 2, f x) =
        ∫ x in (0 : ℝ)..1 / 2, f x :=
    intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable 0 a) (hf.intervalIntegrable a (1 / 2))
  calc
    (∫ t : UnitAddCircle, dist t 0 * circleFejerKernel R t ∂circleHaar) =
        2 * ∫ x in (0 : ℝ)..1 / 2, f x := circleFejerKernel_distance_interval_pos R
    _ = 2 * ((∫ x in (0 : ℝ)..a, f x) + (∫ x in a..1 / 2, f x)) := by rw [hsplit]
    _ ≤ 2 * ((∫ x in (0 : ℝ)..a, (R : ℝ) * x) +
        (∫ x in a..1 / 2, (1 / (4 * (R : ℝ))) * x⁻¹)) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hsmall hlarge) (by norm_num)
    _ = 1 / (R : ℝ) + Real.log ((R : ℝ) / 2) / (2 * (R : ℝ)) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      rw [integral_id, integral_inv_of_pos ha (by norm_num : (0 : ℝ) < 1 / 2)]
      have hq : (1 / 2 : ℝ) / a = (R : ℝ) / 2 := by
        dsimp [a]
        field_simp
      rw [hq]
      dsimp [a]
      field_simp
      ring

/-- 论文 `lem:smoothing` 第 356–359 行：Fejér 核第一距离矩的统一对数界。
常数 `1+(log 2)⁻¹` 与阶数 `R` 无关。 -/
theorem circleFejerKernel_distance_moment_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℕ, 2 ≤ R →
      (∫ t : UnitAddCircle, dist t 0 * circleFejerKernel R t ∂circleHaar) ≤
        C * Real.log (2 * (R : ℝ)) / (R : ℝ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1 + (Real.log 2)⁻¹, by positivity, ?_⟩
  intro R hR
  have hRp : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
  have hR2 : (2 : ℝ) ≤ R := by exact_mod_cast hR
  let L : ℝ := Real.log (2 * (R : ℝ))
  let T : ℝ := Real.log ((R : ℝ) / 2)
  have hlogLower : Real.log 2 ≤ L := by
    dsimp [L]
    apply Real.log_le_log (by norm_num : (0 : ℝ) < 2)
    nlinarith
  have hL : 0 ≤ L := le_trans hlog2.le hlogLower
  have hlogTail : T ≤ L := by
    dsimp [T, L]
    apply Real.log_le_log (by positivity : (0 : ℝ) < (R : ℝ) / 2)
    nlinarith
  have hone : (1 : ℝ) ≤ (Real.log 2)⁻¹ * L := by
    have hdiv : (1 : ℝ) ≤ L / Real.log 2 :=
      (le_div_iff₀ hlog2).2 (by simpa using hlogLower)
    simpa [div_eq_mul_inv, mul_comm] using hdiv
  have hsum : 1 + T / 2 ≤ (1 + (Real.log 2)⁻¹) * L := by
    nlinarith
  have hexp := circleFejerKernel_distance_moment_explicit R hR
  calc
    (∫ t : UnitAddCircle, dist t 0 * circleFejerKernel R t ∂circleHaar) ≤
        1 / (R : ℝ) + T / (2 * (R : ℝ)) := hexp
    _ = (1 + T / 2) / (R : ℝ) := by ring
    _ ≤ (1 + (Real.log 2)⁻¹) * L / (R : ℝ) :=
      div_le_div_of_nonneg_right hsum hRp.le

end LonelyRunner
