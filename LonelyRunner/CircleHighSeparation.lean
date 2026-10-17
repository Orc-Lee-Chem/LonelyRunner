import LonelyRunner.CircleFourierFinite
import LonelyRunner.CoverMultiplicity

/-!
# 圆周高频分离

对应论文 `lem:separation` 第 400–416 行的高速度断言。仅使用有限 Fourier 求和。
-/

namespace LonelyRunner

open MeasureTheory

private theorem circleShift_nsmul_eq_zero (v : ℕ) (hv : 0 < v) :
    v • (((1 : ℝ) / (v : ℝ) : ℝ) : UnitAddCircle) = 0 := by
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hv)
  rw [← QuotientAddGroup.mk_nsmul]
  have hreal : v • ((1 : ℝ) / (v : ℝ)) = 1 := by
    rw [nsmul_eq_mul]
    field_simp
  rw [hreal]
  apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).2
  refine ⟨1, ?_⟩
  simp

/-- 论文 `lem:separation` 第 415 行：原有闭 Bohr 集在平移 `1/v` 后逐点不变。 -/
theorem bohrSet_shift_inv (v : ℕ) (δ : ℝ) (hv : 0 < v)
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2) (t : UnitAddCircle) :
    t + (((1 : ℝ) / (v : ℝ) : ℝ) : UnitAddCircle) ∈ bohrSet v δ ↔
      t ∈ bohrSet v δ := by
  rw [mem_bohrSet_iff_dist v δ hδ.le hδhalf,
    mem_bohrSet_iff_dist v δ hδ.le hδhalf]
  rw [smul_add, circleShift_nsmul_eq_zero v hv, add_zero]

private theorem circleShift_fourier_eq_one_iff (v : ℕ) (hv : 0 < v) (n : ℤ) :
    fourier n (((1 : ℝ) / (v : ℝ) : ℝ) : UnitAddCircle) = 1 ↔
      (v : ℤ) ∣ n := by
  let h : UnitAddCircle := (((1 : ℝ) / (v : ℝ) : ℝ) : UnitAddCircle)
  have hvc : v • h = 0 := circleShift_nsmul_eq_zero v hv
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hv)
  have hchar : fourier n h = 1 ↔ n • h = 0 := by
    constructor
    · intro hf
      apply AddCircle.injective_toCircle (by norm_num : (1 : ℝ) ≠ 0)
      apply Subtype.ext
      simpa [fourier_apply] using hf
    · intro hf
      simp [fourier_apply, hf]
  rw [hchar]
  constructor
  · intro hn
    have hcoe : n • h = (((n : ℝ) / (v : ℝ) : ℝ) : UnitAddCircle) := by
      dsimp [h]
      rw [← QuotientAddGroup.mk_zsmul]
      congr 1
      simp [zsmul_eq_mul, div_eq_mul_inv, mul_comm]
    rw [hcoe] at hn
    obtain ⟨j, hj⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hn
    have hreal : (n : ℝ) = (v : ℝ) * (j : ℝ) := by
      simp only [zsmul_eq_mul, mul_one] at hj
      have htmp := (div_eq_iff hvR).mp hj.symm
      nlinarith [htmp]
    have hint : n = (v : ℤ) * j := by exact_mod_cast hreal
    exact ⟨j, hint⟩
  · rintro ⟨j, rfl⟩
    rw [mul_comm, mul_zsmul, natCast_zsmul, hvc, smul_zero]

private theorem fourier_mul_bohrIndicator_eq_indicator (v : ℕ) (δ : ℝ)
    (n : ℤ) (t : UnitAddCircle) :
    fourier n t * (bohrIndicator v δ t : ℂ) =
      (bohrSet v δ).indicator (fun s => fourier n s) t := by
  by_cases ht : t ∈ bohrSet v δ
  · simp [bohrIndicator, ht]
  · simp [bohrIndicator, ht]

private theorem fourier_mul_bohrIndicator_integrable (v : ℕ) (δ : ℝ)
    (hv : 0 < v) (hδ : 0 < δ) (hδhalf : δ < 1 / 2) (n : ℤ) :
    Integrable (fun t : UnitAddCircle =>
      fourier n t * (bohrIndicator v δ t : ℂ)) circleHaar := by
  have hs := (bohrSet_measurable_measure v δ hv hδ hδhalf).1
  have hi := (circleFourier_integrable n).indicator hs
  convert hi using 1
  funext t
  exact fourier_mul_bohrIndicator_eq_indicator v δ n t

/-- 论文 `lem:separation` 第 415 行：原 Bohr 集指示函数的频率积分，
在 `v∤n` 时严格为零；证明只用 `1/v` 平移，不使用指示函数的 Fourier 展开。 -/
theorem integral_fourier_bohrIndicator_zero (v : ℕ) (δ : ℝ) (n : ℤ)
    (hv : 0 < v) (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hn : ¬ (v : ℤ) ∣ n) :
    (∫ t : UnitAddCircle,
      fourier n t * (bohrIndicator v δ t : ℂ) ∂circleHaar) = 0 := by
  let h : UnitAddCircle := (((1 : ℝ) / (v : ℝ) : ℝ) : UnitAddCircle)
  let F : UnitAddCircle → ℂ := fun t =>
    (bohrSet v δ).indicator (fun s => fourier n s) t
  have hFint : Integrable F circleHaar :=
    (circleFourier_integrable n).indicator
      (bohrSet_measurable_measure v δ hv hδ hδhalf).1
  have hshift (t : UnitAddCircle) : F (t + h) = fourier n h * F t := by
    have hmem := bohrSet_shift_inv v δ hv hδ hδhalf t
    by_cases ht : t ∈ bohrSet v δ
    · have ht' : t + h ∈ bohrSet v δ := hmem.mpr ht
      simp only [F, Set.indicator_of_mem ht', Set.indicator_of_mem ht]
      simp only [fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]
      ring
    · have ht' : t + h ∉ bohrSet v δ := fun hh => ht (hmem.mp hh)
      simp [F, ht, ht']
  have htrans : (∫ t : UnitAddCircle, F (t + h) ∂circleHaar) =
      (∫ t : UnitAddCircle, F t ∂circleHaar) :=
    MeasureTheory.integral_add_right_eq_self F h
  have hphase : fourier n h * (∫ t : UnitAddCircle, F t ∂circleHaar) =
      (∫ t : UnitAddCircle, F t ∂circleHaar) := by
    calc
      _ = ∫ t : UnitAddCircle, fourier n h * F t ∂circleHaar :=
        (integral_const_mul _ _).symm
      _ = ∫ t : UnitAddCircle, F (t + h) ∂circleHaar := by
        congr 1
        funext t
        exact (hshift t).symm
      _ = _ := htrans
  have hne : fourier n h ≠ 1 := by
    intro heq
    exact hn ((circleShift_fourier_eq_one_iff v hv n).mp heq)
  have hFzero : (∫ t : UnitAddCircle, F t ∂circleHaar) = 0 := by
    have hprod : (fourier n h - 1) *
        (∫ t : UnitAddCircle, F t ∂circleHaar) = 0 := by
      linear_combination hphase
    exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hne)
  convert hFzero using 1
  congr 1
  funext t
  exact fourier_mul_bohrIndicator_eq_indicator v δ n t

private theorem integral_fourier_bohrIndicator_zeroFreq (v : ℕ) (δ : ℝ)
    (hv : 0 < v) (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    (∫ t : UnitAddCircle,
      fourier 0 t * (bohrIndicator v δ t : ℂ) ∂circleHaar) =
        (2 * δ : ℂ) := by
  simp only [fourier_zero, one_mul]
  rw [integral_complex_ofReal, integral_bohrIndicator v δ hv hδ hδhalf]
  norm_cast

private theorem not_dvd_of_natAbs_lt (v : ℕ) (_hv : 0 < v) (n : ℤ)
    (hn : n ≠ 0) (hlt : n.natAbs < v) : ¬ (v : ℤ) ∣ n := by
  intro hdvd
  have hnat : v ∣ n.natAbs := by
    simpa using Int.natAbs_dvd_natAbs.mpr hdvd
  have hpos : 0 < n.natAbs := Int.natAbs_pos.mpr hn
  exact (Nat.not_le_of_gt hlt) (Nat.le_of_dvd hpos hnat)

/-- 论文 `lem:separation` 第 404–416 行的高速度分离。
有限频率集满足 `|k|<R`，若 `v>RG`，则与原 Bohr 指示函数相乘后的积分
只保留零频率系数（零频率未列入 `S` 时按零处理）。 -/
theorem circleFourierPoly_high_separation
    (S : Finset ℤ) (coeff : ℤ → ℂ) (G v R : ℕ) (δ : ℝ)
    (hG : 0 < G) (hv : 0 < v) (_hR : 0 < R)
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hS : ∀ k ∈ S, k.natAbs < R) (hlarge : R * G < v) :
    (∫ t : UnitAddCircle,
      circleFourierPoly S coeff (G • t) *
        (bohrIndicator v δ t : ℂ) ∂circleHaar) =
      (2 * δ : ℂ) * (if (0 : ℤ) ∈ S then coeff 0 else 0) := by
  have hpoint (t : UnitAddCircle) :
      circleFourierPoly S coeff (G • t) * (bohrIndicator v δ t : ℂ) =
        ∑ k ∈ S, coeff k *
          (fourier ((G : ℤ) * k) t * (bohrIndicator v δ t : ℂ)) := by
    rw [circleFourierPoly_nsmul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have htermInt (k : ℤ) : Integrable (fun t : UnitAddCircle =>
      coeff k * (fourier ((G : ℤ) * k) t * (bohrIndicator v δ t : ℂ)))
      circleHaar :=
    (fourier_mul_bohrIndicator_integrable v δ hv hδ hδhalf _).const_mul _
  have hterm (k : ℤ) (hk : k ∈ S) :
      (∫ t : UnitAddCircle,
        fourier ((G : ℤ) * k) t * (bohrIndicator v δ t : ℂ) ∂circleHaar) =
      if k = 0 then (2 * δ : ℂ) else 0 := by
    by_cases hk0 : k = 0
    · subst k
      simp only [mul_zero, ite_true]
      exact integral_fourier_bohrIndicator_zeroFreq v δ hv hδ hδhalf
    · have hGz : (G : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hG)
      have hn0 : (G : ℤ) * k ≠ 0 := mul_ne_zero hGz hk0
      have habs : (((G : ℤ) * k).natAbs) = G * k.natAbs := by
        simp [Int.natAbs_mul]
      have hlt : ((G : ℤ) * k).natAbs < v := by
        rw [habs]
        calc
          G * k.natAbs = k.natAbs * G := Nat.mul_comm _ _
          _ < R * G := Nat.mul_lt_mul_of_pos_right (hS k hk) hG
          _ < v := hlarge
      have hndvd := not_dvd_of_natAbs_lt v hv ((G : ℤ) * k) hn0 hlt
      simp [hk0]
      exact integral_fourier_bohrIndicator_zero v δ ((G : ℤ) * k)
        hv hδ hδhalf hndvd
  calc
    _ = ∫ t : UnitAddCircle, ∑ k ∈ S, coeff k *
          (fourier ((G : ℤ) * k) t * (bohrIndicator v δ t : ℂ)) ∂circleHaar := by
      congr 1
      funext t
      exact hpoint t
    _ = ∑ k ∈ S, coeff k *
          (∫ t : UnitAddCircle,
            fourier ((G : ℤ) * k) t * (bohrIndicator v δ t : ℂ) ∂circleHaar) := by
      rw [integral_finsetSum S (fun k _ => htermInt k)]
      simp_rw [integral_const_mul]
    _ = ∑ k ∈ S, if k = 0 then coeff 0 * (2 * δ : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hterm k hk]
      split_ifs with hk0
      · subst k
        rfl
      · simp
    _ = (2 * δ : ℂ) * (if (0 : ℤ) ∈ S then coeff 0 else 0) := by
      simp [Finset.sum_ite_eq', mul_ite, mul_comm]

end LonelyRunner
