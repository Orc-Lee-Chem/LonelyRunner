import LonelyRunner.DenominatorExceptions
import LonelyRunner.BlockSeparation

/-!
# 论文 `lem:exceptions`（第 604–615 行）：高度例外

高度 `T` 为自然数。平滑常数和最终起点都在引入速度集、尺度和高度之前取得。
-/

namespace LonelyRunner
open MeasureTheory

/-- 论文 `eq:nonexceptions`：高度超过 `(mT)^4 G` 的速度。 -/
noncomputable def heightExceptions (V : Finset ℕ) (G m T : ℕ) : Finset ℕ := by
  classical
  exact V.filter (fun v => (m * T)^4 * G < v)

/-- 核心的实际归一化：拉回恢复原集，归一化速度为正且不超过 `T`，闭弧数至多 `mT`。 -/
theorem heightCore_normalization (C : Finset ℕ) (G m T : ℕ)
    (hG : 0 < G) (hcard : C.card ≤ m)
    (hcore : ∀ c ∈ C, c ∈ inverseBoundedMultiples G (T : ℝ)) :
    let W := C.image (fun c => c / G)
    W.image (fun w => G*w) = C ∧
      (∀ w ∈ W, 0 < w ∧ w ≤ T) ∧
      (∑ w ∈ W, (w : ℝ)) ≤ (m : ℝ) * T := by
  classical
  let W := C.image (fun c => c / G)
  have hW : ∀ w ∈ W, 0 < w ∧ w ≤ T := by
    intro w hw
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨k, hk, hkT, rfl⟩ := hcore c hc
    have hkT' : k ≤ T := by exact_mod_cast hkT
    simpa [Nat.mul_div_cancel_left k hG] using And.intro (by omega : 0 < k) hkT'
  have heq : W.image (fun w => G*w) = C := by
    ext c
    constructor
    · intro hc
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hc
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨k, hk, hkT, heq⟩ := hcore z hz
      simpa [heq, Nat.mul_div_cancel_left k hG] using hz
    · intro hc
      refine Finset.mem_image.mpr ⟨c/G, Finset.mem_image.mpr ⟨c, hc, rfl⟩, ?_⟩
      obtain ⟨k, hk, hkT, rfl⟩ := hcore c hc
      simp [Nat.mul_div_cancel_left k hG]
  have hWcard : W.card ≤ m := (Finset.card_image_le).trans hcard
  refine ⟨heq, hW, ?_⟩
  calc
    (∑ w ∈ W, (w : ℝ)) ≤ ∑ _w ∈ W, (T : ℝ) :=
      Finset.sum_le_sum (fun w hw => by exact_mod_cast (hW w hw).2)
    _ = (W.card : ℝ) * T := by simp
    _ ≤ (m : ℝ) * T := by gcongr

/-- 真实 Fejér 有限展开接入高速度分离；结论为实数积分。 -/
theorem circleFejerSmoothing_high_separation {A : Set UnitAddCircle}
    (hA : MeasurableSet A) (G v R : ℕ) (δ : ℝ)
    (hG : 0 < G) (hv : 0 < v) (hR : 1 ≤ R)
    (hδ : 0 < δ) (hδhalf : δ < 1/2) (hlarge : R*G < v) :
    (∫ t : UnitAddCircle, circleFejerSmoothing A R (G • t) *
      bohrIndicator v δ t ∂circleHaar) = 2*δ*circleHaar.real A := by
  have h := circleFourierPoly_high_separation
    (smoothingFrequencySet R) (smoothingFourierCoeff A R) G v R δ
    hG hv (by omega) hδ hδhalf (smoothingFrequencySet_short R hR) hlarge
  have heq :
      (∫ t : UnitAddCircle,
        ((circleFejerSmoothing A R (G • t) * bohrIndicator v δ t : ℝ) : ℂ)
          ∂circleHaar) = ((2*δ*circleHaar.real A : ℝ) : ℂ) := by
    convert h using 1
    · congr 1
      funext t
      push_cast
      rw [circleFejerSmoothing_eq_poly hA R hR]
    · simp [smoothingFrequencySet_zero, smoothingFourierCoeff]
  rw [integral_complex_ofReal] at heq
  exact_mod_cast heq

/-- 高速度与实际核心并集的交集下界；误差来自已定义的真实卷积，非额外假设。 -/
theorem bohrUnion_high_overlap (W : Finset ℕ) (G v R : ℕ) (δ : ℝ)
    (hW : ∀ w ∈ W, 0 < w) (hG : 0 < G) (hv : 0 < v) (hR : 1 ≤ R)
    (hδ : 0 < δ) (hδhalf : δ < 1/2) (hlarge : R*G < v) :
    2*δ*circleHaar.real (bohrUnion (W.image (fun w => G*w)) δ) -
      (∫ t : UnitAddCircle,
        |circleFejerSmoothing (bohrUnion W δ) R (G • t) -
          circleSetIndicator (bohrUnion (W.image (fun w => G*w)) δ) t|
            ∂circleHaar) ≤
      circleHaar.real (bohrUnion (W.image (fun w => G*w)) δ ∩ bohrSet v δ) := by
  let A := bohrUnion W δ
  let U := bohrUnion (W.image (fun w => G*w)) δ
  let f : UnitAddCircle → ℝ := fun t => circleFejerSmoothing A R (G • t)
  have hA : MeasurableSet A := bohrUnion_measurable_arcs W δ hW hδ.le hδhalf
  have hscale : U = (fun t : UnitAddCircle => G • t) ⁻¹' A :=
    bohrUnion_scale W G δ
  have hU : MeasurableSet U := by rw [hscale]; exact hA.preimage (continuous_nsmul G).measurable
  have hB := (bohrSet_measurable_measure v δ hv hδ hδhalf).1
  have hf : Continuous f := (circleFejerSmoothing_continuous hA R).comp (continuous_nsmul G)
  have hfint : Integrable f circleHaar :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiint : Integrable (circleSetIndicator U) circleHaar :=
    (integrable_const (1 : ℝ)).indicator hU
  have herr : Integrable (fun t => |f t - circleSetIndicator U t|) circleHaar :=
    (hfint.sub hiint).abs
  have hprod : Integrable (fun t => f t * bohrIndicator v δ t) circleHaar := by
    convert hfint.indicator hB using 1
    funext t
    by_cases ht : t ∈ bohrSet v δ <;> simp [bohrIndicator, ht]
  have hinter : Integrable (circleSetIndicator (U ∩ bohrSet v δ)) circleHaar :=
    (integrable_const (1 : ℝ)).indicator (hU.inter hB)
  have hpoint (t : UnitAddCircle) : f t * bohrIndicator v δ t ≤
      circleSetIndicator (U ∩ bohrSet v δ) t + |f t - circleSetIndicator U t| := by
    by_cases hb : t ∈ bohrSet v δ
    · have h := le_abs_self (f t - circleSetIndicator U t)
      by_cases ht : t ∈ U <;> simp_all [bohrIndicator, circleSetIndicator] <;> linarith
    · simp [bohrIndicator, circleSetIndicator, hb]
  have hi := integral_mono hprod (hinter.add herr) hpoint
  change (∫ t : UnitAddCircle, f t * bohrIndicator v δ t ∂circleHaar) ≤
    ∫ t : UnitAddCircle, circleSetIndicator (U ∩ bohrSet v δ) t +
      |f t - circleSetIndicator U t| ∂circleHaar at hi
  rw [integral_add hinter herr] at hi
  have hiMeasure : (∫ t : UnitAddCircle,
      circleSetIndicator (U ∩ bohrSet v δ) t ∂circleHaar) =
      circleHaar.real (U ∩ bohrSet v δ) := integral_indicator_one (hU.inter hB)
  rw [hiMeasure] at hi
  have hsep := circleFejerSmoothing_high_separation hA G v R δ hG hv hR hδ hδhalf hlarge
  have hmass : circleHaar.real U = circleHaar.real A := by
    apply congrArg ENNReal.toReal
    rw [hscale]
    exact (circleHaar_measurePreserving_nsmul G hG).measure_preimage hA.nullMeasurableSet
  change (∫ t : UnitAddCircle, f t * bohrIndicator v δ t ∂circleHaar) = _ at hsep
  rw [hsep, ← hmass] at hi
  linarith

/-- 论文高度例外的一致误差估计：`log(2x⁴)≤8x`，门槛只要求 `m≥64C`。 -/
theorem heightSmoothing_numeric (C m x : ℝ) (hC : 0 < C)
    (hm : 2 ≤ m) (hCm : 64*C ≤ m) (hmx : m ≤ x) :
    C*x*Real.log (2*x^4)/x^4 ≤ 1/(8*m) := by
  have hx : 0 < x := by linarith
  have hm0 : 0 < m := by linarith
  have hlog : Real.log (2*x^4) ≤ 8*x := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity), Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_le_self (by norm_num : (0 : ℝ) ≤ 2), Real.log_le_self hx.le]
  calc
    C*x*Real.log (2*x^4)/x^4 ≤ C*x*(8*x)/x^4 := by gcongr
    _ = 8*C/x^2 := by field_simp
    _ ≤ 8*C/m^2 := by gcongr
    _ ≤ 1/(8*m) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      nlinarith [mul_le_mul_of_nonneg_right hCm hm0.le]

/-- 论文高度例外的统一平滑误差：存在绝对起点，与 `T,G,V` 无关。 -/
theorem heightCore_smoothing_error :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ (C : Finset ℕ) (G m T : ℕ) (δ : ℝ),
      M ≤ m → 0 < G → 1 ≤ T → C.card ≤ m →
      (∀ c ∈ C, c ∈ inverseBoundedMultiples G (T : ℝ)) →
      0 < δ → δ < 1/2 →
      (∫ t : UnitAddCircle,
        |circleFejerSmoothing (bohrUnion (C.image (fun c => c/G)) δ)
            ((m*T)^4) (G • t) - circleSetIndicator (bohrUnion C δ) t|
          ∂circleHaar) ≤ 1/(8*(m : ℝ)) := by
  obtain ⟨C₀, hC₀, herror⟩ := bohrUnion_smoothing_error
  obtain ⟨N, hN⟩ := exists_nat_gt (64*C₀)
  refine ⟨max 2 N, le_max_left _ _, ?_⟩
  intro C G m T δ hM hG hT hcard hcore hδ hδhalf
  have hm2 : 2 ≤ m := (le_max_left _ _).trans hM
  have hNm : N ≤ m := (le_max_right _ _).trans hM
  have hCm : 64*C₀ ≤ (m : ℝ) := hN.le.trans (by exact_mod_cast hNm)
  let W := C.image (fun c => c/G)
  obtain ⟨heq, hW, hsum⟩ := heightCore_normalization C G m T hG hcard hcore
  have hWpos : ∀ w ∈ W, 0 < w := fun w hw => (hW w hw).1
  have hmt : m ≤ m*T := by simpa using Nat.mul_le_mul_left m hT
  have hR : 2 ≤ (m*T)^4 := (hm2.trans hmt).trans (Nat.le_self_pow (by decide) _)
  have hpull := bohrUnion_smoothing_pullback_error W G δ ((m*T)^4)
    hG hWpos hδ.le hδhalf
  rw [heq] at hpull
  rw [hpull]
  have h := herror W δ ((m*T)^4) hWpos hδ.le hδhalf hR
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm2
  have hmx : (m : ℝ) ≤ (m : ℝ)*T := by exact_mod_cast hmt
  have hlog : 0 ≤ Real.log (2*((m : ℝ)*T)^4) := by
    apply Real.log_nonneg
    have hRreal : (2 : ℝ) ≤ ((m : ℝ)*T)^4 := by exact_mod_cast hR
    linarith
  calc
    (∫ t : UnitAddCircle,
      |circleFejerSmoothing (bohrUnion W δ) ((m*T)^4) t -
        circleSetIndicator (bohrUnion W δ) t| ∂circleHaar) ≤
        C₀*(∑ w ∈ W, (w : ℝ))*Real.log (2*(((m*T)^4 : ℕ) : ℝ)) /
          (((m*T)^4 : ℕ) : ℝ) := h
    _ ≤ C₀*((m : ℝ)*T)*Real.log (2*((m : ℝ)*T)^4) / ((m : ℝ)*T)^4 := by
      push_cast
      gcongr
    _ ≤ 1/(8*(m : ℝ)) := heightSmoothing_numeric C₀ m ((m : ℝ)*T) hC₀ hmR hCm hmx

/-- 论文第 612–615 行：高度例外的核心外包含关系，只用自然数高度。 -/
theorem heightExceptions_subset_sdiff (V C : Finset ℕ) (G m T : ℕ)
    (hm : 1 ≤ m) (hT : 1 ≤ T)
    (hcore : ∀ c ∈ C, c ∈ inverseBoundedMultiples G (T : ℝ)) :
    heightExceptions V G m T ⊆ V \ C := by
  intro v hv
  obtain ⟨hvV, hvlarge⟩ := Finset.mem_filter.mp hv
  refine Finset.mem_sdiff.mpr ⟨hvV, ?_⟩
  intro hvC
  obtain ⟨k, hk, hkT, rfl⟩ := hcore v hvC
  have hkT' : k ≤ T := by exact_mod_cast hkT
  have hTmt : T ≤ m*T := by simpa using Nat.mul_le_mul_right T hm
  have hTR : T ≤ (m*T)^4 := hTmt.trans (Nat.le_self_pow (by decide) _)
  have hle : G*k ≤ (m*T)^4*G := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left G (hkT'.trans hTR)
  omega

/-- 论文 `lem:exceptions` 高度部分：绝对起点之后，每个高度例外与核心交集至少
为 `αδ≥1/(8m)`，从而例外数不超过 `8mε`。不要求不可约覆盖。 -/
theorem heightExceptions_bound :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ (V C : Finset ℕ) (G m T : ℕ) (δ : ℝ),
      M ≤ m → (∀ v ∈ V, 0 < v) → m = V.card →
      C ⊆ V → m ≤ 2*C.card → 0 < G → 1 ≤ T →
      (∀ c ∈ C, c ∈ inverseBoundedMultiples G (T : ℝ)) →
      Covers V δ → 0 < δ → δ < 1/2 →
      0 ≤ 2*δ*(m : ℝ)-1 → 2*δ*(m : ℝ)-1 ≤ 1/2 →
      let E := heightExceptions V G m T
      E ⊆ V \ C ∧ (E.card : ℝ) ≤ 8*(m : ℝ)*(2*δ*(m : ℝ)-1) ∧
      (∀ v ∈ E,
        circleHaar.real (bohrUnion C δ)*δ ≤
          circleHaar.real (bohrUnion C δ ∩ bohrSet v δ)) ∧
      1/(8*(m : ℝ)) ≤ circleHaar.real (bohrUnion C δ)*δ := by
  obtain ⟨M, hM2, herr⟩ := heightCore_smoothing_error
  refine ⟨M, hM2, ?_⟩
  intro V C G m T δ hM hV hm hC hmajor hG hT hcore hcover hδ hδhalf hε0 hεhalf
  have hm2 : 2 ≤ m := hM2.trans hM
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hcard : C.card ≤ m := by rw [hm]; exact Finset.card_le_card hC
  let W := C.image (fun c => c/G)
  obtain ⟨heq, hW, hsum⟩ := heightCore_normalization C G m T hG hcard hcore
  have hWpos : ∀ w ∈ W, 0 < w := fun w hw => (hW w hw).1
  have hR : 1 ≤ (m*T)^4 := by
    have : 1 ≤ m*T := Nat.one_le_iff_ne_zero.mpr (by positivity)
    exact this.trans (Nat.le_self_pow (by decide) _)
  have hα := coreUnion_mass_quarter V C m δ hV hm hm2 hC hmajor
    hcover hδ hδhalf hε0 hεhalf
  have hδlower : 1/(2*(m : ℝ)) ≤ δ := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2*(m : ℝ))).2
    nlinarith [hε0]
  have hmass : 1/(8*(m : ℝ)) ≤ circleHaar.real (bohrUnion C δ)*δ := by
    have hquarter : 1/(8*(m : ℝ)) ≤ δ/4 := by
      apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 8*(m : ℝ))
        (by norm_num : (0 : ℝ) < 4)).2
      have hh := (div_le_iff₀ (by positivity : (0 : ℝ) < 2*(m : ℝ))).1 hδlower
      nlinarith
    exact hquarter.trans (by nlinarith [mul_le_mul_of_nonneg_right hα hδ.le])
  have hEsub := heightExceptions_subset_sdiff V C G m T (by omega) hT hcore
  have hterm (v : ℕ) (hv : v ∈ heightExceptions V G m T) :
      circleHaar.real (bohrUnion C δ)*δ ≤
        circleHaar.real (bohrUnion C δ ∩ bohrSet v δ) := by
    have hvV : v ∈ V := (Finset.mem_filter.mp hv).1
    have hvlarge : (m*T)^4*G < v := (Finset.mem_filter.mp hv).2
    have h := bohrUnion_high_overlap W G v ((m*T)^4) δ hWpos hG
      (hV v hvV) hR hδ hδhalf hvlarge
    rw [heq] at h
    have he := herr C G m T δ hM hG hT hcard hcore hδ hδhalf
    dsimp [W] at h
    nlinarith [hmass]
  have houtside := coreOutside_overlap_sum V C δ hV hC hcover hδ hδhalf
  rw [← hm] at houtside
  have hsumup : (∑ v ∈ heightExceptions V G m T,
      circleHaar.real (bohrUnion C δ ∩ bohrSet v δ)) ≤ 2*δ*(m : ℝ)-1 :=
    (Finset.sum_le_sum_of_subset_of_nonneg hEsub
      (fun _ _ _ => ENNReal.toReal_nonneg)).trans houtside
  have hsumlow : ((heightExceptions V G m T).card : ℝ)/(8*(m : ℝ)) ≤
      ∑ v ∈ heightExceptions V G m T,
        circleHaar.real (bohrUnion C δ ∩ bohrSet v δ) := by
    calc
      _ = ∑ _v ∈ heightExceptions V G m T, (1/(8*(m : ℝ)) : ℝ) := by simp; ring
      _ ≤ _ := Finset.sum_le_sum (fun v hv => hmass.trans (hterm v hv))
  have hbound := (div_le_iff₀ (by positivity : (0 : ℝ) < 8*(m : ℝ))).1
    (hsumlow.trans hsumup)
  refine ⟨hEsub, ?_, hterm, hmass⟩
  nlinarith [hbound]

#print axioms circleFejerSmoothing_high_separation
#print axioms heightCore_smoothing_error
#print axioms heightExceptions_bound

end LonelyRunner
