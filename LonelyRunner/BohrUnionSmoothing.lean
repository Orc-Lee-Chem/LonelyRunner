import LonelyRunner.CircleSmoothingError
import LonelyRunner.CircleHighSeparation
import LonelyRunner.BlockExtraction

/-! # Bohr 并集的闭弧表示及 Fejér 平滑 -/
namespace LonelyRunner
open MeasureTheory

/-- 论文 `lem:merge`：正速度 `w` 的 Bohr 集由恰好 `w` 个闭弧表示。 -/
def bohrArcUnion (w : ℕ) (δ : ℝ) : Set UnitAddCircle :=
  circleArcUnion (Finset.range w)
    (fun k => ((k : ℝ) - δ) / (w : ℝ))
    (fun _ => 2 * δ / (w : ℝ))

private theorem integer_coe_zero (n : ℤ) : ((n : ℝ) : UnitAddCircle) = 0 := by
  apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).2
  refine ⟨n, ?_⟩
  simp [zsmul_eq_mul]

theorem bohrSet_eq_bohrArcUnion (w : ℕ) (δ : ℝ)
    (hw : 0 < w) (hδ0 : 0 ≤ δ) (hδhalf : δ < 1 / 2) :
    bohrSet w δ = bohrArcUnion w δ := by
  ext t
  induction t using Quotient.inductionOn with
  | _ x =>
    constructor
    · intro ht
      obtain ⟨y, hy0, hy1, hyt⟩ := (mem_bohrSet_iff w δ (x : UnitAddCircle)).1 ht
      have hwreal : (0 : ℝ) < w := by exact_mod_cast hw
      have hcast : (((w : ℝ) * x - y : ℝ) : UnitAddCircle) = 0 := by
        change ((w : ℝ) * x : UnitAddCircle) - (y : UnitAddCircle) = 0
        rw [show (((w : ℝ) * x : ℝ) : UnitAddCircle) = w • (x : UnitAddCircle) by
          simp [nsmul_eq_mul]]
        rw [← hyt]
        simp
      obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).1 hcast
      have hnreal : (w : ℝ) * x - y = (n : ℝ) := by
        simpa [zsmul_eq_mul] using hn.symm
      let k : ℕ := (n % (w : ℤ)).toNat
      have hk0 : 0 ≤ n % (w : ℤ) := Int.emod_nonneg n (by exact_mod_cast (Nat.ne_of_gt hw))
      have hkreal : (k : ℝ) = ((n % (w : ℤ) : ℤ) : ℝ) := by
        have hkint : (k : ℤ) = n % (w : ℤ) := by
          exact Int.toNat_of_nonneg hk0
        exact_mod_cast hkint
      have hknat : k < w := by
        have hlt : n % (w : ℤ) < (w : ℤ) := Int.emod_lt_of_pos n (by exact_mod_cast hw)
        exact_mod_cast (show (k : ℤ) < (w : ℤ) by simpa [k, Int.toNat_of_nonneg hk0] using hlt)
      let q : ℤ := n / (w : ℤ)
      have hdecomp : (n : ℝ) = (w : ℝ) * (q : ℝ) + (k : ℝ) := by
        have heq := Int.emod_add_ediv_mul n (w : ℤ)
        have : (n : ℤ) = n % (w : ℤ) + n / (w : ℤ) * (w : ℤ) := heq.symm
        exact_mod_cast (by simpa [q, k, Int.toNat_of_nonneg hk0, add_comm, mul_comm] using this)
      have hxeq : (w : ℝ) * (x - (q : ℝ)) = (k : ℝ) + y := by
        nlinarith [hnreal, hdecomp]
      have hxx : x - (q : ℝ) ∈ Set.Icc (((k : ℝ) - δ) / (w : ℝ))
          ((((k : ℝ) - δ) / (w : ℝ)) + 2 * δ / (w : ℝ)) := by
        change ((k : ℝ) - δ) / (w : ℝ) ≤ x - (q : ℝ) ∧
          x - (q : ℝ) ≤ (((k : ℝ) - δ) / (w : ℝ)) + 2 * δ / (w : ℝ)
        constructor
        · apply (div_le_iff₀ hwreal).2
          nlinarith [hy0, hxeq]
        · have hupp : x - (q : ℝ) ≤ ((k : ℝ) + δ) / (w : ℝ) := by
            apply (le_div_iff₀ hwreal).2
            nlinarith [hy1, hxeq]
          convert hupp using 1 <;> ring
      change (x : UnitAddCircle) ∈ circleArcUnion (Finset.range w)
        (fun k => ((k : ℝ) - δ) / (w : ℝ))
        (fun _ => 2 * δ / (w : ℝ))
      change (x : UnitAddCircle) ∈ ⋃ j ∈ Finset.range w,
        closedArc (((j : ℝ) - δ) / (w : ℝ)) (2 * δ / (w : ℝ))
      refine Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr hknat,
        ⟨x - (q : ℝ), hxx, ?_⟩⟩⟩
      change ((x - (q : ℝ) : ℝ) : UnitAddCircle) = (x : UnitAddCircle)
      rw [sub_eq_add_neg, AddCircle.coe_add]
      simp [integer_coe_zero q]
    · intro ht
      change (x : UnitAddCircle) ∈ ⋃ j ∈ Finset.range w,
        closedArc (((j : ℝ) - δ) / (w : ℝ)) (2 * δ / (w : ℝ)) at ht
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp ht
      obtain ⟨hk, x', hx', hxcast⟩ := Set.mem_iUnion.mp hk
      have hwreal : (0 : ℝ) < w := by exact_mod_cast hw
      have hy0 : -δ ≤ (w : ℝ) * x' - (k : ℝ) := by
        have hx0 := (div_le_iff₀ hwreal).1 hx'.1
        nlinarith
      have hy1 : (w : ℝ) * x' - (k : ℝ) ≤ δ := by
        have hx1 := hx'.2
        have hx1' : x' ≤ ((k : ℝ) + δ) / (w : ℝ) := by
          convert hx1 using 1 <;> ring
        have hx1'' := (le_div_iff₀ hwreal).1 hx1'
        nlinarith
      apply (mem_bohrSet_iff w δ (x : UnitAddCircle)).2
      refine ⟨(w : ℝ) * x' - (k : ℝ), hy0, hy1, ?_⟩
      rw [show ((((w : ℝ) * x' - (k : ℝ) : ℝ)) : UnitAddCircle) =
        w • (x' : UnitAddCircle) - ((k : ℝ) : UnitAddCircle) by
          simp [nsmul_eq_mul]]
      have hkzero : ((k : ℝ) : UnitAddCircle) = 0 := by
        simpa using integer_coe_zero (k : ℤ)
      rw [hkzero, sub_zero]
      exact congrArg (w • ·) hxcast

/-- 论文 `lem:merge`：有限速度族的所有闭弧，索引数等于速度之和。 -/
def bohrArcIndices (W : Finset ℕ) : Finset (Σ _w : ℕ, ℕ) :=
  W.sigma (fun w => Finset.range w)

theorem bohrArcIndices_card (W : Finset ℕ) :
    (bohrArcIndices W).card = ∑ w ∈ W, w := by
  simp [bohrArcIndices, Finset.card_sigma]

theorem bohrUnion_eq_circleArcUnion (W : Finset ℕ) (δ : ℝ)
    (hW : ∀ w ∈ W, 0 < w) (hδ0 : 0 ≤ δ) (hδhalf : δ < 1 / 2) :
    bohrUnion W δ = circleArcUnion (bohrArcIndices W)
      (fun p => ((p.2 : ℝ) - δ) / (p.1 : ℝ))
      (fun p => 2 * δ / (p.1 : ℝ)) := by
  ext t
  simp only [bohrUnion, circleArcUnion, bohrArcIndices, Set.mem_iUnion]
  constructor
  · rintro ⟨w, hw, ht⟩
    rw [bohrSet_eq_bohrArcUnion w δ (hW w hw) hδ0 hδhalf] at ht
    change t ∈ ⋃ k ∈ Finset.range w,
      closedArc (((k : ℝ) - δ) / (w : ℝ)) (2 * δ / (w : ℝ)) at ht
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp ht
    obtain ⟨hk, htk⟩ := Set.mem_iUnion.mp hk
    exact ⟨⟨w,k⟩, Finset.mem_sigma.mpr ⟨hw,hk⟩, htk⟩
  · rintro ⟨⟨w,k⟩, hwk, htk⟩
    obtain ⟨hw,hk⟩ := Finset.mem_sigma.mp hwk
    refine ⟨w, hw, ?_⟩
    rw [bohrSet_eq_bohrArcUnion w δ (hW w hw) hδ0 hδhalf]
    change t ∈ ⋃ j ∈ Finset.range w,
      closedArc (((j : ℝ) - δ) / (w : ℝ)) (2 * δ / (w : ℝ))
    exact Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨hk, htk⟩⟩

theorem bohrArc_lengths (W : Finset ℕ) (δ : ℝ)
    (hW : ∀ w ∈ W, 0 < w) (hδ0 : 0 ≤ δ) (hδhalf : δ < 1 / 2) :
    ∀ p ∈ bohrArcIndices W,
      0 ≤ 2 * δ / (p.1 : ℝ) ∧ 2 * δ / (p.1 : ℝ) < 1 := by
  intro ⟨w,k⟩ hp
  have hw : 0 < w := hW w (Finset.mem_sigma.mp hp).1
  have hwreal : (0 : ℝ) < w := by exact_mod_cast hw
  have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast hw
  constructor
  · positivity
  · apply (div_lt_iff₀ hwreal).2
    nlinarith

theorem bohrUnion_measurable_arcs (W : Finset ℕ) (δ : ℝ)
    (hW : ∀ w ∈ W, 0 < w) (hδ0 : 0 ≤ δ) (hδhalf : δ < 1 / 2) :
    MeasurableSet (bohrUnion W δ) := by
  rw [bohrUnion_eq_circleArcUnion W δ hW hδ0 hδhalf]
  exact circleArcUnion_measurable _ _ _ (bohrArc_lengths W δ hW hδ0 hδhalf)

/-- 论文 `lem:merge`：原块 `gW` 的 Bohr 并集，是归一化并集在 `t ↦ g•t` 下的原像。 -/
theorem bohrUnion_scale (W : Finset ℕ) (g : ℕ) (δ : ℝ) :
    bohrUnion (W.image (fun w => g*w)) δ =
      (fun t : UnitAddCircle => g • t) ⁻¹' bohrUnion W δ := by
  ext t
  simp only [bohrUnion, Set.mem_iUnion, Finset.mem_image, Set.mem_preimage]
  constructor
  · rintro ⟨v, hv, ht⟩
    obtain ⟨w, hw, rfl⟩ := hv
    refine ⟨w, hw, ?_⟩
    simpa only [bohrSet, Set.mem_setOf_eq, mul_nsmul] using ht
  · rintro ⟨w, hw, ht⟩
    refine ⟨g*w, ⟨w, hw, rfl⟩, ?_⟩
    simpa only [bohrSet, Set.mem_setOf_eq, mul_nsmul] using ht

theorem bohrUnion_smoothing_bounds (W : Finset ℕ) (δ : ℝ) (R : ℕ)
    (hW : ∀ w ∈ W, 0 < w) (hδ0 : 0 ≤ δ) (hδhalf : δ < 1 / 2)
    (hR : 1 ≤ R) (t : UnitAddCircle) :
    0 ≤ circleFejerSmoothing (bohrUnion W δ) R t ∧
      circleFejerSmoothing (bohrUnion W δ) R t ≤ 1 :=
  circleFejerSmoothing_bounds (bohrUnion_measurable_arcs W δ hW hδ0 hδhalf) R hR t

theorem bohrUnion_smoothing_mean (W : Finset ℕ) (δ : ℝ) (R : ℕ)
    (hW : ∀ w ∈ W, 0 < w) (hδ0 : 0 ≤ δ) (hδhalf : δ < 1 / 2)
    (hR : 1 ≤ R) :
    (∫ t : UnitAddCircle, circleFejerSmoothing (bohrUnion W δ) R t ∂circleHaar) =
      circleHaar.real (bohrUnion W δ) :=
  circleFejerSmoothing_integral (bohrUnion_measurable_arcs W δ hW hδ0 hδhalf) R hR

theorem bohrUnion_smoothing_finiteExpansion (W : Finset ℕ) (δ : ℝ) (R : ℕ)
    (hW : ∀ w ∈ W, 0 < w) (hδ0 : 0 ≤ δ) (hδhalf : δ < 1 / 2)
    (hR : 1 ≤ R) (t : UnitAddCircle) :
    (circleFejerSmoothing (bohrUnion W δ) R t : ℂ) =
      (circleHaar.real (bohrUnion W δ) : ℂ) +
      (∑ j ∈ Finset.range (R-1),
        ((circleFejerCoefficient R ((j+1 : ℕ) : ℤ) : ℂ) *
          circleSetFourierCoeff (bohrUnion W δ) ((j+1 : ℕ) : ℤ)) *
          fourier ((j+1 : ℕ) : ℤ) t) +
      (∑ j ∈ Finset.range (R-1),
        ((circleFejerCoefficient R (-((j+1 : ℕ) : ℤ)) : ℂ) *
          circleSetFourierCoeff (bohrUnion W δ) (-((j+1 : ℕ) : ℤ))) *
          fourier (-((j+1 : ℕ) : ℤ)) t) :=
  circleFejerSmoothing_finiteExpansion
    (bohrUnion_measurable_arcs W δ hW hδ0 hδhalf) R hR t

theorem bohrUnion_smoothing_error :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : Finset ℕ) (δ : ℝ) (R : ℕ),
      (∀ w ∈ W, 0 < w) → 0 ≤ δ → δ < 1 / 2 → 2 ≤ R →
      (∫ t : UnitAddCircle,
        |circleFejerSmoothing (bohrUnion W δ) R t -
          circleSetIndicator (bohrUnion W δ) t| ∂circleHaar) ≤
        C * (∑ w ∈ W, (w : ℝ)) * Real.log (2 * (R : ℝ)) / (R : ℝ) := by
  obtain ⟨C, hC, hmain⟩ := circleArcUnion_fejerSmoothing_error
  refine ⟨C, hC, ?_⟩
  intro W δ R hW hδ0 hδhalf hR
  rw [bohrUnion_eq_circleArcUnion W δ hW hδ0 hδhalf]
  have h := hmain (bohrArcIndices W)
    (fun p => ((p.2 : ℝ) - δ) / (p.1 : ℝ))
    (fun p => 2 * δ / (p.1 : ℝ)) R
    (bohrArc_lengths W δ hW hδ0 hδhalf) hR
  simpa [bohrArcIndices_card, Nat.cast_sum] using h

/-- 论文 `lem:merge`：尺度拉回的平滑误差与归一化集合完全相同。 -/
theorem bohrUnion_smoothing_pullback_error (W : Finset ℕ) (g : ℕ) (δ : ℝ)
    (R : ℕ) (hg : 0 < g) (hW : ∀ w ∈ W, 0 < w)
    (hδ0 : 0 ≤ δ) (hδhalf : δ < 1 / 2) :
    (∫ t : UnitAddCircle,
      |circleFejerSmoothing (bohrUnion W δ) R (g • t) -
        circleSetIndicator (bohrUnion (W.image (fun w => g*w)) δ) t| ∂circleHaar) =
      (∫ t : UnitAddCircle,
      |circleFejerSmoothing (bohrUnion W δ) R t -
        circleSetIndicator (bohrUnion W δ) t| ∂circleHaar) := by
  let A := bohrUnion W δ
  have hA : MeasurableSet A := bohrUnion_measurable_arcs W δ hW hδ0 hδhalf
  have hind : ∀ t : UnitAddCircle,
      circleSetIndicator (bohrUnion (W.image (fun w => g*w)) δ) t =
        circleSetIndicator A (g • t) := by
    intro t
    rw [bohrUnion_scale W g δ]
    rfl
  simp_rw [hind]
  let e : UnitAddCircle → ℝ := fun t =>
    |circleFejerSmoothing A R t - circleSetIndicator A t|
  have he : Measurable e := by
    exact (continuous_abs.measurable.comp
      ((circleFejerSmoothing_continuous hA R).measurable.sub
        (measurable_const.indicator hA)))
  have hmap := (circleHaar_measurePreserving_nsmul g hg).map_eq
  change (∫ t : UnitAddCircle, e (g • t) ∂circleHaar) =
    ∫ t : UnitAddCircle, e t ∂circleHaar
  calc
    (∫ t : UnitAddCircle, e (g • t) ∂circleHaar) =
        ∫ t : UnitAddCircle, e t ∂(Measure.map (fun t : UnitAddCircle => g • t) circleHaar) :=
      (integral_map (continuous_nsmul g).measurable.aemeasurable
        he.aestronglyMeasurable).symm
    _ = _ := by rw [hmap]

#print axioms bohrSet_eq_bohrArcUnion
#print axioms bohrUnion_smoothing_pullback_error

end LonelyRunner
