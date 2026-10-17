import LonelyRunner.CoreGridOverlap

/-! # 论文 `lem:exceptions`：既约分母例外速度的有限计数 -/
namespace LonelyRunner
open MeasureTheory

/-- 论文 `lem:exceptions` 第 601–603 行：既约分母大于 `1/δ` 的速度。 -/
noncomputable def denominatorExceptions (V : Finset ℕ) (G : ℕ) (δ : ℝ) : Finset ℕ := by
  classical
  exact V.filter (fun v => (1 / δ : ℝ) < (reducedDenominator G v : ℝ))

/-- 论文 `lem:exceptions` 第 589 行：多数核心块的 Bohr 并集至少占圆周的四分之一。 -/
theorem coreUnion_mass_quarter (V C : Finset ℕ) (m : ℕ) (δ : ℝ)
    (hV : ∀ v ∈ V, 0 < v) (hm : m = V.card) (hm2 : 2 ≤ m)
    (hC : C ⊆ V) (hCmajor : m ≤ 2 * C.card)
    (hcover : Covers V δ) (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hε0 : 0 ≤ 2 * δ * (m : ℝ) - 1)
    (hεhalf : 2 * δ * (m : ℝ) - 1 ≤ 1 / 2) :
    1 / 4 ≤ circleHaar.real (bohrUnion C δ) := by
  have hCpos : ∀ c ∈ C, 0 < c := fun c hc => hV c (hC hc)
  have hE := coverExcess_le_epsilon V C δ hV hδ hδhalf hC hcover
  rw [← hm] at hE
  have hmass := bohrUnion_measureReal_eq_integral_sub_excess C δ
    hCpos hδ hδhalf
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hCR : (m : ℝ) ≤ 2 * (C.card : ℝ) := by exact_mod_cast hCmajor
  have hδmajor : δ * (m : ℝ) ≤ 2 * δ * (C.card : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hCR hδ.le]
  nlinarith [hδmajor]

/-- 论文 `lem:exceptions` 式 `(outsideoverlap)`：核心并集与外部各速度的交集总测度不超过覆盖超额。 -/
theorem coreOutside_overlap_sum (V C : Finset ℕ) (δ : ℝ)
    (hV : ∀ v ∈ V, 0 < v) (hC : C ⊆ V)
    (hcover : Covers V δ) (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    (∑ v ∈ V \ C,
      circleHaar.real (bohrUnion C δ ∩ bohrSet v δ)) ≤
        2 * δ * (V.card : ℝ) - 1 := by
  let U := bohrUnion C δ
  have hCpos : ∀ c ∈ C, 0 < c := fun c hc => hV c (hC hc)
  have hUmeas : MeasurableSet U := bohrUnion_measurable C δ hCpos hδ hδhalf
  have hdisj : Disjoint C (V \ C) := Finset.disjoint_sdiff
  have hUnion : C ∪ (V \ C) = V := Finset.union_sdiff_of_subset hC
  have hY (t : UnitAddCircle) : coverMultiplicity V δ t =
      coverMultiplicity C δ t + ∑ v ∈ V \ C, bohrIndicator v δ t := by
    calc
      coverMultiplicity V δ t =
          coverMultiplicity (C ∪ (V \ C)) δ t := by rw [hUnion]
      _ = coverMultiplicity C δ t + ∑ v ∈ V \ C, bohrIndicator v δ t := by
        change (∑ v ∈ C ∪ (V \ C), bohrIndicator v δ t) =
          (∑ v ∈ C, bohrIndicator v δ t) +
            ∑ v ∈ V \ C, bohrIndicator v δ t
        exact Finset.sum_union hdisj
  have hterm (v : ℕ) (hv : v ∈ V \ C) :
      Integrable ((U ∩ bohrSet v δ).indicator
        (1 : UnitAddCircle → ℝ)) circleHaar :=
    (integrable_const (μ := circleHaar) (1 : ℝ)).indicator
      (hUmeas.inter
        (bohrSet_measurable_measure v δ (hV v (Finset.mem_sdiff.mp hv).1)
          hδ hδhalf).1)
  have hsumInt : Integrable (fun t : UnitAddCircle =>
      ∑ v ∈ V \ C,
        (U ∩ bohrSet v δ).indicator (1 : UnitAddCircle → ℝ) t)
      circleHaar := integrable_finsetSum _ hterm
  have hVint := coverExcess_integrable V δ hV hδ hδhalf
  have hpoint (t : UnitAddCircle) :
      (∑ v ∈ V \ C,
        (U ∩ bohrSet v δ).indicator (1 : UnitAddCircle → ℝ) t) ≤
      max (coverMultiplicity V δ t - 1) 0 := by
    by_cases ht : t ∈ U
    · have hCge : 1 ≤ coverMultiplicity C δ t := by
        have h := coverMultiplicity_eq_excess_add_unionIndicator C δ t
        rw [Set.indicator_of_mem ht] at h
        change coverMultiplicity C δ t =
          max (coverMultiplicity C δ t - 1) 0 + 1 at h
        have hmax : 0 ≤ max (coverMultiplicity C δ t - 1) 0 := le_max_right _ _
        linarith
      have houtside :
          (∑ v ∈ V \ C,
            (U ∩ bohrSet v δ).indicator (1 : UnitAddCircle → ℝ) t) =
          ∑ v ∈ V \ C, bohrIndicator v δ t := by
        apply Finset.sum_congr rfl
        intro v hv
        by_cases hb : t ∈ bohrSet v δ <;>
          simp [bohrIndicator, Set.indicator, ht, hb]
      have hYpos : 0 ≤ ∑ v ∈ V \ C, bohrIndicator v δ t :=
        Finset.sum_nonneg (fun v hv => by
          by_cases hb : t ∈ bohrSet v δ <;>
            simp [bohrIndicator, hb])
      have hVge : 1 ≤ coverMultiplicity V δ t := by
        rw [hY t]
        linarith
      rw [houtside, max_eq_left (by linarith)]
      rw [hY t]
      linarith
    · have hzero :
          (∑ v ∈ V \ C,
            (U ∩ bohrSet v δ).indicator (1 : UnitAddCircle → ℝ) t) = 0 := by
        apply Finset.sum_eq_zero
        intro v hv
        simp [Set.indicator, ht]
      rw [hzero]
      exact le_max_right _ _
  have hle := integral_mono hsumInt hVint hpoint
  rw [integral_finsetSum (V \ C) hterm] at hle
  have hsumEq :
      (∑ v ∈ V \ C,
        ∫ t : UnitAddCircle,
          (U ∩ bohrSet v δ).indicator (1 : UnitAddCircle → ℝ) t ∂circleHaar) =
      ∑ v ∈ V \ C, circleHaar.real (U ∩ bohrSet v δ) := by
    apply Finset.sum_congr rfl
    intro v hv
    exact integral_indicator_one
      (hUmeas.inter
        (bohrSet_measurable_measure v δ (hV v (Finset.mem_sdiff.mp hv).1)
          hδ hδhalf).1)
  rw [hsumEq] at hle
  change (∑ v ∈ V \ C,
    circleHaar.real (U ∩ bohrSet v δ)) ≤ coverExcess V δ at hle
  rwa [coverExcess_eq_epsilon V δ hV hδ hδhalf hcover] at hle

/-- 论文 `lem:exceptions` 第 601–603 行：核心速度的既约分母为一，因此不进入分母例外集。 -/
theorem denominatorExceptions_subset_sdiff (V C : Finset ℕ) (G : ℕ)
    (δ : ℝ) (hG : 0 < G) (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hC : C ⊆ V) (hCdvd : ∀ c ∈ C, G ∣ c) :
    denominatorExceptions V G δ ⊆ V \ C := by
  intro v hv
  have hv' := Finset.mem_filter.mp hv
  have hvV : v ∈ V := hv'.1
  have hvNotC : v ∉ C := by
    intro hvC
    have hq : reducedDenominator G v = 1 := by
      simp [reducedDenominator, Nat.gcd_eq_left_iff_dvd.mpr (hCdvd v hvC),
        Nat.div_self hG]
    have hδle : (1 : ℝ) ≤ 1 / δ :=
      (le_div_iff₀ hδ).2 (by linarith)
    have hbad : (1 / δ : ℝ) < (reducedDenominator G v : ℝ) := hv'.2
    rw [hq] at hbad
    have hδle' : (1 : ℝ) ≤ δ⁻¹ := by simpa [one_div] using hδle
    norm_num at hbad
    linarith
  exact Finset.mem_sdiff.mpr ⟨hvV, hvNotC⟩

/-- 论文 `lem:exceptions` 的分母例外部分：不加不可约性或速度高度假设。 -/
theorem denominatorExceptions_bound (V C : Finset ℕ) (G m : ℕ) (δ : ℝ)
    (hV : ∀ v ∈ V, 0 < v) (hm : m = V.card) (hm2 : 2 ≤ m)
    (hC : C ⊆ V) (hCmajor : m ≤ 2 * C.card)
    (hG : 0 < G) (hCdvd : ∀ c ∈ C, G ∣ c)
    (hcover : Covers V δ) (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hε0 : 0 ≤ 2 * δ * (m : ℝ) - 1)
    (hεhalf : 2 * δ * (m : ℝ) - 1 ≤ 1 / 2) :
    let E := denominatorExceptions V G δ
    E ⊆ V \ C ∧
      ((E.card : ℝ) ≤ 8 * (m : ℝ) * (2 * δ * (m : ℝ) - 1)) ∧
      (∀ v ∈ V \ E,
        (reducedDenominator G v : ℝ) ≤ 1 / δ ∧
          1 / δ ≤ 2 * (m : ℝ)) := by
  let E := denominatorExceptions V G δ
  let ε : ℝ := 2 * δ * (m : ℝ) - 1
  let α : ℝ := circleHaar.real (bohrUnion C δ)
  have hEsub : E ⊆ V \ C :=
    denominatorExceptions_subset_sdiff V C G δ hG hδ hδhalf hC hCdvd
  have hα : 1 / 4 ≤ α :=
    coreUnion_mass_quarter V C m δ hV hm hm2 hC hCmajor
      hcover hδ hδhalf hε0 hεhalf
  have houtside := coreOutside_overlap_sum V C δ hV hC hcover hδ hδhalf
  rw [← hm] at houtside
  have hmreal : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hδlower : 1 / (2 * (m : ℝ)) ≤ δ := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (m : ℝ))).2
    nlinarith [hε0]
  have hδbound : 1 / δ ≤ 2 * (m : ℝ) := by
    apply (div_le_iff₀ hδ).2
    have h := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (m : ℝ))).1 hδlower
    nlinarith
  have hterm (v : ℕ) (hv : v ∈ E) :
      1 / (8 * (m : ℝ)) ≤
        circleHaar.real (bohrUnion C δ ∩ bohrSet v δ) := by
    have hvV : v ∈ V := (Finset.mem_sdiff.mp (hEsub hv)).1
    have hvq : (1 / δ : ℝ) < (reducedDenominator G v : ℝ) :=
      (Finset.mem_filter.mp hv).2
    have hq : (0 : ℝ) < reducedDenominator G v := by
      exact_mod_cast (reducedDenominator_pos_dvd G v hG).1
    have hprod := (div_lt_iff₀ hδ).1 hvq
    have hinv : 1 / (reducedDenominator G v : ℝ) < δ :=
      (div_lt_iff₀ hq).2 (by nlinarith [hprod])
    have hgrid := coreGridOverlap_lower C G v δ hG (hV v hvV)
      (fun c hc => hV c (hC hc)) hCdvd hδ hδhalf
    have hαδ : α * δ ≤
        circleHaar.real (bohrUnion C δ ∩ bohrSet v δ) := by
      have hmult : α * δ ≤ α *
          (2 * δ - 1 / (reducedDenominator G v : ℝ)) := by
        nlinarith [mul_le_mul_of_nonneg_left hinv.le (by linarith : 0 ≤ α)]
      exact hmult.trans hgrid
    have hδquarter : 1 / (8 * (m : ℝ)) ≤ δ / 4 := by
      apply (div_le_div_iff₀
        (by positivity : (0 : ℝ) < 8 * (m : ℝ))
        (by norm_num : (0 : ℝ) < 4)).2
      have hh := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (m : ℝ))).1 hδlower
      nlinarith
    have hquarter : δ / 4 ≤ α * δ := by
      nlinarith [mul_le_mul_of_nonneg_right hα hδ.le]
    exact hδquarter.trans (hquarter.trans hαδ)
  have hsumlow : (E.card : ℝ) / (8 * (m : ℝ)) ≤
      ∑ v ∈ E, circleHaar.real (bohrUnion C δ ∩ bohrSet v δ) := by
    calc
      (E.card : ℝ) / (8 * (m : ℝ)) =
          ∑ _v ∈ E, (1 / (8 * (m : ℝ)) : ℝ) := by simp; ring
      _ ≤ _ := Finset.sum_le_sum hterm
  have hsumup : (∑ v ∈ E,
      circleHaar.real (bohrUnion C δ ∩ bohrSet v δ)) ≤ ε := by
    have h := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun v => circleHaar.real (bohrUnion C δ ∩ bohrSet v δ)) hEsub
      (fun v hv hnot => ENNReal.toReal_nonneg)
    exact h.trans houtside
  have hcard : (E.card : ℝ) ≤ 8 * (m : ℝ) * ε := by
    have h := hsumlow.trans hsumup
    have hh := (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * (m : ℝ))).1 h
    nlinarith [hh]
  refine ⟨hEsub, hcard, ?_⟩
  intro v hv
  have hvNotE : v ∉ E := (Finset.mem_sdiff.mp hv).2
  have hq : (reducedDenominator G v : ℝ) ≤ 1 / δ := by
    by_contra hbad
    have hmem : v ∈ E := Finset.mem_filter.mpr
      ⟨(Finset.mem_sdiff.mp hv).1, lt_of_not_ge hbad⟩
    exact hvNotE hmem
  exact ⟨hq, hδbound⟩

#print axioms coreUnion_mass_quarter
#print axioms coreOutside_overlap_sum
#print axioms denominatorExceptions_bound

end LonelyRunner
