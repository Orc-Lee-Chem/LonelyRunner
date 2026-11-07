import LonelyRunnerNew.BohrPrototypes

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators
namespace LonelyRunnerNew
attribute [local instance] Classical.propDecidable

def unitBohrMultiplicity (V : Finset ℕ) (r x : ℝ) : ℝ :=
  ∑ v∈V,(forbiddenInUnit v r).indicator (fun _ => (1:ℝ)) x

theorem unitBohrMultiplicity_eq_card (V : Finset ℕ) (r x : ℝ) :
    unitBohrMultiplicity V r x=((V.filter (fun v => x∈forbiddenInUnit v r)).card:ℝ) := by
  unfold unitBohrMultiplicity
  simp only [Set.indicator_apply]
  rw [← Finset.sum_filter]
  simp

theorem unitBohrMultiplicity_eq_indicator (V : Finset ℕ) (r : ℝ) :
    unitBohrMultiplicity V r=(Ico (0:ℝ) 1).indicator (bohrMultiplicity V r) := by
  funext x
  by_cases hx : x∈Ico (0:ℝ) 1
  · simp [unitBohrMultiplicity,bohrMultiplicity,forbiddenInUnit,Set.indicator_apply,hx]
  · simp [unitBohrMultiplicity,forbiddenInUnit,Set.indicator_apply,hx]

theorem unitBohrMultiplicity_integrable (V : Finset ℕ) (hV : positive V) (r : ℝ) :
    Integrable (unitBohrMultiplicity V r) volume := by
  exact integrable_finsetSum _ (fun v hv =>
    (integrableOn_const (volume_ne_top_in_unit (fun _ hx => hx.1))).integrable_indicator
      (forbiddenInUnit_measurable v (hV v hv) r))

theorem unitBohrMultiplicity_integral (V : Finset ℕ) (hV : positive V) (r : ℝ) :
    (∫ x,unitBohrMultiplicity V r x)=∑ v∈V,(volume (forbiddenInUnit v r)).toReal := by
  unfold unitBohrMultiplicity
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl (fun v hv => integral_indicator_one (forbiddenInUnit_measurable v (hV v hv) r))
  · intro v hv
    exact (integrableOn_const (volume_ne_top_in_unit (fun _ hx => hx.1))).integrable_indicator
      (forbiddenInUnit_measurable v (hV v hv) r)

theorem unitBohr_tail_one (V : Finset ℕ) (r x : ℝ) :
    IntervalCoverage.tail (unitBohrMultiplicity V r x) 1=
      unitBohrMultiplicity V r x-(forbiddenUnion V r).indicator (fun _ => (1:ℝ)) x := by
  by_cases hx : x∈forbiddenUnion V r
  · obtain ⟨v,hv,hvx⟩ := Set.mem_iUnion₂.mp hx
    have hmem : v∈V.filter (fun v => x∈forbiddenInUnit v r) := Finset.mem_filter.mpr ⟨hv,hvx⟩
    have hn : (1:ℝ)≤unitBohrMultiplicity V r x := by
      rw [unitBohrMultiplicity_eq_card]
      exact_mod_cast Nat.succ_le_iff.mpr (Finset.card_pos.mpr ⟨v,hmem⟩)
    rw [Set.indicator_of_mem hx,IntervalCoverage.tail,Nat.cast_one,max_eq_right (sub_nonneg.mpr hn)]
  · have hz : unitBohrMultiplicity V r x=0 := by
      rw [unitBohrMultiplicity_eq_card]
      have he : V.filter (fun v => x∈forbiddenInUnit v r)=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro v hv
        obtain ⟨hv,hvx⟩ := Finset.mem_filter.mp hv
        exact hx (Set.mem_iUnion₂.mpr ⟨v,hv,hvx⟩)
      simp [he]
    simp [hz,Set.indicator_of_notMem hx,IntervalCoverage.tail]

theorem unitBohr_tail_integrable (V : Finset ℕ) (hV : positive V) (r : ℝ) :
    Integrable (fun x => IntervalCoverage.tail (unitBohrMultiplicity V r x) 1) volume := by
  simp_rw [unitBohr_tail_one]
  exact (unitBohrMultiplicity_integrable V hV r).sub
    ((integrableOn_const (volume_ne_top_in_unit (forbiddenUnion_subset_unit V r))).integrable_indicator
      (forbiddenUnion_measurable V hV r))

theorem bohr_tail_integral_eq_excess (V : Finset ℕ) (hV : positive V) (r : ℝ) :
    (∫ x in (0:ℝ)..1,IntervalCoverage.tail (bohrMultiplicity V r x) 1)=forbiddenExcess V r := by
  have heq : (fun x => IntervalCoverage.tail (unitBohrMultiplicity V r x) 1)=
      (Ico (0:ℝ) 1).indicator (fun x => IntervalCoverage.tail (bohrMultiplicity V r x) 1) := by
    funext x
    rw [unitBohrMultiplicity_eq_indicator]
    by_cases hx : x∈Ico (0:ℝ) 1 <;> simp [Set.indicator_apply,hx,IntervalCoverage.tail]
  have he : (∫ x,IntervalCoverage.tail (unitBohrMultiplicity V r x) 1)=forbiddenExcess V r := by
    simp_rw [unitBohr_tail_one]
    rw [integral_sub (unitBohrMultiplicity_integrable V hV r)
      ((integrableOn_const (volume_ne_top_in_unit (forbiddenUnion_subset_unit V r))).integrable_indicator
      (forbiddenUnion_measurable V hV r)),unitBohrMultiplicity_integral V hV r]
    have hU : (∫ x,(forbiddenUnion V r).indicator (fun _ => (1:ℝ)) x)=
        (volume (forbiddenUnion V r)).toReal :=
      integral_indicator_one (forbiddenUnion_measurable V hV r)
    rw [hU]
    rfl
  rw [heq,integral_indicator measurableSet_Ico,integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)] at he
  exact he

theorem bohr_tail_initial_eq_gap (V : Finset ℕ) (hV : valid V) :
    (∫ x in (0:ℝ)..1,IntervalCoverage.tail (bohrMultiplicity V (1/(2*(V.card:ℝ))) x) 1)=gap V := by
  rw [bohr_tail_integral_eq_excess V hV.1,forbiddenExcess_eq_gap V hV]

theorem bohr_tail_integral_lower (V : Finset ℕ) (hV : positive V) {r : ℝ}
    (hr : 0≤r) (hrhalf : r≤1/2) :
    2*r*(V.card:ℝ)-1≤∫ x in (0:ℝ)..1,IntervalCoverage.tail (bohrMultiplicity V r x) 1 := by
  rw [bohr_tail_integral_eq_excess V hV,forbiddenExcess]
  have hsum : (∑ v∈V,(volume (forbiddenInUnit v r)).toReal)=2*r*(V.card:ℝ) := by
    calc
      _ = ∑ _v∈V,2*r := Finset.sum_congr rfl (fun v hv => by
        rw [forbiddenInUnit_measure v (hV v hv) r hr hrhalf,
          ENNReal.toReal_ofReal (mul_nonneg (by norm_num) hr)])
      _ = _ := by simp [mul_comm]
  have hle : (volume (forbiddenUnion V r)).toReal≤1 := by
    have hh := ENNReal.toReal_mono (by simp : volume (Ico (0:ℝ) 1)≠⊤)
      (measure_mono (forbiddenUnion_subset_unit V r))
    simpa using hh
  rw [hsum]
  linarith

end LonelyRunnerNew
