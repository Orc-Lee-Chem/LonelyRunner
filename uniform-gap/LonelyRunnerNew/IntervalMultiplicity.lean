import LonelyRunnerNew.IntervalCoverageColoring
import LonelyRunnerNew.IntervalComponentCover
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators
namespace LonelyRunnerNew.IntervalCoverage
variable {ι : Type*} [DecidableEq ι]
attribute [local instance] Classical.propDecidable

def multiplicity (F : Finset ι) (L R : ι → ℝ) (t : ℝ) : ℝ := (active F L R t).card
def tail (x : ℝ) (k : ℕ) : ℝ := max 0 (x-(k:ℝ))

theorem multiplicity_nonneg (F : Finset ι) (L R : ι → ℝ) (t : ℝ) :
    0≤multiplicity F L R t := Nat.cast_nonneg _
theorem multiplicity_le_card (F : Finset ι) (L R : ι → ℝ) (t : ℝ) :
    multiplicity F L R t≤F.card := by
  unfold multiplicity active
  exact_mod_cast Finset.card_filter_le F (fun i => t∈Icc (L i) (R i))

theorem multiplicity_eq_indicators (F : Finset ι) (L R : ι → ℝ) (t : ℝ) :
    multiplicity F L R t=∑ i∈F,(Icc (L i) (R i)).indicator (fun _ => (1:ℝ)) t := by
  symm
  simp only [Set.indicator_apply]
  rw [←Finset.sum_filter]
  simp [multiplicity,active]

theorem multiplicity_integrable (F : Finset ι) (L R : ι → ℝ) :
    Integrable (multiplicity F L R) volume := by
  have he : multiplicity F L R=fun t => ∑ i∈F,(Icc (L i) (R i)).indicator (fun _ => (1:ℝ)) t :=
    funext (multiplicity_eq_indicators F L R)
  rw [he]
  exact integrable_finsetSum _ (fun i hi =>
    ((continuous_const.continuousOn.integrableOn_Icc : IntegrableOn (fun _ : ℝ => (1:ℝ)) (Icc (L i) (R i))).integrable_indicator measurableSet_Icc))

theorem multiplicity_integral (F : Finset ι) (L R : ι → ℝ) :
    (∫ t,multiplicity F L R t)=∑ i∈F,(volume (Icc (L i) (R i))).toReal := by
  simp_rw [multiplicity_eq_indicators]
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl (fun i _ => integral_indicator_one measurableSet_Icc)
  · intro i hi
    exact (continuous_const.continuousOn.integrableOn_Icc : IntegrableOn (fun _ : ℝ => (1:ℝ))
      (Icc (L i) (R i))).integrable_indicator measurableSet_Icc

theorem tail_nonneg (x : ℝ) (k : ℕ) : 0≤tail x k := le_max_left _ _
theorem tail_le {x : ℝ} (hx : 0≤x) (k : ℕ) : tail x k≤x :=
  max_le hx (sub_le_self _ (Nat.cast_nonneg k))
theorem tail_eq_sub_min (x : ℝ) (k : ℕ) : tail x k=x-min x (k:ℝ) := by
  unfold tail
  by_cases h : x≤(k:ℝ)
  · rw [min_eq_left h,max_eq_left (sub_nonpos.mpr h),sub_self]
  · rw [min_eq_right (le_of_not_ge h),max_eq_right (sub_nonneg.mpr (le_of_not_ge h))]

theorem tail_integrable (F : Finset ι) (L R : ι → ℝ) (k : ℕ) :
    Integrable (fun t => tail (multiplicity F L R t) k) volume := by
  have hi := multiplicity_integrable F L R
  have ha : AEStronglyMeasurable (fun t => tail (multiplicity F L R t) k) volume :=
    (continuous_const.max continuous_id).comp_aestronglyMeasurable
      (hi.aestronglyMeasurable.sub aestronglyMeasurable_const)
  apply hi.mono' ha
  filter_upwards with t
  rw [Real.norm_eq_abs,abs_of_nonneg (tail_nonneg _ _)]
  exact tail_le (multiplicity_nonneg F L R t) k

theorem intervalUnion_indicator_integrable (F : Finset ι) (L R : ι → ℝ) :
    Integrable ((intervalUnion F L R).indicator (fun _ => (1:ℝ))) volume := by
  have hcompact : IsCompact (intervalUnion F L R) := F.isCompact_biUnion (fun _ _ => isCompact_Icc)
  exact (integrableOn_const hcompact.measure_ne_top).integrable_indicator hcompact.measurableSet

theorem color_indicator_count {k : ℕ} (F : Finset ι) (L R : ι → ℝ) (col : ι → Fin k) (t : ℝ) :
    (∑ d : Fin k,(intervalUnion (F.filter (fun i => col i=d)) L R).indicator (fun _ => (1:ℝ)) t)=
      (((active F L R t).image col).card:ℝ) := by
  have he (d : Fin k) : t∈intervalUnion (F.filter (fun i => col i=d)) L R ↔
      d∈(active F L R t).image col := by
    simp only [intervalUnion,Set.mem_iUnion,Finset.mem_filter,Finset.mem_image,active,exists_prop]
    constructor
    · rintro ⟨i,⟨hi,hcol⟩,ht⟩
      exact ⟨i,⟨hi,ht⟩,hcol⟩
    · rintro ⟨i,⟨hi,ht⟩,hcol⟩
      exact ⟨i,⟨hi,hcol⟩,ht⟩
  simp_rw [Set.indicator_apply,he]
  rw [←Finset.sum_filter]
  have hf : Finset.univ.filter (fun d => d∈(active F L R t).image col)=(active F L R t).image col := by ext d;simp
  rw [hf]
  simp

theorem color_count_le {k : ℕ} (F : Finset ι) (L R : ι → ℝ) (col : ι → Fin k) (t : ℝ) :
    (∑ d : Fin k,(intervalUnion (F.filter (fun i => col i=d)) L R).indicator (fun _ => (1:ℝ)) t)≤
      min (multiplicity F L R t) (k:ℝ) := by
  rw [color_indicator_count]
  apply le_min
  · unfold multiplicity
    exact_mod_cast Finset.card_image_le (s:=active F L R t) (f:=col)
  · have hh := Finset.card_le_card (Finset.subset_univ ((active F L R t).image col))
    simpa using (show ((((active F L R t).image col).card:ℝ)≤Fintype.card (Fin k)) by exact_mod_cast hh)

theorem balanced_color_count {k : ℕ} (F : Finset ι) (L R : ι → ℝ) (col : ι → Fin k)
    (hc : PairBalanced F L R col) (t : ℝ) :
    (∑ d : Fin k,(intervalUnion (F.filter (fun i => col i=d)) L R).indicator (fun _ => (1:ℝ)) t)=
      min (multiplicity F L R t) (k:ℝ) := by
  rw [color_indicator_count,colors_card F L R col hc t,Nat.cast_min]
  rfl

end LonelyRunnerNew.IntervalCoverage
