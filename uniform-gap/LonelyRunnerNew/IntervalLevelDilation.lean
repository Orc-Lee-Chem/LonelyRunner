import LonelyRunnerNew.IntervalMultiplicity
import LonelyRunnerNew.IntervalUnionDilation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators
namespace LonelyRunnerNew.IntervalCoverage
variable {ι : Type*} [DecidableEq ι]
attribute [local instance] Classical.propDecidable

def colorMass {k : ℕ} (F : Finset ι) (L R : ι → ℝ) (col : ι → Fin k) : ℝ :=
  ∑ d : Fin k,(volume (intervalUnion (F.filter (fun i => col i=d)) L R)).toReal

theorem colorMass_integral {k : ℕ} (F : Finset ι) (L R : ι → ℝ) (col : ι → Fin k) :
    (∫ t,∑ d : Fin k,(intervalUnion (F.filter (fun i => col i=d)) L R).indicator (fun _ => (1:ℝ)) t)=
      colorMass F L R col := by
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl (fun d _ => integral_indicator_one
      ((F.filter (fun i => col i=d)).measurableSet_biUnion (fun _ _ => measurableSet_Icc)))
  · intro d hd
    exact intervalUnion_indicator_integrable _ L R

theorem tail_coloring_le {k : ℕ} (F : Finset ι) (L R : ι → ℝ) (col : ι → Fin k) :
    (∫ t,tail (multiplicity F L R t) k)≤(∫ t,multiplicity F L R t)-colorMass F L R col := by
  have hsum : Integrable (fun t => ∑ d : Fin k,
      (intervalUnion (F.filter (fun i => col i=d)) L R).indicator (fun _ => (1:ℝ)) t) volume :=
    integrable_finsetSum _ (fun d _ => intervalUnion_indicator_integrable _ L R)
  have hh := integral_mono (tail_integrable F L R k) ((multiplicity_integrable F L R).sub hsum)
    (fun t => by rw [tail_eq_sub_min];exact sub_le_sub_left (color_count_le F L R col t) _)
  change (∫ t,tail (multiplicity F L R t) k)≤∫ t,multiplicity F L R t-
    ∑ d : Fin k,(intervalUnion (F.filter (fun i => col i=d)) L R).indicator (fun _ => (1:ℝ)) t at hh
  rwa [integral_sub (multiplicity_integrable F L R) hsum,colorMass_integral] at hh

theorem tail_balanced_eq {k : ℕ} (F : Finset ι) (L R : ι → ℝ) (col : ι → Fin k)
    (hc : PairBalanced F L R col) :
    (∫ t,tail (multiplicity F L R t) k)=(∫ t,multiplicity F L R t)-colorMass F L R col := by
  have hsum : Integrable (fun t => ∑ d : Fin k,
      (intervalUnion (F.filter (fun i => col i=d)) L R).indicator (fun _ => (1:ℝ)) t) volume :=
    integrable_finsetSum _ (fun d _ => intervalUnion_indicator_integrable _ L R)
  have heq : (fun t => tail (multiplicity F L R t) k)=fun t => multiplicity F L R t-
      ∑ d : Fin k,(intervalUnion (F.filter (fun i => col i=d)) L R).indicator (fun _ => (1:ℝ)) t := by
    funext t
    rw [tail_eq_sub_min,balanced_color_count F L R col hc t]
  rw [heq,integral_sub (multiplicity_integrable F L R) hsum,colorMass_integral]

theorem multiplicity_scaled_integral (F : Finset ι) (c r : ι → ℝ) {s : ℝ}
    (hs : 0≤s) (hr : ∀ i∈F,0≤r i) :
    (∫ t,multiplicity F (fun i => c i-s*r i) (fun i => c i+s*r i) t)=s*(∑ i∈F,2*r i) := by
  rw [multiplicity_integral,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Real.volume_Icc,ENNReal.toReal_ofReal (by nlinarith [mul_nonneg hs (hr i hi)])]
  ring

theorem colorMass_dilation {k : ℕ} (F : Finset ι) (c r : ι → ℝ) (col : ι → Fin k)
    {s t : ℝ} (hs : 0<s) (hst : s≤t) (hr : ∀ i∈F,0≤r i) :
    colorMass F (fun i => c i-t*r i) (fun i => c i+t*r i) col/t≤
      colorMass F (fun i => c i-s*r i) (fun i => c i+s*r i) col/s := by
  unfold colorMass
  rw [Finset.sum_div,Finset.sum_div]
  exact Finset.sum_le_sum (fun d _ => union_dilation (F.filter (fun i => col i=d)) c r hs hst
    (fun i hi => hr i (Finset.mem_filter.mp hi).1))

/-- Dilation at every multiplicity level on the line. The coloring is proved
by the greedy endpoint invariant; no finite-flow integrality is assumed. -/
theorem tail_dilation (F : Finset ι) (c r : ι → ℝ) (k : ℕ) {s t : ℝ}
    (hs : 0<s) (hst : s≤t) (hr : ∀ i∈F,0≤r i) :
    (∫ x,tail (multiplicity F (fun i => c i-s*r i) (fun i => c i+s*r i) x) k)/s≤
      (∫ x,tail (multiplicity F (fun i => c i-t*r i) (fun i => c i+t*r i) x) k)/t := by
  have ht : 0<t := hs.trans_le hst
  by_cases hk : k=0
  · subst k
    have heq (a : ℝ) : (fun x => tail (multiplicity F (fun i => c i-a*r i) (fun i => c i+a*r i) x) 0)=
        multiplicity F (fun i => c i-a*r i) (fun i => c i+a*r i) := by
      funext x
      simp only [tail,Nat.cast_zero,sub_zero,max_eq_right (multiplicity_nonneg _ _ _ _)]
    rw [heq s,heq t,multiplicity_scaled_integral F c r hs.le hr,multiplicity_scaled_integral F c r ht.le hr]
    field_simp <;> exact le_rfl
  · obtain ⟨col,hcol⟩ := exists_pair_balanced F (fun i => c i-t*r i) (fun i => c i+t*r i) (Nat.pos_of_ne_zero hk)
    have hsmall := tail_coloring_le F (fun i => c i-s*r i) (fun i => c i+s*r i) col
    have hlarge := tail_balanced_eq F (fun i => c i-t*r i) (fun i => c i+t*r i) col hcol
    have hc := colorMass_dilation F c r col hs hst hr
    have hdiv := div_le_div_of_nonneg_right hsmall hs.le
    rw [multiplicity_scaled_integral F c r hs.le hr] at hdiv
    rw [hlarge,multiplicity_scaled_integral F c r ht.le hr]
    let I := ∑ i∈F,2*r i
    have heS : (s*I-colorMass F (fun i => c i-s*r i) (fun i => c i+s*r i) col)/s=
        I-colorMass F (fun i => c i-s*r i) (fun i => c i+s*r i) col/s := by field_simp
    have heT : (t*I-colorMass F (fun i => c i-t*r i) (fun i => c i+t*r i) col)/t=
        I-colorMass F (fun i => c i-t*r i) (fun i => c i+t*r i) col/t := by field_simp
    rw [heS] at hdiv
    rw [heT]
    exact hdiv.trans (sub_le_sub_left hc I)

end LonelyRunnerNew.IntervalCoverage
