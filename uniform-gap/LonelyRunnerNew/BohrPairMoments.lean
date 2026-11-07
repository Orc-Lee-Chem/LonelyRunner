import LonelyRunnerNew.MultiplicityMoments

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators
namespace LonelyRunnerNew
attribute [local instance] Classical.propDecidable

def bohrPairMass (V : Finset ℕ) (r : ℝ) : ℝ :=
  ∑ u∈V,∑ v∈V,if u=v then 0 else
    (volume (forbiddenInUnit u r∩forbiddenInUnit v r)).toReal
def bohrCommonMass (V : Finset ℕ) (r : ℝ) : ℝ :=
  ∑ u∈V,∑ v∈V,if u=v then 0 else 2*r/height u v
def bohrDifferentMass (V : Finset ℕ) (r : ℝ) : ℝ := bohrPairMass V r-bohrCommonMass V r

theorem unitBohr_pair_identity (V : Finset ℕ) (r x : ℝ) :
    unitBohrMultiplicity V r x*(unitBohrMultiplicity V r x-1)=
      ∑ u∈V,∑ v∈V,if u=v then 0 else
        (forbiddenInUnit u r∩forbiddenInUnit v r).indicator (fun _ => (1:ℝ)) x := by
  let b := fun u => (forbiddenInUnit u r).indicator (fun _ => (1:ℝ)) x
  have hterm (u v : ℕ) : b u*b v=(if u=v then b u else 0)+
      (if u=v then 0 else (forbiddenInUnit u r∩forbiddenInUnit v r).indicator (fun _ => (1:ℝ)) x) := by
    by_cases huv : u=v
    · subst v
      simp only [b,if_pos rfl,add_zero,Set.indicator_apply]
      split_ifs <;> norm_num
    · simp only [huv,if_false,zero_add,b,Set.indicator_apply,Set.mem_inter_iff]
      split_ifs <;> simp_all
  have hs : unitBohrMultiplicity V r x*unitBohrMultiplicity V r x=
      unitBohrMultiplicity V r x+
      ∑ u∈V,∑ v∈V,if u=v then 0 else
        (forbiddenInUnit u r∩forbiddenInUnit v r).indicator (fun _ => (1:ℝ)) x := by
    change (∑ u∈V,b u)*(∑ v∈V,b v)=_
    rw [Finset.sum_mul_sum]
    simp_rw [hterm,Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro u hu
    simp [hu,b]
  nlinarith only [hs]

theorem unitBohr_pair_integrable (V : Finset ℕ) (hV : positive V) (r : ℝ) :
    Integrable (fun x => unitBohrMultiplicity V r x*(unitBohrMultiplicity V r x-1)) volume := by
  simp_rw [unitBohr_pair_identity]
  apply integrable_finsetSum
  intro u hu
  apply integrable_finsetSum
  intro v hv
  by_cases huv : u=v
  · simp only [huv,if_pos rfl]
    exact integrable_zero _ _ _
  · simp only [huv,if_false]
    exact (integrableOn_const (volume_ne_top_in_unit (fun _ hx => hx.1.1))).integrable_indicator
      ((forbiddenInUnit_measurable u (hV u hu) r).inter (forbiddenInUnit_measurable v (hV v hv) r))

theorem unitBohr_pair_integral (V : Finset ℕ) (hV : positive V) (r : ℝ) :
    (∫ x,unitBohrMultiplicity V r x*(unitBohrMultiplicity V r x-1))=bohrPairMass V r := by
  simp_rw [unitBohr_pair_identity]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro u hu
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro v hv
      by_cases huv : u=v
      · simp [huv]
      · simp only [huv,if_false]
        exact integral_indicator_one ((forbiddenInUnit_measurable u (hV u hu) r).inter
          (forbiddenInUnit_measurable v (hV v hv) r))
    · intro v hv
      by_cases huv : u=v
      · simp [huv]
      · simp only [huv,if_false]
        exact (integrableOn_const (volume_ne_top_in_unit (fun _ hx => hx.1.1))).integrable_indicator
          ((forbiddenInUnit_measurable u (hV u hu) r).inter (forbiddenInUnit_measurable v (hV v hv) r))
  · intro u hu
    apply integrable_finsetSum
    intro v hv
    by_cases huv : u=v
    · simp [huv]
    · simp only [huv,if_false]
      exact (integrableOn_const (volume_ne_top_in_unit (fun _ hx => hx.1.1))).integrable_indicator
        ((forbiddenInUnit_measurable u (hV u hu) r).inter (forbiddenInUnit_measurable v (hV v hv) r))

theorem bohrHigherMoment_eq_pair (V : Finset ℕ) (hV : positive V) (r : ℝ) :
    bohrHigherMoment V r=bohrPairMass V r-2*forbiddenExcess V r := by
  have he : (Ico (0:ℝ) 1).indicator (fun x => bohrMultiplicity V r x*(bohrMultiplicity V r x-1)-
      2*IntervalCoverage.tail (bohrMultiplicity V r x) 1)=
      fun x => unitBohrMultiplicity V r x*(unitBohrMultiplicity V r x-1)-
        2*IntervalCoverage.tail (unitBohrMultiplicity V r x) 1 := by
    funext x
    rw [unitBohrMultiplicity_eq_indicator]
    by_cases hx : x∈Ico (0:ℝ) 1 <;> simp [Set.indicator_apply,hx,IntervalCoverage.tail]
  unfold bohrHigherMoment
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),← integral_Ico_eq_integral_Ioc,
    ← integral_indicator measurableSet_Ico,he,integral_sub (unitBohr_pair_integrable V hV r)
      ((unitBohr_tail_integrable V hV r).const_mul 2),integral_const_mul,unitBohr_pair_integral V hV r]
  have ht : (∫ x,IntervalCoverage.tail (unitBohrMultiplicity V r x) 1)=forbiddenExcess V r := by
    have heq : (fun x => IntervalCoverage.tail (unitBohrMultiplicity V r x) 1)=
        (Ico (0:ℝ) 1).indicator (fun x => IntervalCoverage.tail (bohrMultiplicity V r x) 1) := by
      funext x
      rw [unitBohrMultiplicity_eq_indicator]
      by_cases hx : x∈Ico (0:ℝ) 1 <;> simp [Set.indicator_apply,hx,IntervalCoverage.tail]
    rw [heq,integral_indicator measurableSet_Ico,integral_Ico_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),bohr_tail_integral_eq_excess V hV r]
  rw [ht]

theorem bohrCommonMass_scale (V : Finset ℕ) (r s : ℝ) :
    bohrCommonMass V (s*r)=s*bohrCommonMass V r := by
  unfold bohrCommonMass
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  split_ifs <;> ring

/-- Exact dilation after removing the common-center term. Every ordered pair
and every multiplicity level comes from the original speed set. -/
theorem bohrDifferentMass_dilation (V : Finset ℕ) (hV : positive V) {r s : ℝ}
    (hr : 0<r) (hs : 1≤s) (hsr : s*r<1/2) :
    s*bohrDifferentMass V r+2*(forbiddenExcess V (s*r)-s*forbiddenExcess V r)≤
      bohrDifferentMass V (s*r) := by
  have hs0 : 0<s := lt_of_lt_of_le zero_lt_one hs
  have hsr0 : 0<s*r := mul_pos hs0 hr
  have hrt : r≤s*r := by nlinarith
  have hh := bohrHigherMoment_dilation V hV hr hrt hsr
  have hmul := (div_le_div_iff₀ hr hsr0).mp hh
  rw [bohrHigherMoment_eq_pair V hV r,bohrHigherMoment_eq_pair V hV (s*r)] at hmul
  have hp : (bohrPairMass V r-2*forbiddenExcess V r)*s≤
      bohrPairMass V (s*r)-2*forbiddenExcess V (s*r) :=
    (mul_le_mul_iff_right₀ hr).mp (by convert hmul using 1 <;> ring)
  unfold bohrDifferentMass
  rw [bohrCommonMass_scale]
  nlinarith only [hp]

end LonelyRunnerNew
