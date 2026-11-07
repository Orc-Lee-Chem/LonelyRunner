import LonelyRunnerNew.BohrExcessIntegrals
import Mathlib.Algebra.BigOperators.Intervals

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators
namespace LonelyRunnerNew
attribute [local instance] Classical.propDecidable

theorem integer_tail_sum (m n : ℕ) (hmn : m≤n) :
    2*(∑ k∈Finset.range n,IntervalCoverage.tail (m:ℝ) k)=(m:ℝ)*((m:ℝ)+1) := by
  have he : (∑ k∈Finset.range n,IntervalCoverage.tail (m:ℝ) k)=
      ∑ k∈Finset.range m,IntervalCoverage.tail (m:ℝ) k := by
    symm
    apply Finset.sum_subset (Finset.range_mono hmn)
    intro k _ hkm
    have hmk : m≤k := Nat.le_of_not_gt (fun h => hkm (Finset.mem_range.mpr h))
    have hmkR : (m:ℝ)≤k := by exact_mod_cast hmk
    simp [IntervalCoverage.tail,max_eq_left (sub_nonpos.mpr hmkR)]
  rw [he]
  have hterm : (∑ k∈Finset.range m,IntervalCoverage.tail (m:ℝ) k)=
      ∑ k∈Finset.range m,((m:ℝ)-(k:ℝ)) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkm : (k:ℝ)≤m := by exact_mod_cast Nat.le_of_lt (Finset.mem_range.mp hk)
    simp [IntervalCoverage.tail,max_eq_right (sub_nonneg.mpr hkm)]
  rw [hterm,Finset.sum_sub_distrib]
  have hs : (∑ k∈Finset.range m,(k:ℝ))*2=(m:ℝ)*((m:ℝ)-1) := by
    cases m with
    | zero => simp
    | succ m =>
      have hh := Finset.sum_range_id_mul_two (m+1)
      simp only [Nat.add_sub_cancel] at hh
      have hhR : (∑ k∈Finset.range (m+1),(k:ℝ))*2=((m:ℝ)+1)*(m:ℝ) := by
        have hc := congrArg (fun t : ℕ => (t:ℝ)) hh
        push_cast at hc
        exact hc
      push_cast
      nlinarith only [hhR]
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  nlinarith only [hs]

/-- The finite tail identity includes harmless zero terms beyond the maximum
multiplicity. It covers multiplicities zero and one without exceptions. -/
theorem integer_moment_tails (m n : ℕ) (hmn : m≤n+2) :
    (m:ℝ)*((m:ℝ)-1)-2*IntervalCoverage.tail (m:ℝ) 1=
      2*(∑ k∈Finset.range n,IntervalCoverage.tail (m:ℝ) (k+2)) := by
  have hh := integer_tail_sum m (2+n) (by omega)
  rw [Finset.sum_range_add] at hh
  have he0 : IntervalCoverage.tail (m:ℝ) 0=(m:ℝ) := by
    simp [IntervalCoverage.tail,max_eq_right (Nat.cast_nonneg m : (0:ℝ)≤m)]
  have he : (∑ k∈Finset.range 2,IntervalCoverage.tail (m:ℝ) k)=
      (m:ℝ)+IntervalCoverage.tail (m:ℝ) 1 := by
    norm_num [Finset.sum_range_succ,he0]
  rw [he] at hh
  simp_rw [Nat.add_comm 2] at hh
  nlinarith only [hh]

theorem bohrMultiplicity_eq_card (V : Finset ℕ) (r x : ℝ) :
    bohrMultiplicity V r x=((V.filter (fun v => x∈forbidden v r)).card:ℝ) := by
  unfold bohrMultiplicity
  simp only [Set.indicator_apply]
  rw [← Finset.sum_filter]
  simp

theorem bohr_moment_tails (V : Finset ℕ) (r x : ℝ) :
    bohrMultiplicity V r x*(bohrMultiplicity V r x-1)-
      2*IntervalCoverage.tail (bohrMultiplicity V r x) 1=
      2*(∑ k∈Finset.range V.card,IntervalCoverage.tail (bohrMultiplicity V r x) (k+2)) := by
  rw [bohrMultiplicity_eq_card]
  exact integer_moment_tails _ V.card (by
    have := Finset.card_filter_le V (fun v => x∈forbidden v r)
    omega)

theorem bohr_level_intervalIntegrable (V : Finset ℕ) (hV : positive V) {r : ℝ}
    (hr : r<1/2) (k : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun x => IntervalCoverage.tail (bohrMultiplicity V r x) k) volume a b := by
  have he : (fun x => IntervalCoverage.tail (bohrMultiplicity V r x) k)=
      PeriodicArc.level (bohrPrototypes V) bohrCenter (fun ij => r*bohrRadius ij) k := by
    funext x
    rw [PeriodicArc.level,bohrMultiplicity_eq_prototypes V hV r x hr]
  rw [he]
  exact PeriodicArc.level_intervalIntegrable _ _ _ _ _ _

def bohrHigherMoment (V : Finset ℕ) (r : ℝ) : ℝ :=
  ∫ x in (0:ℝ)..1,bohrMultiplicity V r x*(bohrMultiplicity V r x-1)-
    2*IntervalCoverage.tail (bohrMultiplicity V r x) 1

theorem bohrHigherMoment_eq_tails (V : Finset ℕ) (hV : positive V) {r : ℝ} (hr : r<1/2) :
    bohrHigherMoment V r=2*(∑ k∈Finset.range V.card,
      ∫ x in (0:ℝ)..1,IntervalCoverage.tail (bohrMultiplicity V r x) (k+2)) := by
  unfold bohrHigherMoment
  simp_rw [bohr_moment_tails]
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_finsetSum]
  intro k _
  exact bohr_level_intervalIntegrable V hV hr _ _ _

theorem bohrHigherMoment_dilation (V : Finset ℕ) (hV : positive V) {s t : ℝ}
    (hs : 0<s) (hst : s≤t) (ht : t<1/2) :
    bohrHigherMoment V s/s≤bohrHigherMoment V t/t := by
  rw [bohrHigherMoment_eq_tails V hV (hst.trans_lt ht),bohrHigherMoment_eq_tails V hV ht]
  simp_rw [mul_div_assoc,Finset.sum_div]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun k _ => bohr_level_dilation V hV _ hs hst ht))
    (by norm_num)

end LonelyRunnerNew
