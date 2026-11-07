import LonelyRunnerNew.JointCore
import Mathlib.NumberTheory.SmoothNumbers

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew.SmallPrimePeeling

/-- All multiplicities are retained. This is a filtered prime FACTOR LIST,
not the finite set of distinct prime factors. -/
def smoothPart (x : ℕ) : ℕ := (x.primeFactorsList.filter (·∈Certificate.smallPrimes)).prod
def roughPart (x : ℕ) : ℕ := (x.primeFactorsList.filter (·∉Certificate.smallPrimes)).prod

theorem part_positive (x : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    0<(x.primeFactorsList.filter P).prod := by
  apply Nat.pos_of_ne_zero
  apply List.prod_ne_zero
  intro hzero
  exact (Nat.pos_of_mem_primeFactorsList (List.mem_of_mem_filter hzero)).false

theorem smooth_rough_decomposition {x : ℕ} (hx : 0<x) : smoothPart x*roughPart x=x := by
  have h := List.prod_map_filter_mul_prod_map_filter_not (fun p : ℕ => p∈Certificate.smallPrimes) id x.primeFactorsList
  simp only [List.map_id] at h
  exact h.trans (Nat.prod_primeFactorsList hx.ne')

theorem roughPart_rough (x : ℕ) : rough 142 (roughPart x) := by
  refine ⟨part_positive x _,?_⟩
  intro p hp hp142 hd
  have hmem := mem_list_primes_of_dvd_prod hp.prime
    (fun q hq => (Nat.prime_of_mem_primeFactorsList (List.mem_of_mem_filter hq)).prime) hd
  have hn : p∉Certificate.smallPrimes := by
    simpa only [decide_eq_true_eq] using List.of_mem_filter hmem
  exact hn (Certificate.smallPrimes_mem.mpr ⟨hp,hp142⟩)

/-- Injectivity of the rough map requires separation; it is false globally. -/
theorem roughPart_collision : roughPart 2=1 ∧ roughPart 3=1 ∧ (2:ℕ)≠3 := by decide +kernel

end LonelyRunnerNew.SmallPrimePeeling

namespace LonelyRunnerNew.TaggedState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

def coreSmallPairDistance (s : TaggedState Label n) (v u : Label ⊕ Label) : ℝ :=
  ∑ p∈Certificate.smallPrimes,|(s.coreValuation p v:ℝ)-(s.coreValuation p u:ℝ)| * Real.log (p:ℝ)

theorem coreSmallPairDistance_le_cost (s : TaggedState Label n) (centers : ℕ → ℕ) (v u : Label ⊕ Label) :
    s.coreSmallPairDistance v u≤s.coreSmallCost centers v+s.coreSmallCost centers u := by
  unfold coreSmallPairDistance coreSmallCost
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p hp
  have hl : 0≤Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast (Certificate.smallPrimes_mem.mp hp).1.one_lt.le)
  have ht := abs_sub_le (s.coreValuation p v:ℝ) (centers p:ℝ) (s.coreValuation p u:ℝ)
  rw [abs_sub_comm (centers p:ℝ) (s.coreValuation p u:ℝ)] at ht
  have hh := mul_le_mul_of_nonneg_right ht hl
  simpa only [add_mul] using hh

/-- Any pair of vertices in the joint core, not just an edge. This is the
distortion budget needed next for rough-image injectivity and separation. -/
theorem core_pair_distance_le_2750 (s : TaggedState Label n) (centers : ℕ → ℕ)
    (v u : Label ⊕ Label) (hv : s.coreSmallCost centers v≤1375)
    (hu : s.coreSmallCost centers u≤1375) : s.coreSmallPairDistance v u≤2750 := by
  have h := s.coreSmallPairDistance_le_cost centers v u
  linarith

theorem joint_left_pair_distance (s : TaggedState Label n) (centers : ℕ → ℕ)
    {x y : Label} (hx : x∈s.jointLeft (s.coreSmallCost centers))
    (hy : y∈s.jointLeft (s.coreSmallCost centers)) :
    s.coreSmallPairDistance (Sum.inl x) (Sum.inl y)≤2750 :=
  s.core_pair_distance_le_2750 centers _ _ (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2

theorem joint_right_pair_distance (s : TaggedState Label n) (centers : ℕ → ℕ)
    {x y : Label} (hx : x∈s.jointRight (s.coreSmallCost centers))
    (hy : y∈s.jointRight (s.coreSmallCost centers)) :
    s.coreSmallPairDistance (Sum.inr x) (Sum.inr y)≤2750 :=
  s.core_pair_distance_le_2750 centers _ _ (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2

theorem joint_left_rough_image (s : TaggedState Label n) (centers : ℕ → ℕ)
    {x : Label} (_hx : x∈s.jointLeft (s.coreSmallCost centers)) :
    rough 142 (SmallPrimePeeling.roughPart (s.leftValue x)) := SmallPrimePeeling.roughPart_rough _

theorem joint_right_rough_image (s : TaggedState Label n) (centers : ℕ → ℕ)
    {y : Label} (_hy : y∈s.jointRight (s.coreSmallCost centers)) :
    rough 142 (SmallPrimePeeling.roughPart (s.rightValue y)) := SmallPrimePeeling.roughPart_rough _

end LonelyRunnerNew.TaggedState
