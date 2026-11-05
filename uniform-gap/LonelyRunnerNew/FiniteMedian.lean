import LonelyRunnerNew.CoreCutScalar
import Mathlib.Algebra.Order.BigOperators.Group.Finset

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew.FiniteCore
variable {V : Type*} [DecidableEq V]

def mass (F : Finset V) (pi : V → ℝ) (S : Finset V) : ℝ :=
  ∑ v∈F.filter (·∈S),pi v

theorem mass_filter (F : Finset V) (pi : V → ℝ) (P : V → Prop) [DecidablePred P] :
    mass F pi (F.filter P)=∑ v∈F.filter P,pi v := by
  unfold mass
  congr 1
  ext v
  simp

theorem filtered_mass_partition (F : Finset V) (pi : V → ℝ) (P : V → Prop) [DecidablePred P] :
    (∑ v∈F.filter P,pi v)+(∑ v∈F.filter (fun v => ¬P v),pi v)=∑ v∈F,pi v := by
  simp only [Finset.sum_filter,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases h : P v <;> simp [h]

/-- A genuine finite-range median. Zero-probability vertices are allowed. -/
theorem nat_median_exists (F : Finset V) (pi : V → ℝ) (f : V → ℕ)
    (hpi : ∀ v∈F,0≤pi v) (hs : (∑ v∈F,pi v)=1) :
    ∃ m∈F.image f,(∑ v∈F.filter (fun v => f v<m),pi v)≤1/2 ∧
      (∑ v∈F.filter (fun v => m<f v),pi v)≤1/2 := by
  classical
  let N := F.sup f
  have hf : ∀ v∈F,f v≤N := fun v hv => Finset.le_sup hv
  let C := (Finset.range (N+1)).filter (fun k => (1/2:ℝ)≤∑ v∈F.filter (fun v => f v≤k),pi v)
  have hN : N∈C := by
    have hfilter : F.filter (fun v => f v≤N)=F := Finset.filter_eq_self.mpr hf
    simp only [C,Finset.mem_filter,Finset.mem_range]
    exact ⟨by omega,by rw [hfilter,hs];norm_num⟩
  let m := C.min' ⟨N,hN⟩
  have hm : m∈C := Finset.min'_mem _ _
  have hmN : m≤N := Finset.min'_le _ _ hN
  have hcdf : (1/2:ℝ)≤∑ v∈F.filter (fun v => f v≤m),pi v := (Finset.mem_filter.mp hm).2
  have hprev (k : ℕ) (hk : k<m) : (∑ v∈F.filter (fun v => f v≤k),pi v)<(1/2:ℝ) := by
    apply lt_of_not_ge
    intro hc
    have hkC : k∈C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hc⟩
    have hh := Finset.min'_le C _ hkC
    omega
  have hlow : (∑ v∈F.filter (fun v => f v<m),pi v)≤(1/2:ℝ) := by
    by_cases hm0 : m=0
    · simp [hm0]
    · have hh := hprev (m-1) (by omega)
      have he : F.filter (fun v => f v<m)=F.filter (fun v => f v≤m-1) := by
        apply Finset.filter_congr
        intro v hv
        change f v<m ↔ f v≤m-1
        omega
      rw [he]
      exact hh.le
  have hhigh : (∑ v∈F.filter (fun v => m<f v),pi v)≤(1/2:ℝ) := by
    have hh := filtered_mass_partition F pi (fun v => f v≤m)
    simp only [not_le] at hh
    rw [hs] at hh
    linarith
  have him : m∈F.image f := by
    by_contra hn
    have hne : ∀ v∈F,f v≠m := fun v hv he => hn (Finset.mem_image.mpr ⟨v,hv,he⟩)
    by_cases hm0 : m=0
    · have he : F.filter (fun v => f v≤m)=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro v hv
        have hm := Finset.mem_filter.mp hv
        exact hne v hm.1 (by omega)
      rw [he,Finset.sum_empty] at hcdf
      norm_num at hcdf
    · have hh := hprev (m-1) (by omega)
      have he : F.filter (fun v => f v≤m)=F.filter (fun v => f v≤m-1) := by
        apply Finset.filter_congr
        intro v hv
        have hn := hne v hv
        omega
      rw [he] at hcdf
      linarith
  exact ⟨m,him,hlow,hhigh⟩

def levelIndicator (k x : ℕ) : ℝ := if k<x then 1 else 0

theorem levelIndicator_sum (N x : ℕ) (hx : x≤N) :
    (∑ k∈Finset.range N,levelIndicator k x)=(x:ℝ) := by
  have he : (Finset.range N).filter (fun k => k<x)=Finset.range x := by
    ext k
    simp only [Finset.mem_filter,Finset.mem_range]
    omega
  unfold levelIndicator
  rw [← Finset.sum_filter,he]
  simp

theorem levelIndicator_distance (N x y : ℕ) (hx : x≤N) (hy : y≤N) :
    (∑ k∈Finset.range N,|levelIndicator k x-levelIndicator k y|)=|(x:ℝ)-(y:ℝ)| := by
  have hcase (a b : ℕ) (ha : a≤N) (hb : b≤N) (hab : a≤b) :
      (∑ k∈Finset.range N,|levelIndicator k a-levelIndicator k b|)=(b:ℝ)-(a:ℝ) := by
    have hp (k : ℕ) : |levelIndicator k a-levelIndicator k b|=levelIndicator k b-levelIndicator k a := by
      unfold levelIndicator
      by_cases hk : k<a <;> by_cases hh : k<b <;> simp [hk,hh] <;> omega
    simp_rw [hp]
    rw [Finset.sum_sub_distrib,levelIndicator_sum N b hb,levelIndicator_sum N a ha]
  by_cases hxy : x≤y
  · rw [hcase x y hx hy hxy,abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hxy))]
    ring
  · have he : (∑ k∈Finset.range N,|levelIndicator k x-levelIndicator k y|)=
        ∑ k∈Finset.range N,|levelIndicator k y-levelIndicator k x| := by
      apply Finset.sum_congr rfl
      intro k hk
      exact abs_sub_comm _ _
    rw [he,hcase y x hy hx (by omega),abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast (show y≤x by omega)))]

end LonelyRunnerNew.FiniteCore
