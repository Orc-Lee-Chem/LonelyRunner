import LonelyRunnerNew.UnimodalProgression
import LonelyRunnerNew.RCRowIntegrals

noncomputable section
set_option autoImplicit false
open scoped BigOperators
open MeasureTheory
namespace LonelyRunnerNew.RoughRational
attribute [local instance] Classical.propDecidable

def roughDenominators (B : ℝ) : Finset ℕ := (Finset.Icc 1 ⌊B⌋₊).filter (rough 142)

theorem rough_mod_six {b : ℕ} (hb : rough 142 b) : b%6=1 ∨ b%6=5 := by
  have h2 := hb.2 2 Nat.prime_two (by norm_num)
  have h3 := hb.2 3 Nat.prime_three (by norm_num)
  simp only [Nat.dvd_iff_mod_eq_zero] at h2 h3
  omega

theorem rough_denominator_subset (B : ℝ) : roughDenominators B⊆
    (Finset.Icc 1 ⌊B⌋₊).filter (fun b => b%6=1 ∨ b%6=5) := by
  intro b hb
  have hh := Finset.mem_filter.mp hb
  exact Finset.mem_filter.mpr ⟨hh.1,rough_mod_six hh.2⟩

theorem rough_denominator_mem {B : ℝ} (hB : 0≤B) {b : ℕ} (hb : b∈roughDenominators B) :
    (b:ℝ)∈Set.Icc 0 B := by
  have hh := Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1
  exact ⟨Nat.cast_nonneg _,(by exact_mod_cast hh.2 : (b:ℝ)≤⌊B⌋₊).trans (Nat.floor_le hB)⟩

theorem rough_denominator_weighted (g : ℝ → ℝ) {B M : ℝ} (hB : 128≤B)
    (hc : ContinuousOn g (Set.Icc 1 B)) (hb : UnimodalGrid.BetweenLower g 0 B)
    (hpos : ∀x∈Set.Icc 0 B,0≤g x) (hM : ∀x∈Set.Icc 0 B,g x≤M)
    (hInt : IntervalIntegrable g volume 0 B) :
    (∑b∈roughDenominators B,g (b:ℝ))≤(1/3:ℝ)*(∫t in (0:ℝ)..B,g t)+2*M := by
  have hs : (∑b∈roughDenominators B,g (b:ℝ))≤
      ∑b∈(Finset.Icc 1 ⌊B⌋₊).filter (fun b => b%6=1 ∨ b%6=5),g (b:ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (rough_denominator_subset B)
    intro b hb hnot
    have hh := Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1
    apply hpos
    exact ⟨Nat.cast_nonneg _,(by exact_mod_cast hh.2 : (b:ℝ)≤⌊B⌋₊).trans (Nat.floor_le (by linarith))⟩
  exact hs.trans (UnimodalGrid.two_residue_sum g hB hc hb hpos hM hInt)

theorem rough_cap_sum {R T B : ℝ} (hR : 0<R) (hB : 128≤B) (hBT : R*B^2=T) :
    (∑b∈roughDenominators B,RowKernels.cap R T (b:ℝ))≤
      T*(1+Real.log 2)/6+2*Real.sqrt 2*T/B := by
  have hb0 : 0<B := by linarith
  have hp := rough_denominator_weighted (RowKernels.cap R T) hB
    (RowKernels.cap_continuous (by norm_num)) (RowKernels.cap_between hR hb0 hBT)
    (fun x hx => (RowKernels.nonneg hR hb0 hBT hx).1)
    (fun x hx => (RowKernels.upper hR hb0 hBT hx).1) (RowKernels.integrable hR hb0 hBT).1
  rw [RowKernels.cap_integral hR hb0 hBT,(RowKernels.maximum_values hR hb0 hBT).1] at hp
  convert hp using 1 <;> ring

theorem rough_gap_sum {R T B : ℝ} (hR : 0<R) (hB : 128≤B) (hBT : R*B^2=T) :
    (∑b∈roughDenominators B,RowKernels.gap R T (b:ℝ))≤
      T*Real.log 2/6+2*T/(Real.sqrt 2*B) := by
  have hb0 : 0<B := by linarith
  have hp := rough_denominator_weighted (RowKernels.gap R T) hB
    (RowKernels.gap_continuous (by norm_num)) (RowKernels.gap_between hR hb0 hBT)
    (fun x hx => (RowKernels.nonneg hR hb0 hBT hx).2)
    (fun x hx => (RowKernels.upper hR hb0 hBT hx).2) (RowKernels.integrable hR hb0 hBT).2
  rw [RowKernels.gap_integral hR hb0 hBT,(RowKernels.maximum_values hR hb0 hBT).2] at hp
  convert hp using 1 <;> ring

theorem physical_root {R T : ℝ} (hR : 0<R) (hT : 0<T) :
    0<Real.sqrt (T/R) ∧ R*(Real.sqrt (T/R))^2=T := by
  refine ⟨Real.sqrt_pos.mpr (div_pos hT hR),?_⟩
  rw [Real.sq_sqrt (div_pos hT hR).le]
  field_simp

theorem rough_cap_sum_crude {R T : ℝ} (hR : 0<R) (hT : 0<T) :
    (∑b∈roughDenominators (Real.sqrt (T/R)),RowKernels.cap R T (b:ℝ))≤(3/2:ℝ)*T := by
  let B := Real.sqrt (T/R)
  have hs : (∑b∈roughDenominators B,RowKernels.cap R T (b:ℝ))≤
      ∑b∈Finset.Icc 1 ⌊B⌋₊,RowKernels.cap R T (b:ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro b hb hnot
    unfold RowKernels.cap
    exact le_min (by positivity) (div_nonneg hT.le (Nat.cast_nonneg _))
  have he : (∑b∈Finset.Icc 1 ⌊B⌋₊,RowKernels.cap R T (b:ℝ))=RoughRow.capSum ⌊B⌋₊ R T := by
    rw [FiniteSelberg.sum_Icc_one]
    unfold RoughRow.capSum RowKernels.cap
    simp only [Nat.cast_add,Nat.cast_one]
  rw [he] at hs
  exact hs.trans (RoughRow.capSum_floor hR hT)

end LonelyRunnerNew.RoughRational
