import LonelyRunnerNew.KernelCells
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section
open scoped BigOperators
open MeasureTheory
namespace LonelyRunnerNew.KernelSteps

def cell (i : ℤ) : Set ℝ := Set.Ico (i:ℝ) ((i:ℝ)+1)
def step (F : Finset ℤ) (x : ℤ → ℝ) (u : ℝ) : ℝ :=
  ∑ i ∈ F, (cell i).indicator (fun _ => x i) u

theorem continuous_integrable_cell (h : ℝ → ℝ) (hc : Continuous h) (i : ℤ) :
    IntegrableOn h (cell i) :=
  hc.continuousOn.integrableOn_Icc.mono_set Set.Ico_subset_Icc_self

theorem step_mul_integrable (F : Finset ℤ) (x : ℤ → ℝ) (h : ℝ → ℝ) (hc : Continuous h) :
    Integrable (fun u => step F x u*h u) := by
  have he : (fun u => step F x u*h u) =
      (fun u => ∑ i ∈ F, (cell i).indicator (fun u => x i*h u) u) := by
    funext u
    unfold step
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hu : u ∈ cell i <;> simp [hu]
  rw [he]
  apply integrable_finsetSum
  intro i hi
  exact (continuous_integrable_cell _ (hc.const_mul _) i).integrable_indicator measurableSet_Ico

theorem step_mul_integral (F : Finset ℤ) (x : ℤ → ℝ) (h : ℝ → ℝ) (hc : Continuous h) :
    (∫ u, step F x u*h u) = ∑ i ∈ F, x i*(∫ u in cell i, h u) := by
  have he : (fun u => step F x u*h u) =
      (fun u => ∑ i ∈ F, (cell i).indicator (fun u => x i*h u) u) := by
    funext u
    unfold step
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hu : u ∈ cell i <;> simp [hu]
  rw [he, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    unfold cell
    rw [integral_indicator measurableSet_Ico, integral_const_mul]
  · intro i hi
    exact (continuous_integrable_cell _ (hc.const_mul _) i).integrable_indicator measurableSet_Ico

theorem cell_eq {i j : ℤ} {u : ℝ} (hi : u ∈ cell i) (hj : u ∈ cell j) : i=j := by
  have hij : (i:ℝ) < (j:ℝ)+1 := lt_of_le_of_lt hi.1 hj.2
  have hji : (j:ℝ) < (i:ℝ)+1 := lt_of_le_of_lt hj.1 hi.2
  have hij' : i < j+1 := by exact_mod_cast hij
  have hji' : j < i+1 := by exact_mod_cast hji
  omega

theorem step_eq_at_cell (F : Finset ℤ) (x : ℤ → ℝ) {i : ℤ} (hi : i ∈ F)
    {u : ℝ} (hu : u ∈ cell i) : step F x u=x i := by
  unfold step
  rw [Finset.sum_eq_single i]
  · simp [hu]
  · intro j hj hji
    have : u ∉ cell j := fun h => hji (cell_eq h hu)
    simp [this]
  · exact fun h => (h hi).elim

theorem norm_power_step (F : Finset ℤ) (x : ℤ → ℝ) (u : ℝ) :
    |step F x u|^(4/3:ℝ) = step F (fun i => |x i|^(4/3:ℝ)) u := by
  by_cases hex : ∃ i ∈ F, u ∈ cell i
  · obtain ⟨i,hi,hu⟩ := hex
    rw [step_eq_at_cell F x hi hu, step_eq_at_cell F _ hi hu]
  · have hnone : ∀ i ∈ F, u ∉ cell i := by simpa using hex
    have hz (y : ℤ → ℝ) : step F y u=0 := by
      unfold step
      apply Finset.sum_eq_zero
      intro i hi
      simp [hnone i hi]
    rw [hz x,hz (fun i => |x i|^(4/3:ℝ))]
    norm_num

theorem cell_one_integral (i : ℤ) : (∫ u in cell i, (1:ℝ))=1 := by
  unfold cell
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : (i:ℝ)≤(i:ℝ)+1)]
  simp

theorem step_integral (F : Finset ℤ) (x : ℤ → ℝ) :
    (∫ u, step F x u) = ∑ i ∈ F, x i := by
  simpa only [mul_one, cell_one_integral] using step_mul_integral F x (fun _ => 1) continuous_const

theorem norm_power_integral (F : Finset ℤ) (x : ℤ → ℝ) :
    (∫ u, |step F x u|^(4/3:ℝ)) = ∑ i ∈ F, |x i|^(4/3:ℝ) := by
  simp_rw [norm_power_step]
  exact step_integral F _

theorem norm_power_integrable (F : Finset ℤ) (x : ℤ → ℝ) :
    Integrable (fun u => |step F x u|^(4/3:ℝ)) := by
  simp_rw [norm_power_step]
  simpa only [mul_one] using step_mul_integrable F (fun i => |x i|^(4/3:ℝ)) (fun _ => 1) continuous_const

theorem cell_potential_continuous (a : ℝ) (j : ℤ) :
    Continuous (fun u : ℝ => ∫ v in cell j, Real.exp (-a*|u-v|)) := by
  have hc : Continuous (Function.uncurry (fun u v : ℝ => Real.exp (-a*|u-v|))) := by fun_prop
  have hh := continuous_parametric_integral_of_continuous (μ := volume) hc
    (isCompact_Icc (a := (j:ℝ)) (b := (j:ℝ)+1))
  simpa only [cell, integral_Icc_eq_integral_Ico] using hh

def potential (a : ℝ) (F : Finset ℤ) (y : ℤ → ℝ) (u : ℝ) : ℝ :=
  ∫ v, step F y v*Real.exp (-a*|u-v|)

theorem potential_eq_sum (a : ℝ) (F : Finset ℤ) (y : ℤ → ℝ) (u : ℝ) :
    potential a F y u = ∑ j ∈ F, y j*(∫ v in cell j, Real.exp (-a*|u-v|)) :=
  step_mul_integral F y _ (by fun_prop)

theorem potential_continuous (a : ℝ) (F : Finset ℤ) (y : ℤ → ℝ) :
    Continuous (potential a F y) := by
  have he : potential a F y = fun u => ∑ j ∈ F, y j*(∫ v in cell j, Real.exp (-a*|u-v|)) := by
    funext u
    exact potential_eq_sum a F y u
  rw [he]
  exact continuous_finsetSum _ (fun j _ => (cell_potential_continuous a j).const_mul _)

theorem bilinear_integrable (a : ℝ) (F G : Finset ℤ) (x y : ℤ → ℝ) :
    Integrable (fun u => step F x u*potential a G y u) :=
  step_mul_integrable F x _ (potential_continuous a G y)

theorem joint_integrable (a : ℝ) (F G : Finset ℤ) (x y : ℤ → ℝ) :
    Integrable (fun uv : ℝ × ℝ => step F x uv.1*step G y uv.2*
      Real.exp (-a*|uv.1-uv.2|)) (volume.prod volume) := by
  have he : (fun uv : ℝ × ℝ => step F x uv.1*step G y uv.2*Real.exp (-a*|uv.1-uv.2|)) =
      fun uv => ∑ i ∈ F, ∑ j ∈ G,
        (cell i ×ˢ cell j).indicator (fun uv => x i*y j*Real.exp (-a*|uv.1-uv.2|)) uv := by
    funext uv
    simp only [step, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hu : uv.1 ∈ cell i <;> by_cases hv : uv.2 ∈ cell j <;> simp [hu,hv]
  rw [he]
  apply integrable_finsetSum
  intro i hi
  apply integrable_finsetSum
  intro j hj
  have hc : Continuous (fun uv : ℝ × ℝ => x i*y j*Real.exp (-a*|uv.1-uv.2|)) := by fun_prop
  have hh := hc.continuousOn.integrableOn_compact (μ := volume.prod volume)
    ((isCompact_Icc (a := (i:ℝ)) (b := (i:ℝ)+1)).prod
      (isCompact_Icc (a := (j:ℝ)) (b := (j:ℝ)+1)))
  have hsub : cell i ×ˢ cell j ⊆ Set.Icc (i:ℝ) ((i:ℝ)+1) ×ˢ Set.Icc (j:ℝ) ((j:ℝ)+1) := by
    intro uv huv
    exact ⟨⟨huv.1.1,huv.1.2.le⟩,⟨huv.2.1,huv.2.2.le⟩⟩
  exact (hh.mono_set hsub).integrable_indicator (measurableSet_Ico.prod measurableSet_Ico)

theorem bilinear_cell_identity (a : ℝ) (F G : Finset ℤ) (x y : ℤ → ℝ) :
    (∫ u, step F x u*(∫ v, step G y v*Real.exp (-a*|u-v|))) =
      ∑ i ∈ F, ∑ j ∈ G, KernelCells.cellIntegral a ((i-j).natAbs:ℝ)*x i*y j := by
  change (∫ u, step F x u*potential a G y u) = _
  rw [step_mul_integral F x _ (potential_continuous a G y)]
  apply Finset.sum_congr rfl
  intro i hi
  simp_rw [potential_eq_sum]
  rw [integral_finsetSum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [integral_const_mul]
    have hcell : (∫ u in cell i, ∫ v in cell j, Real.exp (-a*|u-v|)) =
        KernelCells.cellIntegral a ((i-j).natAbs:ℝ) := by
      unfold cell
      simp_rw [integral_Ico_eq_integral_Ioc]
      rw [← intervalIntegral.integral_of_le (by linarith : (i:ℝ)≤(i:ℝ)+1)]
      simp_rw [← intervalIntegral.integral_of_le (by linarith : (j:ℝ)≤(j:ℝ)+1)]
      exact KernelCells.integer_translated_cell a i j
    rw [hcell]
    ring
  · intro j hj
    exact continuous_integrable_cell _ ((cell_potential_continuous a j).const_mul (y j)) i

end LonelyRunnerNew.KernelSteps
