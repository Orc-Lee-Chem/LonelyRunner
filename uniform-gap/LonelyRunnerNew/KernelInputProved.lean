import LonelyRunnerNew.GreenKernel
import LonelyRunnerNew.Inputs
import LonelyRunnerNew.LargePrimeTails

noncomputable section
open scoped BigOperators
namespace LonelyRunnerNew
namespace KernelProbability

theorem norm_one (F : Finset ℤ) (f : ℤ → ℝ) (hf : ∀ i∈F,0≤f i)
    (hs : (∑ i∈F,f i)=1) : GreenPotential.N F (fun i => (f i)^(3/4:ℝ))=1 := by
  unfold GreenPotential.N
  have he : (∑ i∈F,|(f i)^(3/4:ℝ)|^(4/3:ℝ))=1 := by
    calc
      _ = ∑ i∈F,f i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [abs_of_nonneg (Real.rpow_nonneg (hf i hi) _),← Real.rpow_mul (hf i hi)]
        norm_num
      _ = 1 := hs
  rw [he]
  norm_num

theorem diagonal_le_one (F : Finset ℤ) (f g : ℤ → ℝ)
    (hf : ∀ i∈F,0≤f i) (hg : ∀ i∈F,0≤g i)
    (hsf : (∑ i∈F,f i)=1) (hsg : (∑ i∈F,g i)=1) :
    (∑ i∈F,(f i)^(3/4:ℝ)*(g i)^(3/4:ℝ))≤1 := by
  let m := fun i => (f i+g i)/2
  have hm : ∀ i∈F,0≤m i := fun i hi => by dsimp [m]; linarith [hf i hi,hg i hi]
  have hs : (∑ i∈F,m i)=1 := by
    dsimp [m]
    rw [← Finset.sum_div,Finset.sum_add_distrib,hsf,hsg]
    norm_num
  rw [← hs]
  apply Finset.sum_le_sum
  intro i hi
  have hmi : m i≤1 := by
    rw [← hs]
    exact Finset.single_le_sum hm hi
  calc
    (f i)^(3/4:ℝ)*(g i)^(3/4:ℝ) = (f i*g i)^(3/4:ℝ) := (Real.mul_rpow (hf i hi) (hg i hi)).symm
    _ ≤ (m i)^(3/2:ℝ) := LargePrime.product_rpow_le_mean (hf i hi) (hg i hi)
    _ ≤ (m i)^((1:ℝ)) := Real.rpow_le_rpow_of_exponent_ge' (hm i hi) hmi (by norm_num) (by norm_num)
    _ = m i := Real.rpow_one _

theorem common_support_bound {lam : ℝ} (hl0 : 0<lam) (hl1 : lam<1)
    (F : Finset ℤ) (f g : ℤ → ℝ)
    (hf : ∀ i∈F,0≤f i) (hg : ∀ i∈F,0≤g i)
    (hsf : (∑ i∈F,f i)=1) (hsg : (∑ i∈F,g i)=1) :
    (∑ i∈F,∑ j∈F,lam^(i-j).natAbs*(f i)^(3/4:ℝ)*(g j)^(3/4:ℝ)) ≤ kernelN lam := by
  let a := -Real.log lam
  have ha : 0<a := neg_pos.mpr (Real.log_neg hl0 hl1)
  have he : Real.exp (-a)=lam := by dsimp [a]; rw [neg_neg,Real.exp_log hl0]
  have hc := GreenPotential.sharp_cell_bound ha F (fun i => (f i)^(3/4:ℝ)) (fun j => (g j)^(3/4:ℝ))
    (fun i hi => Real.rpow_nonneg (hf i hi) _) (fun j hj => Real.rpow_nonneg (hg j hj) _)
  rw [norm_one F f hf hsf,norm_one F g hg hsg,mul_one,mul_one,GreenPotential.constant_eq ha] at hc
  have h := KernelCells.enhanced_kernel_of_cell_bound a ha F _ _ hc
  have hd := KernelCells.correction_positive a ha
  rw [KernelCells.correction_coefficient a ha] at hd
  have hD := diagonal_le_one F f g hf hg hsf hsg
  have hmul := mul_le_mul_of_nonneg_left hD hd.le
  rw [he] at h hmul
  dsimp [kernelN]
  change _ ≤ (Real.sqrt 3/2)*lam*a^(3/2:ℝ)/(1-lam)^2+1-2*lam*(a-1+lam)/(1-lam)^2
  linarith

theorem zero_extension_sum (S T : Finset ℤ) (f : ℤ → ℝ) :
    (∑ i∈S∪T,if i∈S then f i else 0)=∑ i∈S,f i := by
  classical
  rw [← Finset.sum_subset (Finset.subset_union_left : S⊆S∪T)
    (fun i _ hi => by simp only [hi,ite_false])]
  apply Finset.sum_congr rfl
  intro i hi
  rw [if_pos hi]

end KernelProbability

/-- The original proposition, including arbitrary integer supports and the
entire open parameter interval. There are no analytic input assumptions. -/
theorem kernelInput_proved : kernelInput := by
  classical
  intro lam hl0 hl1 S T alpha beta ha hb hsa hsb
  let A := fun i => if i∈S then alpha i else 0
  let B := fun j => if j∈T then beta j else 0
  have hA : ∀ i∈S∪T,0≤A i := by intro i _; dsimp [A]; split_ifs with h; exact ha i h; rfl
  have hB : ∀ i∈S∪T,0≤B i := by intro i _; dsimp [B]; split_ifs with h; exact hb i h; rfl
  have hsA : (∑ i∈S∪T,A i)=1 := by rw [KernelProbability.zero_extension_sum]; exact hsa
  have hsB : (∑ i∈S∪T,B i)=1 := by
    rw [Finset.union_comm,KernelProbability.zero_extension_sum]; exact hsb
  have h := KernelProbability.common_support_bound hl0 hl1 (S∪T) A B hA hB hsA hsB
  have he : (∑ i∈S,∑ j∈T,lam^(i-j).natAbs*(alpha i)^(3/4:ℝ)*(beta j)^(3/4:ℝ)) =
      ∑ i∈S∪T,∑ j∈S∪T,lam^(i-j).natAbs*(A i)^(3/4:ℝ)*(B j)^(3/4:ℝ) := by
    calc
      _ = ∑ i∈S,∑ j∈T,lam^(i-j).natAbs*(A i)^(3/4:ℝ)*(B j)^(3/4:ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        simp only [A,B,if_pos hi,if_pos hj]
      _ = _ := by
        rw [← Finset.sum_subset (Finset.subset_union_left : S⊆S∪T)
          (fun i _ hi => by norm_num [A,hi])]
        apply Finset.sum_congr rfl
        intro i hi
        exact Finset.sum_subset Finset.subset_union_right (fun j _ hj => by norm_num [B,hj])
  change (∑ i∈S,∑ j∈T,lam^(i-j).natAbs*(alpha i)^(3/4:ℝ)*(beta j)^(3/4:ℝ)) ≤ kernelN lam
  rw [he]
  exact h

end LonelyRunnerNew
