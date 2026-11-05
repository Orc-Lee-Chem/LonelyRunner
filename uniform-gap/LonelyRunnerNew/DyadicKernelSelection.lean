import LonelyRunnerNew.DyadicPhysicalPartition
import LonelyRunnerNew.SmallPrimeMoments
import Mathlib.Data.Finset.Max

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew.DyadicPhysical

theorem nat_kernel_two {lam : ℝ} (hl0 : 0<lam) (hl1 : lam<1)
    (I J : Finset ℕ) (f g : ℕ → ℝ) (hf : ∀ i∈I,0≤f i) (hg : ∀ j∈J,0≤g j)
    (hsf : (∑ i∈I,f i)=1) (hsg : (∑ j∈J,g j)=1) :
    (∑ i∈I,∑ j∈J,lam^(gap i j)*(f i*g j)^(3/4:ℝ))≤kernelN lam := by
  have hfI : ∀ i∈KernelSteps.natSupport I,0≤f i.toNat := by
    intro i hi
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hi
    simpa only [Int.toNat_natCast] using hf k hk
  have hgJ : ∀ j∈KernelSteps.natSupport J,0≤g j.toNat := by
    intro j hj
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
    simpa only [Int.toNat_natCast] using hg k hk
  have hsI : (∑ i∈KernelSteps.natSupport I,f i.toNat)=1 := by
    unfold KernelSteps.natSupport
    rw [Finset.sum_image KernelSteps.nat_injective.injOn]
    simpa only [Int.toNat_natCast] using hsf
  have hsJ : (∑ j∈KernelSteps.natSupport J,g j.toNat)=1 := by
    unfold KernelSteps.natSupport
    rw [Finset.sum_image KernelSteps.nat_injective.injOn]
    simpa only [Int.toNat_natCast] using hsg
  have h := kernelInput_proved lam hl0 hl1 (KernelSteps.natSupport I) (KernelSteps.natSupport J)
    (fun i => f i.toNat) (fun j => g j.toNat) hfI hgJ hsI hsJ
  simp_rw [KernelSteps.natSupport,Finset.sum_image KernelSteps.nat_injective.injOn] at h
  simp only [Int.toNat_natCast] at h
  calc
    _ = ∑ i∈I,∑ j∈J,lam^(gap i j)*(f i)^(3/4:ℝ)*(g j)^(3/4:ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [Real.mul_rpow (hf i hi) (hg j hj),mul_assoc]
    _ ≤ _ := h

theorem kernelN_ge_one {lam : ℝ} (hl0 : 0<lam) (hl1 : lam<1) : (1:ℝ)≤kernelN lam := by
  have h := nat_kernel_two hl0 hl1 {0} {0} (fun _ => 1) (fun _ => 1)
    (by intros;norm_num) (by intros;norm_num) (by norm_num) (by norm_num)
  simpa [gap] using h

/-- No dependence on the sizes or locations of I and J. -/
theorem weighted_count_kernel {lam L R : ℝ} (hl0 : 0<lam) (hl1 : lam<1)
    (I J : Finset ℕ) (l r : ℕ → ℝ) (hL : 0<L) (hR : 0<R)
    (hl : ∀ i∈I,0≤l i) (hr : ∀ j∈J,0≤r j)
    (hsL : (∑ i∈I,l i)=L) (hsR : (∑ j∈J,r j)=R) :
    (∑ i∈I,∑ j∈J,lam^(gap i j)*(l i*r j)^(3/4:ℝ))≤
      kernelN lam*(L*R)^(3/4:ℝ) := by
  let f := fun i => l i/L
  let g := fun j => r j/R
  have hf : ∀ i∈I,0≤f i := fun i hi => div_nonneg (hl i hi) hL.le
  have hg : ∀ j∈J,0≤g j := fun j hj => div_nonneg (hr j hj) hR.le
  have hsf : (∑ i∈I,f i)=1 := by dsimp [f];rw [← Finset.sum_div,hsL,div_self hL.ne']
  have hsg : (∑ j∈J,g j)=1 := by dsimp [g];rw [← Finset.sum_div,hsR,div_self hR.ne']
  have hk := nat_kernel_two hl0 hl1 I J f g hf hg hsf hsg
  have hA := Real.rpow_pos_of_pos (mul_pos hL hR) (3/4:ℝ)
  have he : (∑ i∈I,∑ j∈J,lam^(gap i j)*(l i*r j)^(3/4:ℝ))=
      (L*R)^(3/4:ℝ)*(∑ i∈I,∑ j∈J,lam^(gap i j)*(f i*g j)^(3/4:ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hprod : f i*g j=(l i*r j)/(L*R) := by dsimp [f,g];ring
    rw [hprod,Real.div_rpow (mul_nonneg (hl i hi) (hr j hj)) (mul_pos hL hR).le]
    field_simp
  rw [he]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hk hA.le

/-- Maximize normalized mass, not raw mass. The kernel proves the full weighted
sum estimate, so no uncontrolled number-of-blocks factor is discarded. -/
theorem select_weighted_block {lam L R : ℝ} (hl0 : 0<lam) (hl1 : lam<1)
    (I J : Finset ℕ) (hI : I.Nonempty) (hJ : J.Nonempty)
    (l r : ℕ → ℝ) (m : ℕ × ℕ → ℝ) (hL : 0<L) (hR : 0<R)
    (hl : ∀ i∈I,0<l i) (hr : ∀ j∈J,0<r j)
    (hsL : (∑ i∈I,l i)=L) (hsR : (∑ j∈J,r j)=R)
    (hm : ∀ ij∈I.product J,0≤m ij) (hM : 0<∑ ij∈I.product J,m ij) :
    ∃ ij∈I.product J,0<m ij ∧
      (∑ kl∈I.product J,m kl)/(L*R)^(3/4:ℝ)≤
        kernelN lam*(m ij/(lam^(gap ij.1 ij.2)*(l ij.1*r ij.2)^(3/4:ℝ))) := by
  let d := fun ij : ℕ × ℕ => lam^(gap ij.1 ij.2)*(l ij.1*r ij.2)^(3/4:ℝ)
  let z := fun ij => m ij/d ij
  have hd : ∀ ij∈I.product J,0<d ij := by
    intro ij hij
    have hh := Finset.mem_product.mp hij
    exact mul_pos (pow_pos hl0 _) (Real.rpow_pos_of_pos (mul_pos (hl ij.1 hh.1) (hr ij.2 hh.2)) _)
  obtain ⟨ij,hij,hmax⟩ := Finset.exists_max_image (I.product J) z (hI.product hJ)
  have hz : 0≤z ij := div_nonneg (hm ij hij) (hd ij hij).le
  have hsum : (∑ kl∈I.product J,m kl)≤z ij*(∑ kl∈I.product J,d kl) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro kl hkl
    exact (div_le_iff₀ (hd kl hkl)).mp (hmax kl hkl)
  have hk := weighted_count_kernel hl0 hl1 I J l r hL hR
    (fun i hi => (hl i hi).le) (fun j hj => (hr j hj).le) hsL hsR
  have hsumD : (∑ kl∈I.product J,d kl)≤kernelN lam*(L*R)^(3/4:ℝ) := by
    simpa only [Finset.product_eq_sprod,Finset.sum_product,d] using hk
  have ht := hsum.trans (mul_le_mul_of_nonneg_left hsumD hz)
  have hbound : (∑ kl∈I.product J,m kl)/(L*R)^(3/4:ℝ)≤kernelN lam*z ij := by
    apply (div_le_iff₀ (Real.rpow_pos_of_pos (mul_pos hL hR) _)).mpr
    nlinarith only [ht]
  have hmpos : 0<m ij := by
    by_contra hn
    have he := le_antisymm (le_of_not_gt hn) (hm ij hij)
    have hz0 : z ij=0 := by dsimp [z];rw [he,zero_div]
    rw [hz0,mul_zero] at hbound
    exact (not_le_of_gt (div_pos hM (Real.rpow_pos_of_pos (mul_pos hL hR) _))) hbound
  exact ⟨ij,hij,hmpos,hbound⟩

end LonelyRunnerNew.DyadicPhysical
