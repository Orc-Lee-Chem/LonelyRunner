import LonelyRunnerNew.RationalCountProved
import LonelyRunnerNew.CenterRationalAdapter

noncomputable section
set_option autoImplicit false
namespace LonelyRunnerNew.TaggedState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

/-- RC on an actual selected left block, using the SAME parent common N.
The selected block is not assumed stable, and no LC probability is changed. -/
theorem normalized_left_subset_count (s : TaggedState Label n) (centers : ℕ → ℕ)
    (L : Finset Label) (hL : L⊆s.left) {ell A T : ℝ} (hell : 4096≤ell) (hA : 0<A) (hT : 0<T)
    (hroughL : ∀x∈s.left,rough 142 (s.leftValue x))
    (hroughR : ∀y∈s.right,rough 142 (s.rightValue y))
    (hsep : separated (Real.exp ell) s)
    (hrange : ∀x∈L,A≤(s.leftValue x:ℝ) ∧ (s.leftValue x:ℝ)<2*A) :
    (RoughRational.count (L.image (fun x => CenterNormalization.ratio
      (s.commonCenter centers) (s.leftValue x))) T:ℝ)≤1+(17/25:ℝ)*T/ell := by
  let N := s.commonCenter centers
  let S := L.image (fun x => CenterNormalization.ratio N (s.leftValue x))
  have hN : (0:ℝ)<N := by exact_mod_cast s.commonCenter_pos centers
  apply RoughRational.countBound_proved ell (A/(N:ℝ)) T hell (div_pos hA hN) hT S
  · intro r hr
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hr
    exact s.normalized_left_rough centers hroughL hroughR (hL hx)
  · intro r hr
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hr
    have hc : (CenterNormalization.ratio N (s.leftValue x):ℝ)=(s.leftValue x:ℝ)/(N:ℝ) := by
      simp [CenterNormalization.ratio]
    rw [hc]
    refine ⟨div_le_div_of_nonneg_right (hrange x hx).1 hN.le,?_⟩
    have hh := div_lt_div_of_pos_right (hrange x hx).2 hN
    convert hh using 1 <;> ring
  · have hs := s.normalized_left_separated centers hsep
    intro r hr t ht hne
    have hm : S⊆s.left.image (fun x => CenterNormalization.ratio N (s.leftValue x)) := by
      intro q hq
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
      exact Finset.mem_image_of_mem _ (hL hx)
    exact hs r (hm hr) t (hm ht) hne

theorem normalized_right_subset_count (s : TaggedState Label n) (centers : ℕ → ℕ)
    (Z : Finset Label) (hZ : Z⊆s.right) {ell B T : ℝ} (hell : 4096≤ell) (hB : 0<B) (hT : 0<T)
    (hroughL : ∀x∈s.left,rough 142 (s.leftValue x))
    (hroughR : ∀y∈s.right,rough 142 (s.rightValue y))
    (hsep : separated (Real.exp ell) s)
    (hrange : ∀y∈Z,B≤(s.rightValue y:ℝ) ∧ (s.rightValue y:ℝ)<2*B) :
    (RoughRational.count (Z.image (fun y => CenterNormalization.ratio
      (s.commonCenter centers) (s.rightValue y))) T:ℝ)≤1+(17/25:ℝ)*T/ell := by
  let N := s.commonCenter centers
  let S := Z.image (fun y => CenterNormalization.ratio N (s.rightValue y))
  have hN : (0:ℝ)<N := by exact_mod_cast s.commonCenter_pos centers
  apply RoughRational.countBound_proved ell (B/(N:ℝ)) T hell (div_pos hB hN) hT S
  · intro r hr
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hr
    exact s.normalized_right_rough centers hroughL hroughR (hZ hy)
  · intro r hr
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hr
    have hc : (CenterNormalization.ratio N (s.rightValue y):ℝ)=(s.rightValue y:ℝ)/(N:ℝ) := by
      simp [CenterNormalization.ratio]
    rw [hc]
    refine ⟨div_le_div_of_nonneg_right (hrange y hy).1 hN.le,?_⟩
    have hh := div_lt_div_of_pos_right (hrange y hy).2 hN
    convert hh using 1 <;> ring
  · have hs := s.normalized_right_separated centers hsep
    intro r hr t ht hne
    have hm : S⊆s.right.image (fun y => CenterNormalization.ratio N (s.rightValue y)) := by
      intro q hq
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hq
      exact Finset.mem_image_of_mem _ (hZ hy)
    exact hs r (hm hr) t (hm ht) hne

end LonelyRunnerNew.TaggedState
