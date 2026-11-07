import LonelyRunnerNew.PhysicalLC
import LonelyRunnerNew.RationalUniversalCount
import LonelyRunnerNew.ActualRationalCount
import LonelyRunnerNew.LabelRankCounting

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew.Saturated

theorem count_image_eq_label_count {ι : Type*} [DecidableEq ι] (F : Finset ι)
    (f : ι → ℚ) (hf : Set.InjOn f (F:Set ι)) (T : ℝ) :
    RoughRational.count (F.image f) T=
      (F.filter (fun x => (RoughRational.product (f x):ℝ)≤T)).card := by
  classical
  unfold RoughRational.count
  rw [Finset.filter_image]
  exact Finset.card_image_of_injOn (hf.mono (Finset.filter_subset _ _))

theorem ratio_product_pos {N x : ℕ} (hN : 0<N) (hx : 0<x) :
    (0:ℝ)<RoughRational.product (CenterNormalization.ratio N x) := by
  have hr := CenterNormalization.ratio_pos hN hx
  have hn := Int.natAbs_pos.mpr (Rat.num_pos.mpr hr).ne'
  exact_mod_cast Nat.mul_pos hn (CenterNormalization.ratio N x).pos

theorem ratio_sector {N : ℕ} (hN : 0<N) {A : ℝ} {x : ℕ}
    (hx : A≤(x:ℝ) ∧ (x:ℝ)<2*A) :
    A/(N:ℝ)≤(CenterNormalization.ratio N x:ℝ) ∧
      (CenterNormalization.ratio N x:ℝ)<2*(A/(N:ℝ)) := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have he : (CenterNormalization.ratio N x:ℝ)=(x:ℝ)/(N:ℝ) := by simp [CenterNormalization.ratio]
  rw [he]
  refine ⟨div_le_div_of_nonneg_right hx.1 hn.le,?_⟩
  have hh := div_lt_div_of_pos_right hx.2 hn
  convert hh using 1 <;> ring

theorem universal_ratio_label_count {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (f : ι → ℕ) (hf : Set.InjOn f (F:Set ι))
    (hp : ∀ x∈F,0<f x) {N : ℕ} (hN : 0<N) {A : ℝ} (hA : 0<A)
    (hr : ∀ x∈F,A≤(f x:ℝ) ∧ (f x:ℝ)<2*A) :
    LabelCountBound F (fun x => (RoughRational.product (CenterNormalization.ratio N (f x)):ℝ))
      0 (Real.sqrt 2) := by
  classical
  intro T hT
  let g : ι → ℚ := fun x => CenterNormalization.ratio N (f x)
  have hg : Set.InjOn g (F:Set ι) := fun x hx y hy he => hf hx hy (CenterNormalization.ratio_injective hN he)
  have hh := RoughRational.count_le_sqrt_two (F.image g) (R:=A/(N:ℝ)) (T:=T)
    (div_pos hA (by exact_mod_cast hN)) hT
    (by intro r hr;obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hr;exact CenterNormalization.ratio_pos hN (hp x hx))
    (by intro r hmem;obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hmem;exact ratio_sector hN (hr x hx))
  rw [count_image_eq_label_count F g hg] at hh
  simpa only [zero_add] using hh

end Saturated
namespace PhysicalState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

def leftProduct (s : PhysicalState Label n) (centers : ℕ → ℕ) (x : Label) : ℝ :=
  RoughRational.product (CenterNormalization.ratio (s.geometry.commonCenter centers) (s.geometry.leftValue x))
def rightProduct (s : PhysicalState Label n) (centers : ℕ → ℕ) (y : Label) : ℝ :=
  RoughRational.product (CenterNormalization.ratio (s.geometry.commonCenter centers) (s.geometry.rightValue y))

theorem leftProduct_pos (s : PhysicalState Label n) (centers : ℕ → ℕ) {x : Label}
    (hx : x∈s.geometry.left) : 0<s.leftProduct centers x :=
  Saturated.ratio_product_pos (s.geometry.commonCenter_pos centers) (s.geometry.left_positive x hx)
theorem rightProduct_pos (s : PhysicalState Label n) (centers : ℕ → ℕ) {y : Label}
    (hy : y∈s.geometry.right) : 0<s.rightProduct centers y :=
  Saturated.ratio_product_pos (s.geometry.commonCenter_pos centers) (s.geometry.right_positive y hy)

theorem universal_label_counts (s : PhysicalState Label n) (centers : ℕ → ℕ) (hr : s.InRange) :
    Saturated.LabelCountBound s.geometry.left (s.leftProduct centers) 0 (Real.sqrt 2) ∧
    Saturated.LabelCountBound s.geometry.right (s.rightProduct centers) 0 (Real.sqrt 2) :=
  ⟨Saturated.universal_ratio_label_count _ _ s.geometry.left_injective s.geometry.left_positive
      (s.geometry.commonCenter_pos centers) s.A_pos hr.1,
    Saturated.universal_ratio_label_count _ _ s.geometry.right_injective s.geometry.right_positive
      (s.geometry.commonCenter_pos centers) s.B_pos hr.2⟩

theorem ordinary_label_counts (s : PhysicalState Label n) (centers : ℕ → ℕ) (hr : s.InRange)
    {ell : ℝ} (hell : 4096≤ell)
    (hL : ∀ x∈s.geometry.left,rough 142 (s.geometry.leftValue x))
    (hR : ∀ y∈s.geometry.right,rough 142 (s.geometry.rightValue y))
    (hsep : TaggedState.separated (Real.exp ell) s.geometry) :
    Saturated.LabelCountBound s.geometry.left (s.leftProduct centers) 1 ((17/25:ℝ)/ell) ∧
    Saturated.LabelCountBound s.geometry.right (s.rightProduct centers) 1 ((17/25:ℝ)/ell) := by
  constructor
  · intro T hT
    have hh := s.geometry.normalized_left_subset_count centers s.geometry.left le_rfl hell s.A_pos hT hL hR hsep hr.1
    have hi : Set.InjOn (fun x => CenterNormalization.ratio (s.geometry.commonCenter centers) (s.geometry.leftValue x))
        (s.geometry.left:Set Label) := fun x hx y hy he => s.geometry.left_injective hx hy
          (CenterNormalization.ratio_injective (s.geometry.commonCenter_pos centers) he)
    rw [Saturated.count_image_eq_label_count _ _ hi] at hh
    calc
      _ ≤ 1+(17/25:ℝ)*T/ell := hh
      _ = _ := by ring
  · intro T hT
    have hh := s.geometry.normalized_right_subset_count centers s.geometry.right le_rfl hell s.B_pos hT hL hR hsep hr.2
    have hi : Set.InjOn (fun y => CenterNormalization.ratio (s.geometry.commonCenter centers) (s.geometry.rightValue y))
        (s.geometry.right:Set Label) := fun x hx y hy he => s.geometry.right_injective hx hy
          (CenterNormalization.ratio_injective (s.geometry.commonCenter_pos centers) he)
    rw [Saturated.count_image_eq_label_count _ _ hi] at hh
    calc
      _ ≤ 1+(17/25:ℝ)*T/ell := hh
      _ = _ := by ring

end PhysicalState
end LonelyRunnerNew
