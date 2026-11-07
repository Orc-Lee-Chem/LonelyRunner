import LonelyRunnerNew.RoughImageSeparation
import LonelyRunnerNew.CoreScore

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew.TaggedState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

/-- Replace values on the existing labelled graph. In particular, equal rough
values on opposite sides do not remove an edge. This operation is not a Step. -/
def roughImage (s : TaggedState Label n) (centers : ℕ → ℕ)
    (hL : ∀ x∈s.left,s.coreSmallCost centers (Sum.inl x)≤1375)
    (hR : ∀ y∈s.right,s.coreSmallCost centers (Sum.inr y)≤1375)
    (hsep : separated (Real.exp 6880) s) : TaggedState Label n :=
  { s with
    leftValue := fun x => SmallPrimePeeling.roughPart (s.leftValue x)
    rightValue := fun y => SmallPrimePeeling.roughPart (s.rightValue y)
    left_positive := fun x _ => SmallPrimePeeling.roughPart_pos (s.leftValue x)
    right_positive := fun y _ => SmallPrimePeeling.roughPart_pos (s.rightValue y)
    left_injective := (s.bounded_rough_injective centers hL hR hsep).1
    right_injective := (s.bounded_rough_injective centers hL hR hsep).2 }

theorem roughImage_frame (s : TaggedState Label n) (centers : ℕ → ℕ)
    (hL : ∀ x∈s.left,s.coreSmallCost centers (Sum.inl x)≤1375)
    (hR : ∀ y∈s.right,s.coreSmallCost centers (Sum.inr y)≤1375)
    (hsep : separated (Real.exp 6880) s) :
    let r := s.roughImage centers hL hR hsep
    r.left=s.left ∧ r.right=s.right ∧ r.edges=s.edges ∧
    r.leftValue=(fun x => SmallPrimePeeling.roughPart (s.leftValue x)) ∧
    r.rightValue=(fun y => SmallPrimePeeling.roughPart (s.rightValue y)) ∧
    r.a=s.a ∧ r.b=s.b := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem roughImage_rough (s : TaggedState Label n) (centers : ℕ → ℕ)
    (hL : ∀ x∈s.left,s.coreSmallCost centers (Sum.inl x)≤1375)
    (hR : ∀ y∈s.right,s.coreSmallCost centers (Sum.inr y)≤1375)
    (hsep : separated (Real.exp 6880) s) :
    let r := s.roughImage centers hL hR hsep
    (∀ x∈r.left,rough 142 (r.leftValue x)) ∧
    (∀ y∈r.right,rough 142 (r.rightValue y)) := by
  exact ⟨fun x _ => SmallPrimePeeling.roughPart_rough _,
    fun y _ => SmallPrimePeeling.roughPart_rough _⟩

theorem roughImage_separated (s : TaggedState Label n) (centers : ℕ → ℕ)
    (hL : ∀ x∈s.left,s.coreSmallCost centers (Sum.inl x)≤1375)
    (hR : ∀ y∈s.right,s.coreSmallCost centers (Sum.inr y)≤1375)
    (hsep : separated (Real.exp 6880) s) :
    separated (Real.exp 4130) (s.roughImage centers hL hR hsep) :=
  s.bounded_rough_separation centers hL hR hsep

theorem roughImage_mass_ge (s : TaggedState Label n) (centers : ℕ → ℕ)
    (hL : ∀ x∈s.left,s.coreSmallCost centers (Sum.inl x)≤1375)
    (hR : ∀ y∈s.right,s.coreSmallCost centers (Sum.inr y)≤1375)
    (hsep : separated (Real.exp 6880) s) :
    s.edgeMass≤(s.roughImage centers hL hR hsep).edgeMass := by
  unfold edgeMass
  change (∑ e∈s.edges,weight s.a s.b (s.leftValue e.1) (s.rightValue e.2))≤
    ∑ e∈s.edges,weight s.a s.b (SmallPrimePeeling.roughPart (s.leftValue e.1))
      (SmallPrimePeeling.roughPart (s.rightValue e.2))
  apply Finset.sum_le_sum
  intro e he
  have hm := Finset.mem_product.mp (s.edges_subset he)
  exact SmallPrimePeeling.weight_le_rough s.a_positive s.b_positive
    (s.left_positive e.1 hm.1) (s.right_positive e.2 hm.2)

theorem roughImage_quality_ge (s : TaggedState Label n) (centers : ℕ → ℕ)
    (hL : ∀ x∈s.left,s.coreSmallCost centers (Sum.inl x)≤1375)
    (hR : ∀ y∈s.right,s.coreSmallCost centers (Sum.inr y)≤1375)
    (hsep : separated (Real.exp 6880) s) :
    s.quality≤(s.roughImage centers hL hR hsep).quality := by
  have hm : (1:ℝ)*s.edgeMass≤(s.roughImage centers hL hR hsep).edgeMass := by
    simpa only [one_mul] using s.roughImage_mass_ge centers hL hR hsep
  simpa only [Real.one_rpow,one_mul] using
    s.quality_restriction_mass_bound (s.roughImage centers hL hR hsep)
      (by exact Finset.Subset.refl _) (by exact Finset.Subset.refl _) rfl rfl
      (by norm_num : (0:ℝ)≤1) hm

theorem roughImage_universal_quality_ge (s : TaggedState Label n) (centers : ℕ → ℕ)
    (hL : ∀ x∈s.left,s.coreSmallCost centers (Sum.inl x)≤1375)
    (hR : ∀ y∈s.right,s.coreSmallCost centers (Sum.inr y)≤1375)
    (hsep : separated (Real.exp 6880) s) :
    s.universalQuality≤(s.roughImage centers hL hR hsep).universalQuality := by
  have hm : (1:ℝ)*s.edgeMass≤(s.roughImage centers hL hR hsep).edgeMass := by
    simpa only [one_mul] using s.roughImage_mass_ge centers hL hR hsep
  simpa only [one_pow,one_mul] using
    s.universal_quality_restriction_mass_bound (s.roughImage centers hL hR hsep)
      (by exact Finset.Subset.refl _) (by exact Finset.Subset.refl _) rfl rfl
      (by norm_num : (0:ℝ)≤1) hm

end LonelyRunnerNew.TaggedState
