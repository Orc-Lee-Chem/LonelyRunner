import LonelyRunnerNew.PeelingHeightWeight

noncomputable section
set_option autoImplicit false
namespace LonelyRunnerNew.SmallPrimePeeling

theorem rough_height_separation {x y : ℕ} (hx : 0<x) (hy : 0<y)
    (hD : smallDistance x y≤2750) (hsep : Real.exp 6880<height x y) :
    Real.exp 4130<height (roughPart x) (roughPart y) := by
  have hh := height_distortion hx hy
  have hmul := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hD)
    (height_pos (y := roughPart y) (roughPart_pos x)).le
  have ht := hsep.trans_le (hh.trans hmul)
  have he : Real.exp (6880:ℝ)=Real.exp (2750:ℝ)*Real.exp (4130:ℝ) := by
    rw [← Real.exp_add]
    norm_num
  rw [he] at ht
  apply lt_of_not_ge
  intro hn
  have hcontra := mul_le_mul_of_nonneg_left hn (Real.exp_pos (2750:ℝ)).le
  exact (not_lt_of_ge hcontra) ht

theorem height_self_of_pos {x : ℕ} (hx : 0<x) : height x x=1 := by
  unfold height
  rw [max_self,Nat.gcd_self,div_self (by exact_mod_cast hx.ne')]

theorem exp_4130_gt_one : (1:ℝ)<Real.exp 4130 := by
  rw [← Real.exp_zero]
  exact Real.exp_lt_exp.mpr (by norm_num)

theorem rough_height_separation_4096 {x y : ℕ} (hx : 0<x) (hy : 0<y)
    (hD : smallDistance x y≤2750) (hsep : Real.exp 6880<height x y) :
    Real.exp 4096<height (roughPart x) (roughPart y) :=
  (Real.exp_lt_exp.mpr (by norm_num : (4096:ℝ)<4130)).trans (rough_height_separation hx hy hD hsep)

end LonelyRunnerNew.SmallPrimePeeling

namespace LonelyRunnerNew.TaggedState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

theorem step_label_support {s t : TaggedState Label n} (h : Step s t) :
    t.left⊆s.left ∧ t.right⊆s.right ∧ t.edges⊆s.edges := by
  cases h with
  | restrict L R hL hR hLN hRN => exact ⟨hL,hR,Finset.inter_subset_left⟩
  | prime L R hL hR hLN hRN p i j hp u v hfL hfR hnL hnR =>
      exact ⟨hL,hR,Finset.inter_subset_left⟩

theorem reachable_label_support {s t : TaggedState Label n}
    (h : Relation.ReflTransGen Step s t) :
    t.left⊆s.left ∧ t.right⊆s.right ∧ t.edges⊆s.edges := by
  induction h with
  | refl => exact ⟨Finset.Subset.refl _,Finset.Subset.refl _,Finset.Subset.refl _⟩
  | tail _ hs ih =>
      have ht := step_label_support hs
      exact ⟨ht.1.trans ih.1,ht.2.1.trans ih.2.1,ht.2.2.trans ih.2.2⟩

theorem coreSmallCost_congr_values (s t : TaggedState Label n)
    (hL : t.leftValue=s.leftValue) (hR : t.rightValue=s.rightValue) (centers : ℕ → ℕ) (v : Label ⊕ Label) :
    t.coreSmallCost centers v=s.coreSmallCost centers v := by
  unfold coreSmallCost coreValuation
  rw [hL,hR]

theorem left_smallDistance_eq (s : TaggedState Label n) (x y : Label) :
    SmallPrimePeeling.smallDistance (s.leftValue x) (s.leftValue y)=s.coreSmallPairDistance (Sum.inl x) (Sum.inl y) := rfl
theorem right_smallDistance_eq (s : TaggedState Label n) (x y : Label) :
    SmallPrimePeeling.smallDistance (s.rightValue x) (s.rightValue y)=s.coreSmallPairDistance (Sum.inr x) (Sum.inr y) := rfl

theorem bounded_rough_separation (s : TaggedState Label n) (centers : ℕ → ℕ)
    (hL : ∀ x∈s.left,s.coreSmallCost centers (Sum.inl x)≤1375)
    (hR : ∀ y∈s.right,s.coreSmallCost centers (Sum.inr y)≤1375)
    (hsep : separated (Real.exp 6880) s) :
    (∀ x∈s.left,∀ y∈s.left,x≠y → Real.exp 4130<height
      (SmallPrimePeeling.roughPart (s.leftValue x)) (SmallPrimePeeling.roughPart (s.leftValue y))) ∧
    (∀ x∈s.right,∀ y∈s.right,x≠y → Real.exp 4130<height
      (SmallPrimePeeling.roughPart (s.rightValue x)) (SmallPrimePeeling.roughPart (s.rightValue y))) := by
  constructor
  · intro x hx y hy hxy
    apply SmallPrimePeeling.rough_height_separation (s.left_positive x hx) (s.left_positive y hy) _ (hsep.1 x hx y hy hxy)
    rw [s.left_smallDistance_eq]
    exact s.core_pair_distance_le_2750 centers _ _ (hL x hx) (hL y hy)
  · intro x hx y hy hxy
    apply SmallPrimePeeling.rough_height_separation (s.right_positive x hx) (s.right_positive y hy) _ (hsep.2 x hx y hy hxy)
    rw [s.right_smallDistance_eq]
    exact s.core_pair_distance_le_2750 centers _ _ (hR x hx) (hR y hy)

theorem bounded_rough_injective (s : TaggedState Label n) (centers : ℕ → ℕ)
    (hL : ∀ x∈s.left,s.coreSmallCost centers (Sum.inl x)≤1375)
    (hR : ∀ y∈s.right,s.coreSmallCost centers (Sum.inr y)≤1375)
    (hsep : separated (Real.exp 6880) s) :
    Set.InjOn (fun x => SmallPrimePeeling.roughPart (s.leftValue x)) (s.left:Set Label) ∧
    Set.InjOn (fun y => SmallPrimePeeling.roughPart (s.rightValue y)) (s.right:Set Label) := by
  have hs := s.bounded_rough_separation centers hL hR hsep
  constructor
  · intro x hx y hy he
    change SmallPrimePeeling.roughPart (s.leftValue x)=SmallPrimePeeling.roughPart (s.leftValue y) at he
    by_contra hxy
    have hh := hs.1 x hx y hy hxy
    rw [he,SmallPrimePeeling.height_self_of_pos (SmallPrimePeeling.roughPart_pos _)] at hh
    linarith [SmallPrimePeeling.exp_4130_gt_one]
  · intro x hx y hy he
    change SmallPrimePeeling.roughPart (s.rightValue x)=SmallPrimePeeling.roughPart (s.rightValue y) at he
    by_contra hxy
    have hh := hs.2 x hx y hy hxy
    rw [he,SmallPrimePeeling.height_self_of_pos (SmallPrimePeeling.roughPart_pos _)] at hh
    linarith [SmallPrimePeeling.exp_4130_gt_one]

end LonelyRunnerNew.TaggedState
