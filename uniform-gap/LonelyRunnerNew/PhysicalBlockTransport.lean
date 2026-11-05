import LonelyRunnerNew.RoughRestabilization
import Mathlib.Data.Finset.Card

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew

def blockScale (a b A B : ℝ) : ℝ := max (a*A) (b*B)

theorem blockScale_pos {a b A B : ℝ} (ha : 0<a) (hA : 0<A) : 0<blockScale a b A B :=
  lt_max_of_lt_left (mul_pos ha hA)

theorem block_denominator_bounds {a b A B : ℝ} (ha : 0<a) (hb : 0<b)
    {x y : ℕ} (hx : A≤(x:ℝ)) (hxU : (x:ℝ)<2*A)
    (hy : B≤(y:ℝ)) (hyU : (y:ℝ)<2*B) :
    blockScale a b A B≤max (a*(x:ℝ)) (b*(y:ℝ)) ∧
      max (a*(x:ℝ)) (b*(y:ℝ))<2*blockScale a b A B := by
  constructor
  · exact max_le_max (mul_le_mul_of_nonneg_left hx ha.le) (mul_le_mul_of_nonneg_left hy hb.le)
  · apply max_lt
    · have h := mul_lt_mul_of_pos_left hxU ha
      have hl : a*A≤blockScale a b A B := le_max_left _ _
      linarith
    · have h := mul_lt_mul_of_pos_left hyU hb
      have hr : b*B≤blockScale a b A B := le_max_right _ _
      linarith

/-- On a dyadic block, the exact current denominator is between D and 2D.
This comparison is necessary independently of roughness or LC. -/
theorem weight_physical_block {a b A B : ℝ} (ha : 0<a) (hb : 0<b)
    (hA : 0<A) {x y : ℕ} (hx : A≤(x:ℝ)) (hxU : (x:ℝ)<2*A)
    (hy : B≤(y:ℝ)) (hyU : (y:ℝ)<2*B) :
    min 1 ((Nat.gcd x y:ℝ)/(2*blockScale a b A B))≤weight a b x y ∧
      weight a b x y≤min 1 ((Nat.gcd x y:ℝ)/blockScale a b A B) := by
  have hD := blockScale_pos (b := b) (B := B) ha hA
  have hbds := block_denominator_bounds ha hb hx hxU hy hyU
  have hd := hD.trans_le hbds.1
  constructor
  · exact min_le_min le_rfl (div_le_div_of_nonneg_left (Nat.cast_nonneg _) hd hbds.2.le)
  · exact min_le_min le_rfl (div_le_div_of_nonneg_left (Nat.cast_nonneg _) hD hbds.1)

theorem physical_block_weight_le_twice {a b A B : ℝ} (ha : 0<a) (hb : 0<b)
    (hA : 0<A) {x y : ℕ} (hx : A≤(x:ℝ)) (hxU : (x:ℝ)<2*A)
    (hy : B≤(y:ℝ)) (hyU : (y:ℝ)<2*B) :
    min 1 ((Nat.gcd x y:ℝ)/blockScale a b A B)≤2*weight a b x y := by
  have hlow := (weight_physical_block ha hb hA hx hxU hy hyU).1
  have hD := blockScale_pos (b := b) (B := B) ha hA
  have hg : 0≤(Nat.gcd x y:ℝ)/(2*blockScale a b A B) := div_nonneg (Nat.cast_nonneg _) (by positivity)
  have he : (Nat.gcd x y:ℝ)/blockScale a b A B=2*((Nat.gcd x y:ℝ)/(2*blockScale a b A B)) := by ring
  have hmin : min 1 ((Nat.gcd x y:ℝ)/blockScale a b A B)≤
      2*min 1 ((Nat.gcd x y:ℝ)/(2*blockScale a b A B)) := by
    rw [he]
    by_cases h : (Nat.gcd x y:ℝ)/(2*blockScale a b A B)≤1
    · rw [min_eq_right h]
      exact min_le_right _ _
    · rw [min_eq_left (le_of_not_ge h)]
      exact (min_le_left _ _).trans (by norm_num)
  exact hmin.trans (mul_le_mul_of_nonneg_left hlow (by norm_num))

theorem block_scale_score_factor {a b A B : ℝ} (ha : 0<a) (hb : 0<b)
    (hA : 0<A) (hB : 0<B) : a*b≤(blockScale a b A B)^2/(A*B) := by
  have hD := blockScale_pos (b := b) (B := B) ha hA
  have hl : a*A≤blockScale a b A B := le_max_left _ _
  have hr : b*B≤blockScale a b A B := le_max_right _ _
  have hm := mul_le_mul hl hr (mul_pos hb hB).le hD.le
  apply (le_div_iff₀ (mul_pos hA hB)).mpr
  nlinarith only [hm]

theorem physical_score_factor_form (X A B D : ℝ) :
    X*(D^2/(A*B))=X/(A*B/D^2) := by
  rw [div_div_eq_mul_div]
  ring

namespace TaggedState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

/-- Retain a labelled edge set, with no assertion that stability survives. -/
def keepEdges (s : TaggedState Label n) (G : Finset (Label × Label)) (hG : G⊆s.edges) :
    TaggedState Label n :=
  { s with edges := G,edges_subset := hG.trans s.edges_subset }

theorem keepEdges_mass_probability (s : TaggedState Label n) (G : Finset (Label × Label))
    (hG : G⊆s.edges) :
    (∑ e∈G,s.edgeProbability e)=(s.keepEdges G hG).edgeMass/s.edgeMass := by
  unfold edgeProbability
  rw [← Finset.sum_div]
  rfl

theorem keepEdges_score_bounds (s : TaggedState Label n) (G : Finset (Label × Label))
    (hG : G⊆s.edges) (hM : 0<s.edgeMass) {delta : ℝ} (hd : 0≤delta)
    (hp : delta≤∑ e∈G,s.edgeProbability e) :
    delta*s.edgeMass≤(s.keepEdges G hG).edgeMass ∧
    delta^q*s.quality≤(s.keepEdges G hG).quality ∧
    delta^4*s.universalQuality≤(s.keepEdges G hG).universalQuality := by
  rw [s.keepEdges_mass_probability G hG] at hp
  have hm := (le_div_iff₀ hM).mp hp
  exact ⟨hm,s.quality_restriction_mass_bound (s.keepEdges G hG) (Finset.Subset.refl _) (Finset.Subset.refl _)
    rfl rfl hd hm,s.universal_quality_restriction_mass_bound (s.keepEdges G hG) (Finset.Subset.refl _)
    (Finset.Subset.refl _) rfl rfl hd hm⟩

def valueEdges (s : TaggedState Label n) (G : Finset (Label × Label)) : Finset (ℕ × ℕ) :=
  G.image (fun e => (s.leftValue e.1,s.rightValue e.2))

theorem value_pair_injective (s : TaggedState Label n) (G : Finset (Label × Label)) (hG : G⊆s.edges) :
    Set.InjOn (fun e : Label × Label => (s.leftValue e.1,s.rightValue e.2)) (G:Set (Label × Label)) := by
  intro e he f hf hval
  have heM := Finset.mem_product.mp (s.edges_subset (hG he))
  have hfM := Finset.mem_product.mp (s.edges_subset (hG hf))
  exact Prod.ext (s.left_injective heM.1 hfM.1 (congrArg Prod.fst hval))
    (s.right_injective heM.2 hfM.2 (congrArg Prod.snd hval))

theorem valueEdges_subset (s : TaggedState Label n) (G : Finset (Label × Label)) (hG : G⊆s.edges) :
    s.valueEdges G⊆(s.left.image s.leftValue).product (s.right.image s.rightValue) := by
  intro e he
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
  have hm := Finset.mem_product.mp (s.edges_subset (hG hf))
  exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hm.1,Finset.mem_image_of_mem _ hm.2⟩

/-- An image sum is justified here by the proved pair injectivity, so every
original labelled edge contributes exactly once. -/
theorem physicalDensity_eq_labels (s : TaggedState Label n) (G : Finset (Label × Label))
    (hG : G⊆s.edges) (D : ℝ) :
    physicalDensity (s.left.image s.leftValue) (s.right.image s.rightValue) (s.valueEdges G) D=
      (∑ e∈G,min 1 ((Nat.gcd (s.leftValue e.1) (s.rightValue e.2):ℝ)/D))/s.area := by
  unfold physicalDensity valueEdges
  rw [Finset.card_image_iff.mpr s.left_injective,Finset.card_image_iff.mpr s.right_injective]
  congr 1
  exact Finset.sum_image (s.value_pair_injective G hG)

theorem block_density_comparison (s : TaggedState Label n) (G : Finset (Label × Label))
    (hG : G⊆s.edges) {A B : ℝ} (hA : 0<A)
    (hL : ∀ x∈s.left,A≤(s.leftValue x:ℝ) ∧ (s.leftValue x:ℝ)<2*A)
    (hR : ∀ y∈s.right,B≤(s.rightValue y:ℝ) ∧ (s.rightValue y:ℝ)<2*B) :
    (∑ e∈G,weight s.a s.b (s.leftValue e.1) (s.rightValue e.2))/s.area≤
      physicalDensity (s.left.image s.leftValue) (s.right.image s.rightValue)
        (s.valueEdges G) (blockScale s.a s.b A B) := by
  rw [s.physicalDensity_eq_labels G hG]
  apply div_le_div_of_nonneg_right _ s.area_pos.le
  apply Finset.sum_le_sum
  intro e he
  have hm := Finset.mem_product.mp (s.edges_subset (hG he))
  exact (weight_physical_block s.a_positive s.b_positive hA (hL e.1 hm.1).1
    (hL e.1 hm.1).2 (hR e.2 hm.2).1 (hR e.2 hm.2).2).2

theorem block_density_of_mass (s : TaggedState Label n) (G : Finset (Label × Label))
    (hG : G⊆s.edges) {A B delta : ℝ} (hA : 0<A)
    (hm : delta*s.edgeMass≤∑ e∈G,weight s.a s.b (s.leftValue e.1) (s.rightValue e.2))
    (hL : ∀ x∈s.left,A≤(s.leftValue x:ℝ) ∧ (s.leftValue x:ℝ)<2*A)
    (hR : ∀ y∈s.right,B≤(s.rightValue y:ℝ) ∧ (s.rightValue y:ℝ)<2*B) :
    delta*s.density≤physicalDensity (s.left.image s.leftValue) (s.right.image s.rightValue)
      (s.valueEdges G) (blockScale s.a s.b A B) := by
  calc
    _ = (delta*s.edgeMass)/s.area := by change delta*(s.edgeMass/s.area)=_;ring
    _ ≤ (∑ e∈G,weight s.a s.b (s.leftValue e.1) (s.rightValue e.2))/s.area :=
      div_le_div_of_nonneg_right hm s.area_pos.le
    _ ≤ _ := s.block_density_comparison G hG hA hL hR

/-- This is the exact score coefficient needed by roughBlockInput; no
rough-block or counting inequality is assumed or asserted here. -/
theorem ordinary_block_score_comparison (s : TaggedState Label n) (G : Finset (Label × Label))
    (hG : G⊆s.edges) {A B delta : ℝ} (hA : 0<A) (hB : 0<B) (hd : 0≤delta)
    (hm : delta*s.edgeMass≤∑ e∈G,weight s.a s.b (s.leftValue e.1) (s.rightValue e.2))
    (hL : ∀ x∈s.left,A≤(s.leftValue x:ℝ) ∧ (s.leftValue x:ℝ)<2*A)
    (hR : ∀ y∈s.right,B≤(s.rightValue y:ℝ) ∧ (s.rightValue y:ℝ)<2*B) :
    delta^q*s.quality≤
      (physicalDensity (s.left.image s.leftValue) (s.right.image s.rightValue)
        (s.valueEdges G) (blockScale s.a s.b A B))^q*s.area*
      ((blockScale s.a s.b A B)^2/(A*B))*(s.area/(n:ℝ)^2)^sigma := by
  let rho := physicalDensity (s.left.image s.leftValue) (s.right.image s.rightValue)
    (s.valueEdges G) (blockScale s.a s.b A B)
  have hden : 0≤s.density := div_nonneg s.edgeMass_nonneg s.area_pos.le
  have hmass := s.block_density_of_mass G hG hA hm hL hR
  have hrho : 0≤rho := (mul_nonneg hd hden).trans hmass
  have hpow := Real.rpow_le_rpow (mul_nonneg hd hden) hmass (by norm_num [q] : 0≤q)
  rw [Real.mul_rpow hd hden] at hpow
  have hscale := block_scale_score_factor s.a_positive s.b_positive hA hB
  have harea := mul_le_mul_of_nonneg_right hpow s.area_pos.le
  have hprod := mul_le_mul harea hscale (mul_nonneg s.a_positive.le s.b_positive.le)
    (mul_nonneg (Real.rpow_nonneg hrho _) s.area_pos.le)
  have hpen : 0≤(s.area/(n:ℝ)^2)^sigma := Real.rpow_nonneg (div_nonneg s.area_pos.le (sq_nonneg _)) _
  have h := mul_le_mul_of_nonneg_right hprod hpen
  change delta^q*(s.density^q*s.area*(s.a*s.b)*(s.area/(n:ℝ)^2)^sigma)≤_
  calc
    _ = (delta^q*s.density^q*s.area)*(s.a*s.b)*(s.area/(n:ℝ)^2)^sigma := by ring
    _ ≤ _ := h

theorem universal_block_score_comparison (s : TaggedState Label n) (G : Finset (Label × Label))
    (hG : G⊆s.edges) {A B delta : ℝ} (hA : 0<A) (hB : 0<B) (hd : 0≤delta)
    (hm : delta*s.edgeMass≤∑ e∈G,weight s.a s.b (s.leftValue e.1) (s.rightValue e.2))
    (hL : ∀ x∈s.left,A≤(s.leftValue x:ℝ) ∧ (s.leftValue x:ℝ)<2*A)
    (hR : ∀ y∈s.right,B≤(s.rightValue y:ℝ) ∧ (s.rightValue y:ℝ)<2*B) :
    delta^4*s.universalQuality≤
      (physicalDensity (s.left.image s.leftValue) (s.right.image s.rightValue)
        (s.valueEdges G) (blockScale s.a s.b A B))^4*s.area*((blockScale s.a s.b A B)^2/(A*B)) := by
  let rho := physicalDensity (s.left.image s.leftValue) (s.right.image s.rightValue)
    (s.valueEdges G) (blockScale s.a s.b A B)
  have hden : 0≤s.density := div_nonneg s.edgeMass_nonneg s.area_pos.le
  have hmass := s.block_density_of_mass G hG hA hm hL hR
  have hrho : 0≤rho := (mul_nonneg hd hden).trans hmass
  have hpow := pow_le_pow_left₀ (mul_nonneg hd hden) hmass 4
  rw [mul_pow] at hpow
  have hscale := block_scale_score_factor s.a_positive s.b_positive hA hB
  have harea := mul_le_mul_of_nonneg_right hpow s.area_pos.le
  have hprod := mul_le_mul harea hscale (mul_nonneg s.a_positive.le s.b_positive.le)
    (mul_nonneg (pow_nonneg hrho 4) s.area_pos.le)
  rw [s.universalQuality_eq_density]
  calc
    _ = (delta^4*s.density^4*s.area)*(s.a*s.b) := by ring
    _ ≤ _ := hprod

/-- Apply actual ordinary LC on this stable rough state, then the proved block
transport. The block membership conditions remain explicit geometric data. -/
theorem ordinary_stable_rough_block_comparison (s : TaggedState Label n)
    (hs : ∀ t,Step s t → t.quality≤s.quality) (hM : 0<s.edgeMass)
    (hroughL : ∀ x∈s.left,rough 142 (s.leftValue x))
    (hroughR : ∀ y∈s.right,rough 142 (s.rightValue y))
    {A B : ℝ} (hA : 0<A) (hB : 0<B)
    (hL : ∀ x∈s.left,A≤(s.leftValue x:ℝ) ∧ (s.leftValue x:ℝ)<2*A)
    (hR : ∀ y∈s.right,B≤(s.rightValue y:ℝ) ∧ (s.rightValue y:ℝ)<2*B) :
    ∃ centers : ℕ → ℕ,
      (27/50:ℝ)≤∑ e∈s.retainedLargeEdges centers,s.edgeProbability e ∧
      (∀ e∈s.retainedLargeEdges centers,∀ p,Nat.Prime p → s.centerBrackets p (centers p) e) ∧
      (27/50:ℝ)^q*s.quality≤
        (physicalDensity (s.left.image s.leftValue) (s.right.image s.rightValue)
          (s.valueEdges (s.retainedLargeEdges centers)) (blockScale s.a s.b A B))^q*s.area*
        ((blockScale s.a s.b A B)^2/(A*B))*(s.area/(n:ℝ)^2)^sigma := by
  obtain ⟨centers,_,hG,hprob,hall⟩ := s.stable_rough_all_prime_retention hs hM hroughL hroughR
  have hraw : (27/50:ℝ)*s.edgeMass≤∑ e∈s.retainedLargeEdges centers,
      weight s.a s.b (s.leftValue e.1) (s.rightValue e.2) := by
    have h := hprob
    simp only [edgeProbability,← Finset.sum_div] at h
    exact (le_div_iff₀ hM).mp h
  exact ⟨centers,hprob,hall,s.ordinary_block_score_comparison _ hG hA hB
    (by norm_num : (0:ℝ)≤27/50) hraw hL hR⟩

theorem universal_stable_rough_block_comparison (s : TaggedState Label n)
    (hs : ∀ t,Step s t → t.universalQuality≤s.universalQuality) (hM : 0<s.edgeMass)
    (hroughL : ∀ x∈s.left,rough 142 (s.leftValue x))
    (hroughR : ∀ y∈s.right,rough 142 (s.rightValue y))
    {A B : ℝ} (hA : 0<A) (hB : 0<B)
    (hL : ∀ x∈s.left,A≤(s.leftValue x:ℝ) ∧ (s.leftValue x:ℝ)<2*A)
    (hR : ∀ y∈s.right,B≤(s.rightValue y:ℝ) ∧ (s.rightValue y:ℝ)<2*B) :
    ∃ centers : ℕ → ℕ,
      (27/50:ℝ)≤∑ e∈s.retainedLargeEdges centers,s.edgeProbability e ∧
      (∀ e∈s.retainedLargeEdges centers,∀ p,Nat.Prime p → s.centerBrackets p (centers p) e) ∧
      (27/50:ℝ)^4*s.universalQuality≤
        (physicalDensity (s.left.image s.leftValue) (s.right.image s.rightValue)
          (s.valueEdges (s.retainedLargeEdges centers)) (blockScale s.a s.b A B))^4*s.area*
        ((blockScale s.a s.b A B)^2/(A*B)) := by
  obtain ⟨centers,_,hG,hprob,hall⟩ := s.universal_rough_all_prime_retention hs hM hroughL hroughR
  have hraw : (27/50:ℝ)*s.edgeMass≤∑ e∈s.retainedLargeEdges centers,
      weight s.a s.b (s.leftValue e.1) (s.rightValue e.2) := by
    have h := hprob
    simp only [edgeProbability,← Finset.sum_div] at h
    exact (le_div_iff₀ hM).mp h
  exact ⟨centers,hprob,hall,s.universal_block_score_comparison _ hG hA hB
    (by norm_num : (0:ℝ)≤27/50) hraw hL hR⟩

/-- The local block of an already selected labelled graph. This theorem uses
no stability of the restriction and asserts no blockwise 27/50 probability. -/
theorem retained_restriction_block_scores (s : TaggedState Label n)
    (G : Finset (Label × Label)) (hG : G⊆s.edges)
    (L R : Finset Label) (hL : L⊆s.left) (hR : R⊆s.right)
    (hLN : L.Nonempty) (hRN : R.Nonempty) {A B : ℝ} (hA : 0<A) (hB : 0<B)
    (hLX : ∀ x∈L,A≤(s.leftValue x:ℝ) ∧ (s.leftValue x:ℝ)<2*A)
    (hRY : ∀ y∈R,B≤(s.rightValue y:ℝ) ∧ (s.rightValue y:ℝ)<2*B) :
    let t := (s.keepEdges G hG).restrict L R hL hR hLN hRN
    t.edges=G∩L.product R ∧ t.a=s.a ∧ t.b=s.b ∧
    t.quality≤
      (physicalDensity (L.image s.leftValue) (R.image s.rightValue)
        (t.valueEdges t.edges) (blockScale s.a s.b A B))^q*t.area*
        ((blockScale s.a s.b A B)^2/(A*B))*(t.area/(n:ℝ)^2)^sigma ∧
    t.universalQuality≤
      (physicalDensity (L.image s.leftValue) (R.image s.rightValue)
        (t.valueEdges t.edges) (blockScale s.a s.b A B))^4*t.area*
        ((blockScale s.a s.b A B)^2/(A*B)) := by
  let t := (s.keepEdges G hG).restrict L R hL hR hLN hRN
  have htL : ∀ x∈t.left,A≤(t.leftValue x:ℝ) ∧ (t.leftValue x:ℝ)<2*A := hLX
  have htR : ∀ y∈t.right,B≤(t.rightValue y:ℝ) ∧ (t.rightValue y:ℝ)<2*B := hRY
  have hm : (1:ℝ)*t.edgeMass≤∑ e∈t.edges,weight t.a t.b (t.leftValue e.1) (t.rightValue e.2) := by
    rw [one_mul]
    exact le_refl _
  have hq := t.ordinary_block_score_comparison t.edges (Finset.Subset.refl _) hA hB
    (by norm_num : (0:ℝ)≤1) hm htL htR
  have hu := t.universal_block_score_comparison t.edges (Finset.Subset.refl _) hA hB
    (by norm_num : (0:ℝ)≤1) hm htL htR
  refine ⟨rfl,rfl,rfl,?_,?_⟩
  · simpa only [Real.one_rpow,one_mul,t,restrict,keepEdges] using hq
  · simpa only [one_pow,one_mul,t,restrict,keepEdges] using hu

end TaggedState
end LonelyRunnerNew
