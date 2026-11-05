import LonelyRunnerNew.DyadicKernelSelection
import LonelyRunnerNew.DyadicScaleAlgebra

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew.TaggedState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

def dyadicState (s : TaggedState Label n) (G : Finset (Label × Label)) (hG : G⊆s.edges)
    (i j : ℕ) (hi : i∈s.leftBlockCodes) (hj : j∈s.rightBlockCodes) : TaggedState Label n :=
  (s.keepEdges G hG).restrict (s.leftBlock i) (s.rightBlock j) (Finset.filter_subset _ _)
    (Finset.filter_subset _ _) (s.leftBlock_nonempty hi) (s.rightBlock_nonempty hj)

def dyadicPhysicalQ (s : TaggedState Label n) (G : Finset (Label × Label)) (hG : G⊆s.edges)
    (i j : ℕ) (hi : i∈s.leftBlockCodes) (hj : j∈s.rightBlockCodes) : ℝ :=
  let t := s.dyadicState G hG i j hi hj
  (physicalDensity (t.left.image t.leftValue) (t.right.image t.rightValue) (t.valueEdges t.edges)
    (blockScale s.a s.b (s.blockA i) (s.blockB j)))^q*t.area*
    ((blockScale s.a s.b (s.blockA i) (s.blockB j))^2/(s.blockA i*s.blockB j))*(t.area/(n:ℝ)^2)^sigma

def dyadicPhysicalQ4 (s : TaggedState Label n) (G : Finset (Label × Label)) (hG : G⊆s.edges)
    (i j : ℕ) (hi : i∈s.leftBlockCodes) (hj : j∈s.rightBlockCodes) : ℝ :=
  let t := s.dyadicState G hG i j hi hj
  (physicalDensity (t.left.image t.leftValue) (t.right.image t.rightValue) (t.valueEdges t.edges)
    (blockScale s.a s.b (s.blockA i) (s.blockB j)))^4*t.area*
    ((blockScale s.a s.b (s.blockA i) (s.blockB j))^2/(s.blockA i*s.blockB j))

theorem dyadicState_mass (s : TaggedState Label n) (G : Finset (Label × Label)) (hG : G⊆s.edges)
    (i j : ℕ) (hi : i∈s.leftBlockCodes) (hj : j∈s.rightBlockCodes) :
    (s.dyadicState G hG i j hi hj).edgeMass=s.blockMass G (i,j) := by
  rw [blockMass,s.blockEdges_eq_inter G hG i j]
  rfl

theorem dyadic_weight_nonneg (s : TaggedState Label n) (x y : ℕ) : 0≤weight s.a s.b x y := by
  exact le_min (by norm_num) (div_nonneg (Nat.cast_nonneg _)
    (le_max_of_le_left (mul_nonneg s.a_positive.le (Nat.cast_nonneg _))))

theorem select_dyadic_normalized (s : TaggedState Label n) (G : Finset (Label × Label))
    (hG : G⊆s.edges) (hM : 0<(s.keepEdges G hG).edgeMass)
    {lam : ℝ} (hl0 : 0<lam) (hl1 : lam<1) :
    ∃ (i : ℕ) (hi : i∈s.leftBlockCodes) (j : ℕ) (hj : j∈s.rightBlockCodes),
      let t := s.dyadicState G hG i j hi hj
      0<t.edgeMass ∧ (s.keepEdges G hG).edgeMass/s.area^(3/4:ℝ)≤
        kernelN lam*(t.edgeMass/(lam^(DyadicPhysical.gap i j)*t.area^(3/4:ℝ))) := by
  have hL : (0:ℝ)<s.left.card := by exact_mod_cast s.left_nonempty.card_pos
  have hR : (0:ℝ)<s.right.card := by exact_mod_cast s.right_nonempty.card_pos
  have hsL : (∑ i∈s.leftBlockCodes,((s.leftBlock i).card:ℝ))=(s.left.card:ℝ) := by
    exact_mod_cast s.leftBlock_card_sum
  have hsR : (∑ j∈s.rightBlockCodes,((s.rightBlock j).card:ℝ))=(s.right.card:ℝ) := by
    exact_mod_cast s.rightBlock_card_sum
  have hm : ∀ ij∈s.leftBlockCodes.product s.rightBlockCodes,0≤s.blockMass G ij := by
    intro ij _
    exact Finset.sum_nonneg (fun e _ => s.dyadic_weight_nonneg _ _)
  have hsum : 0<∑ ij∈s.leftBlockCodes.product s.rightBlockCodes,s.blockMass G ij := by
    rw [s.blockMass_sum G hG]
    exact hM
  obtain ⟨ij,hij,hmij,hb⟩ := DyadicPhysical.select_weighted_block hl0 hl1 s.leftBlockCodes s.rightBlockCodes
    (s.left_nonempty.image _) (s.right_nonempty.image _) (fun i => ((s.leftBlock i).card:ℝ))
    (fun j => ((s.rightBlock j).card:ℝ)) (s.blockMass G) hL hR
    (fun i hi => by exact_mod_cast (s.leftBlock_nonempty hi).card_pos)
    (fun j hj => by exact_mod_cast (s.rightBlock_nonempty hj).card_pos) hsL hsR hm hsum
  have hc := Finset.mem_product.mp hij
  refine ⟨ij.1,hc.1,ij.2,hc.2,?_,?_⟩
  · rwa [s.dyadicState_mass G hG]
  · rw [s.blockMass_sum G hG] at hb
    rw [s.dyadicState_mass G hG]
    change (∑ e∈G,weight s.a s.b (s.leftValue e.1) (s.rightValue e.2))/
      ((s.left.card:ℝ)*(s.right.card:ℝ))^(3/4:ℝ)≤
        kernelN lam*(s.blockMass G ij/(lam^(DyadicPhysical.gap ij.1 ij.2)*
          (((s.leftBlock ij.1).card:ℝ)*((s.rightBlock ij.2).card:ℝ))^(3/4:ℝ)))
    exact hb

theorem selected_ordinary_score (s : TaggedState Label n) (G : Finset (Label × Label)) (hG : G⊆s.edges)
    (i j : ℕ) (hi : i∈s.leftBlockCodes) (hj : j∈s.rightBlockCodes)
    (hb : (s.keepEdges G hG).edgeMass/s.area^(3/4:ℝ)≤
      kernelN (DyadicPhysical.lambda q)*((s.dyadicState G hG i j hi hj).edgeMass/
        ((DyadicPhysical.lambda q)^(DyadicPhysical.gap i j)*(s.dyadicState G hG i j hi hj).area^(3/4:ℝ)))) :
    (s.keepEdges G hG).quality≤(kernelN (DyadicPhysical.lambda q))^q*
      (2:ℝ)^(DyadicPhysical.gap i j)*(s.dyadicState G hG i j hi hj).quality := by
  let t := s.dyadicState G hG i j hi hj
  have hq : 0<q := by norm_num [q]
  have hK : 0≤kernelN (DyadicPhysical.lambda q) := (DyadicPhysical.kernelN_ge_one
    (DyadicPhysical.lambda_pos q) (DyadicPhysical.lambda_lt_one hq)).trans' (by norm_num)
  have hr : 0≤t.edgeMass/((DyadicPhysical.lambda q)^(DyadicPhysical.gap i j)*t.area^(3/4:ℝ)) :=
    div_nonneg t.edgeMass_nonneg (mul_pos (pow_pos (DyadicPhysical.lambda_pos q) _) (Real.rpow_pos_of_pos t.area_pos _)).le
  have hp := Real.rpow_le_rpow (div_nonneg (s.keepEdges G hG).edgeMass_nonneg (Real.rpow_pos_of_pos s.area_pos _).le) hb hq.le
  rw [Real.mul_rpow hK hr,DyadicPhysical.normalized_ratio_rpow hq t.edgeMass_nonneg t.area_pos] at hp
  have hscale : 0≤(s.a*s.b)/((n:ℝ)^2)^sigma :=
    div_nonneg (mul_pos s.a_positive s.b_positive).le (Real.rpow_nonneg (sq_nonneg _) _)
  have hh := mul_le_mul_of_nonneg_right hp hscale
  rw [(s.keepEdges G hG).quality_eq_normalized_mass,t.quality_eq_normalized_mass]
  change ((s.keepEdges G hG).edgeMass/s.area^(3/4:ℝ))^q*((s.a*s.b)/((n:ℝ)^2)^sigma)≤
    (kernelN (DyadicPhysical.lambda q))^q*(2:ℝ)^(DyadicPhysical.gap i j)*
    ((t.edgeMass/t.area^(3/4:ℝ))^q*((s.a*s.b)/((n:ℝ)^2)^sigma))
  convert hh using 1 <;> ring

theorem selected_universal_score (s : TaggedState Label n) (G : Finset (Label × Label)) (hG : G⊆s.edges)
    (i j : ℕ) (hi : i∈s.leftBlockCodes) (hj : j∈s.rightBlockCodes)
    (hb : (s.keepEdges G hG).edgeMass/s.area^(3/4:ℝ)≤
      kernelN (DyadicPhysical.lambda 4)*((s.dyadicState G hG i j hi hj).edgeMass/
        ((DyadicPhysical.lambda 4)^(DyadicPhysical.gap i j)*(s.dyadicState G hG i j hi hj).area^(3/4:ℝ)))) :
    (s.keepEdges G hG).universalQuality≤(kernelN (DyadicPhysical.lambda 4))^4*
      (2:ℝ)^(DyadicPhysical.gap i j)*(s.dyadicState G hG i j hi hj).universalQuality := by
  let t := s.dyadicState G hG i j hi hj
  have hK : 0≤kernelN (DyadicPhysical.lambda 4) := (DyadicPhysical.kernelN_ge_one
    (DyadicPhysical.lambda_pos 4) (DyadicPhysical.lambda_lt_one (by norm_num : (0:ℝ)<4))).trans' (by norm_num)
  have hr : 0≤t.edgeMass/((DyadicPhysical.lambda 4)^(DyadicPhysical.gap i j)*t.area^(3/4:ℝ)) :=
    div_nonneg t.edgeMass_nonneg (mul_pos (pow_pos (DyadicPhysical.lambda_pos 4) _) (Real.rpow_pos_of_pos t.area_pos _)).le
  have hp := pow_le_pow_left₀ (div_nonneg (s.keepEdges G hG).edgeMass_nonneg (Real.rpow_pos_of_pos s.area_pos _).le) hb 4
  rw [mul_pow] at hp
  have he := DyadicPhysical.normalized_ratio_rpow (by norm_num : (0:ℝ)<4) t.edgeMass_nonneg t.area_pos (DyadicPhysical.gap i j)
  norm_num only [Real.rpow_ofNat] at he
  rw [he] at hp
  have hh := mul_le_mul_of_nonneg_right hp (mul_pos s.a_positive s.b_positive).le
  rw [(s.keepEdges G hG).universalQuality_eq_normalized,t.universalQuality_eq_normalized]
  change ((s.keepEdges G hG).edgeMass/s.area^(3/4:ℝ))^4*(s.a*s.b)≤
    (kernelN (DyadicPhysical.lambda 4))^4*(2:ℝ)^(DyadicPhysical.gap i j)*
    ((t.edgeMass/t.area^(3/4:ℝ))^4*(s.a*s.b))
  convert hh using 1 <;> ring

theorem dyadic_ordinary_physical (s : TaggedState Label n) (G : Finset (Label × Label)) (hG : G⊆s.edges)
    (i j : ℕ) (hi : i∈s.leftBlockCodes) (hj : j∈s.rightBlockCodes) :
    (2:ℝ)^(DyadicPhysical.gap i j)*(s.dyadicState G hG i j hi hj).quality≤s.dyadicPhysicalQ G hG i j hi hj := by
  let t := s.dyadicState G hG i j hi hj
  have hL : ∀ x∈t.left,s.blockA i≤(t.leftValue x:ℝ) ∧ (t.leftValue x:ℝ)<2*s.blockA i :=
    fun x hx => s.leftBlock_bounds hx
  have hR : ∀ y∈t.right,s.blockB j≤(t.rightValue y:ℝ) ∧ (t.rightValue y:ℝ)<2*s.blockB j :=
    fun y hy => s.rightBlock_bounds hy
  have hd := t.block_density_comparison t.edges (Finset.Subset.refl _) (s.blockA_pos i) hL hR
  have hd0 : 0≤t.density := div_nonneg t.edgeMass_nonneg t.area_pos.le
  have hp := Real.rpow_le_rpow hd0 hd (by norm_num [q] : 0≤q)
  have hTa : t.a=s.a := rfl
  have hTb : t.b=s.b := rfl
  rw [hTa,hTb] at hp
  have hh := mul_le_mul_of_nonneg_right hp
    (mul_nonneg (mul_nonneg t.area_pos.le (mul_nonneg (mul_pos s.a_positive s.b_positive).le (by positivity : (0:ℝ)≤(2:ℝ)^(DyadicPhysical.gap i j))))
      (Real.rpow_nonneg (div_nonneg t.area_pos.le (sq_nonneg (n:ℝ))) sigma))
  unfold dyadicPhysicalQ
  rw [s.dyadic_block_scale_factor]
  change (2:ℝ)^(DyadicPhysical.gap i j)*(t.density^q*t.area*(s.a*s.b)*(t.area/(n:ℝ)^2)^sigma)≤_
  convert hh using 1 <;> ring

theorem dyadic_universal_physical (s : TaggedState Label n) (G : Finset (Label × Label)) (hG : G⊆s.edges)
    (i j : ℕ) (hi : i∈s.leftBlockCodes) (hj : j∈s.rightBlockCodes) :
    (2:ℝ)^(DyadicPhysical.gap i j)*(s.dyadicState G hG i j hi hj).universalQuality≤s.dyadicPhysicalQ4 G hG i j hi hj := by
  let t := s.dyadicState G hG i j hi hj
  have hL : ∀ x∈t.left,s.blockA i≤(t.leftValue x:ℝ) ∧ (t.leftValue x:ℝ)<2*s.blockA i :=
    fun x hx => s.leftBlock_bounds hx
  have hR : ∀ y∈t.right,s.blockB j≤(t.rightValue y:ℝ) ∧ (t.rightValue y:ℝ)<2*s.blockB j :=
    fun y hy => s.rightBlock_bounds hy
  have hd := t.block_density_comparison t.edges (Finset.Subset.refl _) (s.blockA_pos i) hL hR
  have hp := pow_le_pow_left₀ (div_nonneg t.edgeMass_nonneg t.area_pos.le) hd 4
  change t.density^4≤_ at hp
  have hTa : t.a=s.a := rfl
  have hTb : t.b=s.b := rfl
  rw [hTa,hTb] at hp
  have hh := mul_le_mul_of_nonneg_right hp
    (mul_nonneg t.area_pos.le (mul_nonneg (mul_pos s.a_positive s.b_positive).le (by positivity : (0:ℝ)≤(2:ℝ)^(DyadicPhysical.gap i j))))
  unfold dyadicPhysicalQ4
  rw [s.dyadic_block_scale_factor]
  rw [(s.dyadicState G hG i j hi hj).universalQuality_eq_density]
  change (2:ℝ)^(DyadicPhysical.gap i j)*(t.density^4*t.area*(s.a*s.b))≤_
  convert hh using 1 <;> ring

/-- Full graph selection, with the entire kernel loss explicit and uniform. -/
theorem select_ordinary_physical_block (s : TaggedState Label n) (G : Finset (Label × Label))
    (hG : G⊆s.edges) (hM : 0<(s.keepEdges G hG).edgeMass) :
    ∃ (i : ℕ) (hi : i∈s.leftBlockCodes) (j : ℕ) (hj : j∈s.rightBlockCodes),
      0<(s.dyadicState G hG i j hi hj).edgeMass ∧
      (s.keepEdges G hG).quality≤(kernelN (DyadicPhysical.lambda q))^q*s.dyadicPhysicalQ G hG i j hi hj := by
  have hq : 0<q := by norm_num [q]
  obtain ⟨i,hi,j,hj,hm,hb⟩ := s.select_dyadic_normalized G hG hM
    (DyadicPhysical.lambda_pos q) (DyadicPhysical.lambda_lt_one hq)
  have h := s.selected_ordinary_score G hG i j hi hj hb
  have hp := mul_le_mul_of_nonneg_left (s.dyadic_ordinary_physical G hG i j hi hj)
    (Real.rpow_nonneg (DyadicPhysical.kernelN_ge_one (DyadicPhysical.lambda_pos q)
      (DyadicPhysical.lambda_lt_one hq) |>.trans' (by norm_num)) q)
  exact ⟨i,hi,j,hj,hm,h.trans (by simpa only [mul_assoc] using hp)⟩

theorem select_universal_physical_block (s : TaggedState Label n) (G : Finset (Label × Label))
    (hG : G⊆s.edges) (hM : 0<(s.keepEdges G hG).edgeMass) :
    ∃ (i : ℕ) (hi : i∈s.leftBlockCodes) (j : ℕ) (hj : j∈s.rightBlockCodes),
      0<(s.dyadicState G hG i j hi hj).edgeMass ∧
      (s.keepEdges G hG).universalQuality≤(kernelN (DyadicPhysical.lambda 4))^4*s.dyadicPhysicalQ4 G hG i j hi hj := by
  obtain ⟨i,hi,j,hj,hm,hb⟩ := s.select_dyadic_normalized G hG hM
    (DyadicPhysical.lambda_pos 4) (DyadicPhysical.lambda_lt_one (by norm_num : (0:ℝ)<4))
  have h := s.selected_universal_score G hG i j hi hj hb
  have hp := mul_le_mul_of_nonneg_left (s.dyadic_universal_physical G hG i j hi hj)
    (pow_nonneg ((DyadicPhysical.kernelN_ge_one (DyadicPhysical.lambda_pos 4)
      (DyadicPhysical.lambda_lt_one (by norm_num : (0:ℝ)<4))).trans' (by norm_num)) 4)
  exact ⟨i,hi,j,hj,hm,h.trans (by simpa only [mul_assoc] using hp)⟩

end LonelyRunnerNew.TaggedState
