import LonelyRunnerNew.JointCore

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew.TaggedState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

theorem normalized_mass_restriction_bound (s t : TaggedState Label n)
    (hL : t.left⊆s.left) (hR : t.right⊆s.right) {delta : ℝ} (hd : 0≤delta)
    (hM : delta*s.edgeMass≤t.edgeMass) :
    delta*(s.edgeMass/s.area^(3/4:ℝ))≤t.edgeMass/t.area^(3/4:ℝ) := by
  have harea : t.area≤s.area := by
    unfold area
    exact_mod_cast Nat.mul_le_mul (Finset.card_le_card hL) (Finset.card_le_card hR)
  have hp := Real.rpow_le_rpow t.area_pos.le harea (by norm_num : (0:ℝ)≤3/4)
  calc
    _ = (delta*s.edgeMass)/s.area^(3/4:ℝ) := by ring
    _ ≤ t.edgeMass/s.area^(3/4:ℝ) := div_le_div_of_nonneg_right hM (Real.rpow_nonneg s.area_pos.le _)
    _ ≤ _ := div_le_div₀ t.edgeMass_nonneg le_rfl (Real.rpow_pos_of_pos t.area_pos _) hp

theorem quality_restriction_mass_bound (s t : TaggedState Label n)
    (hL : t.left⊆s.left) (hR : t.right⊆s.right) (ha : t.a=s.a) (hb : t.b=s.b)
    {delta : ℝ} (hd : 0≤delta) (hM : delta*s.edgeMass≤t.edgeMass) :
    delta^q*s.quality≤t.quality := by
  have hn := s.normalized_mass_restriction_bound t hL hR hd hM
  have hsn : 0≤s.edgeMass/s.area^(3/4:ℝ) := div_nonneg s.edgeMass_nonneg (Real.rpow_nonneg s.area_pos.le _)
  have hp := Real.rpow_le_rpow (mul_nonneg hd hsn) hn (by norm_num [q] : 0≤q)
  rw [Real.mul_rpow hd hsn] at hp
  have hK : 0≤(s.a*s.b)/((n:ℝ)^2)^sigma :=
    div_nonneg (mul_nonneg s.a_positive.le s.b_positive.le) (Real.rpow_nonneg (sq_nonneg _) _)
  have hh := mul_le_mul_of_nonneg_right hp hK
  rw [s.quality_eq_normalized_mass,t.quality_eq_normalized_mass,ha,hb]
  simpa only [mul_assoc] using hh

theorem universal_quality_restriction_mass_bound (s t : TaggedState Label n)
    (hL : t.left⊆s.left) (hR : t.right⊆s.right) (ha : t.a=s.a) (hb : t.b=s.b)
    {delta : ℝ} (hd : 0≤delta) (hM : delta*s.edgeMass≤t.edgeMass) :
    delta^4*s.universalQuality≤t.universalQuality := by
  have hn := s.normalized_mass_restriction_bound t hL hR hd hM
  have hsn : 0≤s.edgeMass/s.area^(3/4:ℝ) := div_nonneg s.edgeMass_nonneg (Real.rpow_nonneg s.area_pos.le _)
  have hp := pow_le_pow_left₀ (mul_nonneg hd hsn) hn 4
  rw [mul_pow] at hp
  have hh := mul_le_mul_of_nonneg_right hp (mul_nonneg s.a_positive.le s.b_positive.le)
  rw [s.universalQuality_eq_normalized,t.universalQuality_eq_normalized,ha,hb]
  simpa only [mul_assoc] using hh

theorem stable_joint_core_quality (s : TaggedState Label n)
    (hs : ∀ t,Step s t → t.quality≤s.quality) (hM : 0<s.edgeMass) :
    ∃ t : TaggedState Label n,Step s t ∧
      t.left=s.jointLeft (s.coreSmallCost (s.coreSmallCenters hM)) ∧
      t.right=s.jointRight (s.coreSmallCost (s.coreSmallCenters hM)) ∧
      t.edges=s.jointEdges (s.coreSmallCost (s.coreSmallCenters hM)) ∧
      t.leftValue=s.leftValue ∧ t.rightValue=s.rightValue ∧ t.a=s.a ∧ t.b=s.b ∧
      (Certificate.tbar:ℝ)^q*s.quality≤t.quality := by
  obtain ⟨t,hstep,hL,hR,hE,hvL,hvR,ha,hb,hm,_,_⟩ := s.stable_joint_core_state hs hM
  have hh := s.quality_restriction_mass_bound t (by rw [hL];exact Finset.filter_subset _ _)
    (by rw [hR];exact Finset.filter_subset _ _) ha hb tbar_exact_positive.2.le hm
  exact ⟨t,hstep,hL,hR,hE,hvL,hvR,ha,hb,hh⟩

theorem universal_joint_core_quality (s : TaggedState Label n)
    (hs : ∀ t,Step s t → t.universalQuality≤s.universalQuality) (hM : 0<s.edgeMass) :
    ∃ t : TaggedState Label n,Step s t ∧
      t.left=s.jointLeft (s.coreSmallCost (s.coreSmallCenters hM)) ∧
      t.right=s.jointRight (s.coreSmallCost (s.coreSmallCenters hM)) ∧
      t.edges=s.jointEdges (s.coreSmallCost (s.coreSmallCenters hM)) ∧
      t.leftValue=s.leftValue ∧ t.rightValue=s.rightValue ∧ t.a=s.a ∧ t.b=s.b ∧
      (Certificate.tbar:ℝ)^4*s.universalQuality≤t.universalQuality := by
  obtain ⟨t,hstep,hL,hR,hE,hvL,hvR,ha,hb,hm,_,_⟩ := s.universal_joint_core_state hs hM
  have hh := s.universal_quality_restriction_mass_bound t (by rw [hL];exact Finset.filter_subset _ _)
    (by rw [hR];exact Finset.filter_subset _ _) ha hb tbar_exact_positive.2.le hm
  exact ⟨t,hstep,hL,hR,hE,hvL,hvR,ha,hb,hh⟩

end LonelyRunnerNew.TaggedState
