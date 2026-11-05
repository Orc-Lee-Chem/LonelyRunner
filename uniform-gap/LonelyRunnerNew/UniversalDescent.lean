import LonelyRunnerNew.ValuationDistribution

noncomputable section
open scoped BigOperators
namespace LonelyRunnerNew.TaggedState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

/-- The separate q=4 score, with no ambient-cardinality penalty. -/
def universalQuality (s : TaggedState Label n) : ℝ := s.edgeMass^4/s.area^3*(s.a*s.b)

theorem universalQuality_eq_density (s : TaggedState Label n) :
    s.universalQuality = s.density^4*s.area*(s.a*s.b) := by
  change s.edgeMass^4/s.area^3*(s.a*s.b) = (s.edgeMass/s.area)^4*s.area*(s.a*s.b)
  have ha := s.area_pos.ne'
  field_simp

theorem universal_restrict_full (s : TaggedState Label n)
    (hL : s.left ⊆ s.left) (hR : s.right ⊆ s.right)
    (hLN : s.left.Nonempty) (hRN : s.right.Nonempty) :
    (s.restrict s.left s.right hL hR hLN hRN).universalQuality = s.universalQuality := by
  have hsub : s.edges ⊆ s.left ×ˢ s.right := by
    simpa only [Finset.product_eq_sprod] using s.edges_subset
  simp only [universalQuality, edgeMass, area, restrict, Finset.product_eq_sprod,
    Finset.inter_eq_left.mpr hsub]

theorem universal_divide_zero_full (s : TaggedState Label n) (p : ℕ) (hp : Nat.Prime p)
    (u v : Label → ℕ)
    (hfL : ∀ x ∈ s.left, p^0*u x=s.leftValue x)
    (hfR : ∀ y ∈ s.right, p^0*v y=s.rightValue y) :
    (s.divideLayers s.left s.right (fun _ h => h) (fun _ h => h)
      s.left_nonempty s.right_nonempty p 0 0 hp u v hfL hfR).universalQuality = s.universalQuality := by
  have hsum : (∑ e ∈ s.edges, weight s.a s.b (u e.1) (v e.2)) = s.edgeMass := by
    apply Finset.sum_congr rfl
    intro e he
    have hm := Finset.mem_product.mp (s.edges_subset he)
    rw [show u e.1=s.leftValue e.1 by simpa using hfL e.1 hm.1,
      show v e.2=s.rightValue e.2 by simpa using hfR e.2 hm.2]
  have hsub : s.edges ⊆ s.left ×ˢ s.right := by
    simpa only [Finset.product_eq_sprod] using s.edges_subset
  simpa only [universalQuality, edgeMass, area, divideLayers, Finset.product_eq_sprod,
    Finset.inter_eq_left.mpr hsub, Nat.sub_self, pow_zero, mul_one] using
    congrArg (fun M : ℝ => M^4/s.area^3*(s.a*s.b)) hsum

theorem universal_improving_step_decreases {s t : TaggedState Label n} (hst : Step s t)
    (himprove : s.universalQuality < t.universalQuality) : t.potential < s.potential := by
  cases hst with
  | restrict L R hL hR hLN hRN =>
    by_cases hproper : L ≠ s.left ∨ R ≠ s.right
    · exact potential_restrict_lt s L R hL hR hLN hRN hproper
    · have hLeq : L=s.left := not_not.mp (not_or.mp hproper).1
      have hReq : R=s.right := not_not.mp (not_or.mp hproper).2
      subst L R
      rw [universal_restrict_full] at himprove
      exact (lt_irrefl _ himprove).elim
  | prime L R hL hR hLN hRN p i j hp u v hfL hfR hnL hnR =>
    by_cases hi : i=0
    · by_cases hj : j=0
      · subst i j
        by_cases hproper : L ≠ s.left ∨ R ≠ s.right
        · rw [divide_zero_potential]
          exact potential_restrict_lt s L R hL hR hLN hRN hproper
        · have hLeq : L=s.left := not_not.mp (not_or.mp hproper).1
          have hReq : R=s.right := not_not.mp (not_or.mp hproper).2
          subst L R
          have heq := universal_divide_zero_full s p hp u v hfL hfR
          have hbad : s.universalQuality < s.universalQuality := by simpa only [heq] using himprove
          exact (lt_irrefl _ hbad).elim
      · exact divideLayers_potential_lt s L R hL hR hLN hRN p i j hp u v hfL hfR
          (Or.inr (Nat.pos_of_ne_zero hj))
    · exact divideLayers_potential_lt s L R hL hR hLN hRN p i j hp u v hfL hfR
        (Or.inl (Nat.pos_of_ne_zero hi))

theorem universal_stable_state_exists (s : TaggedState Label n) :
    ∃ t, Relation.ReflTransGen Step s t ∧ s.universalQuality ≤ t.universalQuality ∧
      ∀ u, Step t u → u.universalQuality ≤ t.universalQuality :=
  exists_stable_of_descent Step potential universalQuality
    (fun _ _ hst hi => universal_improving_step_decreases hst hi) s

theorem universal_kernel_le_target {p : ℕ} (hp : Nat.Prime p) (d : ℕ) :
    (p:ℝ)^(-(d:ℝ)/4) ≤ (p:ℝ)^(-(d:ℝ)/q) := by
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.one_lt.le)
  norm_num [q]
  nlinarith [Nat.cast_nonneg (α := ℝ) d]

theorem universalQuality_eq_normalized (s : TaggedState Label n) :
    s.universalQuality = (s.edgeMass/s.area^(3/4:ℝ))^4*(s.a*s.b) := by
  have he : (s.area^(3/4:ℝ))^4=s.area^3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul s.area_pos.le]
    norm_num
  rw [div_pow, he]
  rfl

theorem universal_layer_concentration (s : TaggedState Label n)
    (hstable : ∀ t, Step s t → t.universalQuality ≤ s.universalQuality)
    (hM : 0 < s.edgeMass) (p : ℕ) (hp : Nat.Prime p) (i j : ℕ) :
    s.mu p (i,j) ≤ (p:ℝ)^(-(((i:ℤ)-(j:ℤ)).natAbs:ℝ)/4)*
      (s.alpha p i*s.beta p j)^(3/4:ℝ) := by
  by_cases hL : (s.leftLayer p i).Nonempty
  · by_cases hR : (s.rightLayer p j).Nonempty
    · let t := s.valuationDivide p i j hp hL hR
      have hs := hstable t (s.valuationDivide_step p i j hp hL hR)
      rw [universalQuality_eq_normalized, universalQuality_eq_normalized] at hs
      have hscale : t.a*t.b=(s.a*s.b)*(p:ℝ)^((i:ℤ)-(j:ℤ)).natAbs :=
        prime_layer_scale_product s.a s.b p i j
      rw [hscale] at hs
      have hs' : (t.edgeMass/t.area^(3/4:ℝ))^(4:ℝ)*(p:ℝ)^((i:ℤ)-(j:ℤ)).natAbs ≤
          (s.edgeMass/s.area^(3/4:ℝ))^(4:ℝ) := by
        norm_num only [Real.rpow_ofNat]
        apply (mul_le_mul_iff_left₀ (mul_pos s.a_positive s.b_positive)).mp
        nlinarith only [hs]
      have hpR : (0:ℝ)<p := by exact_mod_cast hp.pos
      have hscaled := scaled_mass_bound t.edgeMass_nonneg hM t.area_pos s.area_pos
        (pow_pos hpR _) hs'
      have harea : t.area/s.area=s.alpha p i*s.beta p j := by
        change ((↑(s.leftLayer p i).card:ℝ)*↑(s.rightLayer p j).card)/
          ((↑s.left.card:ℝ)*↑s.right.card) = _
        unfold alpha beta
        ring
      rw [harea, valuationDivide_mass] at hscaled
      exact layer_root (by norm_num : (0:ℝ)<4) hpR (s.mu_nonneg hM p (i,j))
        (mul_nonneg (s.alpha_nonneg p i) (s.beta_nonneg p j)) hscaled
    · have he := Finset.not_nonempty_iff_eq_empty.mp hR
      simp [mu, rectangleMass, he]
      exact mul_nonneg (Real.rpow_nonneg (by exact_mod_cast hp.pos.le) _)
        (Real.rpow_nonneg (mul_nonneg (s.alpha_nonneg p i) (s.beta_nonneg p j)) _)
  · have he := Finset.not_nonempty_iff_eq_empty.mp hL
    simp [mu, rectangleMass, he]
    exact mul_nonneg (Real.rpow_nonneg (by exact_mod_cast hp.pos.le) _)
      (Real.rpow_nonneg (mul_nonneg (s.alpha_nonneg p i) (s.beta_nonneg p j)) _)

theorem universal_layer_target_kernel (s : TaggedState Label n)
    (hstable : ∀ t, Step s t → t.universalQuality ≤ s.universalQuality)
    (hM : 0 < s.edgeMass) (p : ℕ) (hp : Nat.Prime p) (i j : ℕ) :
    s.mu p (i,j) ≤ (p:ℝ)^(-(((i:ℤ)-(j:ℤ)).natAbs:ℝ)/q)*
      (s.alpha p i*s.beta p j)^(3/4:ℝ) :=
  (s.universal_layer_concentration hstable hM p hp i j).trans
    (mul_le_mul_of_nonneg_right (universal_kernel_le_target hp _)
      (Real.rpow_nonneg (mul_nonneg (s.alpha_nonneg p i) (s.beta_nonneg p j)) _))

theorem universal_rectangle_concentration (s : TaggedState Label n)
    (hstable : ∀ t, Step s t → t.universalQuality ≤ s.universalQuality)
    (hM : 0 < s.edgeMass) (L R : Finset Label) (hL : L ⊆ s.left) (hR : R ⊆ s.right) :
    s.rectangleMass L R/s.edgeMass ≤
      (((L.card:ℝ)/s.left.card)*((R.card:ℝ)/s.right.card))^(3/4:ℝ) := by
  by_cases hLN : L.Nonempty
  · by_cases hRN : R.Nonempty
    · let t := s.restrict L R hL hR hLN hRN
      have hs := hstable t (Step.restrict s L R hL hR hLN hRN)
      rw [universalQuality_eq_normalized, universalQuality_eq_normalized] at hs
      have hscale : t.a*t.b=s.a*s.b := rfl
      rw [hscale] at hs
      have hs' : (t.edgeMass/t.area^(3/4:ℝ))^(4:ℝ)*(1:ℝ) ≤
          (s.edgeMass/s.area^(3/4:ℝ))^(4:ℝ) := by
        norm_num only [Real.rpow_ofNat, mul_one]
        exact (mul_le_mul_iff_left₀ (mul_pos s.a_positive s.b_positive)).mp hs
      have hb := scaled_mass_bound t.edgeMass_nonneg hM t.area_pos s.area_pos (by norm_num : (0:ℝ)<1) hs'
      have hh := layer_root (d := 0) (by norm_num : (0:ℝ)<4) (by norm_num : (0:ℝ)<1)
        (div_nonneg t.edgeMass_nonneg hM.le) (div_pos t.area_pos s.area_pos).le
        (by simpa only [pow_zero] using hb)
      simp only [Real.one_rpow, one_mul] at hh
      have heq : s.edges ∩ L.product R = s.edges.filter (fun e => e.1 ∈ L ∧ e.2 ∈ R) := by ext e; simp
      have hmass : t.edgeMass=s.rectangleMass L R := by
        simp only [edgeMass, t, restrict, heq, rectangleMass]
      have harea : t.area/s.area=((L.card:ℝ)/s.left.card)*((R.card:ℝ)/s.right.card) := by
        change ((L.card:ℝ)*(R.card:ℝ))/((s.left.card:ℝ)*(s.right.card:ℝ)) = _
        ring
      simpa only [hmass,harea] using hh
    · have he := Finset.not_nonempty_iff_eq_empty.mp hRN
      simp [he,rectangleMass]
  · have he := Finset.not_nonempty_iff_eq_empty.mp hLN
    simp [he,rectangleMass]

theorem universalQuality_pos_iff_mass (s : TaggedState Label n) :
    0 < s.universalQuality ↔ 0 < s.edgeMass := by
  constructor
  · intro h
    by_contra hM
    have hz := le_antisymm (le_of_not_gt hM) s.edgeMass_nonneg
    simp [universalQuality,hz] at h
  · intro h
    exact mul_pos (div_pos (pow_pos h _) (pow_pos s.area_pos _))
      (mul_pos s.a_positive s.b_positive)

theorem universal_valuation_rectangle_concentration (s : TaggedState Label n)
    (hstable : ∀ t, Step s t → t.universalQuality ≤ s.universalQuality)
    (hM : 0 < s.edgeMass) (p : ℕ) (A B : Finset ℕ) :
    (∑ ij ∈ A.product B,s.mu p ij) ≤
      ((∑ i ∈ A,s.alpha p i)*(∑ j ∈ B,s.beta p j))^(3/4:ℝ) := by
  rw [mu_sum_rectangle,alpha_sum_subset,beta_sum_subset]
  exact s.universal_rectangle_concentration hstable hM _ _
    (Finset.filter_subset _ _) (Finset.filter_subset _ _)

end LonelyRunnerNew.TaggedState

namespace LonelyRunnerNew
theorem original_universal_stable_state_exists (V : Finset ℕ) (hV : valid V) :
    ∃ t : TaggedState ℕ V.card,
      Relation.ReflTransGen TaggedState.Step (initialTaggedState V hV) t ∧
      (initialTaggedState V hV).universalQuality ≤ t.universalQuality ∧
      (∀ u, TaggedState.Step t u → u.universalQuality ≤ t.universalQuality) ∧
      0 < t.edgeMass := by
  obtain ⟨t,hp,hq,hs⟩ := TaggedState.universal_stable_state_exists (initialTaggedState V hV)
  have hpos := (TaggedState.universalQuality_pos_iff_mass (initialTaggedState V hV)).2
    (initialTaggedState_mass_pos V hV)
  exact ⟨t,hp,hq,hs,(TaggedState.universalQuality_pos_iff_mass t).1 (hpos.trans_le hq)⟩
end LonelyRunnerNew
