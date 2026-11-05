import LonelyRunnerNew.PhysicalDescent

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew.PhysicalState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

theorem score_identity {eta tau : ℝ} (hc : 1+tau=eta/4)
    (M A N K : ℝ) (hM : 0≤M) (hA : 0<A) (hN : 0<N) :
    (M/A)^eta*A*K*(A/N)^tau = (M/A^(3/4:ℝ))^eta*(K/N^tau) := by
  rw [Real.div_rpow hM hA.le,Real.div_rpow hA.le hN.le,
    Real.div_rpow hM (Real.rpow_nonneg hA.le _),←Real.rpow_mul hA.le]
  have hp : A^eta=A^((3/4:ℝ)*eta)*A*A^tau := by
    rw [←Real.rpow_add_one hA.ne',←Real.rpow_add hA]
    congr 1
    linarith
  rw [hp]
  have h1 := (Real.rpow_pos_of_pos hA ((3/4:ℝ)*eta)).ne'
  have h2 := (Real.rpow_pos_of_pos hA tau).ne'
  have h3 := (Real.rpow_pos_of_pos hN tau).ne'
  field_simp

theorem quality_eq_normalized (s : PhysicalState Label n) {eta tau : ℝ}
    (hc : 1+tau=eta/4) :
    s.quality eta tau=(s.edgeMass/s.geometry.area^(3/4:ℝ))^eta*
      (s.scale/((n:ℝ)^2)^tau) :=
  score_identity hc s.edgeMass s.geometry.area ((n:ℝ)^2) s.scale
    s.edgeMass_nonneg s.geometry.area_pos (sq_pos_of_pos s.geometry.ambient_pos)

theorem rectangleMass_nonneg (s : PhysicalState Label n) (L R : Finset Label) :
    0≤s.rectangleMass L R := Finset.sum_nonneg (fun e _ => s.edgeWeight_nonneg e)

/-- Physical-score L04, with empty rectangles explicitly included. -/
theorem stable_rectangle_concentration (s : PhysicalState Label n) {eta tau : ℝ}
    (he : 0<eta) (hc : 1+tau=eta/4)
    (hs : ∀ t,Step s t → t.quality eta tau≤s.quality eta tau) (hM : 0<s.edgeMass)
    (L R : Finset Label) (hL : L⊆s.geometry.left) (hR : R⊆s.geometry.right) :
    s.rectangleMass L R/s.edgeMass ≤
      (((L.card:ℝ)/s.geometry.left.card)*((R.card:ℝ)/s.geometry.right.card))^(3/4:ℝ) := by
  by_cases hLN : L.Nonempty
  · by_cases hRN : R.Nonempty
    · let t := s.restrict L R hL hR hLN hRN
      have hh := hs t (Step.restrict s L R hL hR hLN hRN)
      rw [quality_eq_normalized s hc,quality_eq_normalized t hc] at hh
      have hscale : t.scale=s.scale := rfl
      rw [hscale] at hh
      have hfactor : 0<s.scale/((n:ℝ)^2)^tau := div_pos s.scale_pos
        (Real.rpow_pos_of_pos (sq_pos_of_pos s.geometry.ambient_pos) _)
      have hx := TaggedState.scaled_mass_bound t.edgeMass_nonneg hM
        t.geometry.area_pos s.geometry.area_pos (by norm_num : (0:ℝ)<1)
        (by simpa only [mul_one] using (mul_le_mul_iff_left₀ hfactor).mp hh)
      have hb := TaggedState.layer_root (d:=0) he (by norm_num : (0:ℝ)<1)
        (div_nonneg t.edgeMass_nonneg hM.le) (div_pos t.geometry.area_pos s.geometry.area_pos).le
        (by simpa only [pow_zero] using hx)
      simp only [Real.one_rpow,one_mul] at hb
      have ha : t.geometry.area/s.geometry.area =
          ((L.card:ℝ)/s.geometry.left.card)*((R.card:ℝ)/s.geometry.right.card) := by
        change ((L.card:ℝ)*(R.card:ℝ))/((s.geometry.left.card:ℝ)*(s.geometry.right.card:ℝ))=_
        ring
      rw [restrict_mass,ha] at hb
      exact hb
    · have hz := Finset.not_nonempty_iff_eq_empty.mp hRN
      simp [hz,rectangleMass]
  · have hz := Finset.not_nonempty_iff_eq_empty.mp hLN
    simp [hz,rectangleMass]

def valuationDivide (s : PhysicalState Label n) (p i j : ℕ) (hp : Nat.Prime p)
    (hL : (s.geometry.leftLayer p i).Nonempty) (hR : (s.geometry.rightLayer p j).Nonempty) :
    PhysicalState Label n :=
  s.divideLayers (s.geometry.leftLayer p i) (s.geometry.rightLayer p j)
    (Finset.filter_subset _ _) (Finset.filter_subset _ _) hL hR p i j hp
    (fun x => s.geometry.leftValue x/p^i) (fun y => s.geometry.rightValue y/p^j)
    (fun x hx => (TaggedState.valuation_residual hp (s.geometry.left_positive x (Finset.mem_filter.mp hx).1)
      (Finset.mem_filter.mp hx).2).1)
    (fun y hy => (TaggedState.valuation_residual hp (s.geometry.right_positive y (Finset.mem_filter.mp hy).1)
      (Finset.mem_filter.mp hy).2).1)

theorem valuationDivide_step (s : PhysicalState Label n) (p i j : ℕ) (hp : Nat.Prime p)
    (hL : (s.geometry.leftLayer p i).Nonempty) (hR : (s.geometry.rightLayer p j).Nonempty) :
    Step s (s.valuationDivide p i j hp hL hR) := by
  apply Step.prime
  · intro x hx
    exact (TaggedState.valuation_residual hp (s.geometry.left_positive x (Finset.mem_filter.mp hx).1)
      (Finset.mem_filter.mp hx).2).2.2
  · intro y hy
    exact (TaggedState.valuation_residual hp (s.geometry.right_positive y (Finset.mem_filter.mp hy).1)
      (Finset.mem_filter.mp hy).2).2.2

theorem valuationDivide_mass (s : PhysicalState Label n) (p i j : ℕ) (hp : Nat.Prime p)
    (hL : (s.geometry.leftLayer p i).Nonempty) (hR : (s.geometry.rightLayer p j).Nonempty) :
    (s.valuationDivide p i j hp hL hR).edgeMass=
      s.rectangleMass (s.geometry.leftLayer p i) (s.geometry.rightLayer p j) := by
  apply divideLayers_mass
  · intro x hx
    exact (TaggedState.valuation_residual hp (s.geometry.left_positive x (Finset.mem_filter.mp hx).1)
      (Finset.mem_filter.mp hx).2).2.2
  · intro y hy
    exact (TaggedState.valuation_residual hp (s.geometry.right_positive y (Finset.mem_filter.mp hy).1)
      (Finset.mem_filter.mp hy).2).2.2

/-- Physical-score L05 on actual nonempty valuation fibres. -/
theorem stable_layer_concentration_nonempty (s : PhysicalState Label n) {eta tau : ℝ}
    (he : 0<eta) (hc : 1+tau=eta/4)
    (hs : ∀ t,Step s t → t.quality eta tau≤s.quality eta tau) (hM : 0<s.edgeMass)
    (p i j : ℕ) (hp : Nat.Prime p)
    (hL : (s.geometry.leftLayer p i).Nonempty) (hR : (s.geometry.rightLayer p j).Nonempty) :
    s.rectangleMass (s.geometry.leftLayer p i) (s.geometry.rightLayer p j)/s.edgeMass ≤
      (p:ℝ)^(-(((i:ℤ)-(j:ℤ)).natAbs:ℝ)/eta)*
        (s.geometry.alpha p i*s.geometry.beta p j)^(3/4:ℝ) := by
  let t := s.valuationDivide p i j hp hL hR
  have hh := hs t (s.valuationDivide_step p i j hp hL hR)
  rw [quality_eq_normalized s hc,quality_eq_normalized t hc] at hh
  have hscale : t.scale=s.scale*(p:ℝ)^((i:ℤ)-(j:ℤ)).natAbs := s.divideLayers_scale _ _ _ _ _ _ _ _ _ _ _ _ _ _
  rw [hscale] at hh
  have hf : 0<s.scale/((n:ℝ)^2)^tau := div_pos s.scale_pos
    (Real.rpow_pos_of_pos (sq_pos_of_pos s.geometry.ambient_pos) _)
  have hx : (t.edgeMass/t.geometry.area^(3/4:ℝ))^eta*(p:ℝ)^((i:ℤ)-(j:ℤ)).natAbs ≤
      (s.edgeMass/s.geometry.area^(3/4:ℝ))^eta := by
    apply (mul_le_mul_iff_left₀ hf).mp
    convert hh using 1 <;> ring
  have hpR : (0:ℝ)<p := by exact_mod_cast hp.pos
  have hb := TaggedState.scaled_mass_bound t.edgeMass_nonneg hM t.geometry.area_pos s.geometry.area_pos
    (pow_pos hpR _) hx
  have ha : t.geometry.area/s.geometry.area=s.geometry.alpha p i*s.geometry.beta p j := by
    change ((↑(s.geometry.leftLayer p i).card:ℝ)*↑(s.geometry.rightLayer p j).card)/
      ((↑s.geometry.left.card:ℝ)*↑s.geometry.right.card)=_
    unfold TaggedState.alpha TaggedState.beta
    ring
  rw [ha,valuationDivide_mass] at hb
  exact TaggedState.layer_root he hpR (div_nonneg (s.rectangleMass_nonneg _ _) hM.le)
    (mul_nonneg (s.geometry.alpha_nonneg p i) (s.geometry.beta_nonneg p j)) hb

end LonelyRunnerNew.PhysicalState
