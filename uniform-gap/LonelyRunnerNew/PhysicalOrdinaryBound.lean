import LonelyRunnerNew.PhysicalFourthBound
import LonelyRunnerNew.PhysicalScoreAlgebra

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew.PhysicalState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

theorem roughConstant_nonneg (ell : ℝ) (n : ℕ) : 0≤roughConstant ell n := by
  unfold roughConstant
  apply add_nonneg (by positivity)
  apply mul_nonneg (by norm_num)
  apply Real.rpow_nonneg
  exact div_nonneg (by norm_num) (mul_nonneg (by norm_num) (Nat.cast_nonneg n))

theorem stable_ordinary_physical_bound (s : PhysicalState Label n)
    (hs : ∀ t,Step s t → t.quality q sigma≤s.quality q sigma) (hM : 0<s.edgeMass)
    (hr : s.InRange)
    (hL : ∀ x∈s.geometry.left,rough 142 (s.geometry.leftValue x))
    (hR : ∀ y∈s.geometry.right,rough 142 (s.geometry.rightValue y))
    {ell : ℝ} (hell : 4096≤ell) (hsep : TaggedState.separated (Real.exp ell) s.geometry) :
    s.quality q sigma≤roughConstant ell n := by
  have he : 0<ell := by linarith
  have hfirst0 : 0≤4/(19/100:ℝ)^2*((17/25:ℝ)/ell)^2 := by positivity
  have herr0 : 0≤8/(19/100:ℝ)^2*(2/((27/50:ℝ)*(1/1000)*(n:ℝ)))^sigma := by positivity
  by_cases hsmall : min (s.density*(s.geometry.left.card:ℝ)) (s.density*(s.geometry.right.card:ℝ))<
      2/((27/50:ℝ)*(1/1000))
  · have h4 := s.universal_physical_bound hr hL hR
    have hnorm := s.normalizedFourth_small hsmall
    have hp := Real.rpow_le_rpow s.normalizedFourth_nonneg hnorm (by norm_num [sigma] : (0:ℝ)≤sigma)
    have hh := mul_le_mul h4 hp (Real.rpow_nonneg s.normalizedFourth_nonneg _)
      (by norm_num [Saturated.t0] : (0:ℝ)≤8/Saturated.t0^2)
    rw [←s.ordinary_quality_product hM] at hh
    change s.quality q sigma≤4/(19/100:ℝ)^2*((17/25:ℝ)/ell)^2+
      8/(19/100:ℝ)^2*(2/((27/50:ℝ)*(1/1000)*(n:ℝ)))^sigma
    have hh' : s.quality q sigma≤8/(19/100:ℝ)^2*
        (2/((27/50:ℝ)*(1/1000)*(n:ℝ)))^sigma := by simpa only [Saturated.t0] using hh
    exact hh'.trans (le_add_of_nonneg_left hfirst0)
  · obtain ⟨centers,G,hoff,hG,hkeep,hall⟩ := s.ordinary_all_prime_retention hs hM hL hR
    have hcount := s.ordinary_label_counts centers hr hell hL hR hsep
    have hc : 0<2*Real.sqrt s.Q0 := mul_pos (by norm_num) (Real.sqrt_pos.mpr s.Q0_pos)
    have hk : 0<(17/25:ℝ)/ell := div_pos (by norm_num) he
    have hsum := Saturated.label_sum_plus s.geometry.left s.geometry.right
      (s.leftProduct centers) (s.rightProduct centers) hc hk
      (fun _ hx => s.leftProduct_pos centers hx) (fun _ hy => s.rightProduct_pos centers hy)
      hcount.1 hcount.2
    have hchain := hkeep.trans ((s.retained_mass_le_full_cap centers hr hoff G hG hall).trans hsum)
    change (27/50:ℝ)*s.edgeMass≤(s.geometry.left.card:ℝ)+(s.geometry.right.card:ℝ)+
      s.geometry.area*Saturated.Psi (s.sumParameter ((17/25:ℝ)/ell)) at hchain
    have hdel := min_size_absorption s.density_nonneg
      (by exact_mod_cast s.geometry.left_nonempty.card_pos)
      (by exact_mod_cast s.geometry.right_nonempty.card_pos) (le_of_not_gt hsmall)
    rw [mass_eq_density_area] at hchain
    have hraw : ((27/50:ℝ)*(1-1/1000)*s.density)*s.geometry.area≤
        Saturated.Psi (s.sumParameter ((17/25:ℝ)/ell))*s.geometry.area := by
      change (s.geometry.left.card:ℝ)+(s.geometry.right.card:ℝ)≤
        (27/50:ℝ)*(1/1000)*s.density*s.geometry.area at hdel
      nlinarith only [hchain,hdel]
    have hret := (mul_le_mul_iff_left₀ s.geometry.area_pos).mp hraw
    have hb := (s.ordinary_quality_le_fourth hM).trans (s.fourth_score_of_terminal hk hret)
    have hb' : s.quality q sigma≤4/(19/100:ℝ)^2*((17/25:ℝ)/ell)^2 := by
      dsimp only [Saturated.t0] at hb
      convert hb using 1 <;> ring
    exact hb'.trans (le_add_of_nonneg_right herr0)

/-- Original ordinary physical-score bound, with its stability obtained by
the physical score's own descent. No RC/LC/reconstruction input remains. -/
theorem ordinary_physical_bound (s : PhysicalState Label n) (hr : s.InRange)
    (hL : ∀ x∈s.geometry.left,rough 142 (s.geometry.leftValue x))
    (hR : ∀ y∈s.geometry.right,rough 142 (s.geometry.rightValue y))
    {ell : ℝ} (hell : 4096≤ell) (hsep : TaggedState.separated (Real.exp ell) s.geometry) :
    s.quality q sigma≤roughConstant ell n := by
  by_cases hM : 0<s.edgeMass
  · obtain ⟨t,ht,hq,hs,hpos,htr,htL,htR,htsep⟩ := s.stable_rough_state_exists q sigma
      (by norm_num [q]) hM hr hL hR hsep
    exact hq.trans (t.stable_ordinary_physical_bound hs hpos htr htL htR hell htsep)
  · have hz := le_antisymm (le_of_not_gt hM) s.edgeMass_nonneg
    have hq : s.quality q sigma=0 := by simp [quality,density,hz,Real.zero_rpow (by norm_num [q] : q≠0)]
    rw [hq]
    exact roughConstant_nonneg ell n

end LonelyRunnerNew.PhysicalState
