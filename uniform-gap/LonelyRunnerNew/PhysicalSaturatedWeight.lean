import LonelyRunnerNew.PhysicalCounting
import LonelyRunnerNew.SaturatedIntegral

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew.PhysicalState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

theorem density_nonneg (s : PhysicalState Label n) : 0≤s.density :=
  div_nonneg s.edgeMass_nonneg s.geometry.area_pos.le

theorem density_le_one (s : PhysicalState Label n) : s.density≤1 := by
  have hw : s.edgeMass≤(s.geometry.edges.card:ℝ) := by
    calc
      _ ≤ ∑ _e∈s.geometry.edges,(1:ℝ) := Finset.sum_le_sum (fun _ _ => s.edgeWeight_le_one _)
      _ = _ := by simp
  have hn : s.geometry.edges.card≤s.geometry.left.card*s.geometry.right.card := by
    simpa only [Finset.product_eq_sprod,Finset.card_product] using Finset.card_le_card s.geometry.edges_subset
  apply (div_le_one s.geometry.area_pos).mpr
  exact hw.trans (by unfold TaggedState.area;exact_mod_cast hn)

theorem universal_quality_formula (s : PhysicalState Label n) :
    s.quality 4 0=s.density^4*s.geometry.area/s.Q0 := by
  simp only [quality,Real.rpow_ofNat,Real.rpow_zero,mul_one,scale_eq_inv]
  ring

theorem ordinary_quality_formula (s : PhysicalState Label n) (hM : 0<s.edgeMass) :
    s.quality q sigma=(s.density^4*s.geometry.area/s.Q0)*
      ((s.density^4*s.geometry.area)/(n:ℝ)^2)^sigma := by
  have hr : 0<s.density := div_pos hM s.geometry.area_pos
  have he : q=4+4*sigma := by norm_num [q,sigma]
  have hp : s.density^q=s.density^4*(s.density^4)^sigma := by
    rw [he,Real.rpow_add hr]
    rw [Real.rpow_ofNat,←Real.rpow_natCast,←Real.rpow_mul hr.le]
    norm_num only [Nat.cast_ofNat]
  have hg := s.geometry.area_pos
  have hN := sq_pos_of_pos s.geometry.ambient_pos
  rw [quality,Real.div_rpow hg.le hN.le,scale_eq_inv,hp,
    Real.div_rpow (mul_nonneg (pow_nonneg hr.le _) hg.le) hN.le,
    Real.mul_rpow (pow_nonneg hr.le _) hg.le]
  ring

theorem retained_edge_weight_le_cap (s : PhysicalState Label n) (centers : ℕ → ℕ)
    (hr : s.InRange) (hoff : ∀ p∉s.geometry.primeSupport,centers p=0)
    {e : Label × Label} (he : e∈s.geometry.edges)
    (hall : ∀ p,Nat.Prime p → s.geometry.centerBrackets p (centers p) e) :
    s.edgeWeight e≤Saturated.cap (2*Real.sqrt s.Q0)
      (s.leftProduct centers e.1*s.rightProduct centers e.2) := by
  have hm := Finset.mem_product.mp (s.geometry.edges_subset he)
  have hxp := s.geometry.left_positive e.1 hm.1
  have hyp := s.geometry.right_positive e.2 hm.2
  have hgN := Nat.gcd_pos_of_pos_left (s.geometry.rightValue e.2) hxp
  have hg : (0:ℝ)<Nat.gcd (s.geometry.leftValue e.1) (s.geometry.rightValue e.2) := by exact_mod_cast hgN
  have hp := mul_pos (s.leftProduct_pos centers hm.1) (s.rightProduct_pos centers hm.2)
  have hs : 0<Real.sqrt (s.leftProduct centers e.1*s.rightProduct centers e.2) := Real.sqrt_pos.mpr hp
  have hc : 0<2*Real.sqrt s.Q0 := mul_pos (by norm_num) (Real.sqrt_pos.mpr s.Q0_pos)
  have hid : s.leftProduct centers e.1*s.rightProduct centers e.2*
      (Nat.gcd (s.geometry.leftValue e.1) (s.geometry.rightValue e.2):ℝ)^2=
      (s.geometry.leftValue e.1:ℝ)*(s.geometry.rightValue e.2:ℝ) := by
    dsimp only [leftProduct,rightProduct]
    exact_mod_cast s.retained_product_identity centers hoff he hall
  have hxy : (s.geometry.leftValue e.1:ℝ)*(s.geometry.rightValue e.2:ℝ)≤4*s.A*s.B := by
    have h := mul_le_mul (hr.1 _ hm.1).2.le (hr.2 _ hm.2).2.le
      (by exact_mod_cast hyp.le : (0:ℝ)≤s.geometry.rightValue e.2)
      (mul_nonneg (by norm_num) s.A_pos.le)
    nlinarith only [h]
  rw [Saturated.cap_eq_min hc hp]
  apply min_le_min_left 1
  apply (div_le_div_iff₀ s.D_pos hs).mpr
  apply (sq_le_sq₀ (mul_nonneg hg.le hs.le) (mul_nonneg hc.le s.D_pos.le)).mp
  rw [mul_pow,mul_pow,Real.sq_sqrt hp.le,mul_pow,
    Real.sq_sqrt s.Q0_pos.le]
  have hscale : s.Q0*s.D^2=s.A*s.B := by dsimp [Q0];field_simp [s.D_pos.ne']
  nlinarith only [hid,hxy,hscale]

theorem retained_mass_le_full_cap (s : PhysicalState Label n) (centers : ℕ → ℕ)
    (hr : s.InRange) (hoff : ∀ p∉s.geometry.primeSupport,centers p=0)
    (G : Finset (Label × Label)) (hG : G⊆s.geometry.edges)
    (hall : ∀ e∈G,∀ p,Nat.Prime p → s.geometry.centerBrackets p (centers p) e) :
    (∑ e∈G,s.edgeWeight e)≤∑ x∈s.geometry.left,∑ y∈s.geometry.right,
      Saturated.cap (2*Real.sqrt s.Q0) (s.leftProduct centers x*s.rightProduct centers y) := by
  have hc : 0<2*Real.sqrt s.Q0 := mul_pos (by norm_num) (Real.sqrt_pos.mpr s.Q0_pos)
  calc
    _ ≤ ∑ e∈G,Saturated.cap (2*Real.sqrt s.Q0) (s.leftProduct centers e.1*s.rightProduct centers e.2) :=
      Finset.sum_le_sum (fun e he => s.retained_edge_weight_le_cap centers hr hoff (hG he) (hall e he))
    _ ≤ ∑ e∈s.geometry.left.product s.geometry.right,
        Saturated.cap (2*Real.sqrt s.Q0) (s.leftProduct centers e.1*s.rightProduct centers e.2) :=
      Finset.sum_le_sum_of_subset_of_nonneg (hG.trans s.geometry.edges_subset)
        (fun _ _ _ => Saturated.cap_nonneg hc)
    _ = _ := by rw [Finset.product_eq_sprod,Finset.sum_product]

end LonelyRunnerNew.PhysicalState
