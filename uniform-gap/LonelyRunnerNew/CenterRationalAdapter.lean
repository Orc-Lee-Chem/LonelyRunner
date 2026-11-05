import LonelyRunnerNew.CommonPrimeCenter
import LonelyRunnerNew.RoughRationalSmall

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew.CenterNormalization

def ratio (N x : ℕ) : ℚ := (x:ℚ)/(N:ℚ)

theorem ratio_pos {N x : ℕ} (hN : 0<N) (hx : 0<x) : 0<ratio N x :=
  div_pos (by exact_mod_cast hx) (by exact_mod_cast hN)

theorem ratio_num (N x : ℕ) (hN : 0<N) :
    (ratio N x).num.natAbs=x/Nat.gcd x N := by
  have hq : ratio N x=mkRat (x:ℤ) N := by
    simpa only [ratio,Int.cast_natCast] using (Rat.mkRat_eq_div (x:ℤ) N).symm
  rw [hq,Rat.num_mkRat,ite_eq_right hN.ne',Int.natAbs_natCast,
    ← Int.natCast_ediv,Int.natAbs_natCast,Nat.gcd_comm]

theorem ratio_den (N x : ℕ) (hN : 0<N) : (ratio N x).den=N/Nat.gcd x N := by
  have hq : ratio N x=mkRat (x:ℤ) N := by
    simpa only [ratio,Int.cast_natCast] using (Rat.mkRat_eq_div (x:ℤ) N).symm
  rw [hq,Rat.den_mkRat,ite_eq_right hN.ne',Int.natAbs_natCast,Nat.gcd_comm]

theorem ratio_num_mul_gcd (N x : ℕ) (hN : 0<N) :
    (ratio N x).num.natAbs*Nat.gcd x N=x := by
  rw [ratio_num N x hN,Nat.div_mul_cancel (Nat.gcd_dvd_left x N)]

theorem ratio_den_mul_gcd (N x : ℕ) (hN : 0<N) :
    (ratio N x).den*Nat.gcd x N=N := by
  rw [ratio_den N x hN,Nat.div_mul_cancel (Nat.gcd_dvd_right x N)]

theorem ratio_reduced (N x : ℕ) : Nat.Coprime (ratio N x).num.natAbs (ratio N x).den :=
  (ratio N x).reduced

theorem ratio_roughPoint {Y N x : ℕ} (hN : rough Y N) (hx : rough Y x) :
    RoughRational.roughPoint Y (ratio N x) := by
  have hr := ratio_pos hN.1 hx.1
  refine ⟨hr,rough_of_positive_dvd hx ?_ ?_,rough_of_positive_dvd hN ?_ ?_⟩
  · exact Int.natAbs_pos.mpr (Rat.num_pos.mpr hr).ne'
  · exact ⟨Nat.gcd x N,(ratio_num_mul_gcd N x hN.1).symm⟩
  · exact (ratio N x).pos
  · exact ⟨Nat.gcd x N,(ratio_den_mul_gcd N x hN.1).symm⟩

theorem ratio_injective {N : ℕ} (hN : 0<N) : Function.Injective (ratio N) := by
  intro x y hxy
  unfold ratio at hxy
  have hn : (N:ℚ)≠0 := by exact_mod_cast hN.ne'
  have hh := congrArg (fun z : ℚ => z*(N:ℚ)) hxy
  simp only [div_mul_cancel₀ _ hn] at hh
  exact_mod_cast hh

theorem ratio_crossHeight {N x y : ℕ} (hN : 0<N) (hx : 0<x) (hy : 0<y) :
    RoughRational.crossHeight (ratio N x) (ratio N y)=height x y := by
  have h := RoughRational.crossHeight_div (x:ℚ) (y:ℚ) (N:ℚ)
    (by exact_mod_cast hx) (by exact_mod_cast hy) (by exact_mod_cast hN)
  simpa only [ratio,RoughRational.crossHeight,Rat.num_natCast,Rat.den_natCast,
    Int.natAbs_natCast,mul_one] using h

/-- Exact denominator product on an edge whose valuations bracket N. -/
theorem denominator_product {N x y : ℕ} (hN : 0<N)
    (hcenter : Nat.gcd x N*Nat.gcd y N=N*Nat.gcd x y) :
    ((ratio N x).den*(ratio N y).den)*Nat.gcd x y=N := by
  have h : N*(((ratio N x).den*(ratio N y).den)*Nat.gcd x y)=N*N := by
    calc
      _ = ((ratio N x).den*(ratio N y).den)*(N*Nat.gcd x y) := by ring
      _ = ((ratio N x).den*(ratio N y).den)*(Nat.gcd x N*Nat.gcd y N) := by rw [hcenter]
      _ = ((ratio N x).den*Nat.gcd x N)*((ratio N y).den*Nat.gcd y N) := by ring
      _ = N*N := by rw [ratio_den_mul_gcd N x hN,ratio_den_mul_gcd N y hN]
  exact (mul_left_cancel₀ hN.ne') h

theorem gcd_eq_center_over_denominators {N x y : ℕ} (hN : 0<N)
    (hcenter : Nat.gcd x N*Nat.gcd y N=N*Nat.gcd x y) :
    (Nat.gcd x y:ℝ)=(N:ℝ)/((ratio N x).den*(ratio N y).den:ℕ) := by
  have hp : (0:ℝ)<((ratio N x).den*(ratio N y).den:ℕ) := by
    exact_mod_cast mul_pos (ratio N x).pos (ratio N y).pos
  apply (eq_div_iff hp.ne').mpr
  have h := denominator_product hN hcenter
  exact_mod_cast (by simpa only [Nat.mul_comm] using h)

theorem rational_product_identity {N x y : ℕ} (hN : 0<N)
    (hcenter : Nat.gcd x N*Nat.gcd y N=N*Nat.gcd x y) :
    (RoughRational.product (ratio N x)*RoughRational.product (ratio N y))*
      (Nat.gcd x y)^2=x*y := by
  calc
    _ = ((ratio N x).num.natAbs*(ratio N y).num.natAbs)*
        ((ratio N x).den*(ratio N y).den*Nat.gcd x y)*Nat.gcd x y := by
      unfold RoughRational.product
      ring
    _ = ((ratio N x).num.natAbs*(ratio N y).num.natAbs)*(N*Nat.gcd x y) := by
      rw [denominator_product hN hcenter]
      ring
    _ = ((ratio N x).num.natAbs*(ratio N y).num.natAbs)*
        (Nat.gcd x N*Nat.gcd y N) := by rw [hcenter]
    _ = ((ratio N x).num.natAbs*Nat.gcd x N)*((ratio N y).num.natAbs*Nat.gcd y N) := by ring
    _ = x*y := by rw [ratio_num_mul_gcd N x hN,ratio_num_mul_gcd N y hN]

theorem weight_center_formula {N x y : ℕ} (hN : 0<N)
    (hcenter : Nat.gcd x N*Nat.gcd y N=N*Nat.gcd x y) (a b : ℝ) :
    weight a b x y=min 1 ((N:ℝ)/
      (((ratio N x).den*(ratio N y).den:ℕ)*max (a*(x:ℝ)) (b*(y:ℝ)))) := by
  unfold weight
  rw [gcd_eq_center_over_denominators hN hcenter]
  congr 1
  ring

theorem physical_center_formula {N x y : ℕ} (hN : 0<N)
    (hcenter : Nat.gcd x N*Nat.gcd y N=N*Nat.gcd x y) (D : ℝ) :
    min 1 ((Nat.gcd x y:ℝ)/D)=min 1 ((N:ℝ)/(D*((ratio N x).den*(ratio N y).den:ℕ))) := by
  rw [gcd_eq_center_over_denominators hN hcenter]
  congr 1
  ring

end LonelyRunnerNew.CenterNormalization

namespace LonelyRunnerNew.TaggedState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

theorem normalized_left_card (s : TaggedState Label n) (centers : ℕ → ℕ) :
    (s.left.image (fun x => CenterNormalization.ratio (s.commonCenter centers) (s.leftValue x))).card=s.left.card := by
  apply Finset.card_image_iff.mpr
  intro x hx y hy he
  exact s.left_injective hx hy (CenterNormalization.ratio_injective (s.commonCenter_pos centers) he)

theorem normalized_right_card (s : TaggedState Label n) (centers : ℕ → ℕ) :
    (s.right.image (fun y => CenterNormalization.ratio (s.commonCenter centers) (s.rightValue y))).card=s.right.card := by
  apply Finset.card_image_iff.mpr
  intro x hx y hy he
  exact s.right_injective hx hy (CenterNormalization.ratio_injective (s.commonCenter_pos centers) he)

theorem normalized_left_rough (s : TaggedState Label n) (centers : ℕ → ℕ)
    (hL : ∀ x∈s.left,rough 142 (s.leftValue x))
    (hR : ∀ y∈s.right,rough 142 (s.rightValue y)) {x : Label} (hx : x∈s.left) :
    RoughRational.roughPoint 142 (CenterNormalization.ratio (s.commonCenter centers) (s.leftValue x)) :=
  CenterNormalization.ratio_roughPoint (s.commonCenter_rough centers hL hR) (hL x hx)

theorem normalized_right_rough (s : TaggedState Label n) (centers : ℕ → ℕ)
    (hL : ∀ x∈s.left,rough 142 (s.leftValue x))
    (hR : ∀ y∈s.right,rough 142 (s.rightValue y)) {y : Label} (hy : y∈s.right) :
    RoughRational.roughPoint 142 (CenterNormalization.ratio (s.commonCenter centers) (s.rightValue y)) :=
  CenterNormalization.ratio_roughPoint (s.commonCenter_rough centers hL hR) (hR y hy)

theorem normalized_left_separated (s : TaggedState Label n) (centers : ℕ → ℕ) {P : ℝ}
    (hsep : separated P s) :
    RoughRational.separated P (s.left.image (fun x =>
      CenterNormalization.ratio (s.commonCenter centers) (s.leftValue x))) := by
  intro r hr t ht hrt
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hr
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp ht
  have hxy : x≠y := by intro h;subst y;exact hrt rfl
  rw [CenterNormalization.ratio_crossHeight (s.commonCenter_pos centers) (s.left_positive x hx) (s.left_positive y hy)]
  exact hsep.1 x hx y hy hxy

theorem normalized_right_separated (s : TaggedState Label n) (centers : ℕ → ℕ) {P : ℝ}
    (hsep : separated P s) :
    RoughRational.separated P (s.right.image (fun y =>
      CenterNormalization.ratio (s.commonCenter centers) (s.rightValue y))) := by
  intro r hr t ht hrt
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hr
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp ht
  have hxy : x≠y := by intro h;subst y;exact hrt rfl
  rw [CenterNormalization.ratio_crossHeight (s.commonCenter_pos centers) (s.right_positive x hx) (s.right_positive y hy)]
  exact hsep.2 x hx y hy hxy

end LonelyRunnerNew.TaggedState
