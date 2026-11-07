import LonelyRunnerNew.LCActualEndpoint
import Mathlib.Data.Rat.Floor

noncomputable section
open scoped BigOperators
namespace LonelyRunnerNew.LCNumeric

theorem rational_power_upper {x X : ℝ} (hx : 0 ≤ x) (hX : 0 ≤ X)
    (a b : ℕ) (hb : 0 < b) (hpow : x^a ≤ X^b) : x^((a:ℝ)/(b:ℝ)) ≤ X := by
  apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg hx _) hX hb.ne').mp
  have hbR : (b:ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  rw [← Real.rpow_natCast,← Real.rpow_mul hx,div_mul_cancel₀ _ hbR,Real.rpow_natCast]
  exact hpow

theorem negative_power_upper {x X : ℝ} (hx : 0 < x) (hX : 0 < X)
    (a b : ℕ) (hb : 0 < b) (hpow : 1 ≤ X^b*x^a) : x^(-(a:ℝ)/(b:ℝ)) ≤ X :=
  RationalAnalysis.root_bound hx hX a b hb hpow

/-- Fast, kernel-checkable integer witness for a rational negative root.
No reduction of a large rational power (and its repeated gcds) is required. -/
theorem integer_negative_root (num den base a b : ℕ) (hd : 0 < den)
    (h : den^b ≤ num^b*base^a) :
    (1:ℚ) ≤ ((num:ℚ)/(den:ℚ))^b*(base:ℚ)^a := by
  have hdQ : (0:ℚ) < den := by exact_mod_cast hd
  rw [div_pow,div_mul_eq_mul_div]
  apply (le_div_iff₀ (pow_pos hdQ b)).mpr
  simpa only [one_mul] using (show (den:ℚ)^b ≤ (num:ℚ)^b*(base:ℚ)^a by exact_mod_cast h)

theorem f_monotone : MonotoneOn LCDirection.f (Set.Icc (0:ℝ) (1/2)) := by
  let df := fun x : ℝ => (3/4:ℝ)*(x^(-(1/4):ℝ)-(1-x)^(-(1/4):ℝ))
  apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := df) (convex_Icc 0 (1/2))
  · exact ((Real.continuous_rpow_const (by norm_num : (0:ℝ) ≤ 3/4)).add
      ((Real.continuous_rpow_const (by norm_num : (0:ℝ) ≤ 3/4)).comp (continuous_const.sub continuous_id))).continuousOn
  · intro x hx
    have hxi : x ∈ Set.Ioo (0:ℝ) (1/2) := by simpa only [interior_Icc] using hx
    have hx0 : 0 < x := hxi.1
    have hx1 : x < 1/2 := hxi.2
    have hy0 : 0 < 1-x := by linarith
    have hh := ((hasDerivAt_id x).rpow_const (p := (3/4:ℝ)) (Or.inl hx0.ne')).add
      (((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)).rpow_const (p := (3/4:ℝ)) (Or.inl hy0.ne'))
    apply HasDerivAt.hasDerivWithinAt
    convert hh using 1
    · rfl
    · dsimp [df]
      norm_num only [id_eq,mul_one,zero_sub]
      ring
  · intro x hx
    have hxi : x ∈ Set.Ioo (0:ℝ) (1/2) := by simpa only [interior_Icc] using hx
    have hx0 : 0 < x := hxi.1
    have hx1 : x < 1/2 := hxi.2
    have hpow := Real.rpow_le_rpow_of_nonpos hx0 (show x ≤ 1-x by linarith) (by norm_num : (-(1/4):ℝ) ≤ 0)
    dsimp [df]
    exact mul_nonneg (by norm_num) (sub_nonneg.mpr hpow)

theorem h0_antitone : AntitoneOn LCDirection.h0 (Set.Icc (0:ℝ) (1/2)) := by
  let df := fun x : ℝ => (3/2:ℝ)*(x^(1/2:ℝ)-(1-x)^(1/2:ℝ))
  apply antitoneOn_of_hasDerivWithinAt_nonpos (f' := df) (convex_Icc 0 (1/2))
  · exact ((Real.continuous_rpow_const (by norm_num : (0:ℝ) ≤ 3/2)).add
      ((Real.continuous_rpow_const (by norm_num : (0:ℝ) ≤ 3/2)).comp (continuous_const.sub continuous_id))).continuousOn
  · intro x hx
    have hxm := interior_subset hx
    have hx0 : 0 ≤ x := hxm.1
    have hy0 : 0 ≤ 1-x := by linarith [hxm.2]
    have hh := ((hasDerivAt_id x).rpow_const (p := (3/2:ℝ)) (Or.inr (by norm_num))).add
      (((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)).rpow_const (p := (3/2:ℝ)) (Or.inr (by norm_num)))
    apply HasDerivAt.hasDerivWithinAt
    convert hh using 1
    · rfl
    · dsimp [df]
      norm_num only [id_eq,mul_one,zero_sub]
      ring
  · intro x hx
    have hxm := interior_subset hx
    have hx0 : 0 ≤ x := hxm.1
    have hxy : x ≤ 1-x := by linarith [hxm.2]
    have hh := Real.rpow_le_rpow hx0 hxy (by norm_num : (0:ℝ) ≤ 1/2)
    dsimp [df]
    exact mul_nonpos_of_nonneg_of_nonpos (by norm_num) (sub_nonpos.mpr hh)

def j (u : ℝ) : ℝ := (u*(1-u))^(3/4:ℝ)

theorem j_monotone : MonotoneOn j (Set.Icc (0:ℝ) (1/2)) := by
  intro x hx y hy hxy
  have hp : x*(1-x) ≤ y*(1-y) := by
    have hh := mul_nonneg (sub_nonneg.mpr hxy) (show 0 ≤ 1-x-y by linarith [hx.2,hy.2])
    nlinarith only [hh]
  exact Real.rpow_le_rpow (mul_nonneg hx.1 (by linarith [hx.2])) hp (by norm_num)

theorem grid_cover {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1/2) :
    ∃ i : ℕ,i < 256 ∧ (i:ℝ)/512 ≤ u ∧ u ≤ ((i:ℝ)+1)/512 := by
  let m := ⌊512*u⌋₊
  have hfloor : (m:ℝ) ≤ 512*u := Nat.floor_le (by positivity)
  have hnext : 512*u < (m:ℝ)+1 := Nat.lt_floor_add_one _
  by_cases hm : m < 256
  · exact ⟨m,hm,by linarith,by linarith⟩
  · have hm0 : 256 ≤ m := by omega
    have hmR : (256:ℝ) ≤ m := by exact_mod_cast hm0
    refine ⟨255,by decide,?_,?_⟩ <;> norm_num <;> linarith

/-- Five individual algebraic root witnesses. fUpper/h0Upper are the sums
of the corresponding two witnesses, so no root of a sum is substituted. -/
structure Box where
  lo : ℚ
  hi : ℚ
  f1 : ℚ
  f2 : ℚ
  h1 : ℚ
  h2 : ℚ
  jj : ℚ
  deriving Inhabited,DecidableEq

def Box.Valid (b : Box) : Prop :=
  0 ≤ b.lo ∧ b.lo ≤ b.hi ∧ b.hi ≤ 1/2 ∧
  0 ≤ b.f1 ∧ 0 ≤ b.f2 ∧ 0 ≤ b.h1 ∧ 0 ≤ b.h2 ∧ 0 ≤ b.jj ∧
  b.hi^3 ≤ b.f1^4 ∧ (1-b.hi)^3 ≤ b.f2^4 ∧
  b.lo^3 ≤ b.h1^2 ∧ (1-b.lo)^3 ≤ b.h2^2 ∧
  (b.hi*(1-b.hi))^3 ≤ b.jj^4

instance (b : Box) : Decidable b.Valid := by unfold Box.Valid; infer_instance

theorem Box.bounds (b : Box) (hb : b.Valid) {u : ℝ}
    (hu : (b.lo:ℝ) ≤ u) (hu1 : u ≤ (b.hi:ℝ)) :
    LCDirection.f u ≤ (b.f1+b.f2:ℚ) ∧ LCDirection.h0 u ≤ (b.h1+b.h2:ℚ) ∧ j u ≤ b.jj := by
  rcases hb with ⟨hl,hlh,hh,hf1,hf2,hh1,hh2,hj,hf1p,hf2p,hh1p,hh2p,hjp⟩
  have hlR : (0:ℝ) ≤ b.lo := by exact_mod_cast hl
  have hhR : (b.hi:ℝ) ≤ 1/2 := by
    have hh' : (2:ℚ)*b.hi ≤ 1 := by linarith
    have hhR' : (2:ℝ)*(b.hi:ℝ) ≤ 1 := by exact_mod_cast hh'
    linarith
  have hlhR : (b.lo:ℝ) ≤ b.hi := by exact_mod_cast hlh
  have hhiR : (0:ℝ) ≤ b.hi := hlR.trans (by exact_mod_cast hlh)
  have hf1R := rational_power_upper hhiR (by exact_mod_cast hf1 : (0:ℝ) ≤ b.f1) 3 4 (by decide)
    (by exact_mod_cast hf1p)
  have hf2R := rational_power_upper (show (0:ℝ) ≤ 1-b.hi by linarith)
    (by exact_mod_cast hf2 : (0:ℝ) ≤ b.f2) 3 4 (by decide) (by exact_mod_cast hf2p)
  have hh1R := rational_power_upper hlR (by exact_mod_cast hh1 : (0:ℝ) ≤ b.h1) 3 2 (by decide)
    (by exact_mod_cast hh1p)
  have hh2R := rational_power_upper (show (0:ℝ) ≤ 1-b.lo by linarith)
    (by exact_mod_cast hh2 : (0:ℝ) ≤ b.h2) 3 2 (by decide) (by exact_mod_cast hh2p)
  have hjR := rational_power_upper (show (0:ℝ) ≤ b.hi*(1-b.hi) from mul_nonneg hhiR (by linarith))
    (by exact_mod_cast hj : (0:ℝ) ≤ b.jj) 3 4 (by decide) (by exact_mod_cast hjp)
  have hf := f_monotone ⟨hlR.trans hu,hu1.trans hhR⟩ ⟨hhiR,hhR⟩ hu1
  have hh0 := h0_antitone ⟨hlR,(show (b.lo:ℝ) ≤ 1/2 by linarith)⟩
    ⟨hlR.trans hu,hu1.trans hhR⟩ hu
  have hj0 := j_monotone ⟨hlR.trans hu,hu1.trans hhR⟩ ⟨hhiR,hhR⟩ hu1
  refine ⟨hf.trans ?_,hh0.trans ?_,hj0.trans hjR⟩
  · unfold LCDirection.f
    norm_num only [Nat.cast_ofNat] at hf1R hf2R
    exact_mod_cast add_le_add hf1R hf2R
  · unfold LCDirection.h0
    norm_num only [Nat.cast_ofNat] at hh1R hh2R
    exact_mod_cast add_le_add hh1R hh2R

end LonelyRunnerNew.LCNumeric
