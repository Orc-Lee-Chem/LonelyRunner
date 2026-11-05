import LonelyRunnerNew.Foundation
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section

namespace LonelyRunnerNew.RoughRational

/-- Canonical numerator-times-denominator product of a rational. -/
def product (r : ℚ) : ℕ := r.num.natAbs * r.den

/-- Height of the quotient, computed by reducing its two cross products. -/
def crossHeight (r s : ℚ) : ℝ :=
  height (r.num.natAbs * s.den) (s.num.natAbs * r.den)

def separated (P : ℝ) (S : Finset ℚ) : Prop :=
  ∀ r ∈ S, ∀ s ∈ S, r ≠ s → P < crossHeight r s

def roughPoint (Y : ℕ) (r : ℚ) : Prop :=
  0 < r ∧ rough Y r.num.natAbs ∧ rough Y r.den

def count (S : Finset ℚ) (T : ℝ) : ℕ := (S.filter (fun r => (product r : ℝ) ≤ T)).card

theorem height_eq_reduced_fraction (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    height a b = ((max (((a : ℚ) / (b : ℚ)).num.natAbs)
      (((a : ℚ) / (b : ℚ)).den) : ℕ) : ℝ) := by
  have hq : (a : ℚ) / (b : ℚ) = mkRat (a : ℤ) b := by
    simpa only [Int.cast_natCast] using (Rat.mkRat_eq_div (a : ℤ) b).symm
  have hnum : ((a : ℚ) / (b : ℚ)).num.natAbs = a / Nat.gcd a b := by
    rw [hq, Rat.num_mkRat, ite_eq_right hb.ne', Int.natAbs_natCast,
      ← Int.natCast_ediv, Int.natAbs_natCast, Nat.gcd_comm]
  have hden : ((a : ℚ) / (b : ℚ)).den = b / Nat.gcd a b := by
    rw [hq, Rat.den_mkRat, ite_eq_right hb.ne', Int.natAbs_natCast, Nat.gcd_comm]
  have hg : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha
  have hfa : Nat.gcd a b * (a / Nat.gcd a b) = a := by
    rw [Nat.mul_comm, Nat.div_mul_cancel (Nat.gcd_dvd_left a b)]
  have hfb : Nat.gcd a b * (b / Nat.gcd a b) = b := by
    rw [Nat.mul_comm, Nat.div_mul_cancel (Nat.gcd_dvd_right a b)]
  rw [hnum, hden]
  calc
    height a b = height (Nat.gcd a b * (a / Nat.gcd a b))
        (Nat.gcd a b * (b / Nat.gcd a b)) := by rw [hfa, hfb]
    _ = height (a / Nat.gcd a b) (b / Nat.gcd a b) := height_mul_left _ _ _ hg
    _ = _ := by simp [height, (Nat.coprime_div_gcd_div_gcd hg).gcd_eq_one]

theorem rat_eq_abs_num_div_den (r : ℚ) (hr : 0 < r) :
    r = (r.num.natAbs : ℚ) / (r.den : ℚ) := by
  rw [Nat.cast_natAbs, abs_of_pos (Rat.num_pos.mpr hr),
    Rat.num_div_den]

theorem crossHeight_eq_reduced_quotient (r s : ℚ) (hr : 0 < r) (hs : 0 < s) :
    crossHeight r s = ((max (r / s).num.natAbs (r / s).den : ℕ) : ℝ) := by
  have hq : r / s = (((r.num.natAbs * s.den : ℕ) : ℚ) /
      ((s.num.natAbs * r.den : ℕ) : ℚ)) := by
    conv_lhs => rw [rat_eq_abs_num_div_den r hr, rat_eq_abs_num_div_den s hs]
    simp only [Nat.cast_mul, div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  rw [crossHeight, height_eq_reduced_fraction _ _
    (Nat.mul_pos (Int.natAbs_pos.mpr (Rat.num_pos.mpr hr).ne') s.pos)
    (Nat.mul_pos (Int.natAbs_pos.mpr (Rat.num_pos.mpr hs).ne') r.pos), ← hq]

/-- The rational-height preservation used when RC is applied after division by N. -/
theorem crossHeight_div (r s u : ℚ) (hr : 0 < r) (hs : 0 < s) (hu : 0 < u) :
    crossHeight (r / u) (s / u) = crossHeight r s := by
  rw [crossHeight_eq_reduced_quotient _ _ (div_pos hr hu) (div_pos hs hu),
    div_div_div_cancel_right₀ hu.ne', crossHeight_eq_reduced_quotient r s hr hs]

theorem sector_cross_products_le {R T a b c d : ℝ}
    (_hR : 0 < R) (hT : 0 ≤ T) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hal : R * b ≤ a) (hau : a ≤ 2 * R * b)
    (hcl : R * d ≤ c) (hcu : c ≤ 2 * R * d)
    (hab : a * b ≤ T) (hcd : c * d ≤ T) :
    max (a * d) (c * b) ≤ Real.sqrt 2 * T := by
  have hxy : a * d ≤ 2 * (c * b) := by
    have h1 := mul_le_mul_of_nonneg_right hau hd
    have h2 := mul_le_mul_of_nonneg_left hcl (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hb)
    nlinarith
  have hyx : c * b ≤ 2 * (a * d) := by
    have h1 := mul_le_mul_of_nonneg_right hcu hb
    have h2 := mul_le_mul_of_nonneg_left hal (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hd)
    nlinarith
  have hprod : (a * d) * (c * b) ≤ T ^ 2 := by
    have h := mul_le_mul hab hcd (mul_nonneg hc hd) hT
    nlinarith only [h]
  have hx0 : 0 ≤ a * d := mul_nonneg ha hd
  have hy0 : 0 ≤ c * b := mul_nonneg hc hb
  have hsq : max (a * d) (c * b) ^ 2 ≤ 2 * T ^ 2 := by
    rcases le_total (a * d) (c * b) with h | h
    · rw [max_eq_right h]
      nlinarith [mul_le_mul_of_nonneg_left hyx hy0]
    · rw [max_eq_left h]
      nlinarith [mul_le_mul_of_nonneg_left hxy hx0]
  have hroot : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hrightsq : (Real.sqrt 2 * T) ^ 2 = 2 * T ^ 2 := by
    rw [mul_pow, hroot]
  have hright0 : 0 ≤ Real.sqrt 2 * T := mul_nonneg (Real.sqrt_nonneg _) hT
  have hmax0 : 0 ≤ max (a * d) (c * b) := hx0.trans (le_max_left _ _)
  nlinarith only [hsq, hrightsq, hright0, hmax0]

theorem height_le_max {x y : ℕ} (hx : 0 < x) :
    height x y ≤ ((max x y : ℕ) : ℝ) := by
  have hg : 1 ≤ (Nat.gcd x y : ℝ) := by
    exact_mod_cast Nat.gcd_pos_of_pos_left y hx
  exact div_le_self (by positivity) hg

theorem sector_cross_height_le {R T : ℝ} (hR : 0 < R) (hT : 0 ≤ T)
    (a b c d : ℕ) (ha : 0 < a) (_hb : 0 < b) (_hc : 0 < c) (hd : 0 < d)
    (hal : R * (b : ℝ) ≤ a) (hau : (a : ℝ) ≤ 2 * R * b)
    (hcl : R * (d : ℝ) ≤ c) (hcu : (c : ℝ) ≤ 2 * R * d)
    (hab : (a : ℝ) * b ≤ T) (hcd : (c : ℝ) * d ≤ T) :
    height (a * d) (c * b) ≤ Real.sqrt 2 * T := by
  have hm := sector_cross_products_le hR hT (Nat.cast_nonneg a) (Nat.cast_nonneg b)
    (Nat.cast_nonneg c) (Nat.cast_nonneg d) hal hau hcl hcu hab hcd
  calc
    height (a * d) (c * b) ≤ ((max (a * d) (c * b) : ℕ) : ℝ) :=
      height_le_max (Nat.mul_pos ha hd)
    _ = max ((a : ℝ) * d) ((c : ℝ) * b) := by simp only [Nat.cast_max, Nat.cast_mul]
    _ ≤ Real.sqrt 2 * T := hm

theorem cast_eq_abs_num_div_den (r : ℚ) (hr : 0 < r) :
    (r : ℝ) = (r.num.natAbs : ℝ) / (r.den : ℝ) := by
  have hnum : (r.num.natAbs : ℝ) = (r.num : ℝ) := by
    rw [Nat.cast_natAbs, abs_of_pos (Rat.num_pos.mpr hr)]
  rw [hnum, Rat.cast_def]

theorem crossHeight_le_of_sector {R T : ℝ} (hR : 0 < R) (hT : 0 ≤ T)
    (r s : ℚ) (hr : 0 < r) (hs : 0 < s)
    (hrl : R ≤ (r : ℝ)) (hru : (r : ℝ) ≤ 2 * R)
    (hsl : R ≤ (s : ℝ)) (hsu : (s : ℝ) ≤ 2 * R)
    (hrT : (product r : ℝ) ≤ T) (hsT : (product s : ℝ) ≤ T) :
    crossHeight r s ≤ Real.sqrt 2 * T := by
  have hrden : (0 : ℝ) < r.den := by exact_mod_cast r.pos
  have hsden : (0 : ℝ) < s.den := by exact_mod_cast s.pos
  rw [cast_eq_abs_num_div_den r hr] at hrl hru
  rw [cast_eq_abs_num_div_den s hs] at hsl hsu
  apply sector_cross_height_le hR hT r.num.natAbs r.den s.num.natAbs s.den
    (Int.natAbs_pos.mpr (Rat.num_pos.mpr hr).ne') r.pos
    (Int.natAbs_pos.mpr (Rat.num_pos.mpr hs).ne') s.pos
    ((le_div_iff₀ hrden).mp hrl) ((div_le_iff₀ hrden).mp hru)
    ((le_div_iff₀ hsden).mp hsl) ((div_le_iff₀ hsden).mp hsu)
  · simpa only [product, Nat.cast_mul] using hrT
  · simpa only [product, Nat.cast_mul] using hsT

/-- The small-product branch of RC. It does not need a rough-number theorem. -/
theorem small_product_count_le_one {P R T : ℝ} (hR : 0 < R) (hT : 0 ≤ T)
    (hsmall : Real.sqrt 2 * T ≤ P) (S : Finset ℚ)
    (hpos : ∀ r ∈ S, 0 < r)
    (hsector : ∀ r ∈ S, R ≤ (r : ℝ) ∧ (r : ℝ) ≤ 2 * R)
    (hsep : separated P S) : count S T ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro r hr s hs
  have hrmem := (Finset.mem_filter.mp hr).1
  have hsmem := (Finset.mem_filter.mp hs).1
  by_contra hne
  have hheight := crossHeight_le_of_sector hR hT r s (hpos r hrmem) (hpos s hsmem)
    (hsector r hrmem).1 (hsector r hrmem).2 (hsector s hsmem).1 (hsector s hsmem).2
    (Finset.mem_filter.mp hr).2 (Finset.mem_filter.mp hs).2
  exact (not_lt_of_ge (hheight.trans hsmall)) (hsep r hrmem s hsmem hne)

theorem rc_small_product_bound {ell R T : ℝ} (hell : 4096 ≤ ell) (hR : 0 < R)
    (hT : 0 < T) (hsmall : Real.sqrt 2 * T ≤ Real.exp ell) (S : Finset ℚ)
    (hpos : ∀ r ∈ S, 0 < r)
    (hsector : ∀ r ∈ S, R ≤ (r : ℝ) ∧ (r : ℝ) ≤ 2 * R)
    (hsep : separated (Real.exp ell) S) :
    (count S T : ℝ) ≤ 1 + (17 / 25 : ℝ) * T / ell := by
  have hcount : (count S T : ℝ) ≤ 1 := by
    exact_mod_cast small_product_count_le_one hR hT.le hsmall S hpos hsector hsep
  have hell0 : 0 < ell := by linarith
  exact hcount.trans (le_add_of_nonneg_right (by positivity))

/-- Exact RC obligation, as a named target proposition, not an axiom. -/
def CountBound : Prop :=
  ∀ (ell R T : ℝ), 4096 ≤ ell → 0 < R → 0 < T →
    ∀ S : Finset ℚ, (∀ r ∈ S, roughPoint 142 r) →
      (∀ r ∈ S, R ≤ (r : ℝ) ∧ (r : ℝ) < 2 * R) →
      separated (Real.exp ell) S →
      (count S T : ℝ) ≤ 1 + (17 / 25 : ℝ) * T / ell

/-- The remaining RC range after the proved small-product branch. -/
def LargeRangeCountBound : Prop :=
  ∀ (ell R T : ℝ), 4096 ≤ ell → 0 < R → 0 < T → Real.exp ell < Real.sqrt 2 * T →
    ∀ S : Finset ℚ, (∀ r ∈ S, roughPoint 142 r) →
      (∀ r ∈ S, R ≤ (r : ℝ) ∧ (r : ℝ) < 2 * R) →
      separated (Real.exp ell) S →
      (count S T : ℝ) ≤ 1 + (17 / 25 : ℝ) * T / ell

theorem countBound_iff_largeRange : CountBound ↔ LargeRangeCountBound := by
  constructor
  · intro h ell R T hell hR hT _ S hrough hsector hsep
    exact h ell R T hell hR hT S hrough hsector hsep
  · intro h ell R T hell hR hT S hrough hsector hsep
    by_cases hsmall : Real.sqrt 2 * T ≤ Real.exp ell
    · exact rc_small_product_bound hell hR hT hsmall S (fun r hr => (hrough r hr).1)
        (fun r hr => ⟨(hsector r hr).1, (hsector r hr).2.le⟩) hsep
    · exact h ell R T hell hR hT (lt_of_not_ge hsmall) S hrough hsector hsep

end LonelyRunnerNew.RoughRational
