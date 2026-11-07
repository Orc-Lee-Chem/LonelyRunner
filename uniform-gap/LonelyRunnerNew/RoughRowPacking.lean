import LonelyRunnerNew.RoughRationalRows
import LonelyRunnerNew.CenterRationalAdapter

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew.RoughRational
attribute [local instance] Classical.propDecidable

theorem height_le_of_cross_product {x y k l : ℕ} (hx : 0<x) (hy : 0<y)
    (hk : 0<k) (he : x*k=y*l) : height x y≤(max k l:ℕ) := by
  have hq : (x:ℚ)/(y:ℚ)=CenterNormalization.ratio k l := by
    apply (div_eq_div_iff (by exact_mod_cast hy.ne' : (y:ℚ)≠0) (by exact_mod_cast hk.ne' : (k:ℚ)≠0)).mpr
    exact_mod_cast (by simpa only [Nat.mul_comm] using he)
  rw [height_eq_reduced_fraction x y hx hy,hq,CenterNormalization.ratio_num k l hk,CenterNormalization.ratio_den k l hk]
  exact_mod_cast max_le ((Nat.div_le_self _ _).trans (le_max_right k l))
    ((Nat.div_le_self _ _).trans (le_max_left k l))

def rowSet (S : Finset ℚ) (T : ℝ) (i : ℕ) : Finset ℚ :=
  (countedSet S T).filter (fun r => r.den=i+1)

theorem row_crossHeight (S : Finset ℚ) (T : ℝ) (i : ℕ) {r s : ℚ}
    (hr : r∈rowSet S T i) (hs : s∈rowSet S T i) :
    crossHeight r s=height r.num.natAbs s.num.natAbs := by
  have hrden := (Finset.mem_filter.mp hr).2
  have hsden := (Finset.mem_filter.mp hs).2
  unfold crossHeight
  rw [hrden,hsden]
  simpa only [Nat.mul_comm] using height_mul_left (i+1) r.num.natAbs s.num.natAbs (by omega)

/-- Unbounded multiplicative-neighborhood injectivity. Distinct row points
cannot have equal numerator multiples with multipliers of height at most P. -/
theorem row_multiplier_injective (S : Finset ℚ) (T P : ℝ) (i : ℕ) (K : Finset ℕ)
    (hpos : ∀ r∈S,0<r) (hsep : separated P S)
    (hK : ∀ k∈K,0<k ∧ (k:ℝ)≤P) :
    Set.InjOn (fun z : ℚ × ℕ => z.1.num.natAbs*z.2) ((rowSet S T i).product K:Set (ℚ × ℕ)) := by
  intro z hz w hw he
  change z.1.num.natAbs*z.2=w.1.num.natAbs*w.2 at he
  have hzmem := Finset.mem_product.mp hz
  have hwmem := Finset.mem_product.mp hw
  have hzS : z.1∈S := (Finset.mem_filter.mp (Finset.mem_filter.mp hzmem.1).1).1
  have hwS : w.1∈S := (Finset.mem_filter.mp (Finset.mem_filter.mp hwmem.1).1).1
  have hznum : 0<z.1.num.natAbs := Int.natAbs_pos.mpr (Rat.num_pos.mpr (hpos _ hzS)).ne'
  have hwnum : 0<w.1.num.natAbs := Int.natAbs_pos.mpr (Rat.num_pos.mpr (hpos _ hwS)).ne'
  have hrs : z.1=w.1 := by
    by_contra hn
    have hheight := height_le_of_cross_product hznum hwnum (hK _ hzmem.2).1 he
    have hmax : ((max z.2 w.2:ℕ):ℝ)≤P := by
      rw [Nat.cast_max]
      exact max_le (hK _ hzmem.2).2 (hK _ hwmem.2).2
    have hlt := hsep _ hzS _ hwS hn
    rw [row_crossHeight S T i hzmem.1 hwmem.1] at hlt
    exact (not_lt_of_ge (hheight.trans hmax)) hlt
  have hkl : z.2=w.2 := by
    rw [hrs] at he
    exact (mul_left_cancel₀ hwnum.ne') he
  exact Prod.ext hrs hkl

theorem row_numerator_bounds (S : Finset ℚ) {R T : ℝ} (hR : 0<R) (i : ℕ)
    (hpos : ∀ r∈S,0<r) (hsector : ∀ r∈S,R≤(r:ℝ) ∧ (r:ℝ)<2*R)
    {r : ℚ} (hr : r∈rowSet S T i) :
    R*(i+1:ℝ)≤(r.num.natAbs:ℝ) ∧
      (r.num.natAbs:ℝ)≤min (2*R*(i+1:ℝ)) (T/(i+1:ℝ)) := by
  have hh := Finset.mem_filter.mp hr
  have hrS := (Finset.mem_filter.mp hh.1).1
  have hp := (Finset.mem_filter.mp hh.1).2
  have hd : (0:ℝ)<(i+1:ℝ) := by positivity
  have hs := hsector r hrS
  rw [cast_eq_abs_num_div_den r (hpos r hrS),hh.2] at hs
  norm_num only [Nat.cast_add,Nat.cast_one] at hs
  have hl := (le_div_iff₀ hd).mp hs.1
  have hu := (div_lt_iff₀ hd).mp hs.2
  have hprod : (r.num.natAbs:ℝ)*(i+1:ℝ)≤T := by
    simpa only [product,hh.2,Nat.cast_mul,Nat.cast_add,Nat.cast_one] using hp
  exact ⟨hl,le_min hu.le ((le_div_iff₀ hd).mpr hprod)⟩

theorem row_singleton_of_small_upper (S : Finset ℚ) {R T P : ℝ} (hR : 0<R) (i : ℕ)
    (hpos : ∀ r∈S,0<r) (hsector : ∀ r∈S,R≤(r:ℝ) ∧ (r:ℝ)<2*R)
    (hsep : separated P S) (hsmall : min (2*R*(i+1:ℝ)) (T/(i+1:ℝ))≤P) : rowCount S T i≤1 := by
  apply Finset.card_le_one.mpr
  intro r hr s hs
  by_contra hn
  have hrS := (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).1
  have hsS := (Finset.mem_filter.mp (Finset.mem_filter.mp hs).1).1
  have hlt := hsep r hrS s hsS hn
  rw [row_crossHeight S T i hr hs] at hlt
  have hrnum : 0<r.num.natAbs := Int.natAbs_pos.mpr (Rat.num_pos.mpr (hpos r hrS)).ne'
  have hg : (1:ℝ)≤Nat.gcd r.num.natAbs s.num.natAbs := by
    exact_mod_cast Nat.gcd_pos_of_pos_left s.num.natAbs hrnum
  have hmax : max (r.num.natAbs:ℝ) (s.num.natAbs:ℝ)≤P :=
    max_le ((row_numerator_bounds S hR i hpos hsector hr).2.trans hsmall)
      ((row_numerator_bounds S hR i hpos hsector hs).2.trans hsmall)
  have hh : height r.num.natAbs s.num.natAbs≤P := by
    unfold height
    rw [Nat.cast_max]
    exact (div_le_self (by positivity) hg).trans hmax
  exact (not_lt_of_ge hh) hlt

theorem rough_mul_values {Y a b : ℕ} (ha : rough Y a) (hb : rough Y b) : rough Y (a*b) := by
  refine ⟨mul_pos ha.1 hb.1,?_⟩
  intro p hp hY hd
  rcases hp.dvd_mul.mp hd with h | h
  · exact ha.2 p hp hY h
  · exact hb.2 p hp hY h

def roughMultipliers (Y Z : ℕ) : Finset ℕ := (Finset.Icc 1 Z).filter (rough Y)
def roughIntegerInterval (Y : ℕ) (L U : ℝ) : Finset ℕ :=
  (Finset.range (⌊U⌋₊+1)).filter (fun m => rough Y m ∧ L≤(m:ℝ))

theorem roughMultipliers_nonempty {Y Z : ℕ} (hZ : 0<Z) : (roughMultipliers Y Z).Nonempty := by
  refine ⟨1,Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_refl _,hZ⟩,?_⟩⟩
  exact ⟨by norm_num,fun p hp _ => hp.not_dvd_one⟩

/-- A proved packing bound for every row and every positive multiplier cutoff
Z<=exp ell. The remaining analytic sieve must bound this actual rough interval;
no rough counting estimate or finite cutoff on the original problem is assumed. -/
theorem row_rough_packing (S : Finset ℚ) {R T ell : ℝ} (hR : 0<R) (hT : 0<T)
    (i Z : ℕ) (hZ : 0<Z) (hZell : (Z:ℝ)≤Real.exp ell)
    (hrough : ∀ r∈S,roughPoint 142 r)
    (hsector : ∀ r∈S,R≤(r:ℝ) ∧ (r:ℝ)<2*R) (hsep : separated (Real.exp ell) S) :
    rowCount S T i*(roughMultipliers 142 Z).card≤
      (roughIntegerInterval 142 (R*(i+1:ℝ))
        ((min (2*R*(i+1:ℝ)) (T/(i+1:ℝ)))*(Z:ℝ))).card := by
  let K := roughMultipliers 142 Z
  let F := (rowSet S T i).product K
  let f := fun z : ℚ × ℕ => z.1.num.natAbs*z.2
  have hK (k : ℕ) (hk : k∈K) : 0<k ∧ k≤Z ∧ rough 142 k := by
    have h := Finset.mem_filter.mp hk
    have hi := Finset.mem_Icc.mp h.1
    exact ⟨hi.1,hi.2,h.2⟩
  have hinj := row_multiplier_injective S T (Real.exp ell) i K (fun r hr => (hrough r hr).1)
    hsep (fun k hk => ⟨(hK k hk).1,(by exact_mod_cast (hK k hk).2.1 : (k:ℝ)≤Z).trans hZell⟩)
  have hsub : F.image f⊆roughIntegerInterval 142 (R*(i+1:ℝ))
      ((min (2*R*(i+1:ℝ)) (T/(i+1:ℝ)))*(Z:ℝ)) := by
    intro m hm
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hm
    have hzM := Finset.mem_product.mp hz
    have hzS := (Finset.mem_filter.mp (Finset.mem_filter.mp hzM.1).1).1
    have hb := row_numerator_bounds S hR i (fun r hr => (hrough r hr).1) hsector hzM.1
    have hk := hK z.2 hzM.2
    have hkR : (z.2:ℝ)≤Z := by exact_mod_cast hk.2.1
    have hk1 : (1:ℝ)≤z.2 := by exact_mod_cast hk.1
    have hu : (f z:ℝ)≤(min (2*R*(i+1:ℝ)) (T/(i+1:ℝ)))*(Z:ℝ) := by
      exact_mod_cast (mul_le_mul hb.2 hkR (Nat.cast_nonneg _) (le_min (by positivity) (by positivity)))
    have hl : R*(i+1:ℝ)≤(f z:ℝ) := by
      have hh := mul_le_mul_of_nonneg_left hk1 (Nat.cast_nonneg z.1.num.natAbs : (0:ℝ)≤_)
      have hh' : (z.1.num.natAbs:ℝ)≤(f z:ℝ) := by simpa only [f,Nat.cast_mul,mul_one] using hh
      exact hb.1.trans hh'
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr ((Nat.le_floor_iff (by positivity)).mpr hu)),?_,hl⟩
    exact rough_mul_values (hrough _ hzS).2.1 hk.2.2
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_iff.mpr hinj,Finset.product_eq_sprod,Finset.card_product] at hc
  exact hc

end LonelyRunnerNew.RoughRational
