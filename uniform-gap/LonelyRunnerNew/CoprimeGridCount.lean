import LonelyRunnerNew.BohrPrototypes
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.LinearCombination

noncomputable section
set_option autoImplicit false
open Set
open scoped BigOperators
namespace LonelyRunnerNew
attribute [local instance] Classical.propDecidable

def integerWindow (L U : ℝ) : Finset ℤ := Finset.Icc ⌈L⌉ ⌊U⌋
def gridResidue (a b : ℕ) (m : ℤ) : ℕ := ((Nat.gcdA a b*m)%(b:ℤ)).toNat
def eligibleGrid (a b : ℕ) (r z : ℝ) : Finset ℕ :=
  (Finset.range b).filter (fun j => (j+z)/(b:ℝ)∈forbidden a r)

theorem mem_integerWindow {L U : ℝ} {m : ℤ} :
    m∈integerWindow L U ↔ L≤(m:ℝ) ∧ (m:ℝ)≤U := by
  simp [integerWindow,Int.ceil_le,Int.le_floor]

theorem integerWindow_card_bounds {L U : ℝ} (hLU : L≤U) :
    U-L-1≤((integerWindow L U).card:ℝ) ∧ ((integerWindow L U).card:ℝ)≤U-L+1 := by
  have he : ⌈L⌉≤⌊U⌋+1 := Int.ceil_le.mpr (by
    push_cast
    linarith [Int.lt_floor_add_one U])
  have hc := Int.card_Icc_of_le ⌈L⌉ ⌊U⌋ he
  have hcR := congrArg (fun t : ℤ => (t:ℝ)) hc
  push_cast at hcR
  change ((integerWindow L U).card:ℝ)=(⌊U⌋:ℝ)+1-(⌈L⌉:ℝ) at hcR
  have hfl := Int.lt_floor_add_one U
  have hcl := Int.ceil_lt_add_one L
  constructor <;> linarith [Int.floor_le U,Int.le_ceil L]

theorem gridResidue_lt (a b : ℕ) (hb : 0<b) (m : ℤ) : gridResidue a b m<b := by
  have hbI : (0:ℤ)<b := by exact_mod_cast hb
  have hlo := Int.emod_nonneg (Nat.gcdA a b*m) hbI.ne'
  have hhi := Int.emod_lt_of_pos (Nat.gcdA a b*m) hbI
  unfold gridResidue
  exact_mod_cast (show ((Nat.gcdA a b*m)%(b:ℤ)).toNat < (b:ℤ) by
    rwa [Int.toNat_of_nonneg hlo])

theorem gridResidue_solution (a b : ℕ) (hab : a.Coprime b) (hb : 0<b) (m : ℤ) :
    ∃ k : ℤ,(a:ℤ)*(gridResidue a b m:ℤ)-(b:ℤ)*k=m := by
  have hz := Nat.gcd_eq_gcd_ab a b
  rw [hab.gcd_eq_one] at hz
  norm_num only [Int.natCast_one] at hz
  have hbI : (0:ℤ)<b := by exact_mod_cast hb
  let e := Nat.gcdA a b*m
  have hrem : (gridResidue a b m:ℤ)=e%(b:ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg _ hbI.ne')
  have he := Int.mul_ediv_add_emod e (b:ℤ)
  rw [←hrem] at he
  refine ⟨-Nat.gcdB a b*m-(a:ℤ)*(e/(b:ℤ)),?_⟩
  dsimp [e] at he ⊢
  linear_combination -m*hz+(a:ℤ)*he

theorem solution_gridResidue (a b : ℕ) (hab : a.Coprime b) {j : ℕ} (hj : j<b)
    (m k : ℤ) (h : (a:ℤ)*(j:ℤ)-(b:ℤ)*k=m) : gridResidue a b m=j := by
  have hz := Nat.gcd_eq_gcd_ab a b
  rw [hab.gcd_eq_one] at hz
  norm_num only [Int.natCast_one] at hz
  have he : Nat.gcdA a b*m=(b:ℤ)*(-Nat.gcdB a b*(j:ℤ)-Nat.gcdA a b*k)+(j:ℤ) := by
    linear_combination -(j:ℤ)*hz-Nat.gcdA a b*h
  have hji : (j:ℤ)<b := by exact_mod_cast hj
  simp [gridResidue,he,Int.add_emod,Int.mul_emod,
    Int.emod_eq_of_lt (Int.natCast_nonneg j) hji]

theorem grid_witness_iff (a b j : ℕ) (hb : 0<b) (r z : ℝ) (k : ℤ) :
    |(a:ℝ)*((j:ℝ)+z)/(b:ℝ)-(k:ℝ)|≤r ↔
      -((b:ℝ)*r)-(a:ℝ)*z≤((a:ℤ)*(j:ℤ)-(b:ℤ)*k:ℤ) ∧
      (((a:ℤ)*(j:ℤ)-(b:ℤ)*k:ℤ):ℝ)≤(b:ℝ)*r-(a:ℝ)*z := by
  have hbR : (0:ℝ)<b := by exact_mod_cast hb
  rw [abs_le]
  have h1 : -(r:ℝ)≤(a:ℝ)*((j:ℝ)+z)/(b:ℝ)-(k:ℝ) ↔
      -(b:ℝ)*r-(a:ℝ)*z≤((a:ℤ)*(j:ℤ)-(b:ℤ)*k:ℤ) := by
    rw [le_sub_iff_add_le,le_div_iff₀ hbR]
    push_cast
    constructor <;> intro h <;> nlinarith only [h]
  have h2 : (a:ℝ)*((j:ℝ)+z)/(b:ℝ)-(k:ℝ)≤r ↔
      (((a:ℤ)*(j:ℤ)-(b:ℤ)*k:ℤ):ℝ)≤(b:ℝ)*r-(a:ℝ)*z := by
    rw [sub_le_iff_le_add,div_le_iff₀ hbR]
    push_cast
    constructor <;> intro h <;> nlinarith only [h]
  simpa only [neg_mul] using and_congr h1 h2

theorem eligibleGrid_eq_image (a b : ℕ) (hab : a.Coprime b) (hb : 0<b) (r z : ℝ) :
    eligibleGrid a b r z=(integerWindow (-((b:ℝ)*r)-(a:ℝ)*z) ((b:ℝ)*r-(a:ℝ)*z)).image (gridResidue a b) := by
  ext j
  constructor
  · intro hj
    obtain ⟨hj,hjx⟩ := Finset.mem_filter.mp hj
    obtain ⟨k,hk⟩ := hjx
    have hm := (grid_witness_iff a b j hb r z k).mp (by simpa [mul_div_assoc] using hk)
    exact Finset.mem_image.mpr ⟨(a:ℤ)*(j:ℤ)-(b:ℤ)*k,mem_integerWindow.mpr hm,
      solution_gridResidue a b hab (Finset.mem_range.mp hj) _ k rfl⟩
  · intro hj
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨k,hk⟩ := gridResidue_solution a b hab hb m
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (gridResidue_lt a b hb m),k,?_⟩
    have hh := (grid_witness_iff a b (gridResidue a b m) hb r z k).mpr (by
      rw [hk]
      exact mem_integerWindow.mp hm)
    simpa [mul_div_assoc] using hh

theorem gridResidue_inj_window (a b : ℕ) (hab : a.Coprime b) (hb : 0<b)
    (r z : ℝ) (hr : r<1/2) :
    Set.InjOn (gridResidue a b) (integerWindow (-((b:ℝ)*r)-(a:ℝ)*z) ((b:ℝ)*r-(a:ℝ)*z)) := by
  intro m hm l hl heq
  obtain ⟨k,hk⟩ := gridResidue_solution a b hab hb m
  obtain ⟨k',hk'⟩ := gridResidue_solution a b hab hb l
  rw [heq] at hk
  have hd : (b:ℤ)∣m-l := ⟨k'-k,by linear_combination hk'-hk⟩
  have hmR := mem_integerWindow.mp hm
  have hlR := mem_integerWindow.mp hl
  have hbR : (0:ℝ)<b := by exact_mod_cast hb
  have hdist : |((m-l:ℤ):ℝ)|<(b:ℝ) := by
    push_cast
    rw [abs_lt]
    constructor <;> nlinarith only [hmR.1,hmR.2,hlR.1,hlR.2,mul_pos hbR (show 0<1-2*r by linarith)]
  have hdistI : |m-l|<(b:ℤ) := by exact_mod_cast hdist
  exact sub_eq_zero.mp (Int.eq_zero_of_abs_lt_dvd hd hdistI)

theorem eligibleGrid_card_bounds (a b : ℕ) (hab : a.Coprime b) (hb : 0<b)
    {r : ℝ} (hr : 0≤r) (hrhalf : r<1/2) (z : ℝ) :
    2*(b:ℝ)*r-1≤((eligibleGrid a b r z).card:ℝ) ∧
      ((eligibleGrid a b r z).card:ℝ)≤2*(b:ℝ)*r+1 := by
  rw [eligibleGrid_eq_image a b hab hb r z,Finset.card_image_of_injOn (gridResidue_inj_window a b hab hb r z hrhalf)]
  have hbR : (0:ℝ)≤b := Nat.cast_nonneg _
  have hh := integerWindow_card_bounds (show -((b:ℝ)*r)-(a:ℝ)*z≤(b:ℝ)*r-(a:ℝ)*z by
    nlinarith only [mul_nonneg hbR hr])
  constructor <;> linarith only [hh.1,hh.2]

end LonelyRunnerNew
