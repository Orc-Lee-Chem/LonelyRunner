import LonelyRunnerNew.SelbergQuadratic
import Mathlib.Algebra.Order.Floor.Semifield

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew.FiniteSelberg
attribute [local instance] Classical.propDecidable

def interval (U A : ℝ) : Finset ℕ :=
  (Finset.range (⌊A⌋₊+1)).filter (fun n => U≤(n:ℝ))
def multiples (m : ℕ) (U A : ℝ) : Finset ℕ := (interval U A).filter (fun n => m∣n)

theorem mem_interval {U A : ℝ} (hA : 0≤A) (n : ℕ) :
    n∈interval U A ↔ U≤(n:ℝ) ∧ (n:ℝ)≤A := by
  simp only [interval,Finset.mem_filter,Finset.mem_range,Nat.lt_succ_iff]
  rw [Nat.le_floor_iff hA]
  exact and_comm

theorem multiples_image {U A : ℝ} (hU : 0<U) (hUA : U≤A) {m : ℕ} (hm : 0<m) :
    multiples m U A=(Finset.Icc ⌈U/(m:ℝ)⌉₊ ⌊A/(m:ℝ)⌋₊).image (fun k => m*k) := by
  have hmR : (0:ℝ)<m := by exact_mod_cast hm
  have hA : 0≤A := hU.le.trans hUA
  ext n
  constructor
  · intro hn
    have hh := Finset.mem_filter.mp hn
    have hi := (mem_interval hA n).mp hh.1
    obtain ⟨k,hk⟩ := hh.2
    refine Finset.mem_image.mpr ⟨k,Finset.mem_Icc.mpr ⟨?_,?_⟩,hk.symm⟩
    · apply Nat.ceil_le.mpr
      apply (div_le_iff₀ hmR).mpr
      have he : (n:ℝ)=(m:ℝ)*(k:ℝ) := by exact_mod_cast hk
      nlinarith [hi.1]
    · apply (Nat.le_floor_iff (div_nonneg hA hmR.le)).mpr
      apply (le_div_iff₀ hmR).mpr
      have he : (n:ℝ)=(m:ℝ)*(k:ℝ) := by exact_mod_cast hk
      nlinarith [hi.2]
  · intro hn
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hn
    have hh := Finset.mem_Icc.mp hk
    have hlo := Nat.le_ceil (U/(m:ℝ))
    have hhi := (Nat.le_floor_iff (div_nonneg hA hmR.le)).mp hh.2
    have hkl : U/(m:ℝ)≤(k:ℝ) := hlo.trans (by exact_mod_cast hh.1)
    exact Finset.mem_filter.mpr ⟨(mem_interval hA _).mpr ⟨by exact_mod_cast (by
      have hi := (div_le_iff₀ hmR).mp hkl
      simpa only [Nat.cast_mul,mul_comm] using hi : U≤((m*k:ℕ):ℝ)),by
      rw [Nat.cast_mul]
      nlinarith [(le_div_iff₀ hmR).mp hhi]⟩,dvd_mul_right _ _⟩

theorem multiples_card {U A : ℝ} (hU : 0<U) (hUA : U≤A) {m : ℕ} (hm : 0<m) :
    (multiples m U A).card=⌊A/(m:ℝ)⌋₊+1-⌈U/(m:ℝ)⌉₊ := by
  rw [multiples_image hU hUA hm,Finset.card_image_iff.mpr,Nat.card_Icc]
  intro k hk l hl he
  exact Nat.eq_of_mul_eq_mul_left hm he

/-- Closed endpoints, including an interval with no positive multiple.
All floor/ceil operations and the empty case are checked exactly. -/
theorem multiples_error {U A : ℝ} (hU : 0<U) (hUA : U≤A) {m : ℕ} (hm : 0<m) :
    |((multiples m U A).card:ℝ)-(A-U)/(m:ℝ)|≤1 := by
  have hmR : (0:ℝ)<m := by exact_mod_cast hm
  have hA : 0<A := hU.trans_le hUA
  let a := ⌊A/(m:ℝ)⌋₊
  let b := ⌈U/(m:ℝ)⌉₊
  have haf : (a:ℝ)≤A/(m:ℝ) := Nat.floor_le (by positivity)
  have haf' : A/(m:ℝ)<(a:ℝ)+1 := Nat.lt_floor_add_one _
  have hbc : U/(m:ℝ)≤(b:ℝ) := Nat.le_ceil _
  have hbc' : (b:ℝ)<U/(m:ℝ)+1 := Nat.ceil_lt_add_one (by positivity)
  rw [multiples_card hU hUA hm]
  change |(((a+1-b:ℕ):ℝ))-(A-U)/(m:ℝ)|≤1
  by_cases hle : b≤a+1
  · rw [Nat.cast_sub hle,Nat.cast_add,Nat.cast_one]
    apply abs_le.mpr
    rw [sub_div]
    constructor <;> linarith
  · have hab : a+1≤b := by omega
    have hz : a+1-b=0 := by omega
    rw [hz,Nat.cast_zero,zero_sub,abs_neg,abs_of_nonneg (div_nonneg (by linarith) hmR.le)]
    have hh : (a:ℝ)+1≤b := by exact_mod_cast hab
    rw [sub_div]
    linarith

theorem rough_divisor_one {X n d : ℕ} (hn : rough X n)
    (hd : d∈Finset.Icc 1 X) (hdn : d∣n) : d=1 :=
  RoughRational.rough_small_eq_one
    (rough_of_positive_dvd hn (Finset.mem_Icc.mp hd).1 hdn) (Finset.mem_Icc.mp hd).2

theorem rough_weight_sum {X n : ℕ} (hX : 0<X) (hn : rough X n) :
    (∑d∈Finset.Icc 1 X,if d∣n then weight X d else 0)=1 := by
  have h1 : 1∈Finset.Icc 1 X := by simp;omega
  rw [Finset.sum_eq_single_of_mem 1 h1]
  · simp only [one_dvd,ite_true,weight_one hX]
  · intro d hd hn1
    have hnd : ¬d∣n := fun h => hn1 (rough_divisor_one hn hd h)
    simp [hnd]

theorem rough_card_le_square {X : ℕ} (hX : 0<X) {U A : ℝ} (hU : 0<U) (hUA : U≤A) :
    ((RoughRational.roughIntegerInterval X U A).card:ℝ)≤
      ∑n∈interval U A,(∑d∈Finset.Icc 1 X,if d∣n then weight X d else 0)^2 := by
  let F := RoughRational.roughIntegerInterval X U A
  have hsub : F⊆interval U A := by
    intro n hn
    have hh := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨hh.1,hh.2.2⟩
  have he : (F.card:ℝ)=∑n∈F,(∑d∈Finset.Icc 1 X,if d∣n then weight X d else 0)^2 := by
    have hh : ∀n∈F,(∑d∈Finset.Icc 1 X,if d∣n then weight X d else 0)^2=(1:ℝ) := by
      intro n hn
      rw [rough_weight_sum hX (Finset.mem_filter.mp hn).2.1]
      norm_num
    simp_rw [Finset.sum_congr rfl hh]
    simp
  rw [he]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n hn _ => sq_nonneg _)

theorem square_sum_expansion (X : ℕ) (w : ℕ → ℝ) (U A : ℝ) :
    (∑n∈interval U A,(∑d∈Finset.Icc 1 X,if d∣n then w d else 0)^2)=
      ∑d∈Finset.Icc 1 X,∑e∈Finset.Icc 1 X,
        w d*w e*((multiples (Nat.lcm d e) U A).card:ℝ) := by
  let I := Finset.Icc 1 X
  let S := interval U A
  have he (n : ℕ) : (∑d∈I,if d∣n then w d else 0)^2=
      ∑d∈I,∑e∈I,if Nat.lcm d e∣n then w d*w e else 0 := by
    rw [pow_two,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    simp only [Nat.lcm_dvd_iff]
    by_cases hd : d∣n <;> by_cases he : e∣n <;> simp [hd,he]
  change (∑n∈S,(∑d∈I,if d∣n then w d else 0)^2)=_
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  rw [←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
  dsimp only [multiples,S]
  ring

theorem square_sum_upper (X : ℕ) (w : ℕ → ℝ) {U A : ℝ} (hU : 0<U) (hUA : U≤A) :
    (∑n∈interval U A,(∑d∈Finset.Icc 1 X,if d∣n then w d else 0)^2)≤
      (A-U)*quadratic X w+(∑d∈Finset.Icc 1 X,|w d|)^2 := by
  rw [square_sum_expansion]
  have he (d : ℕ) (hd : d∈Finset.Icc 1 X) (e : ℕ) (he : e∈Finset.Icc 1 X) :
      w d*w e*((multiples (Nat.lcm d e) U A).card:ℝ)≤
      (A-U)*(w d*w e/(Nat.lcm d e:ℝ))+|w d| * |w e| := by
    have hm := Nat.lcm_pos (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp he).1
    have hh := multiples_error hU hUA hm
    have hmul := mul_le_mul_of_nonneg_left hh (abs_nonneg (w d*w e))
    have hb : w d*w e*(((multiples (Nat.lcm d e) U A).card:ℝ)-(A-U)/(Nat.lcm d e:ℝ))≤|w d*w e| := by
      calc
        _ ≤ |w d*w e*(((multiples (Nat.lcm d e) U A).card:ℝ)-(A-U)/(Nat.lcm d e:ℝ))| := le_abs_self _
        _ = |w d*w e| * |((multiples (Nat.lcm d e) U A).card:ℝ)-(A-U)/(Nat.lcm d e:ℝ)| := abs_mul _ _
        _ ≤ _ := by simpa only [mul_one] using hmul
    simp only [abs_mul,div_eq_mul_inv] at hb ⊢
    nlinarith only [hb]
  have hs := Finset.sum_le_sum (fun d hd => Finset.sum_le_sum (fun e he' => he d hd e he'))
  apply hs.trans_eq
  unfold quadratic
  rw [pow_two,Finset.sum_mul]
  simp_rw [Finset.mul_sum,←Finset.sum_add_distrib]

end LonelyRunnerNew.FiniteSelberg
