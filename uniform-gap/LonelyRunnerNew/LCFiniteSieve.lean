import LonelyRunnerNew.LCNumericIntervals
import Mathlib.Data.List.Count

noncomputable section
open scoped BigOperators
namespace LonelyRunnerNew.LCNumeric

/-- A zero marks an INCLUDED candidate. Every excluded integer must carry a
proper divisor. Thus correctness needs no external primality oracle. -/
def SieveValid (start : ℕ) : List ℕ → Prop
  | [] => True
  | d::rest => (d=0 ∨ (2 ≤ d ∧ d < start ∧ start % d=0)) ∧ SieveValid (start+1) rest

instance (start : ℕ) (ds : List ℕ) : Decidable (SieveValid start ds) := by
  induction ds generalizing start with
  | nil => exact isTrue trivial
  | cons d rest ih =>
    change Decidable ((d=0 ∨ (2 ≤ d ∧ d < start ∧ start % d=0)) ∧ SieveValid (start+1) rest)
    letI := ih (start+1)
    infer_instance

def checkSieve (start : ℕ) : List ℕ → Bool
  | [] => true
  | d::rest => decide (d=0 ∨ (2≤d ∧ d<start ∧ start%d=0)) && checkSieve (start+1) rest

theorem checkSieve_sound (start : ℕ) (ds : List ℕ) (h : checkSieve start ds=true) :
    SieveValid start ds := by
  induction ds generalizing start with
  | nil => trivial
  | cons d rest ih =>
    simp only [checkSieve,Bool.and_eq_true,decide_eq_true_eq] at h
    exact ⟨h.1,ih (start+1) h.2⟩

theorem prime_marker_zero {start d : ℕ} (hp : Nat.Prime start)
    (h : d=0 ∨ (2 ≤ d ∧ d < start ∧ start % d=0)) : d=0 := by
  rcases h with h | ⟨hd,hdlt,hmod⟩
  · exact h
  · have hh := hp.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero hmod)
    omega

/-- Every prime in the entire interval is counted, including both endpoints
according to the exact [start,start+length) convention. -/
theorem sieve_count_upper (start : ℕ) (ds : List ℕ) (hv : SieveValid start ds)
    (P : Finset ℕ) (hP : ∀ p ∈ P,Nat.Prime p ∧ start ≤ p ∧ p < start+ds.length) :
    P.card ≤ ds.count 0 := by
  induction ds generalizing start P with
  | nil =>
    have hE : P=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      have h := hP p hp
      simp only [List.length_nil,add_zero] at h
      omega
    simp [hE]
  | cons d rest ih =>
    have hrest : ∀ p ∈ P.erase start,Nat.Prime p ∧ start+1 ≤ p ∧ p < start+1+rest.length := by
      intro p hp
      have hpm := Finset.mem_erase.mp hp
      have h := hP p hpm.2
      simp only [List.length_cons] at h
      exact ⟨h.1,by omega,by omega⟩
    have hh := ih (start+1) hv.2 (P.erase start) hrest
    by_cases hs : start ∈ P
    · have hd : d=0 := prime_marker_zero (hP start hs).1 hv.1
      have hcard := Finset.card_erase_add_one hs
      simp only [hd,List.count_cons_self]
      omega
    · have he : P.erase start=P := Finset.erase_eq_of_notMem hs
      rw [he] at hh
      by_cases hd : d=0
      · simp only [hd,List.count_cons_self]
        omega
      · simpa only [List.count_cons_of_ne hd] using hh

theorem sieve_weight_upper (start : ℕ) (ds : List ℕ) (hv : SieveValid start ds)
    (P : Finset ℕ) (hP : ∀ p ∈ P,Nat.Prime p ∧ start ≤ p ∧ p < start+ds.length)
    {W : ℝ} (hW : 0 ≤ W) (weight : ℕ → ℝ) (hw : ∀ p ∈ P,weight p ≤ W) :
    (∑ p ∈ P,weight p) ≤ (ds.count 0:ℝ)*W := by
  calc
    _ ≤ ∑ _p ∈ P,W := Finset.sum_le_sum hw
    _ = (P.card:ℝ)*W := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast sieve_count_upper start ds hv P hP) hW

/-- An included candidate carries an exact upper root for n^(-100/67).
Excluded candidates carry divisors; their upper entry is unused. -/
structure WeightedMarker where
  divisor : ℕ
  num : ℕ
  den : ℕ
  deriving Inhabited,DecidableEq

def WeightedMarker.upper (m : WeightedMarker) : ℚ := (m.num:ℚ)/m.den

def WeightedMarker.Valid (m : WeightedMarker) (n : ℕ) : Prop :=
  if m.divisor=0 then 0 < n ∧ 0 < m.num ∧ 0 < m.den ∧ m.den^67 ≤ m.num^67*n^100
  else 2 ≤ m.divisor ∧ m.divisor < n ∧ n%m.divisor=0
instance instDecidableWeightedMarkerValid (m : WeightedMarker) (n : ℕ) : Decidable (m.Valid n) := by
  unfold WeightedMarker.Valid; infer_instance

def WeightedSieveValid (start : ℕ) : List WeightedMarker → Prop
  | [] => True
  | m::rest => m.Valid start ∧ WeightedSieveValid (start+1) rest
instance instDecidableWeightedSieveValid (start : ℕ) (ms : List WeightedMarker) : Decidable (WeightedSieveValid start ms) := by
  induction ms generalizing start with
  | nil => exact isTrue trivial
  | cons m rest ih =>
    change Decidable (m.Valid start ∧ WeightedSieveValid (start+1) rest)
    letI := ih (start+1)
    infer_instance

def weightedSieveSum : List WeightedMarker → ℚ
  | [] => 0
  | m::rest => (if m.divisor=0 then m.upper else 0)+weightedSieveSum rest

theorem weightedSieveSum_nonneg (start : ℕ) (ms : List WeightedMarker)
    (hv : WeightedSieveValid start ms) : 0 ≤ weightedSieveSum ms := by
  induction ms generalizing start with
  | nil => exact le_rfl
  | cons m rest ih =>
    have hh := ih (start+1) hv.2
    unfold weightedSieveSum
    by_cases hd : m.divisor=0
    · have hm := hv.1
      simp only [WeightedMarker.Valid,hd,ite_true] at hm
      simp only [hd,ite_true]
      have hup : (0:ℚ) < m.upper := div_pos (by exact_mod_cast hm.2.1) (by exact_mod_cast hm.2.2.1)
      linarith
    · simp only [hd,ite_false,zero_add]
      exact hh

/-- This is a complete weighted sieve bound, with no external assertion
that a supplied prime list is complete or that its entries are prime. -/
theorem weighted_sieve_upper (start : ℕ) (ms : List WeightedMarker)
    (hv : WeightedSieveValid start ms) (P : Finset ℕ)
    (hP : ∀ p ∈ P,Nat.Prime p ∧ start ≤ p ∧ p < start+ms.length) :
    (∑ p ∈ P,(p:ℝ)^(-(100:ℝ)/67)) ≤ (weightedSieveSum ms:ℝ) := by
  induction ms generalizing start P with
  | nil =>
    have he : P=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      have hh := hP p hp
      simp only [List.length_nil,add_zero] at hh
      omega
    simp [he,weightedSieveSum]
  | cons m rest ih =>
    have hrest : ∀ p ∈ P.erase start,Nat.Prime p ∧ start+1 ≤ p ∧ p < start+1+rest.length := by
      intro p hp
      have hm := Finset.mem_erase.mp hp
      have hh := hP p hm.2
      simp only [List.length_cons] at hh
      exact ⟨hh.1,by omega,by omega⟩
    have hh := ih (start+1) hv.2 (P.erase start) hrest
    have hnon : (0:ℝ) ≤ weightedSieveSum rest := by
      exact_mod_cast weightedSieveSum_nonneg (start+1) rest hv.2
    by_cases hs : start ∈ P
    · have hd : m.divisor=0 := by
        apply prime_marker_zero (hP start hs).1
        by_cases hd : m.divisor=0
        · exact Or.inl hd
        · exact Or.inr (by simpa only [WeightedMarker.Valid,hd,ite_false] using hv.1)
      have hm := hv.1
      simp only [WeightedMarker.Valid,hd,ite_true] at hm
      have hroot := negative_power_upper (show (0:ℝ) < start by exact_mod_cast hm.1)
        (show (0:ℝ) < m.upper by
          exact_mod_cast (show (0:ℚ) < m.upper from div_pos (by exact_mod_cast hm.2.1) (by exact_mod_cast hm.2.2.1)))
        100 67 (by decide)
        (by exact_mod_cast integer_negative_root m.num m.den start 100 67 hm.2.2.1 hm.2.2.2)
      norm_num only [Nat.cast_ofNat] at hroot
      have hsum := Finset.sum_erase_add P (fun p => (p:ℝ)^(-(100:ℝ)/67)) hs
      rw [← hsum]
      simp only [weightedSieveSum,hd,ite_true,Rat.cast_add]
      have hroot' : (start:ℝ)^(-(100:ℝ)/67) ≤ m.upper := by simpa only [neg_div] using hroot
      linarith
    · rw [Finset.erase_eq_of_notMem hs] at hh
      apply hh.trans
      have hmore : weightedSieveSum rest ≤ weightedSieveSum (m::rest) := by
        change weightedSieveSum rest ≤ (if m.divisor=0 then m.upper else 0)+weightedSieveSum rest
        by_cases hd : m.divisor=0
        · have hm := hv.1
          simp only [WeightedMarker.Valid,hd,ite_true] at hm
          simp only [hd,ite_true]
          have hup : (0:ℚ) < m.upper := div_pos (by exact_mod_cast hm.2.1) (by exact_mod_cast hm.2.2.1)
          linarith
        · simp only [hd,ite_false,zero_add,le_refl]
      exact_mod_cast hmore

end LonelyRunnerNew.LCNumeric
