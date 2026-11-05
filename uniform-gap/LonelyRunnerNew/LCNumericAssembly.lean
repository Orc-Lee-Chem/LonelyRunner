import LonelyRunnerNew.LCNumericActualTail
import LonelyRunnerNew.LCFiniteSieve

noncomputable section
open scoped BigOperators
namespace LonelyRunnerNew.LCNumeric

theorem lastCoefficient_nonneg (steps : List CellStep) (c : Scale)
    (hv : ∀ d∈steps,d.Valid c) : 0 ≤ lastCoefficient steps := by
  induction steps with
  | nil => exact le_rfl
  | cons d rest ih =>
    cases rest with
    | nil =>
      have hd := hv d List.mem_cons_self
      exact hd.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    | cons e rest =>
      exact ih (fun x hx => hv x (List.mem_cons_of_mem _ hx))

theorem sum_le_cover {ι : Type*} [DecidableEq ι] (P : Finset ℕ) (I : Finset ι)
    (w : ℕ → ℝ) (lo hi : ι → ℕ) (bound : ι → ℝ)
    (hw : ∀ p∈P,0≤w p)
    (hcover : ∀ p∈P,∃ i∈I,lo i≤p ∧ p<hi i)
    (hbound : ∀ i∈I,(∑ p∈P.filter (fun p => lo i≤p ∧ p<hi i),w p) ≤ bound i) :
    (∑ p∈P,w p) ≤ ∑ i∈I,bound i := by
  have hp (p : ℕ) (hp : p∈P) : w p ≤ ∑ i∈I,if lo i≤p ∧ p<hi i then w p else 0 := by
    obtain ⟨i,hiI,hin⟩ := hcover p hp
    calc
      w p = if lo i≤p ∧ p<hi i then w p else 0 := by simp [hin]
      _ ≤ _ := Finset.single_le_sum (s:=I)
        (f:=fun j => if lo j≤p ∧ p<hi j then w p else 0)
        (fun _ _ => by split_ifs; exact hw p hp; exact le_rfl) hiI
  have hh := Finset.sum_le_sum hp
  rw [Finset.sum_comm] at hh
  simp_rw [← Finset.sum_filter] at hh
  exact hh.trans (Finset.sum_le_sum hbound)

theorem adjacent_cover (cuts : List ℕ) (p : ℕ) (hlo : cuts.headD 0 < p)
    (hhi : p ≤ cuts.getLastD 0) :
    ∃ i : ℕ,i+1<cuts.length ∧ cuts[i]!<p ∧ p≤cuts[i+1]! := by
  induction cuts with
  | nil => simp at hlo hhi; omega
  | cons a rest ih =>
    cases rest with
    | nil => simp at hlo hhi; omega
    | cons b rest =>
      by_cases hb : p≤b
      · refine ⟨0,by simp,?_,?_⟩
        · change a<p; simpa using hlo
        · simpa using hb
      · have hblo : (b::rest).headD 0 < p := by simpa using (show b<p by omega)
        have hlast : p≤(b::rest).getLastD 0 := by simpa using hhi
        obtain ⟨i,hi,h1,h2⟩ := ih hblo hlast
        refine ⟨i+1,?_,?_,?_⟩
        · simp only [List.length_cons] at hi ⊢; omega
        · simpa using h1
        · simpa [Nat.add_assoc] using h2

end LonelyRunnerNew.LCNumeric

namespace LonelyRunnerNew.TaggedState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

theorem band_numeric_of_actual (s : TaggedState Label n) (hM : 0<s.edgeMass)
    (b : LCNumeric.Band) (hb : b.Valid LCNumeric.Data.boxes)
    (p : ℕ) (hp : Nat.Prime p) (hpB : b.lower≤p) (k : ℕ)
    (hseed : s.zMinus p k+s.zPlus p k ≤ (121/1000:ℝ))
    (hit : LCDirection.directionalInequality ((p:ℝ)^(-1/q)) (s.zMinus p k) (s.zPlus p k))
    (hE : s.primeException p k ≤ (s.zMinus p k)^(3/2:ℝ)+(s.zPlus p k)^(3/2:ℝ)) :
    s.primeException p k ≤ (LCNumeric.lastCoefficient b.steps:ℝ)*(p:ℝ)^(-(100:ℝ)/67) := by
  let z := s.zMinus p k+s.zPlus p k
  have hz0 := add_nonneg (s.zMinus_nonneg p k) (s.zPlus_nonneg p k)
  by_cases hz : z=0
  · rw [s.primeException_zero_of_zero_deficit hM p k hz hE]
    have hc : (0:ℝ) ≤ LCNumeric.lastCoefficient b.steps := by
      exact_mod_cast LCNumeric.lastCoefficient_nonneg b.steps b.scale hb.2.2.2.2.2.1
    exact mul_nonneg hc (Real.rpow_nonneg (by positivity) _)
  · have hzP : 0<z := lt_of_le_of_ne hz0 (Ne.symm hz)
    have hu := LCDirection.directionRatio_spec (s.zMinus_nonneg p k) (s.zPlus_nonneg p k) hzP
    have hn := LCDirection.normalize_iteration (s.zMinus_nonneg p k) (s.zPlus_nonneg p k) hzP hit
    have he : s.primeException p k ≤ z^(3/2:ℝ)*
        LCDirection.h0 (LCDirection.directionRatio (s.zMinus p k) (s.zPlus p k)) := by
      rw [LCDirection.h0,← LCDirection.normalized_power_sum (s.zMinus_nonneg p k) (s.zPlus_nonneg p k) hzP]
      exact hE
    have hh := b.sound LCNumeric.Data.boxes LCNumeric.actual_grid_valid hb hp hpB hu.1 hu.2.1 hzP hseed hn he
    simpa only [mul_comm] using hh

theorem ordinary_band_numeric (s : TaggedState Label n)
    (hs : ∀ t,Step s t → t.quality≤s.quality) (hM : 0<s.edgeMass)
    (b : LCNumeric.Band) (hb : b.Valid LCNumeric.Data.boxes)
    (p : ℕ) (hp : Nat.Prime p) (hpB : b.lower≤p) (k : ℕ) (hk : k∈s.valuationSupport p)
    (hseed : s.zMinus p k+s.zPlus p k ≤ (121/1000:ℝ)) :
    s.primeException p k ≤ (LCNumeric.lastCoefficient b.steps:ℝ)*(p:ℝ)^(-(100:ℝ)/67) :=
  s.band_numeric_of_actual hM b hb p hp hpB k hseed
    (s.actual_directional_iteration hs hM p hp k hk) (s.actual_same_direction hs hM p k)

theorem universal_band_numeric (s : TaggedState Label n)
    (hs : ∀ t,Step s t → t.universalQuality≤s.universalQuality) (hM : 0<s.edgeMass)
    (b : LCNumeric.Band) (hb : b.Valid LCNumeric.Data.boxes)
    (p : ℕ) (hp : Nat.Prime p) (hpB : b.lower≤p) (k : ℕ) (hk : k∈s.valuationSupport p)
    (hseed : s.zMinus p k+s.zPlus p k ≤ (121/1000:ℝ)) :
    s.primeException p k ≤ (LCNumeric.lastCoefficient b.steps:ℝ)*(p:ℝ)^(-(100:ℝ)/67) :=
  s.band_numeric_of_actual hM b hb p hp hpB k hseed
    (s.actual_universal_directional_iteration hs hM p hp k hk) (s.actual_universal_same_direction hs hM p k)

end LonelyRunnerNew.TaggedState
