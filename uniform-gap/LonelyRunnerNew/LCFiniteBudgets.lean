import LonelyRunnerNew.LCFiniteSmallBudget
import LonelyRunnerNew.LCNumericMiddleIndex

noncomputable section
open scoped BigOperators
namespace LonelyRunnerNew.LCNumeric

theorem middle_prime_budget (P : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ p∈P,0≤w p) (hP : ∀ p∈P,Nat.Prime p ∧ 10000<p ∧ p≤1000000)
    (hpoint : ∀ p∈P,w p ≤ (tailCoefficient:ℝ)*(p:ℝ)^(-(100:ℝ)/67)) :
    (∑ p∈P,w p) < (23/1000:ℝ) := by
  have hc : (0:ℝ)≤tailCoefficient := by norm_num [tailCoefficient]
  have hbound (i : Fin 463) :
      (∑ p∈P.filter (fun p => Index.middleLo i≤p ∧ p<Index.middleHi i),w p) ≤
        (tailCoefficient:ℝ)*(Index.middleCount i:ℝ)*(Index.middlePower i:ℝ) := by
    let Pr := P.filter (fun p => Index.middleLo i≤p ∧ p<Index.middleHi i)
    have hlo : (0:ℝ)<Index.middleLo i := by exact_mod_cast Index.middle_lo_pos i
    have hup : (0:ℝ)<Index.middlePower i := by exact_mod_cast Index.middle_power_pos i
    have hroot := negative_power_upper hlo hup 100 67 (by decide) (by exact_mod_cast Index.middle_power_root i)
    norm_num only [Nat.cast_ofNat] at hroot
    have hPr : ∀ p∈Pr,Nat.Prime p ∧ Index.middleLo i≤p ∧ p<Index.middleLo i+(Index.middleRows i).length := by
      intro p hp
      have hm := Finset.mem_filter.mp hp
      have hlen := Index.middle_sieve_length i
      exact ⟨(hP p hm.1).1,hm.2.1,by omega⟩
    have hwgt : ∀ p∈Pr,(p:ℝ)^(-(100:ℝ)/67) ≤ (Index.middlePower i:ℝ) := by
      intro p hp
      have hm := (Finset.mem_filter.mp hp).2.1
      have hh := Real.rpow_le_rpow_of_nonpos (y:=(p:ℝ)) hlo (by exact_mod_cast hm)
        (by norm_num : (-(100:ℝ)/67)≤0)
      exact hh.trans (by simpa only [neg_div] using hroot)
    have hweight := sieve_weight_upper (Index.middleLo i) (Index.middleRows i) (Index.middle_sieve_valid i)
      Pr hPr hup.le (fun p => (p:ℝ)^(-(100:ℝ)/67)) hwgt
    rw [Index.middle_sieve_count] at hweight
    calc
      (∑ p∈Pr,w p) ≤ ∑ p∈Pr,(tailCoefficient:ℝ)*(p:ℝ)^(-(100:ℝ)/67) :=
        Finset.sum_le_sum (fun p hp => hpoint p (Finset.mem_filter.mp hp).1)
      _ = (tailCoefficient:ℝ)*(∑ p∈Pr,(p:ℝ)^(-(100:ℝ)/67)) := by rw [Finset.mul_sum]
      _ ≤ (tailCoefficient:ℝ)*((Index.middleCount i:ℝ)*(Index.middlePower i:ℝ)) :=
        mul_le_mul_of_nonneg_left hweight hc
      _ = _ := by ring
  have hcover : ∀ p∈P,∃ i∈(Finset.univ:Finset (Fin 463)),Index.middleLo i≤p ∧ p<Index.middleHi i := by
    intro p hp
    obtain ⟨i,hi⟩ := Index.middle_cover (hP p hp).2.1 (hP p hp).2.2
    exact ⟨i,Finset.mem_univ _,hi⟩
  have hh := sum_le_cover P Finset.univ w Index.middleLo Index.middleHi
    (fun i => (tailCoefficient:ℝ)*(Index.middleCount i:ℝ)*(Index.middlePower i:ℝ)) hw hcover (fun i _ => hbound i)
  have hq : (1000:ℚ)*(tailCoefficient*(∑ i : Fin 463,(Index.middleCount i:ℚ)*Index.middlePower i)) < 23 := by
    linarith [Index.middle_budget]
  have hr : (1000:ℝ)*((tailCoefficient:ℝ)*(∑ i : Fin 463,(Index.middleCount i:ℝ)*(Index.middlePower i:ℝ))) < 23 := by
    exact_mod_cast hq
  have heq : (∑ i : Fin 463,(tailCoefficient:ℝ)*(Index.middleCount i:ℝ)*(Index.middlePower i:ℝ)) =
      (tailCoefficient:ℝ)*(∑ i : Fin 463,(Index.middleCount i:ℝ)*(Index.middlePower i:ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq] at hh
  linarith

end LonelyRunnerNew.LCNumeric
