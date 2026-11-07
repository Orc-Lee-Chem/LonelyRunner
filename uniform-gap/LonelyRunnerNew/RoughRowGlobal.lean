import LonelyRunnerNew.RoughRowBoundary
import LonelyRunnerNew.NumericEndgame
import Mathlib.Algebra.BigOperators.Intervals

noncomputable section
open scoped BigOperators
namespace LonelyRunnerNew.RoughRow

def harmonicSum (m : ℕ) : ℝ := ∑ i ∈ Finset.range m, 1/(i+1:ℝ)
def capSum (m : ℕ) (R T : ℝ) : ℝ :=
  ∑ i ∈ Finset.range m, min (2*R*(i+1:ℝ)) (T/(i+1:ℝ))

theorem sum_succ (m : ℕ) : (∑ i ∈ Finset.range m, (i+1:ℝ)) = (m:ℝ)*(m+1)/2 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem harmonic_tail_le_log (k m : ℕ) (hk : 0 < k) (hkm : k ≤ m) :
    harmonicSum m - harmonicSum k ≤ Real.log ((m:ℝ)/k) := by
  have hkR : (0:ℝ)<k := by exact_mod_cast hk
  induction m, hkm using Nat.le_induction with
  | base => simp [hkR.ne']
  | succ m hkm ih =>
    have hmR : (0:ℝ)<m := lt_of_lt_of_le hkR (by exact_mod_cast hkm)
    have hm1 : (0:ℝ)<m+1 := by positivity
    have hs := Real.one_sub_inv_le_log_of_pos (div_pos hm1 hmR)
    rw [Real.log_div hm1.ne' hmR.ne'] at hs
    have he : 1-(((m:ℝ)+1)/m)⁻¹ = 1/((m:ℝ)+1) := by field_simp; ring
    rw [he] at hs
    rw [Real.log_div hmR.ne' hkR.ne'] at ih
    rw [harmonicSum, Finset.sum_range_succ]
    change harmonicSum m + 1/((m:ℝ)+1) - harmonicSum k ≤ _
    rw [Nat.cast_add, Nat.cast_one, Real.log_div hm1.ne' hkR.ne']
    linarith

theorem capSum_split (m k : ℕ) (hkm : k ≤ m) (R T : ℝ) :
    capSum m R T ≤ R*(k:ℝ)*(k+1)+T*(harmonicSum m-harmonicSum k) := by
  have hsplit := Finset.sum_range_add_sum_Ico
    (fun i : ℕ => min (2*R*(i+1:ℝ)) (T/(i+1:ℝ))) hkm
  unfold capSum
  rw [← hsplit]
  have hl : (∑ i ∈ Finset.range k, min (2*R*(i+1:ℝ)) (T/(i+1:ℝ))) ≤
      2*R*(∑ i ∈ Finset.range k, (i+1:ℝ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => min_le_left _ _)
  have hr : (∑ i ∈ Finset.Ico k m, min (2*R*(i+1:ℝ)) (T/(i+1:ℝ))) ≤
      T*(∑ i ∈ Finset.Ico k m, 1/(i+1:ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    simpa only [mul_one_div] using min_le_right (2*R*(i+1:ℝ)) (T/(i+1:ℝ))
  rw [sum_succ] at hl
  rw [Finset.sum_Ico_eq_sub (fun i : ℕ => 1/(i+1:ℝ)) hkm] at hr
  change _ ≤ T*(harmonicSum m-harmonicSum k) at hr
  linarith

theorem rowSum_eq_capSum (m : ℕ) (R T : ℝ) :
    rowSum m R T = (569/1000:ℝ)*capSum m R T -
      (499/2000:ℝ)*R*(m:ℝ)*(m+1) := by
  unfold rowSum capSum
  simp only [Nat.cast_add, Nat.cast_one]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [← Finset.mul_sum, sum_succ]
  ring

theorem log_five_thirds_lt : Real.log (5/3:ℝ) < 13/25 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num)).2
  have h := Endgame.expPoly_le_exp (by norm_num : (0:ℝ)≤13/25) 3
  norm_num [Endgame.expPoly, Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith

set_option maxHeartbeats 1600000 in
theorem rowSum_le_fourteen (m : ℕ) (hm : m ≤ 14) (R T : ℝ) (hT : 0 ≤ T) :
    rowSum m R T ≤ (639/2000:ℝ)*T := by
  have hl1 := min_le_left (2*R*(1:ℝ)) (T/(1:ℝ))
  have hr1 := min_le_right (2*R*(1:ℝ)) (T/(1:ℝ))
  have hl2 := min_le_left (2*R*(2:ℝ)) (T/(2:ℝ))
  have hr2 := min_le_right (2*R*(2:ℝ)) (T/(2:ℝ))
  have hl3 := min_le_left (2*R*(3:ℝ)) (T/(3:ℝ))
  have hr3 := min_le_right (2*R*(3:ℝ)) (T/(3:ℝ))
  have hl4 := min_le_left (2*R*(4:ℝ)) (T/(4:ℝ))
  have hr4 := min_le_right (2*R*(4:ℝ)) (T/(4:ℝ))
  have hl5 := min_le_left (2*R*(5:ℝ)) (T/(5:ℝ))
  have hr5 := min_le_right (2*R*(5:ℝ)) (T/(5:ℝ))
  have hl6 := min_le_left (2*R*(6:ℝ)) (T/(6:ℝ))
  have hr6 := min_le_right (2*R*(6:ℝ)) (T/(6:ℝ))
  have hl7 := min_le_left (2*R*(7:ℝ)) (T/(7:ℝ))
  have hr7 := min_le_right (2*R*(7:ℝ)) (T/(7:ℝ))
  have hl8 := min_le_left (2*R*(8:ℝ)) (T/(8:ℝ))
  have hr8 := min_le_right (2*R*(8:ℝ)) (T/(8:ℝ))
  have hl9 := min_le_left (2*R*(9:ℝ)) (T/(9:ℝ))
  have hr9 := min_le_right (2*R*(9:ℝ)) (T/(9:ℝ))
  have hl10 := min_le_left (2*R*(10:ℝ)) (T/(10:ℝ))
  have hr10 := min_le_right (2*R*(10:ℝ)) (T/(10:ℝ))
  have hl11 := min_le_left (2*R*(11:ℝ)) (T/(11:ℝ))
  have hr11 := min_le_right (2*R*(11:ℝ)) (T/(11:ℝ))
  have hl12 := min_le_left (2*R*(12:ℝ)) (T/(12:ℝ))
  have hr12 := min_le_right (2*R*(12:ℝ)) (T/(12:ℝ))
  have hl13 := min_le_left (2*R*(13:ℝ)) (T/(13:ℝ))
  have hr13 := min_le_right (2*R*(13:ℝ)) (T/(13:ℝ))
  have hl14 := min_le_left (2*R*(14:ℝ)) (T/(14:ℝ))
  have hr14 := min_le_right (2*R*(14:ℝ)) (T/(14:ℝ))
  simp only [mul_one, div_one] at hl1 hr1
  interval_cases m <;>
    norm_num only [rowSum, Finset.sum_range_succ, Finset.sum_empty,
      Nat.cast_zero, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, zero_add, add_zero,
      mul_one, div_one] <;>
    linarith only [hT, hl1, hr1, hl2, hr2, hl3, hr3, hl4, hr4, hl5, hr5, hl6, hr6, hl7, hr7, hl8, hr8, hl9, hr9, hl10, hr10, hl11, hr11, hl12, hr12, hl13, hr13, hl14, hr14]

theorem rowSum_large (m : ℕ) (hm : 15 ≤ m) (R T : ℝ) (hR : 0 < R) (hT : 0 < T)
    (hphysical : (m:ℝ)^2*R ≤ T) :
    rowSum m R T ≤ (639/2000:ℝ)*T := by
  let k := 2*m/3
  have hk : 0 < k ∧ k ≤ m ∧ 3*k ≤ 2*m ∧ 3*m ≤ 5*k := by dsimp [k]; omega
  have hm0 : (0:ℝ)≤m := Nat.cast_nonneg _
  have hm15 : (15:ℝ)≤m := by exact_mod_cast hm
  have hk0 : (0:ℝ)≤k := Nat.cast_nonneg _
  have hkpos : (0:ℝ)<k := by exact_mod_cast hk.1
  have hkupper : (k:ℝ)≤2*(m:ℝ)/3 := by
    have hh : (3:ℝ)*k≤2*m := by exact_mod_cast hk.2.2.1
    linarith
  have hklower : 3*(m:ℝ)≤5*k := by exact_mod_cast hk.2.2.2
  have hsq := (sq_le_sq₀ hk0 (by positivity : (0:ℝ)≤2*(m:ℝ)/3)).2 hkupper
  have hcoef : (569/1000:ℝ)*k*(k+1)-(499/2000:ℝ)*m*(m+1) ≤ (13/1000:ℝ)*(m:ℝ)^2 := by
    nlinarith [mul_nonneg hm0 (sub_nonneg.mpr hm15)]
  have htail := harmonic_tail_le_log k m hk.1 hk.2.1
  have hlog : Real.log ((m:ℝ)/k) < 13/25 := by
    apply lt_of_le_of_lt _ log_five_thirds_lt
    apply Real.log_le_log (div_pos (by linarith) hkpos)
    apply (div_le_iff₀ hkpos).2
    linarith
  have hcap := capSum_split m k hk.2.1 R T
  have hrow : rowSum m R T ≤
      (569/1000:ℝ)*T*(13/25)+
      R*((569/1000:ℝ)*k*(k+1)-(499/2000:ℝ)*m*(m+1)) := by
    rw [rowSum_eq_capSum]
    nlinarith [mul_le_mul_of_nonneg_left (htail.trans hlog.le) (mul_nonneg (by norm_num : (0:ℝ)≤569/1000) hT.le)]
  have hcR := mul_le_mul_of_nonneg_left hcoef hR.le
  nlinarith

theorem rowSum_physical (m : ℕ) (R T : ℝ) (hR : 0 < R) (hT : 0 < T)
    (hphysical : (m:ℝ)^2*R ≤ T) :
    rowSum m R T ≤ (639/2000:ℝ)*T := by
  by_cases hm : m ≤ 14
  · exact rowSum_le_fourteen m hm R T hT.le
  · exact rowSum_large m (by omega) R T hR hT hphysical

theorem log_two_lt : Real.log (2:ℝ) < 7/10 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num)).2
  have h := Endgame.expPoly_le_exp (by norm_num : (0:ℝ)≤7/10) 3
  norm_num [Endgame.expPoly, Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith

theorem capSum_physical (m : ℕ) (R T : ℝ) (hR : 0 < R) (hT : 0 < T)
    (hphysical : (m:ℝ)^2*R ≤ T) : capSum m R T ≤ (3/2:ℝ)*T := by
  by_cases hm : m ≤ 2
  · have h1 := min_le_right (2*R) T
    have h2 := min_le_right (2*R*2) (T/2)
    interval_cases m <;>
      norm_num only [capSum, Finset.sum_range_succ, Finset.sum_empty,
        Nat.cast_zero, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
        zero_add, add_zero, mul_one, div_one] <;> linarith only [h1,h2,hT]
  · have hm3 : 3 ≤ m := by omega
    let k := (m+1)/2
    have hk : 0 < k ∧ k ≤ m ∧ m ≤ 2*k ∧ 2*k ≤ m+1 := by dsimp [k]; omega
    have hm0 : (0:ℝ)≤m := Nat.cast_nonneg _
    have hmR : (3:ℝ)≤m := by exact_mod_cast hm3
    have hk0 : (0:ℝ)≤k := Nat.cast_nonneg _
    have hkpos : (0:ℝ)<k := by exact_mod_cast hk.1
    have hkupper : (k:ℝ)≤((m:ℝ)+1)/2 := by
      have hh : (2:ℝ)*k ≤ (m:ℝ)+1 := by exact_mod_cast hk.2.2.2
      linarith
    have hsq := (sq_le_sq₀ hk0 (by positivity : (0:ℝ)≤((m:ℝ)+1)/2)).2 hkupper
    have hcoef : (k:ℝ)*(k+1) ≤ (3/4:ℝ)*(m:ℝ)^2 := by
      nlinarith [mul_nonneg hm0 (sub_nonneg.mpr hmR)]
    have htail := harmonic_tail_le_log k m hk.1 hk.2.1
    have hlog : Real.log ((m:ℝ)/k) < 7/10 := by
      apply lt_of_le_of_lt _ log_two_lt
      apply Real.log_le_log (div_pos (by linarith) hkpos)
      apply (div_le_iff₀ hkpos).2
      exact_mod_cast hk.2.2.1
    have hcap := capSum_split m k hk.2.1 R T
    have hcR := mul_le_mul_of_nonneg_left hcoef hR.le
    nlinarith [mul_le_mul_of_nonneg_left (htail.trans hlog.le) hT.le]

theorem floor_physical {R T : ℝ} (hR : 0 < R) (hT : 0 < T) :
    ((⌊Real.sqrt (T/R)⌋₊ : ℕ):ℝ)^2*R ≤ T := by
  have hratio : 0 ≤ T/R := (div_pos hT hR).le
  have hf : ((⌊Real.sqrt (T/R)⌋₊:ℕ):ℝ) ≤ Real.sqrt (T/R) :=
    Nat.floor_le (Real.sqrt_nonneg _)
  have hs := (sq_le_sq₀ (Nat.cast_nonneg _) (Real.sqrt_nonneg (T/R))).2 hf
  rw [Real.sq_sqrt hratio] at hs
  exact (le_div_iff₀ hR).mp hs

theorem rowSum_floor {R T : ℝ} (hR : 0 < R) (hT : 0 < T) :
    rowSum ⌊Real.sqrt (T/R)⌋₊ R T ≤ (639/2000:ℝ)*T :=
  rowSum_physical _ R T hR hT (floor_physical hR hT)

theorem capSum_floor {R T : ℝ} (hR : 0 < R) (hT : 0 < T) :
    capSum ⌊Real.sqrt (T/R)⌋₊ R T ≤ (3/2:ℝ)*T :=
  capSum_physical _ R T hR hT (floor_physical hR hT)

/-- Summation of the actual proposed row inequality. The row bound remains
explicit: this theorem does not prove a sieve or packing input. -/
theorem aggregate_rows (m : ℕ) (R T L Z Y : ℝ) (hR : 0 < R) (hT : 0 < T)
    (hphysical : (m:ℝ)^2*R ≤ T) (hL : 0 < L) (hZ : 0 < Z) (hY : 0 < Y+1)
    (counts : ℕ → ℝ)
    (hrows : ∀ i < m, counts i ≤ 1+
      ((569/1000:ℝ)*min (2*R*(i+1:ℝ)) (T/(i+1:ℝ))-(499/1000:ℝ)*R*(i+1:ℝ)+
        (569/1000:ℝ)*min (2*R*(i+1:ℝ)) (T/(i+1:ℝ))/(Y+1))/L+
      min (2*R*(i+1:ℝ)) (T/(i+1:ℝ))/Z) :
    (∑ i ∈ Finset.range m, counts i) ≤ (m:ℝ)+
      ((639/2000:ℝ)*T+(1707/2000:ℝ)*T/(Y+1))/L+(3/2:ℝ)*T/Z := by
  have hsum := Finset.sum_le_sum (fun i hi => hrows i (Finset.mem_range.mp hi))
  have heq : (∑ i ∈ Finset.range m, (1+
      ((569/1000:ℝ)*min (2*R*(i+1:ℝ)) (T/(i+1:ℝ))-(499/1000:ℝ)*R*(i+1:ℝ)+
        (569/1000:ℝ)*min (2*R*(i+1:ℝ)) (T/(i+1:ℝ))/(Y+1))/L+
      min (2*R*(i+1:ℝ)) (T/(i+1:ℝ))/Z)) =
      (m:ℝ)+(rowSum m R T+(569/1000:ℝ)*capSum m R T/(Y+1))/L+capSum m R T/Z := by
    simp only [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    unfold rowSum capSum
    push_cast
    ring
  rw [heq] at hsum
  have hr := rowSum_physical m R T hR hT hphysical
  have hc := capSum_physical m R T hR hT hphysical
  apply hsum.trans
  apply add_le_add
  · apply add_le_add le_rfl
    apply (div_le_div_iff_of_pos_right hL).2
    have hcap := (div_le_div_iff_of_pos_right hY).2
      (mul_le_mul_of_nonneg_left hc (by norm_num : (0:ℝ)≤569/1000))
    convert add_le_add hr hcap using 1 <;> ring
  · exact (div_le_div_iff_of_pos_right hZ).2 hc

end LonelyRunnerNew.RoughRow

