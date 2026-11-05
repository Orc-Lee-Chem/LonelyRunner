import LonelyRunnerNew.PairGridIntegral

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators
namespace LonelyRunnerNew
attribute [local instance] Classical.propDecidable

theorem coprime_pair_intersection_bounds (a b : ℕ) (ha : 0<a) (hb : 0<b)
    (hab : a.Coprime b) {r : ℝ} (hr : 0≤r) (hrhalf : r<1/2) :
    4*r^2-2*r/(b:ℝ)≤(volume (forbiddenInUnit a r∩forbiddenInUnit b r)).toReal ∧
      (volume (forbiddenInUnit a r∩forbiddenInUnit b r)).toReal≤4*r^2+2*r/(b:ℝ) := by
  let F := fun z => ∑ j∈Finset.range b,pairIndicator a b r (((j:ℝ)+z)/(b:ℝ))
  let I := (forbidden 1 r).indicator (fun _ => (1:ℝ))
  have hI : IntervalIntegrable I volume 0 1 :=
    bounded_intervalIntegrable I (measurable_const.indicator (forbidden_measurable 1 (by norm_num) r))
      (fun z => by dsimp [I];simp only [Set.indicator_apply];split_ifs <;> norm_num) _ _
  have hF : IntervalIntegrable F volume 0 1 := by
    have hh := IntervalIntegrable.sum (Finset.range b)
      (f:=fun j z => pairIndicator a b r (((j:ℝ)+z)/(b:ℝ)))
      (a:=(0:ℝ)) (b:=(1:ℝ)) (μ:=volume) (fun j _ => bounded_intervalIntegrable _
        ((pairIndicator_measurable a b ha hb r).comp ((measurable_const.add measurable_id).div_const _))
        (fun z => pairIndicator_abs_le a b r _) _ _)
    have hfun : (∑ j∈Finset.range b,fun z => pairIndicator a b r (((j:ℝ)+z)/(b:ℝ)))=F := by
      funext z
      simp only [Finset.sum_apply,F]
    rwa [hfun] at hh
  have hp : ∀ z,(2*(b:ℝ)*r-1)*I z≤F z ∧ F z≤(2*(b:ℝ)*r+1)*I z := by
    intro z
    dsimp only [F]
    rw [pair_grid_count a b hb r z]
    by_cases hz : z∈forbidden 1 r
    · simpa [I,Set.indicator_of_mem hz] using eligibleGrid_card_bounds a b hab hb hr hrhalf z
    · simp [I,Set.indicator_of_notMem hz]
  have hlo := intervalIntegral.integral_mono (by norm_num : (0:ℝ)≤1) (hI.const_mul (2*(b:ℝ)*r-1)) hF
    (fun z => (hp z).1)
  have hhi := intervalIntegral.integral_mono (by norm_num : (0:ℝ)≤1) hF (hI.const_mul (2*(b:ℝ)*r+1))
    (fun z => (hp z).2)
  have hIv : (∫ z in (0:ℝ)..1,I z)=2*r := by
    rw [indicator_interval_measure _ (forbidden_measurable 1 (by norm_num) r)]
    change (volume (forbiddenInUnit 1 r)).toReal=2*r
    rw [forbiddenInUnit_measure 1 (by norm_num) r hr hrhalf.le,ENNReal.toReal_ofReal (by positivity)]
  have hFv : (∫ z in (0:ℝ)..1,F z)=(b:ℝ)*(volume (forbiddenInUnit a r∩forbiddenInUnit b r)).toReal := by
    rw [grid_integral b hb _ (pairIndicator_measurable a b ha hb r) (pairIndicator_abs_le a b r),
      pairIndicator_integral a b ha hb r]
  rw [intervalIntegral.integral_const_mul,hIv,hFv] at hlo
  rw [intervalIntegral.integral_const_mul,hIv,hFv] at hhi
  have hbR : (0:ℝ)<b := by exact_mod_cast hb
  constructor
  · apply (mul_le_mul_iff_right₀ hbR).mp
    have he : (b:ℝ)*(4*r^2-2*r/(b:ℝ))=(2*(b:ℝ)*r-1)*(2*r) := by field_simp;ring
    rw [he]
    nlinarith only [hlo]
  · apply (mul_le_mul_iff_right₀ hbR).mp
    have he : (b:ℝ)*(4*r^2+2*r/(b:ℝ))=(2*(b:ℝ)*r+1)*(2*r) := by field_simp;ring
    rw [he]
    nlinarith only [hhi]

theorem ordered_pair_intersection_bounds (u v : ℕ) (hu : 0<u) (hv : 0<v) (huv : u≤v)
    {r : ℝ} (hr : 0≤r) (hrhalf : r<1/2) :
    4*r^2-2*r/height u v≤(volume (forbiddenInUnit u r∩forbiddenInUnit v r)).toReal ∧
      (volume (forbiddenInUnit u r∩forbiddenInUnit v r)).toReal≤4*r^2+2*r/height u v := by
  have hd : 0<Nat.gcd u v := Nat.gcd_pos_of_pos_left v hu
  have ha : 0<u/Nat.gcd u v := Nat.div_pos (Nat.gcd_le_left v hu) hd
  have hb : 0<v/Nat.gcd u v := Nat.div_pos (Nat.gcd_le_right u hv) hd
  have hc := Nat.coprime_div_gcd_div_gcd hd
  have hh := coprime_pair_intersection_bounds (u/Nat.gcd u v) (v/Nat.gcd u v) ha hb hc hr hrhalf
  have hH : (((v/Nat.gcd u v:ℕ):ℝ))=height u v := by
    rw [Nat.cast_div (Nat.gcd_dvd_right u v) (by exact_mod_cast hd.ne')]
    simp [height,max_eq_right huv]
  rw [hH,←pair_measure_gcd u v hu r] at hh
  exact hh

theorem pair_intersection_bounds (u v : ℕ) (hu : 0<u) (hv : 0<v)
    {r : ℝ} (hr : 0≤r) (hrhalf : r<1/2) :
    4*r^2-2*r/height u v≤(volume (forbiddenInUnit u r∩forbiddenInUnit v r)).toReal ∧
      (volume (forbiddenInUnit u r∩forbiddenInUnit v r)).toReal≤4*r^2+2*r/height u v := by
  rcases le_total u v with huv | hvu
  · exact ordered_pair_intersection_bounds u v hu hv huv hr hrhalf
  · have hh := ordered_pair_intersection_bounds v u hv hu hvu hr hrhalf
    simpa only [height,Nat.max_comm,Nat.gcd_comm,Set.inter_comm] using hh

theorem pair_different_bounds (u v : ℕ) (hu : 0<u) (hv : 0<v)
    {r : ℝ} (hr : 0≤r) (hrhalf : r<1/2) :
    max 0 (4*r^2-4*r/height u v)≤
      (volume (forbiddenInUnit u r∩forbiddenInUnit v r)).toReal-2*r/height u v ∧
      (volume (forbiddenInUnit u r∩forbiddenInUnit v r)).toReal-2*r/height u v≤4*r^2 := by
  have hh := pair_intersection_bounds u v hu hv hr hrhalf
  have hcommon := forbidden_pair_intersection_lower hu hv hr hrhalf.le
  have hd : 4*r/height u v=2*(2*r/height u v) := by ring
  rw [hd]
  constructor
  · apply max_le <;> linarith only [hh.1,hcommon]
  · linarith only [hh.2]

end LonelyRunnerNew
