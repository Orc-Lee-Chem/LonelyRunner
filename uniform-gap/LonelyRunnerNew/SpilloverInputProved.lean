import LonelyRunnerNew.TwoSpeedIntersection
import LonelyRunnerNew.SpilloverEndpointAssembly
import LonelyRunnerNew.ForestInputProved

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators
namespace LonelyRunnerNew
attribute [local instance] Classical.propDecidable

def differentPair (u v : ℕ) (r : ℝ) : ℝ :=
  (volume (forbiddenInUnit u r∩forbiddenInUnit v r)).toReal-2*r/height u v

theorem bohrDifferentMass_eq_sum (V : Finset ℕ) (r : ℝ) :
    bohrDifferentMass V r=∑ u∈V,∑ v∈V,if u=v then 0 else differentPair u v r := by
  unfold bohrDifferentMass bohrPairMass bohrCommonMass
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro u _
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro v _
  by_cases huv : u=v <;> simp [huv,differentPair]

theorem orderedPair_count (V : Finset ℕ) :
    (∑ u∈V,∑ v∈V,if u=v then (0:ℝ) else 1)=(V.card:ℝ)^2-(V.card:ℝ) := by
  have hterm (u v : ℕ) : (if u=v then (0:ℝ) else 1)=1-(if u=v then (1:ℝ) else 0) := by
    split_ifs <;> norm_num
  simp_rw [hterm,Finset.sum_sub_distrib]
  have hrow (u : ℕ) (hu : u∈V) : (∑ v∈V,if u=v then (1:ℝ) else 0)=1 := by simp [hu]
  have hs : (∑ u∈V,∑ v∈V,if u=v then (1:ℝ) else 0)=(V.card:ℝ) := by
    trans ∑ _u∈V,(1:ℝ)
    · exact Finset.sum_congr rfl hrow
    · simp
  rw [hs]
  simp
  ring

theorem bohrDifferentMass_upper (V : Finset ℕ) (hV : positive V) {r : ℝ}
    (hr : 0≤r) (hrhalf : r<1/2) :
    bohrDifferentMass V r≤4*r^2*((V.card:ℝ)^2-(V.card:ℝ)) := by
  rw [bohrDifferentMass_eq_sum,←orderedPair_count,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u hu
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v hv
  by_cases huv : u=v
  · simp [huv]
  · simpa [huv,differentPair] using (pair_different_bounds u v (hV u hu) (hV v hv) hr hrhalf).2

theorem initial_pair_deficit (V : Finset ℕ) (hV : valid V) (u : ℕ) (hu : u∈V)
    (v : ℕ) (hv : v∈V) :
    (if u=v then (0:ℝ) else 1)-WPair V.card u v≤
      (V.card:ℝ)^2*(if u=v then 0 else differentPair u v (1/(2*(V.card:ℝ)))) := by
  by_cases huv : u=v
  · simp [huv,WPair]
  · have hn : (0:ℝ)<V.card := by exact_mod_cast valid_card_pos hV
    have hr : 0≤1/(2*(V.card:ℝ)) := by positivity
    have hrhalf : 1/(2*(V.card:ℝ))<(1/2:ℝ) := by
      apply (div_lt_iff₀ (by positivity : (0:ℝ)<2*(V.card:ℝ))).mpr
      have hn2 : (2:ℝ)≤V.card := by exact_mod_cast hV.2
      linarith
    have hh := (pair_different_bounds u v (hV.1 u hu) (hV.1 v hv) hr hrhalf).1
    change max 0 (4*(1/(2*(V.card:ℝ)))^2-4*(1/(2*(V.card:ℝ)))/height u v)≤
      differentPair u v (1/(2*(V.card:ℝ))) at hh
    simp only [huv,if_false,WPair]
    by_cases hcap : 2*(V.card:ℝ)/height u v≤1
    · rw [min_eq_right hcap]
      have h := le_trans (le_max_right _ _) hh
      have he : (V.card:ℝ)^2*(4*(1/(2*(V.card:ℝ)))^2-4*(1/(2*(V.card:ℝ)))/height u v)=
          1-2*(V.card:ℝ)/height u v := by field_simp;ring
      have hs := mul_le_mul_of_nonneg_left h (sq_nonneg (V.card:ℝ))
      rwa [he] at hs
    · rw [min_eq_left (le_of_not_ge hcap),sub_self]
      exact mul_nonneg (sq_nonneg _) ((le_max_left _ _).trans hh)

theorem bohrDifferentMass_initial_lower (V : Finset ℕ) (hV : valid V) :
    1-1/(V.card:ℝ)-W V≤bohrDifferentMass V (1/(2*(V.card:ℝ))) := by
  have hs := Finset.sum_le_sum (fun u hu => Finset.sum_le_sum (fun v hv => initial_pair_deficit V hV u hu v hv))
  simp_rw [Finset.sum_sub_distrib,←Finset.mul_sum] at hs
  rw [orderedPair_count,←bohrDifferentMass_eq_sum] at hs
  rw [W_eq_pair_sum]
  have hn : (0:ℝ)<V.card := by exact_mod_cast valid_card_pos hV
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hn)).mp
  have he : (V.card:ℝ)^2*(1-1/(V.card:ℝ)-
      (∑ u∈V,∑ v∈V,WPair V.card u v)/(V.card:ℝ)^2)=
      (V.card:ℝ)^2-(V.card:ℝ)-(∑ u∈V,∑ v∈V,WPair V.card u v) := by field_simp <;> ring
  rw [he]
  exact hs

theorem bohrDifferentMass_expanded_upper (V : Finset ℕ) (hV : valid V) :
    bohrDifferentMass V ((7/5:ℝ)*(1/(2*(V.card:ℝ))))≤(7/5:ℝ)^2*(1-1/(V.card:ℝ)) := by
  have hn : (0:ℝ)<V.card := by exact_mod_cast valid_card_pos hV
  have hn2 : (2:ℝ)≤V.card := by exact_mod_cast hV.2
  have hr : 0≤(7/5:ℝ)*(1/(2*(V.card:ℝ))) := by positivity
  have hrhalf : (7/5:ℝ)*(1/(2*(V.card:ℝ)))<(1/2:ℝ) := by
    rw [show (7/5:ℝ)*(1/(2*(V.card:ℝ)))=(7/10:ℝ)/(V.card:ℝ) by ring]
    apply (div_lt_iff₀ hn).mpr
    nlinarith only [hn2]
  have hh := bohrDifferentMass_upper V hV.1 hr hrhalf
  have he : 4*((7/5:ℝ)*(1/(2*(V.card:ℝ))))^2*((V.card:ℝ)^2-(V.card:ℝ))=
      (7/5:ℝ)^2*(1-1/(V.card:ℝ)) := by field_simp;ring
  rwa [he] at hh

theorem spilloverInput_proved : spilloverInput := by
  intro V hV
  have hh := spillover_of_actual_pair_mass_bounds V hV (bohrDifferentMass_initial_lower V hV)
    (bohrDifferentMass_expanded_upper V hV)
  have hn : (0:ℝ)<V.card := by exact_mod_cast valid_card_pos hV
  have hp : 0<1/(5*(V.card:ℝ)) := by positivity
  linarith only [hh,hp]

/-- The direct original formula, with no unproved mathematical parameters. -/
theorem lonely_runner_gap :
    ∀ V : Finset ℕ,(∀ v∈V,0<v) → 2≤V.card →
      ∃ t : ℝ,0≤t ∧ t<1 ∧ ∀ v∈V,∀ k : ℤ,
        |(v:ℝ)*t-(k:ℝ)| > (1+Real.exp (-6888:ℝ))/(2*(V.card:ℝ)) :=
  frozen_of_spillover spilloverInput_proved

/-- Adapter to the independently frozen target. -/
theorem frozen_target_proved : LonelyRunnerSpec.V1.Statement := lonely_runner_gap

end LonelyRunnerNew
