import LonelyRunnerNew.ForestDeletion
import LonelyRunnerNew.WSubsetComparison
import LonelyRunnerNew.RoughBlockProved

noncomputable section
set_option autoImplicit false
namespace LonelyRunnerNew

/-- Original C2, proved by finite deletion rather than a spanning forest.
There are no intersection-measure or deletion-budget inputs. -/
theorem forestInput_proved : forestInput := by
  intro P delta hP hd hcontrol V hV
  obtain ⟨S,hSV,hSN,hsep,hbudget⟩ := separated_subset_of_gap V hV hP
  have hk : (0:ℝ)<S.card := by exact_mod_cast hSN.card_pos
  have hn : (0:ℝ)<V.card := by exact_mod_cast valid_card_pos hV
  have hkn : (S.card:ℝ)≤V.card := by exact_mod_cast Finset.card_le_card hSV
  let z := (S.card:ℝ)/(V.card:ℝ)
  have hz0 : 0≤z := (div_pos hk hn).le
  have hz1 : z≤1 := (div_le_one hn).mpr hkn
  have hWS : W S≤delta := by
    by_cases hS2 : 2≤S.card
    · exact hcontrol S ⟨fun v hv => hV.1 v (hSV hv),hS2⟩ hsep
    · have hS1 : S.card=1 := by have := hSN.card_pos;omega
      obtain ⟨u,rfl⟩ := Finset.card_eq_one.mp hS1
      simpa only [W_singleton] using hd
  have hzWS : z*W S≤delta :=
    (mul_le_mul_of_nonneg_left hWS hz0).trans (by simpa using mul_le_mul_of_nonneg_right hz1 hd)
  have hcomp := W_subset_comparison V S hSV hSN
  change W V≤z*W S+1-z^2 at hcomp
  change 1-z≤P*gap V at hbudget
  nlinarith only [hcomp,hzWS,hbudget,sq_nonneg (1-z)]

/-- With the already proved arithmetic and C2, only C1 remains. This is a
conditional adapter, not an unconditional proof of the frozen final target. -/
theorem frozen_of_spillover (hspill : spilloverInput) : LonelyRunnerSpec.V1.Statement :=
  frozen_of_spillover_forest hspill forestInput_proved

end LonelyRunnerNew
