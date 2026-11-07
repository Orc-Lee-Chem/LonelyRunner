import Mathlib.Data.Finset.Card
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.Linarith

noncomputable section
set_option autoImplicit false
namespace LonelyRunnerNew

/-- Finite deletion with an actual decreasing budget. A second, distinct
vertex remains at every deletion, so the terminal set is nonempty. -/
theorem separated_subset_of_deletion {α : Type*} [DecidableEq α]
    (V : Finset α) (hV : V.Nonempty) (R : α → α → Prop) (F : Finset α → ℝ)
    (K : ℝ) (hK : 0≤K) (hF : ∀ S,S⊆V → 0≤F S)
    (hdrop : ∀ S,S⊆V → ∀ u∈S,∀ v∈S,u≠v → ¬R u v →
      1≤K*(F S-F (S.erase u))) :
    ∃ S,S⊆V ∧ S.Nonempty ∧ (∀ u∈S,∀ v∈S,u≠v → R u v) ∧
      (V.card:ℝ)-(S.card:ℝ)≤K*F V := by
  classical
  have aux : ∀ S : Finset α,S⊆V → S.Nonempty →
      ∃ T,T⊆S ∧ T.Nonempty ∧ (∀ u∈T,∀ v∈T,u≠v → R u v) ∧
        (S.card:ℝ)-(T.card:ℝ)≤K*F S := by
    intro S
    refine Finset.strongInductionOn S ?_
    intro S ih hsub hne
    by_cases hs : ∀ u∈S,∀ v∈S,u≠v → R u v
    · exact ⟨S,le_rfl,hne,hs,by simpa only [sub_self] using mul_nonneg hK (hF S hsub)⟩
    · push Not at hs
      obtain ⟨u,hu,v,hv,hneuv,hbad⟩ := hs
      have herase : S.erase u⊂S := Finset.erase_ssubset hu
      have hkeep : (S.erase u).Nonempty := ⟨v,Finset.mem_erase.mpr ⟨hneuv.symm,hv⟩⟩
      obtain ⟨T,hT,hTN,hTR,hbound⟩ := ih (S.erase u) herase (Finset.erase_subset u S |>.trans hsub) hkeep
      have hd := hdrop S hsub u hu v hv hneuv hbad
      have hcardN := Finset.card_erase_add_one hu
      have hcard : ((S.erase u).card:ℝ)+1=(S.card:ℝ) := by exact_mod_cast hcardN
      refine ⟨T,hT.trans (Finset.erase_subset u S),hTN,hTR,?_⟩
      nlinarith only [hd,hbound,hcard]
  exact aux V le_rfl hV

end LonelyRunnerNew
