import LonelyRunnerNew.ForbiddenExcess
import LonelyRunnerNew.FiniteDeletion

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
namespace LonelyRunnerNew

theorem close_pair_excess_drop (V : Finset ℕ) (hV : valid V) {P : ℝ} (hP : 1≤P)
    (S : Finset ℕ) (hSV : S⊆V) (u : ℕ) (hu : u∈S) (v : ℕ) (hv : v∈S)
    (hne : u≠v) (hclose : height u v≤P) :
    1≤((V.card:ℝ)*P)*(forbiddenExcess S (1/(2*(V.card:ℝ)))-
      forbiddenExcess (S.erase u) (1/(2*(V.card:ℝ)))) := by
  have hn : (0:ℝ)<V.card := by exact_mod_cast valid_card_pos hV
  have hP0 : 0<P := by linarith
  let r := 1/(2*(V.card:ℝ))
  have hr : 0≤r := by dsimp [r];positivity
  have hrh : r≤1/2 := by
    dsimp [r]
    apply (div_le_iff₀ (by positivity : (0:ℝ)<2*(V.card:ℝ))).mpr
    have h1 : (1:ℝ)≤V.card := by exact_mod_cast valid_card_pos hV
    linarith
  have hp : positive S := fun x hx => hV.1 x (hSV hx)
  have hpair := forbidden_pair_intersection_lower (hp u hu) (hp v hv) hr hrh
  have hsub : forbiddenInUnit u r∩forbiddenInUnit v r⊆
      forbiddenInUnit u r∩forbiddenUnion (S.erase u) r := by
    intro t ht
    refine ⟨ht.1,?_⟩
    exact Set.mem_iUnion₂.mpr ⟨v,Finset.mem_erase.mpr ⟨hne.symm,hv⟩,ht.2⟩
  have hfinite : volume (forbiddenInUnit u r∩forbiddenUnion (S.erase u) r)≠⊤ :=
    volume_ne_top_in_unit (fun _ hx => hx.1.1)
  have hmono := ENNReal.toReal_mono hfinite (measure_mono (μ:=volume) hsub)
  have hrat : 1/((V.card:ℝ)*P)≤2*r/height u v := by
    calc
      _ = 2*r/P := by dsimp [r];ring
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (height_pos (hp u hu)) hclose
  have hh := mul_le_mul_of_nonneg_left (hrat.trans (hpair.trans hmono)) (mul_pos hn hP0).le
  have hc : ((V.card:ℝ)*P)*(1/((V.card:ℝ)*P))=1 := by field_simp
  rw [hc] at hh
  rw [forbiddenExcess_erase S hp hu]
  exact hh

/-- The deletion budget always uses radius 1/(2*|V|), even on strict subsets.
The final separated set is nonempty and has a certified cardinality loss. -/
theorem separated_subset_of_gap (V : Finset ℕ) (hV : valid V) {P : ℝ} (hP : 1≤P) :
    ∃ S,S⊆V ∧ S.Nonempty ∧ separated P S ∧
      1-(S.card:ℝ)/(V.card:ℝ)≤P*gap V := by
  have hn : (0:ℝ)<V.card := by exact_mod_cast valid_card_pos hV
  have hP0 : 0<P := by linarith
  obtain ⟨S,hSV,hSN,hsep,hbudget⟩ := separated_subset_of_deletion V
    (Finset.card_pos.mp (valid_card_pos hV)) (fun u v => P<height u v)
    (fun S => forbiddenExcess S (1/(2*(V.card:ℝ)))) ((V.card:ℝ)*P)
    (mul_pos hn hP0).le
    (fun S hSV => forbiddenExcess_nonneg S (fun x hx => hV.1 x (hSV hx)) _)
    (by
      intro S hSV u hu v hv hne hbad
      exact close_pair_excess_drop V hV hP S hSV u hu v hv hne (le_of_not_gt hbad))
  rw [forbiddenExcess_eq_gap V hV] at hbudget
  refine ⟨S,hSV,hSN,hsep,?_⟩
  have heq : 1-(S.card:ℝ)/(V.card:ℝ)=((V.card:ℝ)-(S.card:ℝ))/(V.card:ℝ) := by field_simp
  rw [heq]
  apply (div_le_iff₀ hn).mpr
  nlinarith only [hbudget]

end LonelyRunnerNew
