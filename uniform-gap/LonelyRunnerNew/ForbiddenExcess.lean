import LonelyRunnerNew.ForbiddenCommonCenter

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators
namespace LonelyRunnerNew

/-- All subsets use this same externally fixed radius. -/
def forbiddenUnion (S : Finset ℕ) (r : ℝ) : Set ℝ := ⋃ v∈S,forbiddenInUnit v r
def forbiddenExcess (S : Finset ℕ) (r : ℝ) : ℝ :=
  (∑ v∈S,(volume (forbiddenInUnit v r)).toReal)-(volume (forbiddenUnion S r)).toReal

theorem forbiddenUnion_subset_unit (S : Finset ℕ) (r : ℝ) :
    forbiddenUnion S r⊆Ico (0:ℝ) 1 := by
  intro t ht
  obtain ⟨v,hv,h⟩ := Set.mem_iUnion₂.mp ht
  exact h.1

theorem forbiddenUnion_measurable (S : Finset ℕ) (hS : positive S) (r : ℝ) :
    MeasurableSet (forbiddenUnion S r) := by
  exact S.measurableSet_biUnion (fun v hv => forbiddenInUnit_measurable v (hS v hv) r)

theorem forbiddenUnion_insert (S : Finset ℕ) (u : ℕ) (r : ℝ) :
    forbiddenUnion (insert u S) r=forbiddenInUnit u r∪forbiddenUnion S r := by
  simp [forbiddenUnion]

theorem forbiddenExcess_empty (r : ℝ) : forbiddenExcess ∅ r=0 := by
  simp [forbiddenExcess,forbiddenUnion]

theorem forbiddenExcess_insert (S : Finset ℕ) (hS : positive S) (u : ℕ) (hu : 0<u)
    (huS : u∉S) (r : ℝ) :
    forbiddenExcess (insert u S) r=forbiddenExcess S r+
      (volume (forbiddenInUnit u r∩forbiddenUnion S r)).toReal := by
  have hB := forbiddenInUnit_measurable u hu r
  have hU := forbiddenUnion_measurable S hS r
  have hBf : volume (forbiddenInUnit u r)≠⊤ := volume_ne_top_in_unit (fun _ hx => hx.1)
  have hUf : volume (forbiddenUnion S r)≠⊤ := volume_ne_top_in_unit (forbiddenUnion_subset_unit S r)
  have hUf' : volume (forbiddenInUnit u r∪forbiddenUnion S r)≠⊤ :=
    volume_ne_top_in_unit (by intro t ht;rcases ht with ht | ht;exact ht.1;exact forbiddenUnion_subset_unit S r ht)
  have hIf : volume (forbiddenInUnit u r∩forbiddenUnion S r)≠⊤ :=
    volume_ne_top_in_unit (fun _ hx => hx.1.1)
  have he := congrArg ENNReal.toReal (measure_union_add_inter (μ:=volume) (forbiddenInUnit u r) hU)
  rw [ENNReal.toReal_add hUf' hIf,ENNReal.toReal_add hBf hUf] at he
  simp only [forbiddenExcess,Finset.sum_insert huS,forbiddenUnion_insert]
  linarith

theorem forbiddenExcess_nonneg (S : Finset ℕ) (hS : positive S) (r : ℝ) :
    0≤forbiddenExcess S r := by
  induction S using Finset.induction_on with
  | empty => simp [forbiddenExcess_empty]
  | @insert u S hu ih =>
    have hp : positive S := fun v hv => hS v (Finset.mem_insert_of_mem hv)
    rw [forbiddenExcess_insert S hp u (hS u (Finset.mem_insert_self _ _)) hu r]
    exact add_nonneg (ih hp) ENNReal.toReal_nonneg

theorem forbiddenExcess_erase (S : Finset ℕ) (hS : positive S) {u : ℕ} (hu : u∈S) (r : ℝ) :
    forbiddenExcess S r-forbiddenExcess (S.erase u) r=
      (volume (forbiddenInUnit u r∩forbiddenUnion (S.erase u) r)).toReal := by
  have hh := forbiddenExcess_insert (S.erase u) (fun v hv => hS v (Finset.mem_of_mem_erase hv))
    u (hS u hu) (Finset.notMem_erase u S) r
  rw [Finset.insert_erase hu] at hh
  linarith

theorem uncovered_eq_complement (V : Finset ℕ) :
    uncovered V=Ico (0:ℝ) 1\forbiddenUnion V (1/(2*(V.card:ℝ))) := by
  classical
  ext t
  simp only [uncovered,Set.mem_setOf_eq,Set.mem_sdiff,forbiddenUnion,Set.mem_iUnion,
    forbiddenInUnit,Set.mem_inter_iff,forbidden,lonelyAt]
  constructor
  · rintro ⟨ht,hl⟩
    refine ⟨ht,?_⟩
    rintro ⟨v,hv,hvt,k,hk⟩
    exact (not_le_of_gt (hl v hv k)) hk
  · rintro ⟨ht,hn⟩
    refine ⟨ht,?_⟩
    intro v hv k
    apply lt_of_not_ge
    intro hk
    exact hn ⟨v,hv,ht,k,hk⟩

theorem forbiddenExcess_eq_gap (V : Finset ℕ) (hV : valid V) :
    forbiddenExcess V (1/(2*(V.card:ℝ)))=gap V := by
  have hn : (0:ℝ)<V.card := by exact_mod_cast valid_card_pos hV
  let r := 1/(2*(V.card:ℝ))
  have hr : 0≤r := by dsimp [r];positivity
  have hrh : r≤1/2 := by
    dsimp [r]
    apply (div_le_iff₀ (by positivity : (0:ℝ)<2*(V.card:ℝ))).mpr
    have hn1 : (1:ℝ)≤V.card := by exact_mod_cast valid_card_pos hV
    linarith
  have hsum : (∑ v∈V,(volume (forbiddenInUnit v r)).toReal)=1 := by
    have he (v : ℕ) (hv : v∈V) : (volume (forbiddenInUnit v r)).toReal=2*r := by
      rw [forbiddenInUnit_measure v (hV.1 v hv) r hr hrh,ENNReal.toReal_ofReal (by positivity)]
    rw [Finset.sum_congr rfl he]
    simp only [Finset.sum_const,nsmul_eq_mul]
    dsimp [r]
    field_simp
  have he := measure_sdiff_add_inter (μ:=volume) (Ico (0:ℝ) 1) (forbiddenUnion_measurable V hV.1 r)
  rw [Set.inter_eq_right.mpr (forbiddenUnion_subset_unit V r)] at he
  have hUf := volume_ne_top_in_unit (forbiddenUnion_subset_unit V r)
  have hGf : volume (Ico (0:ℝ) 1\forbiddenUnion V r)≠⊤ := volume_ne_top_in_unit Set.sdiff_subset
  have heR := congrArg ENNReal.toReal he
  rw [ENNReal.toReal_add hGf hUf] at heR
  norm_num at heR
  rw [forbiddenExcess,hsum]
  unfold gap
  rw [uncovered_eq_complement]
  change 1-(volume (forbiddenUnion V r)).toReal=(volume (Ico (0:ℝ) 1\forbiddenUnion V r)).toReal
  linarith

end LonelyRunnerNew
