import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew.Saturated

/-- Counts labels, including all ties in w. It never counts the deduplicated
image of w. The rational-product adapter must prove injectivity separately. -/
def LabelCountBound {ι : Type*} [DecidableEq ι] (F : Finset ι) (w : ι → ℝ)
    (delta kappa : ℝ) : Prop :=
  ∀ T : ℝ,0<T → ((F.filter (fun x => w x≤T)).card:ℝ)≤delta+kappa*T

theorem sorted_enumeration {ι : Type*} [DecidableEq ι] (F : Finset ι) (w : ι → ℝ) :
    ∃ e : Fin F.card ≃ {x // x∈F},Monotone (fun i => w (e i).val) := by
  let e : Fin F.card ≃ {x // x∈F} :=
    (Fintype.equivFinOfCardEq (by simp : Fintype.card {x // x∈F}=F.card)).symm
  let f : Fin F.card → ℝ := fun i => w (e i).val
  exact ⟨(Tuple.sort f).trans e,Tuple.monotone_sort f⟩

theorem enumeration_filter_card {ι : Type*} [DecidableEq ι] (F : Finset ι) (w : ι → ℝ)
    (e : Fin F.card ≃ {x // x∈F}) (T : ℝ) :
    (Finset.univ.filter (fun i => w (e i).val≤T)).card=(F.filter (fun x => w x≤T)).card := by
  classical
  apply Finset.card_bij (fun i _ => (e i).val)
  · intro i hi
    exact Finset.mem_filter.mpr ⟨(e i).property,(Finset.mem_filter.mp hi).2⟩
  · intro i hi j hj he
    exact e.injective (Subtype.ext he)
  · intro x hx
    refine ⟨e.symm ⟨x,(Finset.mem_filter.mp hx).1⟩,?_,?_⟩
    · simp only [Finset.mem_filter,Finset.mem_univ,true_and,Equiv.apply_symm_apply]
      exact (Finset.mem_filter.mp hx).2
    · simp

/-- Every sorted position has a certified lower rank, even when several
distinct labels carry exactly the same numerical weight. -/
theorem enumeration_rank {ι : Type*} [DecidableEq ι] (F : Finset ι) (w : ι → ℝ)
    (e : Fin F.card ≃ {x // x∈F}) (hmono : Monotone (fun i => w (e i).val))
    {delta kappa : ℝ} (hpos : ∀ x∈F,0<w x) (hcount : LabelCountBound F w delta kappa)
    (i : Fin F.card) : (i.val:ℝ)+1≤delta+kappa*w (e i).val := by
  have hcard : i.val<(Finset.univ.filter (fun j => w (e j).val≤w (e i).val)).card :=
    (Tuple.lt_card_le_iff_apply_le_of_monotone hmono).mpr le_rfl
  rw [enumeration_filter_card] at hcard
  have hi : (i.val:ℝ)+1≤((F.filter (fun x => w x≤w (e i).val)).card:ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hcard)
  exact hi.trans (hcount _ (hpos _ (e i).property))

theorem sum_enumeration {ι : Type*} [DecidableEq ι] (F : Finset ι)
    (e : Fin F.card ≃ {x // x∈F}) (f : ι → ℝ) :
    (∑ i : Fin F.card,f (e i).val)=∑ x∈F,f x := by
  rw [←Finset.sum_coe_sort F f]
  exact e.sum_comp (fun x : {x // x∈F} => f x.val)

end LonelyRunnerNew.Saturated
