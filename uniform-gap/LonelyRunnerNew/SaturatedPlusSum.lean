import LonelyRunnerNew.SaturatedRankSum

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew.Saturated

theorem tuple_sum_plus (a b : ℕ) (x : Fin a → ℝ) (y : Fin b → ℝ)
    {c kappa : ℝ} (hc : 0<c) (hk : 0<kappa) (hx : ∀ i,0<x i) (hy : ∀ j,0<y j)
    (hrx : ∀ i,(i.val:ℝ)+1≤1+kappa*x i) (hry : ∀ j,(j.val:ℝ)+1≤1+kappa*y j) :
    (∑ i : Fin a,∑ j : Fin b,cap c (x i*y j))≤
      (a:ℝ)+(b:ℝ)+(a:ℝ)*(b:ℝ)*Psi (c*kappa/Real.sqrt ((a:ℝ)*(b:ℝ))) := by
  cases a with
  | zero => simp
  | succ a =>
    cases b with
    | zero => simp; positivity
    | succ b =>
      have ht := ranked_sum_bound a b (a+1) (b+1) (by omega) (by omega) (by omega) (by omega)
        (fun i => x i.succ) (fun j => y j.succ) hc hk
        (fun i => hx i.succ) (fun j => hy j.succ)
        (by intro i;have hh := hrx i.succ;simp only [Fin.val_succ,Nat.cast_add,Nat.cast_one] at hh;linarith)
        (by intro j;have hh := hry j.succ;simp only [Fin.val_succ,Nat.cast_add,Nat.cast_one] at hh;linarith)
      have hrow : (∑ j : Fin b,cap c (x 0*y j.succ))≤(b:ℝ) := by
        calc
          _ ≤ ∑ _j : Fin b,(1:ℝ) := Finset.sum_le_sum (fun _ _ => cap_le_one hc)
          _ = (b:ℝ) := by simp
      have hcol : (∑ i : Fin a,cap c (x i.succ*y 0))≤(a:ℝ) := by
        calc
          _ ≤ ∑ _i : Fin a,(1:ℝ) := Finset.sum_le_sum (fun _ _ => cap_le_one hc)
          _ = (a:ℝ) := by simp
      have hfirst : cap c (x 0*y 0)≤1 := cap_le_one hc
      simp_rw [Fin.sum_univ_succ,Finset.sum_add_distrib]
      push_cast at ht ⊢
      linarith

theorem label_sum_plus {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (F : Finset ι) (G : Finset κ) (x : ι → ℝ) (y : κ → ℝ)
    {c kappa : ℝ} (hc : 0<c) (hk : 0<kappa)
    (hx : ∀ i∈F,0<x i) (hy : ∀ j∈G,0<y j)
    (hcx : LabelCountBound F x 1 kappa) (hcy : LabelCountBound G y 1 kappa) :
    (∑ i∈F,∑ j∈G,cap c (x i*y j))≤
      (F.card:ℝ)+(G.card:ℝ)+(F.card:ℝ)*(G.card:ℝ)*
        Psi (c*kappa/Real.sqrt ((F.card:ℝ)*(G.card:ℝ))) := by
  obtain ⟨e,he⟩ := sorted_enumeration F x
  obtain ⟨f,hf⟩ := sorted_enumeration G y
  have heq : (∑ i∈F,∑ j∈G,cap c (x i*y j))=
      ∑ i : Fin F.card,∑ j : Fin G.card,cap c (x (e i).val*y (f j).val) := by
    rw [←sum_enumeration F e]
    apply Finset.sum_congr rfl
    intro i hi
    exact (sum_enumeration G f _).symm
  rw [heq]
  exact tuple_sum_plus F.card G.card _ _ hc hk
    (fun i => hx _ (e i).property) (fun j => hy _ (f j).property)
    (enumeration_rank F x e he hx hcx) (enumeration_rank G y f hf hy hcy)

end LonelyRunnerNew.Saturated
