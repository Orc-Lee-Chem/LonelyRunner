import LonelyRunnerNew.SaturatedGrid

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew.Saturated

theorem ranked_sum_bound (a b m n : ℕ) (hm : 0<m) (hn : 0<n) (ham : a≤m) (hbn : b≤n)
    (x : Fin a → ℝ) (y : Fin b → ℝ) {c kappa : ℝ} (hc : 0<c) (hk : 0<kappa)
    (hx : ∀ i,0<x i) (hy : ∀ j,0<y j)
    (hxrank : ∀ i,(i.val:ℝ)+1≤kappa*x i) (hyrank : ∀ j,(j.val:ℝ)+1≤kappa*y j) :
    (∑ i : Fin a,∑ j : Fin b,cap c (x i*y j))≤
      (m:ℝ)*(n:ℝ)*Psi (c*kappa/Real.sqrt ((m:ℝ)*(n:ℝ))) := by
  have hmR : (0:ℝ)<m := by exact_mod_cast hm
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  let K := ((m:ℝ)*(n:ℝ))/kappa^2
  let t := c*kappa/Real.sqrt ((m:ℝ)*(n:ℝ))
  have hK : 0<K := div_pos (mul_pos hmR hnR) (sq_pos_of_pos hk)
  have ht : 0<t := div_pos (mul_pos hc hk) (Real.sqrt_pos.mpr (mul_pos hmR hnR))
  have hscale : c/Real.sqrt K=t := by
    dsimp [K,t]
    rw [Real.sqrt_div (mul_nonneg hmR.le hnR.le),Real.sqrt_sq_eq_abs,abs_of_pos hk]
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
    ring
  have hpoint (i : Fin a) (j : Fin b) :
      cap c (x i*y j)≤cap t ((((i.val:ℝ)+1)/(m:ℝ))*(((j.val:ℝ)+1)/(n:ℝ))) := by
    have hxi : ((i.val:ℝ)+1)/kappa≤x i := (div_le_iff₀ hk).mpr (by simpa only [mul_comm] using hxrank i)
    have hyj : ((j.val:ℝ)+1)/kappa≤y j := (div_le_iff₀ hk).mpr (by simpa only [mul_comm] using hyrank j)
    have hp := mul_le_mul hxi hyj (by positivity : (0:ℝ)≤((j.val:ℝ)+1)/kappa) (hx i).le
    have he : (((i.val:ℝ)+1)/kappa)*(((j.val:ℝ)+1)/kappa)=
        K*((((i.val:ℝ)+1)/(m:ℝ))*(((j.val:ℝ)+1)/(n:ℝ))) := by
      dsimp [K]
      field_simp
    have hh := cap_antitone hc hp
    rw [he,cap_rescale hK,hscale] at hh
    exact hh
  have hsum : (∑ i : Fin a,∑ j : Fin b,cap c (x i*y j))≤
      ∑ i : Fin a,∑ j : Fin b,cap t ((((i.val:ℝ)+1)/(m:ℝ))*(((j.val:ℝ)+1)/(n:ℝ))) :=
    Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hpoint i j))
  have heq : (∑ i : Fin a,∑ j : Fin b,
      cap t ((((i.val:ℝ)+1)/(m:ℝ))*(((j.val:ℝ)+1)/(n:ℝ))))=
      ∑ i∈Finset.range a,∑ j∈Finset.range b,
      cap t ((((i:ℝ)+1)/(m:ℝ))*(((j:ℝ)+1)/(n:ℝ))) := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ∑ j : Fin b,
      cap t ((((i:ℝ)+1)/(m:ℝ))*(((j.val:ℝ)+1)/(n:ℝ)))) a]
    apply Finset.sum_congr rfl
    intro i hi
    exact Fin.sum_univ_eq_sum_range (fun j : ℕ =>
      cap t ((((i:ℝ)+1)/(m:ℝ))*(((j:ℝ)+1)/(n:ℝ)))) b
  rw [heq] at hsum
  have hext : (∑ i∈Finset.range a,∑ j∈Finset.range b,
      cap t ((((i:ℝ)+1)/(m:ℝ))*(((j:ℝ)+1)/(n:ℝ))))≤
      ∑ i∈Finset.range m,∑ j∈Finset.range n,
      cap t ((((i:ℝ)+1)/(m:ℝ))*(((j:ℝ)+1)/(n:ℝ))) := by
    calc
      _ ≤ ∑ i∈Finset.range a,∑ j∈Finset.range n,
          cap t ((((i:ℝ)+1)/(m:ℝ))*(((j:ℝ)+1)/(n:ℝ))) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono hbn) (fun _ _ _ => cap_nonneg ht))
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono ham)
        (fun _ _ _ => Finset.sum_nonneg (fun _ _ => cap_nonneg ht))
  exact hsum.trans (hext.trans (double_grid_bound m n hm hn ht))

theorem label_sum_no_plus {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (F : Finset ι) (G : Finset κ) (hF : F.Nonempty) (hG : G.Nonempty)
    (x : ι → ℝ) (y : κ → ℝ) {c kappa : ℝ} (hc : 0<c) (hk : 0<kappa)
    (hx : ∀ i∈F,0<x i) (hy : ∀ j∈G,0<y j)
    (hcx : LabelCountBound F x 0 kappa) (hcy : LabelCountBound G y 0 kappa) :
    (∑ i∈F,∑ j∈G,cap c (x i*y j))≤
      (F.card:ℝ)*(G.card:ℝ)*Psi (c*kappa/Real.sqrt ((F.card:ℝ)*(G.card:ℝ))) := by
  obtain ⟨e,he⟩ := sorted_enumeration F x
  obtain ⟨f,hf⟩ := sorted_enumeration G y
  have heq : (∑ i∈F,∑ j∈G,cap c (x i*y j))=
      ∑ i : Fin F.card,∑ j : Fin G.card,cap c (x (e i).val*y (f j).val) := by
    rw [←sum_enumeration F e]
    apply Finset.sum_congr rfl
    intro i hi
    exact (sum_enumeration G f _).symm
  rw [heq]
  apply ranked_sum_bound F.card G.card F.card G.card hF.card_pos hG.card_pos le_rfl le_rfl
    _ _ hc hk (fun i => hx _ (e i).property) (fun j => hy _ (f j).property)
  · intro i
    simpa only [zero_add] using enumeration_rank F x e he hx hcx i
  · intro j
    simpa only [zero_add] using enumeration_rank G y f hf hy hcy j

end LonelyRunnerNew.Saturated
