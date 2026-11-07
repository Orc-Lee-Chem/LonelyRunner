import LonelyRunnerNew.SeparatedEstimates
import Mathlib.Algebra.Order.BigOperators.Group.Finset

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew

theorem capped_scale_le {C t : ℝ} (hC : 1≤C) : min 1 (C*t)≤C*min 1 t := by
  by_cases ht : t≤1
  · rw [min_eq_right ht]
    exact min_le_right _ _
  · rw [min_eq_left (le_of_not_ge ht),mul_one]
    exact (min_le_left _ _).trans hC

theorem sum_subset_loss {α : Type*} [DecidableEq α] (F G : Finset α) (hGF : G⊆F)
    (f : α → ℝ) (hf : ∀ x∈F,f x≤1) :
    (∑ x∈F,f x)≤(∑ x∈G,f x)+(F.card:ℝ)-(G.card:ℝ) := by
  have hh := Finset.sum_le_sum_of_subset_of_nonneg (f:=fun x => (1:ℝ)-f x) hGF
    (fun x hx _ => sub_nonneg.mpr (hf x hx))
  simp only [Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul,mul_one] at hh
  linarith

def WPair (N : ℝ) (u v : ℕ) : ℝ := if u=v then 0 else min 1 (2*N/height u v)

theorem W_eq_pair_sum (V : Finset ℕ) : W V=(∑ u∈V,∑ v∈V,WPair V.card u v)/(V.card:ℝ)^2 := rfl

theorem W_singleton (u : ℕ) : W {u}=0 := by simp [W]

/-- The radius/cardinality factor changes in W, while the geometric deletion
budget in ForbiddenExcess keeps the original radius fixed. -/
theorem W_subset_comparison (V S : Finset ℕ) (hSV : S⊆V) (hS : S.Nonempty) :
    W V≤((S.card:ℝ)/(V.card:ℝ))*W S+1-((S.card:ℝ)/(V.card:ℝ))^2 := by
  have hk : (0:ℝ)<S.card := by exact_mod_cast hS.card_pos
  have hn : (0:ℝ)<V.card := by exact_mod_cast hS.card_pos.trans_le (Finset.card_le_card hSV)
  have hkn : (S.card:ℝ)≤V.card := by exact_mod_cast Finset.card_le_card hSV
  have hC : 1≤(V.card:ℝ)/(S.card:ℝ) := (one_le_div hk).mpr hkn
  have hp : S.product S⊆V.product V := by
    intro e he
    have hh := Finset.mem_product.mp he
    exact Finset.mem_product.mpr ⟨hSV hh.1,hSV hh.2⟩
  have hrem := sum_subset_loss (V.product V) (S.product S) hp
    (fun e => WPair V.card e.1 e.2) (by
      intro e he
      unfold WPair
      split_ifs <;> first | norm_num | exact min_le_left _ _)
  simp only [Finset.product_eq_sprod,Finset.card_product,Finset.sum_product,Nat.cast_mul] at hrem
  have hpoint (u v : ℕ) : WPair V.card u v≤((V.card:ℝ)/(S.card:ℝ))*WPair S.card u v := by
    unfold WPair
    split_ifs with he
    · simp
    · have heq : 2*(V.card:ℝ)/height u v=((V.card:ℝ)/(S.card:ℝ))*(2*(S.card:ℝ)/height u v) := by
        field_simp
      rw [heq]
      exact capped_scale_le hC
  have hsum : (∑ u∈S,∑ v∈S,WPair V.card u v)≤
      ((V.card:ℝ)/(S.card:ℝ))*(∑ u∈S,∑ v∈S,WPair S.card u v) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro u hu
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun v _ => hpoint u v)
  rw [W_eq_pair_sum V,W_eq_pair_sum S]
  apply (div_le_iff₀ (sq_pos_of_pos hn)).mpr
  have heq : (((S.card:ℝ)/(V.card:ℝ))*
      ((∑ u∈S,∑ v∈S,WPair S.card u v)/(S.card:ℝ)^2)+1-((S.card:ℝ)/(V.card:ℝ))^2)*
      (V.card:ℝ)^2=
      ((V.card:ℝ)/(S.card:ℝ))*(∑ u∈S,∑ v∈S,WPair S.card u v)+(V.card:ℝ)^2-(S.card:ℝ)^2 := by
    field_simp
    <;> ring
  rw [heq]
  nlinarith only [hrem,hsum]

end LonelyRunnerNew
