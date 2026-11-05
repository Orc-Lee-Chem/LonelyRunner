import LonelyRunnerNew.StableConcentration
import Mathlib.NumberTheory.Padics.PadicVal.Basic

noncomputable section
open scoped BigOperators

namespace LonelyRunnerNew.TaggedState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

def leftLayer (s : TaggedState Label n) (p i : ℕ) : Finset Label :=
  s.left.filter (fun x => padicValNat p (s.leftValue x) = i)
def rightLayer (s : TaggedState Label n) (p j : ℕ) : Finset Label :=
  s.right.filter (fun y => padicValNat p (s.rightValue y) = j)

theorem valuation_residual {p a i : ℕ} (hp : Nat.Prime p) (ha : 0 < a)
    (hi : padicValNat p a = i) :
    p ^ i * (a / p ^ i) = a ∧ 0 < a / p ^ i ∧ ¬ p ∣ a / p ^ i := by
  letI : Fact p.Prime := ⟨hp⟩
  have hd : p ^ i ∣ a := (padicValNat_dvd_iff_le ha.ne').2 hi.ge
  have hf : p ^ i * (a / p ^ i) = a := Nat.mul_div_cancel' hd
  refine ⟨hf, Nat.pos_of_mul_pos_left (hf.symm ▸ ha), ?_⟩
  intro h
  have hsucc : p ^ (i + 1) ∣ a := by
    rw [← hf, pow_succ]
    exact Nat.mul_dvd_mul_left (p ^ i) h
  exact pow_succ_padicValNat_not_dvd ha.ne' (hi.symm ▸ hsucc)

def valuationDivide (s : TaggedState Label n) (p i j : ℕ) (hp : Nat.Prime p)
    (hL : (s.leftLayer p i).Nonempty) (hR : (s.rightLayer p j).Nonempty) :
    TaggedState Label n :=
  s.divideLayers (s.leftLayer p i) (s.rightLayer p j)
    (Finset.filter_subset _ _) (Finset.filter_subset _ _) hL hR p i j hp
    (fun x => s.leftValue x / p^i) (fun y => s.rightValue y / p^j)
    (fun x hx => (valuation_residual hp (s.left_positive x (Finset.mem_filter.mp hx).1)
      (Finset.mem_filter.mp hx).2).1)
    (fun y hy => (valuation_residual hp (s.right_positive y (Finset.mem_filter.mp hy).1)
      (Finset.mem_filter.mp hy).2).1)

theorem valuationDivide_step (s : TaggedState Label n) (p i j : ℕ) (hp : Nat.Prime p)
    (hL : (s.leftLayer p i).Nonempty) (hR : (s.rightLayer p j).Nonempty) :
    Step s (s.valuationDivide p i j hp hL hR) := by
  apply Step.prime
  · intro x hx
    exact (valuation_residual hp (s.left_positive x (Finset.mem_filter.mp hx).1)
      (Finset.mem_filter.mp hx).2).2.2
  · intro y hy
    exact (valuation_residual hp (s.right_positive y (Finset.mem_filter.mp hy).1)
      (Finset.mem_filter.mp hy).2).2.2

theorem valuationDivide_mass (s : TaggedState Label n) (p i j : ℕ) (hp : Nat.Prime p)
    (hL : (s.leftLayer p i).Nonempty) (hR : (s.rightLayer p j).Nonempty) :
    (s.valuationDivide p i j hp hL hR).edgeMass =
      s.rectangleMass (s.leftLayer p i) (s.rightLayer p j) := by
  have heq : s.edges ∩ (s.leftLayer p i).product (s.rightLayer p j) =
      s.edges.filter (fun e => e.1 ∈ s.leftLayer p i ∧ e.2 ∈ s.rightLayer p j) := by
    ext e
    simp
  unfold edgeMass rectangleMass
  change (∑ e ∈ s.edges ∩ (s.leftLayer p i).product (s.rightLayer p j), _) = _
  rw [heq]
  apply Finset.sum_congr rfl
  intro e he
  have hm := (Finset.mem_filter.mp he).2
  exact (s.divideLayers_edge_weight _ _ _ _ hL hR p i j hp _ _ _ _
    (fun x hx => (valuation_residual hp (s.left_positive x (Finset.mem_filter.mp hx).1)
      (Finset.mem_filter.mp hx).2).2.2)
    (fun y hy => (valuation_residual hp (s.right_positive y (Finset.mem_filter.mp hy).1)
      (Finset.mem_filter.mp hy).2).2.2) e.1 e.2 hm.1 hm.2).symm

theorem scaled_mass_bound {M D A B F exponent : ℝ} (hM : 0 ≤ M) (hD : 0 < D)
    (hA : 0 < A) (hB : 0 < B) (hF : 0 < F)
    (h : (M / A ^ (3/4:ℝ)) ^ exponent * F ≤ (D / B ^ (3/4:ℝ)) ^ exponent) :
    (M/D) ^ exponent ≤ (A/B) ^ ((3/4:ℝ)*exponent) / F := by
  rw [Real.div_rpow hM (Real.rpow_nonneg hA.le _), ← Real.rpow_mul hA.le,
    Real.div_rpow hD.le (Real.rpow_nonneg hB.le _), ← Real.rpow_mul hB.le,
    div_mul_eq_mul_div] at h
  have hc := (div_le_div_iff₀ (Real.rpow_pos_of_pos hA ((3/4:ℝ)*exponent))
    (Real.rpow_pos_of_pos hB ((3/4:ℝ)*exponent))).mp h
  rw [Real.div_rpow hM hD.le, Real.div_rpow hA.le hB.le]
  apply (le_div_iff₀ hF).2
  rw [div_mul_eq_mul_div]
  apply (div_le_div_iff₀ (Real.rpow_pos_of_pos hD exponent)
    (Real.rpow_pos_of_pos hB ((3/4:ℝ)*exponent))).2
  nlinarith only [hc]

theorem stable_layer_power (s : TaggedState Label n)
    (hstable : ∀ t, Step s t → t.quality ≤ s.quality) (hM : 0 < s.edgeMass)
    (p i j : ℕ) (hp : Nat.Prime p)
    (hL : (s.leftLayer p i).Nonempty) (hR : (s.rightLayer p j).Nonempty) :
    (s.rectangleMass (s.leftLayer p i) (s.rightLayer p j) / s.edgeMass) ^ q ≤
      (((s.leftLayer p i).card : ℝ) / s.left.card *
        (((s.rightLayer p j).card : ℝ) / s.right.card)) ^ ((3/4:ℝ)*q) /
          (p : ℝ) ^ ((i:ℤ)-(j:ℤ)).natAbs := by
  let t := s.valuationDivide p i j hp hL hR
  have hc : 0 < (s.a*s.b) / ((n:ℝ)^2)^sigma :=
    div_pos (mul_pos s.a_positive s.b_positive)
      (Real.rpow_pos_of_pos (sq_pos_of_pos s.ambient_pos) _)
  have hs := hstable t (valuationDivide_step s p i j hp hL hR)
  rw [quality_eq_normalized_mass, quality_eq_normalized_mass] at hs
  have ht : t.a*t.b = (s.a*s.b)*(p:ℝ)^((i:ℤ)-(j:ℤ)).natAbs :=
    prime_layer_scale_product s.a s.b p i j
  rw [ht] at hs
  have hfactor : (s.a*s.b*(p:ℝ)^((i:ℤ)-(j:ℤ)).natAbs)/((n:ℝ)^2)^sigma =
      (p:ℝ)^((i:ℤ)-(j:ℤ)).natAbs*((s.a*s.b)/((n:ℝ)^2)^sigma) := by ring
  rw [hfactor, ← mul_assoc] at hs
  have hscaled := scaled_mass_bound t.edgeMass_nonneg hM t.area_pos s.area_pos
    (pow_pos (by exact_mod_cast hp.pos : (0:ℝ)<p) _)
    ((mul_le_mul_iff_left₀ hc).mp hs)
  have harea : t.area/s.area =
      (((s.leftLayer p i).card:ℝ)/s.left.card)*
        (((s.rightLayer p j).card:ℝ)/s.right.card) := by
    change ((↑(s.leftLayer p i).card:ℝ)*↑(s.rightLayer p j).card)/
      ((↑s.left.card:ℝ)*↑s.right.card) = _
    ring
  rw [harea, valuationDivide_mass] at hscaled
  exact hscaled

end LonelyRunnerNew.TaggedState
