import LonelyRunnerNew.PhysicalOrdinaryBound
import LonelyRunnerNew.DyadicRoughAssembly

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew

/-- The original U,Z,E are the literal label and edge sets; no diagonal is
removed and no physical denominator is replaced by max(ax,by). -/
def physicalOfSets (n : ℕ) (U Z : Finset ℕ) (E : Finset (ℕ × ℕ))
    (hU : U.Nonempty) (hZ : Z.Nonempty) (hUn : U.card≤n) (hZn : Z.card≤n)
    (hE : E⊆U.product Z) (hpU : ∀ x∈U,0<x) (hpZ : ∀ y∈Z,0<y)
    (A B D : ℝ) (hA : 0<A) (hB : 0<B) (hD : 0<D) : PhysicalState ℕ n where
  geometry := {
    left := U
    right := Z
    left_nonempty := hU
    right_nonempty := hZ
    leftValue := id
    rightValue := id
    left_positive := hpU
    right_positive := hpZ
    left_injective := fun _ _ _ _ h => h
    right_injective := fun _ _ _ _ h => h
    left_budget := hUn
    right_budget := hZn
    edges := E
    edges_subset := hE
    a := 1
    b := 1
    a_positive := by norm_num
    b_positive := by norm_num }
  A := A
  B := B
  D := D
  A_pos := hA
  B_pos := hB
  D_pos := hD

theorem physicalOfSets_quality (n : ℕ) (U Z : Finset ℕ) (E : Finset (ℕ × ℕ))
    (hU : U.Nonempty) (hZ : Z.Nonempty) (hUn : U.card≤n) (hZn : Z.card≤n)
    (hE : E⊆U.product Z) (hpU : ∀ x∈U,0<x) (hpZ : ∀ y∈Z,0<y)
    (A B D : ℝ) (hA : 0<A) (hB : 0<B) (hD : 0<D) :
    (physicalOfSets n U Z E hU hZ hUn hZn hE hpU hpZ A B D hA hB hD).quality q sigma=
      (physicalDensity U Z E D)^q*((U.card:ℝ)*(Z.card:ℝ))/(A*B/D^2)*
        (((U.card:ℝ)*(Z.card:ℝ))/(n:ℝ)^2)^sigma := by
  change (physicalDensity U Z E D)^q*((U.card:ℝ)*(Z.card:ℝ))*(D^2/(A*B))*
      (((U.card:ℝ)*(Z.card:ℝ))/(n:ℝ)^2)^sigma=_
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]

/-- The original frozen rough-block input, with every physical stability,
LC, counting, saturated summation and terminal estimate internally proved. -/
theorem roughBlockInput_proved : roughBlockInput := by
  intro n U Z E A B D ell hn hU hZ hUn hZn hE hA hB hD hell hrU hrZ hSU hSZ
  let s := physicalOfSets n U Z E hU hZ hUn hZn hE
    (fun x hx => (hrU x hx).1.1) (fun y hy => (hrZ y hy).1.1) A B D hA hB hD
  have hr : s.InRange := ⟨fun x hx => (hrU x hx).2,fun y hy => (hrZ y hy).2⟩
  have hL : ∀ x∈s.geometry.left,rough 142 (s.geometry.leftValue x) := fun x hx => (hrU x hx).1
  have hR : ∀ y∈s.geometry.right,rough 142 (s.geometry.rightValue y) := fun y hy => (hrZ y hy).1
  have hsep : TaggedState.separated (Real.exp ell) s.geometry := ⟨hSU,hSZ⟩
  have hb := s.ordinary_physical_bound hr hL hR hell hsep
  dsimp only [s] at hb
  rw [physicalOfSets_quality] at hb
  exact hb

theorem frozen_of_spillover_forest (hspill : spilloverInput) (hforest : forestInput) :
    LonelyRunnerSpec.V1.Statement :=
  frozen_of_rough_block_spillover_forest roughBlockInput_proved hspill hforest

end LonelyRunnerNew
