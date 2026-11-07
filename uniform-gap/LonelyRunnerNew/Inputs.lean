import LonelyRunnerNew.Definitions

/- Named propositions, not axioms. All remain independent proof obligations. -/
noncomputable section
open scoped BigOperators
namespace LonelyRunnerNew

def roughBlockInput : Prop :=
  ∀ (n : ℕ) (U Z : Finset ℕ) (E : Finset (ℕ × ℕ)) (A B D ell : ℝ),
    0 < n → U.Nonempty → Z.Nonempty →
    U.card ≤ n → Z.card ≤ n → E ⊆ U.product Z →
    0 < A → 0 < B → 0 < D → 4096 ≤ ell →
    (∀ x ∈ U, rough 142 x ∧ A ≤ (x : ℝ) ∧ (x : ℝ) < 2*A) →
    (∀ y ∈ Z, rough 142 y ∧ B ≤ (y : ℝ) ∧ (y : ℝ) < 2*B) →
    separated (Real.exp ell) U → separated (Real.exp ell) Z →
    Real.rpow (physicalDensity U Z E D) q * ((U.card : ℝ)*(Z.card : ℝ)) /
      (A*B/D^2) * Real.rpow (((U.card : ℝ)*(Z.card : ℝ))/(n : ℝ)^2) sigma ≤
      roughConstant ell n

def kernelInput : Prop :=
  ∀ (lam : ℝ), 0 < lam → lam < 1 →
  ∀ (S T : Finset ℤ) (alpha beta : ℤ → ℝ),
    (∀ i ∈ S, 0 ≤ alpha i) → (∀ j ∈ T, 0 ≤ beta j) →
    (∑ i ∈ S, alpha i) = 1 → (∑ j ∈ T, beta j) = 1 →
    (∑ i ∈ S, ∑ j ∈ T,
      lam ^ (i-j).natAbs * Real.rpow (alpha i) (3/4 : ℝ) *
      Real.rpow (beta j) (3/4 : ℝ)) ≤ kernelN lam

def spilloverInput : Prop :=
  ∀ V : Finset ℕ, valid V → 3/35 - W V/2 ≤ gap V

/- This eliminates the auxiliary R0 from the original forest input.
   The original inequalities R0 ≤ gap and W ≤ delta+2*P*R0 imply it.
   It must be proved from that geometric construction, not postulated. -/
def forestInput : Prop :=
  ∀ (P delta : ℝ), 1 ≤ P → 0 ≤ delta → separatedControl P delta →
  ∀ V : Finset ℕ, valid V → W V ≤ delta + 2*P*gap V

end LonelyRunnerNew
