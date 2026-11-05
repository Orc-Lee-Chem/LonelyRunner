import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Nat.GCD.Basic

/- Core definitions. Analytic input propositions are declared separately. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace LonelyRunnerNew

def q : ℝ := 201 / 50
def sigma : ℝ := 1 / 200
def c : ℝ := Real.exp (-6888)
def positive (V : Finset ℕ) : Prop := ∀ v ∈ V, 0 < v
def valid (V : Finset ℕ) : Prop := positive V ∧ 2 ≤ V.card
def height (x y : ℕ) : ℝ := ((max x y : ℕ) : ℝ) / (Nat.gcd x y : ℝ)
def separated (P : ℝ) (V : Finset ℕ) : Prop :=
  ∀ x ∈ V, ∀ y ∈ V, x ≠ y → P < height x y
def rough (Y x : ℕ) : Prop :=
  0 < x ∧ ∀ p : ℕ, Nat.Prime p → p ≤ Y → ¬ p ∣ x
def weight (a b : ℝ) (x y : ℕ) : ℝ :=
  min 1 ((Nat.gcd x y : ℝ) / max (a * (x : ℝ)) (b * (y : ℝ)))
def density (X Z : Finset ℕ) (E : Finset (ℕ × ℕ)) (a b : ℝ) : ℝ :=
  (∑ e ∈ E, weight a b e.1 e.2) / ((X.card : ℝ) * (Z.card : ℝ))
def quality (n : ℕ) (X Z : Finset ℕ) (E : Finset (ℕ × ℕ)) (a b : ℝ) : ℝ :=
  Real.rpow (density X Z E a b) q * ((X.card : ℝ) * (Z.card : ℝ)) * (a*b) *
  Real.rpow (((X.card : ℝ) * (Z.card : ℝ)) / (n : ℝ)^2) sigma
def W (V : Finset ℕ) : ℝ :=
  (∑ x ∈ V, ∑ y ∈ V, if x = y then 0 else
    min 1 (2 * (V.card : ℝ) / height x y)) / (V.card : ℝ)^2
def separatedControl (P delta : ℝ) : Prop :=
  ∀ V : Finset ℕ, valid V → separated P V → W V ≤ delta

def lonelyAt (V : Finset ℕ) (t radius : ℝ) : Prop :=
  ∀ v ∈ V, ∀ k : ℤ, radius < |(v : ℝ)*t - (k : ℝ)|
def uncovered (V : Finset ℕ) : Set ℝ :=
  {t | t ∈ Set.Ico (0 : ℝ) 1 ∧ lonelyAt V t (1/(2*(V.card : ℝ)))}
def gap (V : Finset ℕ) : ℝ := (volume (uncovered V)).toReal
def mainStatement : Prop :=
  ∀ V : Finset ℕ, valid V → ∃ t : ℝ,
    t ∈ Set.Ico (0 : ℝ) 1 ∧ lonelyAt V t ((1+c)/(2*(V.card : ℝ)))

def physicalDensity (U Z : Finset ℕ) (E : Finset (ℕ × ℕ)) (D : ℝ) : ℝ :=
  (∑ e ∈ E, min 1 ((Nat.gcd e.1 e.2 : ℝ)/D)) /
    ((U.card : ℝ)*(Z.card : ℝ))
def roughConstant (ell : ℝ) (n : ℕ) : ℝ :=
  4/(19/100 : ℝ)^2 * ((17/25 : ℝ)/ell)^2 +
  8/(19/100 : ℝ)^2 * Real.rpow (2/((27/50 : ℝ)*(1/1000 : ℝ)*(n : ℝ))) sigma
def kernelN (lam : ℝ) : ℝ :=
  (Real.sqrt 3/2)*lam*Real.rpow (-Real.log lam) (3/2 : ℝ)/(1-lam)^2 +
  1 - 2*lam*(-Real.log lam-1+lam)/(1-lam)^2

end LonelyRunnerNew
