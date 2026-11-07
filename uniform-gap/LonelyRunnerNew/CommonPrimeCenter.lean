import LonelyRunnerNew.RoughRestabilization
import Mathlib.Data.Nat.Factorization.Basic

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew.TaggedState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

/-- One positive integer for the centers of this one state, not one per edge. -/
def commonCenter (s : TaggedState Label n) (centers : ℕ → ℕ) : ℕ :=
  ∏ p∈s.primeSupport,p^(centers p)

theorem commonCenter_pos (s : TaggedState Label n) (centers : ℕ → ℕ) :
    0<s.commonCenter centers := by
  exact Finset.prod_pos (fun p hp => pow_pos (s.prime_of_mem_primeSupport hp).pos _)

theorem commonCenter_factorization_support (s : TaggedState Label n) (centers : ℕ → ℕ) (p : ℕ) :
    (s.commonCenter centers).factorization p=if p∈s.primeSupport then centers p else 0 := by
  classical
  unfold commonCenter
  rw [Nat.factorization_prod_apply (fun q hq => pow_ne_zero _ (s.prime_of_mem_primeSupport hq).ne_zero)]
  have hterm (q : ℕ) (hq : q∈s.primeSupport) :
      (q^(centers q)).factorization p=if q=p then centers q else 0 := by
    rw [(s.prime_of_mem_primeSupport hq).factorization_pow]
    simp only [Finsupp.single_apply]
  calc
    _ = ∑ q∈s.primeSupport,if q=p then centers q else 0 := Finset.sum_congr rfl hterm
    _ = _ := by simp

theorem commonCenter_factorization (s : TaggedState Label n) (centers : ℕ → ℕ)
    (hoff : ∀ p∉s.primeSupport,centers p=0) (p : ℕ) :
    (s.commonCenter centers).factorization p=centers p := by
  rw [commonCenter_factorization_support]
  split_ifs with hp
  · rfl
  · exact (hoff p hp).symm

theorem commonCenter_rough (s : TaggedState Label n) (centers : ℕ → ℕ)
    (hL : ∀ x∈s.left,rough 142 (s.leftValue x))
    (hR : ∀ y∈s.right,rough 142 (s.rightValue y)) : rough 142 (s.commonCenter centers) := by
  refine ⟨s.commonCenter_pos centers,?_⟩
  intro p hp hY hd
  have hnot := s.rough_prime_not_mem_support hL hR hp hY
  have hz : (s.commonCenter centers).factorization p=0 := by
    rw [commonCenter_factorization_support,if_neg hnot]
  have hpos := hp.factorization_pos_of_dvd (s.commonCenter_pos centers).ne' hd
  omega

theorem bracket_factorization (s : TaggedState Label n) (centers : ℕ → ℕ)
    (hoff : ∀ p∉s.primeSupport,centers p=0) {e : Label × Label}
    (hall : ∀ p,Nat.Prime p → s.centerBrackets p (centers p) e) (p : ℕ) :
    min ((s.leftValue e.1).factorization p) ((s.rightValue e.2).factorization p)≤
      (s.commonCenter centers).factorization p ∧
    (s.commonCenter centers).factorization p≤
      max ((s.leftValue e.1).factorization p) ((s.rightValue e.2).factorization p) := by
  by_cases hp : Nat.Prime p
  · rw [s.commonCenter_factorization centers hoff,Nat.factorization_def _ hp,Nat.factorization_def _ hp]
    exact hall p hp
  · simp only [Nat.factorization_eq_zero_of_not_prime _ hp,min_self,max_self,le_refl,and_self]

theorem commonCenter_divisibility (s : TaggedState Label n) (centers : ℕ → ℕ)
    (hoff : ∀ p∉s.primeSupport,centers p=0) {e : Label × Label} (he : e∈s.edges)
    (hall : ∀ p,Nat.Prime p → s.centerBrackets p (centers p) e) :
    Nat.gcd (s.leftValue e.1) (s.rightValue e.2)∣s.commonCenter centers ∧
      s.commonCenter centers∣Nat.lcm (s.leftValue e.1) (s.rightValue e.2) := by
  have hm := Finset.mem_product.mp (s.edges_subset he)
  have hx := s.left_positive e.1 hm.1
  have hy := s.right_positive e.2 hm.2
  constructor
  · apply (Nat.factorization_le_iff_dvd (Nat.gcd_pos_of_pos_left _ hx).ne' (s.commonCenter_pos centers).ne').mp
    rw [Nat.factorization_gcd hx.ne' hy.ne']
    intro p
    exact (s.bracket_factorization centers hoff hall p).1
  · apply (Nat.factorization_le_iff_dvd (s.commonCenter_pos centers).ne' (Nat.lcm_ne_zero hx.ne' hy.ne')).mp
    rw [Nat.factorization_lcm hx.ne' hy.ne']
    intro p
    exact (s.bracket_factorization centers hoff hall p).2

theorem min_center_identity (a b k : ℕ) (hlo : min a b≤k) (hhi : k≤max a b) :
    min a k+min b k=k+min a b := by omega

/-- This exact identity is the arithmetic content needed before rational
normalization. All-prime bracketing is proved by LC at the actual call site. -/
theorem commonCenter_gcd_identity (s : TaggedState Label n) (centers : ℕ → ℕ)
    (hoff : ∀ p∉s.primeSupport,centers p=0) {e : Label × Label} (he : e∈s.edges)
    (hall : ∀ p,Nat.Prime p → s.centerBrackets p (centers p) e) :
    Nat.gcd (s.leftValue e.1) (s.commonCenter centers)*
        Nat.gcd (s.rightValue e.2) (s.commonCenter centers)=
      s.commonCenter centers*Nat.gcd (s.leftValue e.1) (s.rightValue e.2) := by
  have hm := Finset.mem_product.mp (s.edges_subset he)
  have hx := s.left_positive e.1 hm.1
  have hy := s.right_positive e.2 hm.2
  have hN := s.commonCenter_pos centers
  have hgx := Nat.gcd_pos_of_pos_left (s.commonCenter centers) hx
  have hgy := Nat.gcd_pos_of_pos_left (s.commonCenter centers) hy
  have hg := Nat.gcd_pos_of_pos_left (s.rightValue e.2) hx
  apply Nat.eq_of_factorization_eq' (mul_pos hgx hgy).ne' (mul_pos hN hg).ne'
  rw [Nat.factorization_mul hgx.ne' hgy.ne',Nat.factorization_mul hN.ne' hg.ne',
    Nat.factorization_gcd hx.ne' hN.ne',Nat.factorization_gcd hy.ne' hN.ne',
    Nat.factorization_gcd hx.ne' hy.ne']
  ext p
  have h := s.bracket_factorization centers hoff hall p
  exact min_center_identity _ _ _ h.1 h.2

end LonelyRunnerNew.TaggedState
