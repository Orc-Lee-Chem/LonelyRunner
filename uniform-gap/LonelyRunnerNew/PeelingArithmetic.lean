import LonelyRunnerNew.CorePeelingBounds
import Mathlib.Data.Nat.Factorization.Basic

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew.SmallPrimePeeling

theorem smoothPart_pos (x : ℕ) : 0<smoothPart x := part_positive x _
theorem roughPart_pos (x : ℕ) : 0<roughPart x := part_positive x _

theorem count_filtered (l : List ℕ) (P : ℕ → Prop) [DecidablePred P] (p : ℕ) :
    (l.filter P).count p=if P p then l.count p else 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases ha : P a <;> by_cases hp : P p <;> by_cases he : a=p <;>
      simp_all [List.count_cons]

theorem part_factorization (x : ℕ) (P : ℕ → Prop) [DecidablePred P] (p : ℕ) :
    ((x.primeFactorsList.filter P).prod).factorization p=if P p then x.factorization p else 0 := by
  have hperm := Nat.primeFactorsList_unique (n := (x.primeFactorsList.filter P).prod) rfl
    (fun q hq => Nat.prime_of_mem_primeFactorsList (List.mem_of_mem_filter hq))
  have h := hperm.count_eq p
  rw [count_filtered,Nat.primeFactorsList_count_eq,Nat.primeFactorsList_count_eq] at h
  exact h.symm

theorem smoothPart_factorization (x p : ℕ) :
    (smoothPart x).factorization p=if p∈Certificate.smallPrimes then x.factorization p else 0 :=
  part_factorization x _ p
theorem roughPart_factorization (x p : ℕ) :
    (roughPart x).factorization p=if p∉Certificate.smallPrimes then x.factorization p else 0 :=
  part_factorization x _ p

theorem prime_dvd_smoothPart {x p : ℕ} (hp : Nat.Prime p) (hd : p∣smoothPart x) :
    p∈Certificate.smallPrimes := by
  have hm := mem_list_primes_of_dvd_prod hp.prime
    (fun q hq => (Nat.prime_of_mem_primeFactorsList (List.mem_of_mem_filter hq)).prime) hd
  simpa only [decide_eq_true_eq] using List.of_mem_filter hm

theorem cross_coprime (x y : ℕ) : Nat.Coprime (smoothPart x) (roughPart y) := by
  apply Nat.coprime_of_dvd
  intro p hp hds hdr
  have hs := prime_dvd_smoothPart hp hds
  have hpdata := Certificate.smallPrimes_mem.mp hs
  exact False.elim ((roughPart_rough y).2 p hp hpdata.2 hdr)

theorem gcd_smooth_rough {x y : ℕ} (hx : 0<x) (hy : 0<y) :
    Nat.gcd x y=Nat.gcd (smoothPart x) (smoothPart y)*Nat.gcd (roughPart x) (roughPart y) := by
  have hgs := Nat.gcd_pos_of_pos_left (smoothPart y) (smoothPart_pos x)
  have hgr := Nat.gcd_pos_of_pos_left (roughPart y) (roughPart_pos x)
  apply Nat.eq_of_factorization_eq' (Nat.gcd_pos_of_pos_left y hx).ne' (mul_pos hgs hgr).ne'
  rw [Nat.factorization_gcd hx.ne' hy.ne',Nat.factorization_mul hgs.ne' hgr.ne',
    Nat.factorization_gcd (smoothPart_pos x).ne' (smoothPart_pos y).ne',
    Nat.factorization_gcd (roughPart_pos x).ne' (roughPart_pos y).ne']
  ext p
  by_cases hp : p∈Certificate.smallPrimes <;>
    simp [Finsupp.inf_apply,smoothPart_factorization,roughPart_factorization,hp]

theorem smooth_support (x : ℕ) : (smoothPart x).factorization.support⊆Certificate.smallPrimes := by
  intro p hp
  by_contra hn
  have he : (smoothPart x).factorization p=0 := by simp [smoothPart_factorization,hn]
  exact (Finsupp.mem_support_iff.mp hp) he

theorem smoothPart_product (x : ℕ) :
    smoothPart x=∏ p∈Certificate.smallPrimes,p^(padicValNat p x) := by
  rw [← Nat.prod_factorization_pow_eq_self (smoothPart_pos x).ne',
    Finsupp.prod_of_support_subset _ (smooth_support x) (fun p k => p^k) (by intros;simp)]
  apply Finset.prod_congr rfl
  intro p hp
  rw [smoothPart_factorization,if_pos hp,Nat.factorization_def x (Certificate.smallPrimes_mem.mp hp).1]

theorem smooth_gcd_product (x y : ℕ) :
    Nat.gcd (smoothPart x) (smoothPart y)=
      ∏ p∈Certificate.smallPrimes,p^(min (padicValNat p x) (padicValNat p y)) := by
  have hg := Nat.gcd_pos_of_pos_left (smoothPart y) (smoothPart_pos x)
  have hs : (Nat.gcd (smoothPart x) (smoothPart y)).factorization.support⊆Certificate.smallPrimes := by
    intro p hp
    have hn := Finsupp.mem_support_iff.mp hp
    by_contra hnot
    apply hn
    rw [Nat.factorization_gcd (smoothPart_pos x).ne' (smoothPart_pos y).ne']
    simp [Finsupp.inf_apply,smoothPart_factorization,hnot]
  rw [← Nat.prod_factorization_pow_eq_self hg.ne',
    Finsupp.prod_of_support_subset _ hs (fun p k => p^k) (by intros;simp)]
  apply Finset.prod_congr rfl
  intro p hp
  rw [Nat.factorization_gcd (smoothPart_pos x).ne' (smoothPart_pos y).ne']
  simp only [Finsupp.inf_apply,smoothPart_factorization,if_pos hp,
    Nat.factorization_def x (Certificate.smallPrimes_mem.mp hp).1,
    Nat.factorization_def y (Certificate.smallPrimes_mem.mp hp).1]

end LonelyRunnerNew.SmallPrimePeeling
