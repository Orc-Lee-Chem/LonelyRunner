import LonelyRunnerNew.SelbergWeights
import LonelyRunnerNew.SmallPrimeAnalytic

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew.FiniteSelberg
attribute [local instance] Classical.propDecidable

def primes (X : ℕ) : Finset ℕ := (Finset.Icc 2 X).filter Nat.Prime
def eulerProduct (X : ℕ) : ℝ := ∏p∈primes X,(1+2/((p:ℝ)*((p:ℝ)-1)))

theorem sum_Icc_one (X : ℕ) (f : ℕ → ℝ) :
    (∑k∈Finset.Icc 1 X,f k)=∑i∈Finset.range X,f (i+1) := by
  have hi : Finset.Icc 1 X=(Finset.range X).image (fun i => i+1) := by
    ext n
    simp only [Finset.mem_Icc,Finset.mem_image,Finset.mem_range]
    constructor
    · intro h;exact ⟨n-1,by omega,by omega⟩
    · rintro ⟨i,hi,rfl⟩;omega
  rw [hi,Finset.sum_image]
  intro i hi j hj h;change i+1=j+1 at h;omega

theorem reciprocal_telescope (X : ℕ) :
    (∑k∈Finset.Icc 1 X,1/((k:ℝ)*((k:ℝ)+1)))=1-1/(X+1:ℝ) := by
  rw [sum_Icc_one]
  have he : (∑i∈Finset.range X,1/(((i+1:ℕ):ℝ)*(((i+1:ℕ):ℝ)+1)))=
      ∑i∈Finset.range X,(1/(i+1:ℝ)-1/(i+2:ℝ)) := by
    apply Finset.sum_congr rfl
    intro i hi
    push_cast
    field_simp
    ring
  rw [he]
  simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_zero,zero_add,one_div_one,add_assoc,show (1+1:ℝ)=2 by norm_num] using
    Finset.sum_range_sub' (fun i : ℕ => 1/(i+1:ℝ)) X

theorem odd_prime_kernel {p : ℕ} (hp : Nat.Prime p) (hne : p≠2) :
    0<(p-1)/2 ∧ p=2*((p-1)/2)+1 ∧
      2/((p:ℝ)*((p:ℝ)-1))≤(2/3:ℝ)/((((p-1)/2:ℕ):ℝ)*((((p-1)/2:ℕ):ℝ)+1)) := by
  have ho := hp.eq_two_or_odd
  have hodd : p%2=1 := by rcases ho with he | h;exact False.elim (hne he);exact h
  have hp2 := hp.two_le
  have hk : 0<(p-1)/2 := by omega
  have he : p=2*((p-1)/2)+1 := by omega
  refine ⟨hk,he,?_⟩
  have hkr : (1:ℝ)≤((p-1)/2:ℕ) := by exact_mod_cast hk
  have hpr : (p:ℝ)=2*(((p-1)/2:ℕ):ℝ)+1 := by exact_mod_cast he
  have hd1 : 0<(p:ℝ)*((p:ℝ)-1) := by nlinarith
  have hd2 : 0<((((p-1)/2:ℕ):ℝ)*((((p-1)/2:ℕ):ℝ)+1)) := by nlinarith
  apply (div_le_div_iff₀ hd1 hd2).mpr
  nlinarith [mul_nonneg (by linarith : (0:ℝ)≤(((p-1)/2:ℕ):ℝ)-1) (by linarith : (0:ℝ)≤(((p-1)/2:ℕ):ℝ))]

theorem odd_prime_sum (X : ℕ) :
    (∑p∈(primes X).erase 2,2/((p:ℝ)*((p:ℝ)-1)))≤(2/3:ℝ) := by
  let P := (primes X).erase 2
  let k := fun p : ℕ => (p-1)/2
  let t := fun i : ℕ => (2/3:ℝ)/((i:ℝ)*((i:ℝ)+1))
  have hp (p : ℕ) (h : p∈P) : Nat.Prime p ∧ p≠2 ∧ p≤X := by
    have hh := Finset.mem_erase.mp h
    have hi := Finset.mem_filter.mp hh.2
    exact ⟨hi.2,hh.1,(Finset.mem_Icc.mp hi.1).2⟩
  have hinj : Set.InjOn k (P:Set ℕ) := by
    intro p hpM q hqM he
    have heP := (odd_prime_kernel (hp p hpM).1 (hp p hpM).2.1).2.1
    have heQ := (odd_prime_kernel (hp q hqM).1 (hp q hqM).2.1).2.1
    change (p-1)/2=(q-1)/2 at he
    omega
  have hsub : P.image k⊆Finset.Icc 1 X := by
    intro i hi
    obtain ⟨p,hpM,rfl⟩ := Finset.mem_image.mp hi
    have hkp := (odd_prime_kernel (hp p hpM).1 (hp p hpM).2.1).1
    have hx := (hp p hpM).2.2
    apply Finset.mem_Icc.mpr
    dsimp [k];omega
  calc
    _ ≤ ∑p∈P,t (k p) := Finset.sum_le_sum (fun p hpM => by
      have h := (odd_prime_kernel (hp p hpM).1 (hp p hpM).2.1).2.2
      simpa only [t,k] using h)
    _ = ∑i∈P.image k,t i := (Finset.sum_image hinj).symm
    _ ≤ ∑i∈Finset.Icc 1 X,t i := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i hi _ => by dsimp [t];positivity)
    _ = (2/3:ℝ)*(1-1/(X+1:ℝ)) := by
      simp only [t,div_eq_mul_inv]
      rw [←Finset.mul_sum]
      congr 1
      simpa only [one_div,div_eq_mul_inv,one_mul] using reciprocal_telescope X
    _ ≤ 2/3 := by
      have hh : 0≤1/(X+1:ℝ) := by positivity
      linarith

theorem exp_two_thirds_lt_two : Real.exp (2/3:ℝ)<2 := by
  have h := Certificate.rational_log_enclosure 2 (by norm_num) 2
  have hc : (2/3:ℚ)<Certificate.logLowerQ 2 2 := by norm_num [Certificate.logLowerQ,Finset.sum_range_succ]
  have hcR : (2/3:ℝ)<(Certificate.logLowerQ 2 2:ℝ) := by
    have hh := (Rat.cast_lt (K:=ℝ)).mpr hc
    push_cast at hh
    exact hh
  have hlog : (2/3:ℝ)<Real.log 2 := hcR.trans_le (by simpa using h.1)
  have he := Real.exp_lt_exp.mpr hlog
  simpa only [Real.exp_log (by norm_num : (0:ℝ)<2)] using he

/-- Entire prime Euler factor bound by a finite telescoping sum. -/
theorem eulerProduct_lt_four {X : ℕ} (hX : 2≤X) : eulerProduct X<4 := by
  have htwo : 2∈primes X := by simp [primes,hX,Nat.prime_two]
  have hall (p : ℕ) : 0≤2/((p:ℝ)*((p:ℝ)-1)) := by
    by_cases h : p≤1
    · interval_cases p <;> norm_num
    · have hp : (1:ℝ)<p := by exact_mod_cast (by omega : 1<p)
      positivity
  have he := Real.prod_one_add_le_exp_sum ((primes X).erase 2) hall
  have hh := Real.exp_le_exp.mpr (odd_prime_sum X)
  have hb := he.trans hh
  have hprod : eulerProduct X=2*(∏p∈(primes X).erase 2,(1+2/((p:ℝ)*((p:ℝ)-1)))) := by
    unfold eulerProduct
    conv_lhs => rw [←Finset.insert_erase htwo]
    rw [Finset.prod_insert (Finset.notMem_erase _ _)]
    norm_num
  rw [hprod]
  have h := exp_two_thirds_lt_two
  linarith

end LonelyRunnerNew.FiniteSelberg
