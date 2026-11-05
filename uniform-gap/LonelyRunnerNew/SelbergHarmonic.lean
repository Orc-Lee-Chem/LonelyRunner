import LonelyRunnerNew.SelbergWeights
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.Harmonic.Bounds

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew.FiniteSelberg
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 800000

def radical (n : ℕ) : ℕ := ∏p∈n.primeFactors,p
def radicalFiber (X r : ℕ) : Finset ℕ := (Finset.Icc 1 X).filter (fun n => radical n=r)

theorem radical_pos (n : ℕ) : 0<radical n :=
  Finset.prod_pos (fun p hp => (Nat.mem_primeFactors.mp hp).1.pos)

theorem radical_squarefree (n : ℕ) : Squarefree (radical n) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    change IsRelPrime p q
    rw [←Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes (Nat.mem_primeFactors.mp hp).1 (Nat.mem_primeFactors.mp hq).1).mpr hpq
  · intro p hp
    exact (Nat.mem_primeFactors.mp hp).1.squarefree

theorem radical_mem_support {X n : ℕ} (hn : n∈Finset.Icc 1 X) : radical n∈support X := by
  have hh := Finset.mem_Icc.mp hn
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨radical_pos n,
    (Nat.le_of_dvd hh.1 (Nat.prod_primeFactors_dvd n)).trans hh.2⟩,radical_squarefree n⟩

theorem fiber_primes {X r n : ℕ} (hn : n∈radicalFiber X r) : n.primeFactors=r.primeFactors := by
  have he := (Finset.mem_filter.mp hn).2
  calc
    n.primeFactors=(radical n).primeFactors := (Nat.primeFactors_prod_primeFactors n).symm
    _ =r.primeFactors := congrArg Nat.primeFactors he

theorem finite_geometric_reciprocal {p : ℕ} (hp : 2≤p) (X : ℕ) :
    (∑a∈Finset.Icc 1 X,1/(p:ℝ)^a)≤1/((p:ℝ)-1) := by
  have hpr : (1:ℝ)<p := by exact_mod_cast hp
  have h0 : (0:ℝ)<p := by linarith
  have he : (∑a∈Finset.Icc 1 X,1/(p:ℝ)^a)=
      (1/(p:ℝ))*∑i∈Finset.range X,(1/(p:ℝ))^i := by
    rw [Finset.mul_sum]
    have hi : Finset.Icc 1 X=(Finset.range X).image (fun i => i+1) := by
      ext a
      simp only [Finset.mem_Icc,Finset.mem_image,Finset.mem_range]
      constructor
      · intro h;exact ⟨a-1,by omega,by omega⟩
      · rintro ⟨i,hi,rfl⟩;omega
    rw [hi,Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro i hi
      simp [pow_succ,div_pow,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc]
    · intro i hi j hj he
      change i+1=j+1 at he
      omega
  rw [he]
  have hgeo := geom_sum_mul_neg (1/(p:ℝ)) X
  have hp0 := pow_nonneg (by positivity : (0:ℝ)≤1/(p:ℝ)) X
  have hden : 0<1-1/(p:ℝ) := by apply sub_pos.mpr;exact (div_lt_one₀ h0).mpr hpr
  have hb : (∑i∈Finset.range X,(1/(p:ℝ))^i)≤1/(1-1/(p:ℝ)) :=
    (le_div_iff₀ hden).mpr (by linarith)
  calc
    _ ≤ (1/(p:ℝ))*(1/(1-1/(p:ℝ))) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by field_simp <;> ring

theorem squarefree_totient_product {r : ℕ} (hr : Squarefree r) :
    (r.totient:ℝ)=∏p∈r.primeFactors,((p:ℝ)-1) := by
  have he : r.totient=∏p∈r.primeFactors,(p-1) := by
    rw [Nat.totient_eq_div_primeFactors_mul r,Nat.prod_primeFactors_of_squarefree hr,
      Nat.div_self (Nat.pos_of_ne_zero hr.ne_zero),one_mul]
  rw [he,Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro p hp
  rw [Nat.cast_sub (Nat.mem_primeFactors.mp hp).1.one_le,Nat.cast_one]

/-- The radical fibre is injected into an actual finite exponent box.
No infinite Euler product or unproved radical counting estimate is used. -/
theorem radical_fiber_bound (X r : ℕ) (hr : Squarefree r) :
    (∑n∈radicalFiber X r,1/(n:ℝ))≤1/(r.totient:ℝ) := by
  let I := {p : ℕ // p∈r.primeFactors}
  let box := Fintype.piFinset (fun _ : I => Finset.Icc 1 X)
  let f : ℕ → I → ℕ := fun n p => n.factorization p.val
  let term : (I → ℕ) → ℝ := fun e => ∏p : I,1/(p.val:ℝ)^(e p)
  have hmem (n : ℕ) (hn : n∈radicalFiber X r) : f n∈box := by
    apply Fintype.mem_piFinset.mpr
    intro p
    have hp : p.val∈n.primeFactors := (fiber_primes hn).symm ▸ p.property
    have hd := Nat.mem_primeFactors.mp hp
    have hfac : 0<n.factorization p.val := hd.1.factorization_pos_of_dvd hd.2.2 hd.2.1
    have hm := Nat.mul_factorization_le (n:=n) (p:=p.val)
    have hl := Nat.mul_le_mul_right (n.factorization p.val) hd.1.one_le
    have hnX := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2
    exact Finset.mem_Icc.mpr ⟨hfac,by nlinarith⟩
  have hinj : Set.InjOn f (radicalFiber X r:Set ℕ) := by
    intro n hn m hm he
    have hnpos := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
    have hmpos := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
    apply Nat.eq_of_factorization_eq' (by omega) (by omega)
    ext p
    by_cases hp : p∈r.primeFactors
    · exact congrFun he ⟨p,hp⟩
    · have hnp : p∉n.factorization.support := by simpa only [Nat.support_factorization,fiber_primes hn] using hp
      have hmp : p∉m.factorization.support := by simpa only [Nat.support_factorization,fiber_primes hm] using hp
      have hn0 := Finsupp.notMem_support_iff.mp hnp
      have hm0 := Finsupp.notMem_support_iff.mp hmp
      rw [hn0,hm0]
  have heq (n : ℕ) (hn : n∈radicalFiber X r) : term (f n)=1/(n:ℝ) := by
    have hnpos := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
    have hp : (∏p∈r.primeFactors,p^(n.factorization p))=n := by
      rw [←fiber_primes hn]
      exact (Nat.prod_primeFactors_pow_factorization (by omega)).symm
    dsimp only [term,f]
    simp only [one_div,Finset.prod_inv_distrib,←Nat.cast_pow]
    rw [Finset.prod_coe_sort r.primeFactors (fun p : ℕ => ((p^(n.factorization p):ℕ):ℝ)),←Nat.cast_prod,hp]
  calc
    (∑n∈radicalFiber X r,1/(n:ℝ))=(∑e∈(radicalFiber X r).image f,term e) := by
      rw [Finset.sum_image hinj]
      exact Finset.sum_congr rfl (fun n hn => (heq n hn).symm)
    _ ≤ ∑e∈box,term e := Finset.sum_le_sum_of_subset_of_nonneg
      (by intro e he;obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp he;exact hmem n hn)
      (fun e he _ => Finset.prod_nonneg (fun p hp => by positivity))
    _ = ∏p : I,∑a∈Finset.Icc 1 X,1/(p.val:ℝ)^a := by
      dsimp only [box,term]
      exact Finset.sum_prod_piFinset (Finset.Icc 1 X) (fun (p : I) (a : ℕ) => 1/(p.val:ℝ)^a)
    _ ≤ ∏p : I,1/((p.val:ℝ)-1) := Finset.prod_le_prod₀
      (fun p hp => Finset.sum_nonneg (fun a ha => by positivity))
      (fun p hp => finite_geometric_reciprocal (Nat.mem_primeFactors.mp p.property).1.two_le X)
    _ =1/(r.totient:ℝ) := by
      simp only [one_div,Finset.prod_inv_distrib]
      rw [Finset.prod_coe_sort r.primeFactors (fun p : ℕ => (p:ℝ)-1),←squarefree_totient_product hr]

theorem harmonic_le_G (X : ℕ) : (∑n∈Finset.Icc 1 X,1/(n:ℝ))≤G X := by
  have hs : (∑n∈Finset.Icc 1 X,1/(n:ℝ))=
      ∑r∈support X,∑n∈radicalFiber X r,1/(n:ℝ) := by
    exact (Finset.sum_fiberwise_of_maps_to (fun n hn => radical_mem_support hn) (fun n => 1/(n:ℝ))).symm
  rw [hs]
  exact Finset.sum_le_sum (fun r hr => radical_fiber_bound X r (mem_support hr).2.2)

theorem log_le_G (X : ℕ) : Real.log (X+1:ℝ)≤G X := by
  have hh := log_add_one_le_harmonic X
  simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,Nat.cast_add,Nat.cast_one] at hh
  exact hh.trans (by simpa only [one_div] using harmonic_le_G X)

end LonelyRunnerNew.FiniteSelberg
