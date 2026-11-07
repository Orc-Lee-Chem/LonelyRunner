import LonelyRunnerNew.RoughRowPacking
import LonelyRunnerNew.PeelingArithmetic
import LonelyRunnerNew.RoughStepInvariants

noncomputable section
set_option autoImplicit false
namespace LonelyRunnerNew.RoughRational.Asymmetric

def smooth (X x : ℕ) : ℕ := (x.primeFactorsList.filter (·≤X)).prod
def remainder (X x : ℕ) : ℕ := (x.primeFactorsList.filter (fun p => ¬p≤X)).prod

theorem smooth_pos (X x : ℕ) : 0<smooth X x := SmallPrimePeeling.part_positive x _
theorem remainder_pos (X x : ℕ) : 0<remainder X x := SmallPrimePeeling.part_positive x _

theorem decomposition {x : ℕ} (X : ℕ) (hx : 0<x) : remainder X x*smooth X x=x := by
  have h := List.prod_map_filter_mul_prod_map_filter_not (fun p : ℕ => p≤X) id x.primeFactorsList
  simp only [List.map_id] at h
  simpa only [smooth,remainder,mul_comm] using h.trans (Nat.prod_primeFactorsList hx.ne')

theorem remainder_rough (X x : ℕ) : rough X (remainder X x) := by
  refine ⟨remainder_pos X x,?_⟩
  intro p hp hle hd
  have hm := mem_list_primes_of_dvd_prod hp.prime
    (fun q hq => (Nat.prime_of_mem_primeFactorsList (List.mem_of_mem_filter hq)).prime) hd
  have hn : ¬p≤X := by simpa only [decide_eq_true_eq] using List.of_mem_filter hm
  exact hn hle

/-- First threshold crossing in a factor list; primality is unnecessary.
The upper bound Z^2<=X is used only when all remaining factors are <Z. -/
theorem divisor_from_list (l : List ℕ) (X Z : ℕ) (hZ : 0<Z) (hX : Z^2≤X)
    (hf : ∀p∈l,0<p ∧ p≤X) (hprod : Z≤l.prod) :
    ∃d : ℕ,d∣l.prod ∧ Z≤d ∧ d≤X := by
  induction l with
  | nil =>
      refine ⟨1,by simp,by simpa using hprod,?_⟩
      have hx : 1≤Z^2 := one_le_pow₀ hZ
      exact hx.trans hX
  | cons p l ih =>
      have hp := hf p (by simp)
      by_cases hpZ : Z≤p
      · exact ⟨p,by simp,hpZ,hp.2⟩
      by_cases hlZ : Z≤l.prod
      · obtain ⟨d,hd,hdl,hdu⟩ := ih (fun q hq => hf q (by simp [hq])) hlZ
        exact ⟨d,hd.trans (by simp),hdl,hdu⟩
      · refine ⟨p*l.prod,by simp,by simpa using hprod,?_⟩
        have h1 : p≤Z := by omega
        have h2 : l.prod≤Z := by omega
        exact (by nlinarith [Nat.mul_le_mul h1 h2] : p*l.prod≤Z^2).trans hX

theorem smooth_divisor {X Z x : ℕ} (hZ : 0<Z) (hX : Z^2≤X)
    (hlarge : Z<smooth X x) : ∃d : ℕ,d∣smooth X x ∧ Z≤d ∧ d≤X := by
  apply divisor_from_list _ X Z hZ hX _ hlarge.le
  intro p hp
  exact ⟨Nat.pos_of_mem_primeFactorsList (List.mem_of_mem_filter hp),
    by simpa only [decide_eq_true_eq] using List.of_mem_filter hp⟩

/-- No chosen divisor is an extra hypothesis: smooth factorization and first
threshold crossing construct it for every low-remainder numerator. -/
theorem allocation_divisor {X Z x : ℕ} {A : ℝ} (hZ : 0<Z) (hX : Z^2≤X)
    (hx : 0<x) (hxA : (x:ℝ)≤A)
    (hr : (remainder X x:ℝ)≤A/(X:ℝ)) :
    ∃d : ℕ,0<d ∧ d≤X ∧ d∣x ∧ ((x/d:ℕ):ℝ)*(Z:ℝ)≤A := by
  have hXpos : 0<X := lt_of_lt_of_le (pow_pos hZ _) hX
  have hXr : (0:ℝ)<X := by exact_mod_cast hXpos
  have hex := decomposition X hx
  have hu := smooth_pos X x
  by_cases hz : smooth X x≤Z
  · refine ⟨1,by norm_num,by omega,one_dvd _,?_⟩
    simp only [Nat.div_one]
    have hb := (le_div_iff₀ hXr).mp hr
    have hzR : (smooth X x:ℝ)≤Z := by exact_mod_cast hz
    have hsq : (Z:ℝ)^2≤X := by exact_mod_cast hX
    have he : (x:ℝ)=(remainder X x:ℝ)*(smooth X x:ℝ) := by exact_mod_cast hex.symm
    calc
      (x:ℝ)*Z = (remainder X x:ℝ)*((smooth X x:ℝ)*Z) := by rw [he];ring
      _ ≤ (remainder X x:ℝ)*((Z:ℝ)*Z) := by gcongr
      _ ≤ (remainder X x:ℝ)*X := by nlinarith [mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg (remainder X x): (0:ℝ)≤_)]
      _ ≤ A := hb
  · obtain ⟨d,hd,hZdl,hdX⟩ := smooth_divisor hZ hX (lt_of_not_ge hz)
    have hdx : d∣x := hd.trans ⟨remainder X x,hex.symm.trans (Nat.mul_comm _ _)⟩
    refine ⟨d,lt_of_lt_of_le hZ hZdl,hdX,hdx,?_⟩
    have he : ((x/d:ℕ):ℝ)*(d:ℝ)=(x:ℝ) := by exact_mod_cast Nat.div_mul_cancel hdx
    have hl : (Z:ℝ)≤d := by exact_mod_cast hZdl
    exact (mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg (x/d))).trans (he.le.trans hxA)

theorem smooth_ge_of_rough {Y X x : ℕ} (hx : rough Y x) (hu : smooth X x≠1) :
    Y+1≤smooth X x := by
  have hd : smooth X x∣x := ⟨remainder X x,(decomposition X hx.1).symm.trans (Nat.mul_comm _ _)⟩
  have hrough := rough_of_positive_dvd hx (smooth_pos X x) hd
  obtain ⟨p,hp,hpd⟩ := Nat.exists_prime_and_dvd hu
  have hy : Y<p := lt_of_not_ge (fun h => hrough.2 p hp h hpd)
  have hpbound := Nat.le_of_dvd (smooth_pos X x) hpd
  omega

end LonelyRunnerNew.RoughRational.Asymmetric
