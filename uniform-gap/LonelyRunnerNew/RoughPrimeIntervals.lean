import LonelyRunnerNew.AsymmetricParameters
import LonelyRunnerNew.ChebyshevExplicit

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew.RoughRational
attribute [local instance] Classical.propDecidable

theorem rough_interval_theta {X : ℕ} {U A L : ℝ} (hU : 1<U) (hUA : U≤A)
    (hsmall : A<(X:ℝ)^2) (hL : 0<L) (hlog : L≤Real.log U) :
    ((roughIntegerInterval X U A).card:ℝ)≤(Chebyshev.theta A-Chebyshev.theta (U-1))/L := by
  let F := roughIntegerInterval X U A
  let Q := (Finset.Ioc 0 ⌊U-1⌋₊).filter Nat.Prime
  let W := (Finset.Ioc 0 ⌊A⌋₊).filter Nat.Prime
  have hA : 0≤A := by linarith
  have hf (n : ℕ) (hn : n∈F) : rough X n ∧ U≤(n:ℝ) ∧ (n:ℝ)≤A := by
    have hh := Finset.mem_filter.mp hn
    refine ⟨hh.2.1,hh.2.2,?_⟩
    have hi := Finset.mem_range.mp hh.1
    have hnf : n≤⌊A⌋₊ := by omega
    exact (by exact_mod_cast hnf : (n:ℝ)≤⌊A⌋₊).trans (Nat.floor_le hA)
  have hprime (n : ℕ) (hn : n∈F) : Nat.Prime n := by
    have hh := hf n hn
    have hsq : n<X^2 := by exact_mod_cast hh.2.2.trans_lt hsmall
    rcases rough_below_square_prime hh.1 hsq with he | hp
    · have hn1 : (n:ℝ)=1 := by exact_mod_cast he
      linarith [hh.2.1]
    · exact hp
  have hsub : F∪Q⊆W := by
    intro n hn
    apply Finset.mem_filter.mpr
    rcases Finset.mem_union.mp hn with hn | hn
    · have hh := hf n hn
      exact ⟨Finset.mem_Ioc.mpr ⟨hh.1.1,(Nat.le_floor_iff hA).mpr hh.2.2⟩,hprime n hn⟩
    · have hh := Finset.mem_filter.mp hn
      have hb := Finset.mem_Ioc.mp hh.1
      have hnf : ⌊U-1⌋₊≤⌊A⌋₊ := Nat.floor_mono (by linarith)
      exact ⟨Finset.mem_Ioc.mpr ⟨hb.1,hb.2.trans hnf⟩,hh.2⟩
  have hdis : Disjoint F Q := by
    apply Finset.disjoint_left.mpr
    intro n hn hq
    have hh := hf n hn
    have hi := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hq).1).2
    have hr : (n:ℝ)≤U-1 := (by exact_mod_cast hi : (n:ℝ)≤⌊U-1⌋₊).trans (Nat.floor_le (by linarith))
    linarith [hh.2.1]
  have hsum : (∑n∈F,Real.log (n:ℝ))+Chebyshev.theta (U-1)≤Chebyshev.theta A := by
    have hh := Finset.sum_le_sum_of_subset_of_nonneg (f:=fun n : ℕ => Real.log (n:ℝ)) hsub
      (fun n hn _ => Real.log_nonneg (by
        have hi := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).1
        exact_mod_cast hi))
    rw [Finset.sum_union hdis] at hh
    exact hh
  have hweight : (F.card:ℝ)*L≤∑n∈F,Real.log (n:ℝ) := by
    rw [←nsmul_eq_mul,←Finset.sum_const]
    apply Finset.sum_le_sum
    intro n hn
    exact hlog.trans (Real.log_le_log (by linarith) (hf n hn).2.1)
  apply (le_div_iff₀ hL).mpr
  linarith

theorem rough_interval_theta_upper {X : ℕ} {A L : ℝ} (hA : 0≤A)
    (hsmall : A<(X:ℝ)^2) (hL : 0<L) (hlog : L≤Real.log (X:ℝ)) :
    ((roughIntegerInterval X 1 A).card:ℝ)≤1+Chebyshev.theta A/L := by
  let F := roughIntegerInterval X 1 A
  let W := (Finset.Ioc 0 ⌊A⌋₊).filter Nat.Prime
  have hf (n : ℕ) (hn : n∈F) : rough X n ∧ (n:ℝ)≤A := by
    have hh := Finset.mem_filter.mp hn
    have hi := Finset.mem_range.mp hh.1
    refine ⟨hh.2.1,?_⟩
    exact (by exact_mod_cast (by omega : n≤⌊A⌋₊) : (n:ℝ)≤⌊A⌋₊).trans (Nat.floor_le hA)
  have hp (n : ℕ) (hn : n∈F.erase 1) : Nat.Prime n ∧ X<n := by
    have hh := Finset.mem_erase.mp hn
    have hr := hf n hh.2
    have hs : n<X^2 := by exact_mod_cast hr.2.trans_lt hsmall
    have hprime := (rough_below_square_prime hr.1 hs).resolve_left hh.1
    exact ⟨hprime,lt_of_not_ge (fun he => hr.1.2 n hprime he (dvd_refl n))⟩
  have hsub : F.erase 1⊆W := by
    intro n hn
    have hh := hf n (Finset.mem_erase.mp hn).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hh.1.1,(Nat.le_floor_iff hA).mpr hh.2⟩,(hp n hn).1⟩
  have hs : ∑n∈F.erase 1,Real.log (n:ℝ)≤Chebyshev.theta A := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n hn _ => Real.log_nonneg (by
      have hi := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).1
      exact_mod_cast hi))
  have hw : ((F.erase 1).card:ℝ)*L≤∑n∈F.erase 1,Real.log (n:ℝ) := by
    rw [←nsmul_eq_mul,←Finset.sum_const]
    apply Finset.sum_le_sum
    intro n hn
    have hXpos : (0:ℝ)<X := by
      by_contra hh
      have he : X=0 := by have hz := Nat.cast_nonneg X (α:=ℝ);exact_mod_cast (by linarith : (X:ℝ)=0)
      subst X
      norm_num at hlog
      linarith
    exact hlog.trans (Real.log_le_log hXpos (by exact_mod_cast (hp n hn).2.le))
  have hc : F.card≤(F.erase 1).card+1 := by
    by_cases hm : 1∈F
    · rw [Finset.card_erase_of_mem hm]
      have hh := Finset.card_pos.mpr ⟨1,hm⟩
      omega
    · simp [Finset.erase_eq_of_notMem hm]
  have hcr : (F.card:ℝ)≤((F.erase 1).card:ℝ)+1 := by exact_mod_cast hc
  have hd := (le_div_iff₀ hL).mpr (hw.trans hs)
  linarith

end LonelyRunnerNew.RoughRational
