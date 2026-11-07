import LonelyRunnerNew.RCLargeScalar

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew.RoughRational
attribute [local instance] Classical.propDecidable

theorem large_rows_aggregate (S : Finset ℚ) {R T ell : ℝ} (hR : 0<R) (hT : 0<T)
    (hell : 4096≤ell) (hB : 128≤Real.sqrt (T/R))
    (hrough : ∀r∈S,roughPoint 142 r)
    (hsector : ∀r∈S,R≤(r:ℝ) ∧ (r:ℝ)<2*R) (hsep : separated (Real.exp ell) S) :
    (count S T:ℝ)≤
      (T*Real.log 2/6+2*T/(Real.sqrt 2*Real.sqrt (T/R))+
        (T*(1+Real.log 2)/6+2*Real.sqrt 2*T/Real.sqrt (T/R))/143)/((1/5:ℝ)*ell)+
      Real.sqrt (T/R)*(32*Real.exp ((2/5:ℝ)*ell)/((1/5:ℝ)*ell)^2)+
      3*T*Real.exp (-ell/10) := by
  let B := Real.sqrt (T/R)
  let F := roughDenominators B
  let L := (1/5:ℝ)*ell
  let E := 32*Real.exp ((2/5:ℝ)*ell)/L^2
  let v := Real.exp (-ell/10)
  have hb0 : 0<B := (physical_root hR hT).1
  have hBT : R*B^2=T := (physical_root hR hT).2
  have hL : 0<L := by
    dsimp only [L]
    have he : 0<ell := by linarith
    positivity
  have hrow (b : ℕ) (hb : b∈F) : (rowCount S T (b-1):ℝ)≤
      (RowKernels.gap R T (b:ℝ)+RowKernels.cap R T (b:ℝ)/143)/L+E+
      2*RowKernels.cap R T (b:ℝ)*v := by
    have hi := Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1
    have hindex : b-1<⌊Real.sqrt (T/R)⌋₊ := by
      have hbm : b≤⌊Real.sqrt (T/R)⌋₊ := hi.2
      omega
    have hh := row_selberg_bound S hR hT hell (alpha:=1/5) (le_refl _) (by norm_num)
      hindex hrough hsector hsep
    have hcast : ((b-1:ℕ):ℝ)+1=(b:ℝ) := by exact_mod_cast (by omega : b-1+1=b)
    have hcap : rowUpper R T (b-1)=RowKernels.cap R T (b:ℝ) := by
      unfold rowUpper RowKernels.cap
      rw [hcast]
    rw [hcap,hcast,show 2*(1/5:ℝ)*ell=(2/5:ℝ)*ell by ring] at hh
    exact hh
  have hsum := Finset.sum_le_sum (fun b hb => hrow b hb)
  have hmainSum : (∑b∈F,(RowKernels.gap R T (b:ℝ)+RowKernels.cap R T (b:ℝ)/143)/L)=
      ((∑b∈F,RowKernels.gap R T (b:ℝ))+(∑b∈F,RowKernels.cap R T (b:ℝ))/143)/L := by
    rw [←Finset.sum_div,Finset.sum_add_distrib,←Finset.sum_div]
  have hpackSum : (∑b∈F,2*RowKernels.cap R T (b:ℝ)*v)=2*v*(∑b∈F,RowKernels.cap R T (b:ℝ)) := by
    rw [←Finset.sum_mul,←Finset.mul_sum]
    ring
  simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul] at hsum
  rw [hmainSum,hpackSum] at hsum
  have hn : (count S T:ℝ)=∑b∈F,(rowCount S T (b-1):ℝ) :=
    count_eq_rough_rows S hR hT hrough (fun r hr => (hsector r hr).1)
  rw [←hn] at hsum
  have hcap := rough_cap_sum hR hB hBT
  have hgap := rough_gap_sum hR hB hBT
  have hcrude := rough_cap_sum_crude hR hT
  have hcard := denominator_card_le hb0.le
  have hm := div_le_div_of_nonneg_right
    (add_le_add hgap (div_le_div_of_nonneg_right hcap (by norm_num : (0:ℝ)≤143))) hL.le
  have hE : 0≤E := by dsimp only [E];positivity
  have herr := mul_le_mul_of_nonneg_right hcard hE
  have hp := mul_le_mul_of_nonneg_left hcrude (by dsimp only [v];positivity : (0:ℝ)≤2*v)
  change (count S T:ℝ)≤
    (T*Real.log 2/6+2*T/(Real.sqrt 2*B)+(T*(1+Real.log 2)/6+2*Real.sqrt 2*T/B)/143)/L+B*E+3*T*v
  linarith

theorem rc_large_B (S : Finset ℚ) {R T ell : ℝ} (hR : 0<R) (hT : 0<T)
    (hell : 4096≤ell) (hRn : 1/Real.sqrt 2≤R) (hlarge : Real.exp ell<Real.sqrt 2*T)
    (hB : 128≤Real.sqrt (T/R)) (hrough : ∀r∈S,roughPoint 142 r)
    (hsector : ∀r∈S,R≤(r:ℝ) ∧ (r:ℝ)<2*R) (hsep : separated (Real.exp ell) S) :
    (count S T:ℝ)≤1+(17/25:ℝ)*T/ell := by
  have he : 0<ell := by linarith
  have ha := large_rows_aggregate S hR hT hell hB hrough hsector hsep
  have hm := mul_le_mul_of_nonneg_left ha (div_pos he hT).le
  rw [mul_add,mul_add] at hm
  have hpEq : (ell/T)*(3*T*Real.exp (-ell/10))=3*ell*Real.exp (-ell/10) := by field_simp <;> ring
  rw [hpEq] at hm
  have hmain := large_main_scalar he hT hB
  have hscreen := large_screen_scalar hR hT he hRn hlarge
  have hb := Asymmetric.large_B_budget hell
  rw [add_mul] at hb
  have hnormalized : (ell/T)*(count S T:ℝ)<673/1000 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hnormalized.le hT.le
  have hEq : T*((ell/T)*(count S T:ℝ))=ell*(count S T:ℝ) := by field_simp
  rw [hEq] at hmul
  have hfinal : (count S T:ℝ)≤(17/25:ℝ)*T/ell := by
    apply (le_div_iff₀ he).mpr
    nlinarith
  linarith

end LonelyRunnerNew.RoughRational
