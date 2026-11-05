import LonelyRunnerNew.RCDenominatorSums

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew.RoughRational
attribute [local instance] Classical.propDecidable

theorem row_zero_of_not_rough (S : Finset ℚ) (T : ℝ) (i : ℕ)
    (hrough : ∀r∈S,roughPoint 142 r) (hn : ¬rough 142 (i+1)) : rowCount S T i=0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro r hr
  have hh := Finset.mem_filter.mp hr
  have hs := (Finset.mem_filter.mp hh.1).1
  have hd := (hrough r hs).2.2
  exact hn (by simpa only [hh.2] using hd)

theorem count_eq_rough_rows (S : Finset ℚ) {R T : ℝ} (hR : 0<R) (hT : 0<T)
    (hrough : ∀r∈S,roughPoint 142 r) (hl : ∀r∈S,R≤(r:ℝ)) :
    (count S T:ℝ)=∑b∈roughDenominators (Real.sqrt (T/R)),(rowCount S T (b-1):ℝ) := by
  let m := ⌊Real.sqrt (T/R)⌋₊
  have he := count_eq_sum_rows S T m (fun r hr => denominator_le_floor hR hT r
    (hrough r (Finset.mem_filter.mp hr).1).1 (hl r (Finset.mem_filter.mp hr).1) (Finset.mem_filter.mp hr).2)
  have hc : (count S T:ℝ)=∑i∈Finset.range m,(rowCount S T i:ℝ) := by exact_mod_cast he
  have hs := FiniteSelberg.sum_Icc_one m (fun b => (rowCount S T (b-1):ℝ))
  simp only [Nat.add_sub_cancel] at hs
  rw [←hs] at hc
  rw [hc]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro b hb hn
  have hb1 := (Finset.mem_Icc.mp hb).1
  have hnb : ¬rough 142 b := by
    intro h
    exact hn (Finset.mem_filter.mpr ⟨hb,h⟩)
  have he := row_zero_of_not_rough S T (b-1) hrough (by simpa only [Nat.sub_add_cancel hb1] using hnb)
  simp only [he,Nat.cast_zero]

theorem denominator_card_le {B : ℝ} (hB : 0≤B) : ((roughDenominators B).card:ℝ)≤B := by
  have hn : (roughDenominators B).card≤⌊B⌋₊ := by
    have hh := Finset.card_filter_le (s:=Finset.Icc 1 ⌊B⌋₊) (p:=rough 142)
    simpa only [roughDenominators,Nat.card_Icc,Nat.add_sub_cancel] using hh
  exact (by exact_mod_cast hn : ((roughDenominators B).card:ℝ)≤⌊B⌋₊).trans (Nat.floor_le hB)

theorem normalized_root_ratio {R T ell : ℝ} (hR : 0<R) (hT : 0<T)
    (hRn : 1/Real.sqrt 2≤R) (hlarge : Real.exp ell<Real.sqrt 2*T) :
    Real.sqrt (T/R)/T≤Real.sqrt 2*Real.exp (-ell/2) := by
  let B := Real.sqrt (T/R)
  obtain ⟨hb0,hBT⟩ := physical_root hR hT
  have hs : 0<Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hRone : 1≤R*Real.sqrt 2 := (div_le_iff₀ hs).mp hRn
  have hRtwo : Real.sqrt 2≤2*R := by
    calc
      _ =1*Real.sqrt 2 := by ring
      _ ≤(R*Real.sqrt 2)*Real.sqrt 2 := mul_le_mul_of_nonneg_right hRone hs.le
      _ =_ := by rw [mul_assoc,←pow_two,hsq];ring
  have hP : Real.exp ell≤2*R*T := hlarge.le.trans (mul_le_mul_of_nonneg_right hRtwo hT.le)
  have hE : 1≤2*R*T*Real.exp (-ell) := by
    have hm := mul_le_mul_of_nonneg_right hP (Real.exp_nonneg (-ell))
    rw [←Real.exp_add,add_neg_cancel,Real.exp_zero] at hm
    exact hm
  have hBsq : B^2≤2*T^2*Real.exp (-ell) := by
    calc
      _ =1*B^2 := by ring
      _ ≤(2*R*T*Real.exp (-ell))*B^2 := mul_le_mul_of_nonneg_right hE (sq_nonneg B)
      _ =2*T*Real.exp (-ell)*(R*B^2) := by ring
      _ =_ := by rw [hBT];ring
  have hex : Real.exp (-ell/2)^2=Real.exp (-ell) := by rw [pow_two,←Real.exp_add];congr 1;ring
  have hright : (Real.sqrt 2*T*Real.exp (-ell/2))^2=2*T^2*Real.exp (-ell) := by
    rw [mul_pow,mul_pow,hsq,hex]
  have hroot : B≤Real.sqrt 2*T*Real.exp (-ell/2) := by
    have hh : 0≤Real.sqrt 2*T*Real.exp (-ell/2) := by positivity
    nlinarith
  apply (div_le_iff₀ hT).mpr
  convert hroot using 1 <;> ring

end LonelyRunnerNew.RoughRational
