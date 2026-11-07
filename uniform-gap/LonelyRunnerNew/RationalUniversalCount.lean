import LonelyRunnerNew.RationalCountProved

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew.RoughRational

/-- Universal counting without separation or roughness. Reduction is the
standard rational numerator/denominator, and the map keeps every distinct r. -/
theorem count_le_sqrt_two (S : Finset ℚ) {R T : ℝ} (hR : 0<R) (hT : 0<T)
    (hpos : ∀ r∈S,0<r) (hsector : ∀ r∈S,R≤(r:ℝ) ∧ (r:ℝ)<2*R) :
    (count S T:ℝ)≤Real.sqrt 2*T := by
  classical
  let F := countedSet S T
  let a := ⌊Real.sqrt (2*R*T)⌋₊
  let b := ⌊Real.sqrt (T/R)⌋₊
  let G := (Finset.Icc 1 a).product (Finset.Icc 1 b)
  let f : ℚ → ℕ × ℕ := fun r => (r.num.natAbs,r.den)
  have hmap (r : ℚ) (hr : r∈F) : f r∈G := by
    have hm := Finset.mem_filter.mp hr
    have hp := hpos r hm.1
    have hd : (0:ℝ)<r.den := by exact_mod_cast r.pos
    have hn : (0:ℝ)<r.num.natAbs := by exact_mod_cast Int.natAbs_pos.mpr (Rat.num_pos.mpr hp).ne'
    have hu := (hsector r hm.1).2
    rw [cast_eq_abs_num_div_den r hp] at hu
    have hu' := (div_lt_iff₀ hd).mp hu
    have hprod : (r.num.natAbs:ℝ)*(r.den:ℝ)≤T := by simpa [product] using hm.2
    have hsq : (r.num.natAbs:ℝ)^2≤2*R*T := by
      have h1 := mul_le_mul_of_nonneg_right hu'.le hn.le
      have h2 := mul_le_mul_of_nonneg_left hprod (by positivity : (0:ℝ)≤2*R)
      nlinarith
    have hnum : r.num.natAbs≤a := (Nat.le_floor_iff (Real.sqrt_nonneg _)).mpr
      ((Real.le_sqrt hn.le (by positivity)).mpr hsq)
    have hden : r.den≤b := denominator_le_floor hR hT r hp (hsector r hm.1).1 hm.2
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨by exact_mod_cast hn,hnum⟩,
      Finset.mem_Icc.mpr ⟨r.pos,hden⟩⟩
  have hinj : Set.InjOn f (F:Set ℚ) := by
    intro r hr s hs he
    have hm := Prod.mk.inj he
    rw [rat_eq_abs_num_div_den r (hpos r (Finset.mem_filter.mp hr).1),
      rat_eq_abs_num_div_den s (hpos s (Finset.mem_filter.mp hs).1),hm.1,hm.2]
  have hc : F.card≤G.card := Finset.card_le_card_of_injOn f hmap hinj
  have hGn : G.card=a*b := by simp [G]
  rw [hGn] at hc
  have hcR : (count S T:ℝ)≤(a:ℝ)*(b:ℝ) := by exact_mod_cast hc
  have ha : (a:ℝ)≤Real.sqrt (2*R*T) := Nat.floor_le (Real.sqrt_nonneg _)
  have hb : (b:ℝ)≤Real.sqrt (T/R) := Nat.floor_le (Real.sqrt_nonneg _)
  have hmul := mul_le_mul ha hb (Nat.cast_nonneg b) (Real.sqrt_nonneg _)
  have heq : Real.sqrt (2*R*T)*Real.sqrt (T/R)=Real.sqrt 2*T := by
    apply (sq_eq_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (mul_nonneg (Real.sqrt_nonneg _) hT.le)).mp
    rw [mul_pow,mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
    field_simp
    <;> ring
  exact hcR.trans (hmul.trans_eq heq)

end LonelyRunnerNew.RoughRational
