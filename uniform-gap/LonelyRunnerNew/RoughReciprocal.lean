import LonelyRunnerNew.RoughRowPacking

noncomputable section
set_option autoImplicit false
namespace LonelyRunnerNew.RoughRational
attribute [local instance] Classical.propDecidable

theorem inv_abs_num {r : ℚ} (hr : 0<r) : (r⁻¹).num.natAbs=r.den := by
  simp [Rat.num_inv,Int.sign_eq_one_iff_pos.mpr (Rat.num_pos.mpr hr)]

theorem product_inv {r : ℚ} (hr : 0<r) : product r⁻¹=product r := by
  rw [product,product,inv_abs_num hr,Rat.den_inv_of_ne_zero hr.ne',Nat.mul_comm]

theorem roughPoint_inv {Y : ℕ} {r : ℚ} (hr : roughPoint Y r) : roughPoint Y r⁻¹ := by
  refine ⟨inv_pos.mpr hr.1,?_,?_⟩
  · rw [inv_abs_num hr.1];exact hr.2.2
  · rw [Rat.den_inv_of_ne_zero hr.1.ne'];exact hr.2.1

theorem crossHeight_inv {r s : ℚ} (hr : 0<r) (hs : 0<s) :
    crossHeight r⁻¹ s⁻¹=crossHeight r s := by
  simp only [crossHeight,inv_abs_num hr,inv_abs_num hs,
    Rat.den_inv_of_ne_zero hr.ne',Rat.den_inv_of_ne_zero hs.ne']
  simp [height,Nat.mul_comm,Nat.gcd_comm,max_comm]

def reciprocalSet (S : Finset ℚ) : Finset ℚ := S.image (fun r => r⁻¹)

theorem count_reciprocal (S : Finset ℚ) (T : ℝ) (hpos : ∀r∈S,0<r) :
    count (reciprocalSet S) T=count S T := by
  have he : (reciprocalSet S).filter (fun r => (product r:ℝ)≤T)=
      (S.filter (fun r => (product r:ℝ)≤T)).image (fun r => r⁻¹) := by
    ext r
    simp only [reciprocalSet,Finset.mem_filter,Finset.mem_image]
    constructor
    · rintro ⟨⟨s,hs,rfl⟩,ht⟩
      exact ⟨s,⟨hs,by simpa [product_inv (hpos s hs)] using ht⟩,rfl⟩
    · rintro ⟨s,⟨hs,ht⟩,rfl⟩
      exact ⟨⟨s,hs,rfl⟩,by simpa [product_inv (hpos s hs)] using ht⟩
  unfold count
  rw [he,Finset.card_image_iff.mpr]
  exact fun _ _ _ _ h => inv_injective h

theorem separated_reciprocal {S : Finset ℚ} {P : ℝ}
    (hpos : ∀r∈S,0<r) (hs : separated P S) : separated P (reciprocalSet S) := by
  intro r hr s hsm hne
  obtain ⟨r,hr0,rfl⟩ := Finset.mem_image.mp hr
  obtain ⟨s,hs0,rfl⟩ := Finset.mem_image.mp hsm
  rw [crossHeight_inv (hpos r hr0) (hpos s hs0)]
  exact hs r hr0 s hs0 (fun he => hne (congrArg Inv.inv he))

/-- Actual minimum of the reciprocal finite set supplies the strict upper
sector endpoint. No replacement of (1/(2R),1/R] by a half-open interval. -/
theorem reciprocal_sector {S : Finset ℚ} {R : ℝ} (hne : S.Nonempty) (hR : 0<R)
    (hpos : ∀r∈S,0<r) (hsector : ∀r∈S,R≤(r:ℝ) ∧ (r:ℝ)<2*R) :
    ∃ R' : ℝ, 1/(2*R)<R' ∧
      ∀r∈reciprocalSet S,R'≤(r:ℝ) ∧ (r:ℝ)<2*R' := by
  have hn : (reciprocalSet S).Nonempty := hne.image _
  let m := (reciprocalSet S).min' hn
  have hm : m∈reciprocalSet S := Finset.min'_mem _ _
  obtain ⟨s,hs,hsm⟩ := Finset.mem_image.mp hm
  have hmreal : (m:ℝ)=1/(s:ℝ) := by rw [← hsm]; simp
  have hspos : (0:ℝ)<(s:ℝ) := by exact_mod_cast hpos s hs
  have hl : 1/(2*R)<(m:ℝ) := by
    rw [hmreal]
    exact one_div_lt_one_div_of_lt hspos (hsector s hs).2
  refine ⟨(m:ℝ),hl,?_⟩
  intro r hr
  have hlo : (m:ℝ)≤(r:ℝ) := by exact_mod_cast Finset.min'_le _ _ hr
  obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hr
  have htpos : (0:ℝ)<(t:ℝ) := by exact_mod_cast hpos t ht
  have hhi : ((t⁻¹:ℚ):ℝ)≤1/R := by
    simpa using (one_div_le_one_div_of_le hR (hsector t ht).1)
  refine ⟨hlo,hhi.trans_lt ?_⟩
  have he : 2*(1/(2*R))=1/R := by field_simp <;> ring
  linarith

theorem reciprocal_sector_normalized {S : Finset ℚ} {R : ℝ} (hne : S.Nonempty)
    (hR : 0<R) (hsmall : R<1/Real.sqrt 2)
    (hpos : ∀r∈S,0<r) (hsector : ∀r∈S,R≤(r:ℝ) ∧ (r:ℝ)<2*R) :
    ∃ R' : ℝ, 1/Real.sqrt 2<R' ∧
      ∀r∈reciprocalSet S,R'≤(r:ℝ) ∧ (r:ℝ)<2*R' := by
  obtain ⟨R',hl,hs⟩ := reciprocal_sector hne hR hpos hsector
  have hsqrt : 0<Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have he : 1/(2*(1/Real.sqrt 2))=1/Real.sqrt 2 := by
    have hh := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
    field_simp
    nlinarith
  have hi := one_div_lt_one_div_of_lt (mul_pos (by norm_num) hR)
    (mul_lt_mul_of_pos_left hsmall (by norm_num : (0:ℝ)<2))
  rw [he] at hi
  exact ⟨R',hi.trans hl,hs⟩

/-- An equivalence of targets: the general R branch is completely discharged
by reciprocal transport, including cardinality and the half-open endpoint. -/
theorem largeRange_iff_normalized : LargeRangeCountBound ↔
    (∀(ell R T : ℝ),4096≤ell → 0<R → 1/Real.sqrt 2≤R → 0<T →
      Real.exp ell<Real.sqrt 2*T → ∀S : Finset ℚ,
      (∀r∈S,roughPoint 142 r) → (∀r∈S,R≤(r:ℝ) ∧ (r:ℝ)<2*R) →
      separated (Real.exp ell) S → (count S T:ℝ)≤1+(17/25:ℝ)*T/ell) := by
  constructor
  · intro h ell R T hell hR _ hT hlarge S hr hs hsep
    exact h ell R T hell hR hT hlarge S hr hs hsep
  · intro h ell R T hell hR hT hlarge S hr hs hsep
    by_cases hn : S.Nonempty
    · by_cases hl : 1/Real.sqrt 2≤R
      · exact h ell R T hell hR hl hT hlarge S hr hs hsep
      · obtain ⟨R',hR',hsector⟩ := reciprocal_sector_normalized hn hR
          (lt_of_not_ge hl) (fun r hrm => (hr r hrm).1) hs
        have hp : 0<R' := (one_div_pos.mpr (Real.sqrt_pos.mpr (by norm_num))).trans hR'
        have hb := h ell R' T hell hp hR'.le hT hlarge (reciprocalSet S)
          (by
            intro r hrm
            obtain ⟨s,hsm,rfl⟩ := Finset.mem_image.mp hrm
            exact roughPoint_inv (hr s hsm))
          hsector (separated_reciprocal (fun r hrm => (hr r hrm).1) hsep)
        rw [count_reciprocal S T (fun r hrm => (hr r hrm).1)] at hb
        exact hb
    · have he : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      subst S
      simp only [count,Finset.filter_empty,Finset.card_empty,Nat.cast_zero]
      have : 0<ell := by linarith
      positivity

end LonelyRunnerNew.RoughRational
