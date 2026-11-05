import LonelyRunnerNew.AsymmetricPacking

noncomputable section
set_option autoImplicit false
namespace LonelyRunnerNew.RoughRational
attribute [local instance] Classical.propDecidable

theorem rough_small_eq_one {Y x : ℕ} (hx : rough Y x) (hle : x≤Y) : x=1 := by
  by_contra hn
  obtain ⟨p,hp,hpd⟩ := Nat.exists_prime_and_dvd hn
  exact hx.2 p hp ((Nat.le_of_dvd hx.1 hpd).trans hle) hpd

theorem rough_below_square_prime {X x : ℕ} (hx : rough X x) (hsmall : x<X^2) :
    x=1 ∨ Nat.Prime x := by
  by_cases h1 : x=1
  · exact Or.inl h1
  right
  by_contra hn
  have hp := Nat.minFac_prime h1
  have hd := Nat.minFac_dvd x
  have hl : X<x.minFac := lt_of_not_ge (fun h => hx.2 _ hp h hd)
  have hh := Nat.minFac_sq_le_self hx.1 hn
  nlinarith

theorem small_B_denominator_one {R T : ℝ} (hR : 0<R) (hT : 0<T)
    (hB : Real.sqrt (T/R)<128) {r : ℚ} (hr : roughPoint 142 r)
    (hl : R≤(r:ℝ)) (ht : (product r:ℝ)≤T) : r.den=1 := by
  have hb := denominator_le_floor hR hT r hr.1 hl ht
  have hf : (⌊Real.sqrt (T/R)⌋₊:ℝ)<128 :=
    (Nat.floor_le (Real.sqrt_nonneg _)).trans_lt hB
  have hn : r.den≤142 := by
    have h : ⌊Real.sqrt (T/R)⌋₊<128 := by exact_mod_cast hf
    omega
  exact rough_small_eq_one hr.2.2 hn

theorem small_B_count_one_row (S : Finset ℚ) {R T : ℝ} (hR : 0<R) (hT : 0<T)
    (hB : Real.sqrt (T/R)<128) (hrough : ∀r∈S,roughPoint 142 r)
    (hl : ∀r∈S,R≤(r:ℝ)) : count S T=rowCount S T 0 := by
  unfold count rowCount countedSet
  congr 1
  ext r
  simp only [Finset.mem_filter,Nat.zero_add]
  constructor
  · intro h
    exact ⟨h,small_B_denominator_one hR hT hB (hrough r h.1) (hl r h.1) h.2⟩
  · exact fun h => h.1

theorem row_numerator_injective (S : Finset ℚ) (T : ℝ) (i : ℕ)
    (hpos : ∀r∈S,0<r) :
    Set.InjOn (fun r : ℚ => r.num.natAbs) (rowSet S T i:Set ℚ) := by
  intro r hr s hs he
  have hrS := (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).1
  have hsS := (Finset.mem_filter.mp (Finset.mem_filter.mp hs).1).1
  have hrd := (Finset.mem_filter.mp hr).2
  have hsd := (Finset.mem_filter.mp hs).2
  change r.num.natAbs=s.num.natAbs at he
  rw [rat_eq_abs_num_div_den r (hpos r hrS),rat_eq_abs_num_div_den s (hpos s hsS),he,hrd,hsd]

/-- The new asymmetric packing bound is applied to the actual original
rational denominator fibre, rather than an unrelated natural-number model. -/
theorem row_asymmetric_packing (S : Finset ℚ) {R T P : ℝ} (hR : 0<R) (hT : 0<T)
    (i X Z : ℕ) (hZ : 0<Z) (hX : Z^2≤X) (hP : ((X*Z:ℕ):ℝ)≤P)
    (hrough : ∀r∈S,roughPoint 142 r)
    (hsector : ∀r∈S,R≤(r:ℝ) ∧ (r:ℝ)<2*R) (hsep : separated P S) :
    (rowCount S T i:ℝ)≤
      (roughIntegerInterval X (R*(i+1:ℝ)) (min (2*R*(i+1:ℝ)) (T/(i+1:ℝ)))).card+
      (roughIntegerInterval X 1 ((min (2*R*(i+1:ℝ)) (T/(i+1:ℝ)))/143)).card+
      (min (2*R*(i+1:ℝ)) (T/(i+1:ℝ)))/(Z:ℝ) := by
  let N := (rowSet S T i).image (fun r : ℚ => r.num.natAbs)
  have hn (x : ℕ) (hx : x∈N) : ∃r∈rowSet S T i,r.num.natAbs=x := Finset.mem_image.mp hx
  have hroughN : ∀x∈N,rough 142 x := by
    intro x hx
    obtain ⟨r,hr,rfl⟩ := hn x hx
    exact (hrough r (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).1).2.1
  have hb : ∀x∈N,R*(i+1:ℝ)≤(x:ℝ) ∧
      (x:ℝ)≤min (2*R*(i+1:ℝ)) (T/(i+1:ℝ)) := by
    intro x hx
    obtain ⟨r,hr,rfl⟩ := hn x hx
    exact row_numerator_bounds S hR i (fun r hr => (hrough r hr).1) hsector hr
  have hs : Asymmetric.numeratorsSeparated P N := by
    intro x hx y hy hne
    obtain ⟨r,hr,rfl⟩ := hn x hx
    obtain ⟨s,hs,rfl⟩ := hn y hy
    have hh := hsep r (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).1
      s (Finset.mem_filter.mp (Finset.mem_filter.mp hs).1).1 (fun he => hne (congrArg (fun t : ℚ => t.num.natAbs) he))
    simpa only [row_crossHeight S T i hr hs] using hh
  have hpack := Asymmetric.asymmetric_packing N 142 X Z hZ hX hP
    (by positivity : (0:ℝ)≤min (2*R*(i+1:ℝ)) (T/(i+1:ℝ))) hroughN hb hs
  have hc : N.card=rowCount S T i := Finset.card_image_iff.mpr
    (row_numerator_injective S T i (fun r hr => (hrough r hr).1))
  rw [hc] at hpack
  norm_num only [Nat.cast_ofNat] at hpack
  exact hpack

end LonelyRunnerNew.RoughRational
