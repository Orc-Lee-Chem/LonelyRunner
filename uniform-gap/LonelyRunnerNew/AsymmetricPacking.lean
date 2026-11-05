import LonelyRunnerNew.AsymmetricFactors

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew.RoughRational.Asymmetric
attribute [local instance] Classical.propDecidable

def numeratorsSeparated (P : ℝ) (S : Finset ℕ) : Prop :=
  ∀x∈S,∀y∈S,x≠y → P<height x y

/-- Algebraic collision bound for unequal numerator-dependent divisors. -/
theorem allocation_collision {x y d e j k X Z : ℕ}
    (hx : 0<x) (hy : 0<y) (hd : 0<d) (he : 0<e)
    (hdx : d∣x) (hey : e∣y) (hj : 0<j) (hk : 0<k)
    (hdX : d≤X) (heX : e≤X) (hjZ : j≤Z) (hkZ : k≤Z)
    (h : x/d*j=y/e*k) : height x y≤((X*Z:ℕ):ℝ) := by
  have hmul := congrArg (fun n : ℕ => n*(d*e)) h
  have hcross : x*(j*e)=y*(k*d) := by
    calc
      x*(j*e) = (x/d*j)*(d*e) := by
        conv_lhs => rw [←Nat.div_mul_cancel hdx]
        ring
      _ = (y/e*k)*(d*e) := hmul
      _ = y*(k*d) := by
        conv_rhs => rw [←Nat.div_mul_cancel hey]
        ring
  apply (height_le_of_cross_product hx hy (mul_pos hj he) hcross).trans
  exact_mod_cast max_le (by nlinarith [Nat.mul_le_mul hjZ heX] : j*e≤X*Z)
    (by nlinarith [Nat.mul_le_mul hkZ hdX] : k*d≤X*Z)

theorem allocated_injective (S : Finset ℕ) (d : ℕ → ℕ) (X Z : ℕ) (P : ℝ)
    (hpos : ∀x∈S,0<x) (hsep : numeratorsSeparated P S)
    (hP : ((X*Z:ℕ):ℝ)≤P)
    (hd : ∀x∈S,0<d x ∧ d x≤X ∧ d x∣x) :
    Set.InjOn (fun z : ℕ × ℕ => z.1/d z.1*z.2) (S.product (Finset.Icc 1 Z):Set (ℕ × ℕ)) := by
  intro z hz w hw h
  obtain ⟨hzS,hzJ⟩ := Finset.mem_product.mp hz
  obtain ⟨hwS,hwJ⟩ := Finset.mem_product.mp hw
  obtain ⟨hz1,hzZ⟩ := Finset.mem_Icc.mp hzJ
  obtain ⟨hw1,hwZ⟩ := Finset.mem_Icc.mp hwJ
  have heq : z.1=w.1 := by
    by_contra hn
    have hle := allocation_collision (hpos _ hzS) (hpos _ hwS) (hd _ hzS).1
      (hd _ hwS).1 (hd _ hzS).2.2 (hd _ hwS).2.2 hz1 hw1
      (hd _ hzS).2.1 (hd _ hwS).2.1 hzZ hwZ h
    exact (not_lt_of_ge (hle.trans hP)) (hsep _ hzS _ hwS hn)
  have hdivpos : 0<w.1/d w.1 := Nat.div_pos
    (Nat.le_of_dvd (hpos _ hwS) (hd _ hwS).2.2) (hd _ hwS).1
  have hj : z.2=w.2 := by
    change z.1/d z.1*z.2=w.1/d w.1*w.2 at h
    rw [heq] at h
    exact mul_left_cancel₀ hdivpos.ne' h
  exact Prod.ext heq hj

theorem allocated_card (S : Finset ℕ) (d : ℕ → ℕ) (X Z : ℕ) (P A : ℝ)
    (hA : 0≤A) (hpos : ∀x∈S,0<x) (hsep : numeratorsSeparated P S)
    (hP : ((X*Z:ℕ):ℝ)≤P)
    (hd : ∀x∈S,0<d x ∧ d x≤X ∧ d x∣x ∧ ((x/d x:ℕ):ℝ)*(Z:ℝ)≤A) :
    (S.card:ℝ)*(Z:ℝ)≤A := by
  let F := S.product (Finset.Icc 1 Z)
  let f := fun z : ℕ × ℕ => z.1/d z.1*z.2
  have hinj := allocated_injective S d X Z P hpos hsep hP
    (fun x hx => ⟨(hd x hx).1,(hd x hx).2.1,(hd x hx).2.2.1⟩)
  have hsub : F.image f⊆Finset.Icc 1 ⌊A⌋₊ := by
    intro n hn
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hx,hj⟩ := Finset.mem_product.mp hz
    obtain ⟨hj1,hjZ⟩ := Finset.mem_Icc.mp hj
    have hp : 0<z.1/d z.1 := Nat.div_pos (Nat.le_of_dvd (hpos _ hx) (hd _ hx).2.2.1) (hd _ hx).1
    refine Finset.mem_Icc.mpr ⟨mul_pos hp hj1,?_⟩
    apply (Nat.le_floor_iff hA).mpr
    change ((z.1/d z.1*z.2:ℕ):ℝ)≤A
    rw [Nat.cast_mul]
    apply (mul_le_mul_of_nonneg_left (by exact_mod_cast hjZ : (z.2:ℝ)≤Z) (Nat.cast_nonneg _)).trans
    exact (hd _ hx).2.2.2
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_iff.mpr hinj] at hc
  have hnat : S.card*Z≤⌊A⌋₊ := by
    simpa only [F,Finset.product_eq_sprod,Finset.card_product,Nat.card_Icc,Nat.add_sub_cancel] using hc
  exact (by exact_mod_cast hnat : (S.card:ℝ)*Z≤⌊A⌋₊).trans (Nat.floor_le hA)

theorem low_remainder_card (S : Finset ℕ) (X Z : ℕ) {P A : ℝ}
    (hZ : 0<Z) (hX : Z^2≤X) (hP : ((X*Z:ℕ):ℝ)≤P) (hA : 0≤A)
    (hpos : ∀x∈S,0<x) (hbound : ∀x∈S,(x:ℝ)≤A)
    (hsep : numeratorsSeparated P S)
    (hrem : ∀x∈S,(remainder X x:ℝ)≤A/(X:ℝ)) :
    (S.card:ℝ)≤A/(Z:ℝ) := by
  have hex : ∀x∈S,∃d : ℕ,0<d ∧ d≤X ∧ d∣x ∧ ((x/d:ℕ):ℝ)*(Z:ℝ)≤A :=
    fun x hx => allocation_divisor hZ hX (hpos x hx) (hbound x hx) (hrem x hx)
  let d : ℕ → ℕ := fun x => if h:x∈S then Classical.choose (hex x h) else 1
  have hd (x : ℕ) (hx : x∈S) : 0<d x ∧ d x≤X ∧ d x∣x ∧ ((x/d x:ℕ):ℝ)*(Z:ℝ)≤A := by
    simpa only [d,dif_pos hx] using Classical.choose_spec (hex x hx)
  exact (le_div_iff₀ (by exact_mod_cast hZ : (0:ℝ)<Z)).mpr
    (allocated_card S d X Z P A hA hpos hsep hP hd)

theorem high_remainder_injective (S : Finset ℕ) (X : ℕ) {P A : ℝ}
    (hX : 0<X) (hXP : (X:ℝ)≤P) (hA : 0≤A)
    (hpos : ∀x∈S,0<x) (hbound : ∀x∈S,(x:ℝ)≤A)
    (hsep : numeratorsSeparated P S)
    (hrem : ∀x∈S,A/(X:ℝ)<(remainder X x:ℝ)) :
    Set.InjOn (remainder X) (S:Set ℕ) := by
  have hu (x : ℕ) (hx : x∈S) : (smooth X x:ℝ)<X := by
    have hr : (0:ℝ)<remainder X x := by exact_mod_cast remainder_pos X x
    have he : (x:ℝ)=(remainder X x:ℝ)*(smooth X x:ℝ) := by exact_mod_cast (decomposition X (hpos x hx)).symm
    have hb := (div_lt_iff₀ (by exact_mod_cast hX : (0:ℝ)<X)).mp (hrem x hx)
    nlinarith [hbound x hx]
  intro x hx y hy heq
  by_contra hn
  have hh := hsep x hx y hy hn
  rw [←decomposition X (hpos x hx),←decomposition X (hpos y hy),heq,
    height_mul_left _ _ _ (remainder_pos X y)] at hh
  have hb := height_le_max (smooth_pos X x) (y:=smooth X y)
  have hm : ((max (smooth X x) (smooth X y):ℕ):ℝ)<X := by
    rw [Nat.cast_max]
    exact max_lt (hu x hx) (hu y hy)
  exact (not_lt_of_ge (hb.trans hm.le |>.trans hXP)) hh

theorem high_remainder_card (S : Finset ℕ) (Y X : ℕ) {P U A : ℝ}
    (hX : 0<X) (hXP : (X:ℝ)≤P) (hA : 0≤A)
    (hrough : ∀x∈S,rough Y x) (hbound : ∀x∈S,U≤(x:ℝ) ∧ (x:ℝ)≤A)
    (hsep : numeratorsSeparated P S)
    (hrem : ∀x∈S,A/(X:ℝ)<(remainder X x:ℝ)) :
    S.card≤(roughIntegerInterval X U A).card+(roughIntegerInterval X 1 (A/(Y+1:ℝ))).card := by
  have hinj := high_remainder_injective S X hX hXP hA (fun x hx => (hrough x hx).1)
    (fun x hx => (hbound x hx).2) hsep hrem
  have hsub : S.image (remainder X)⊆(roughIntegerInterval X U A)∪
      (roughIntegerInterval X 1 (A/(Y+1:ℝ))) := by
    intro r hr
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hr
    have he := decomposition X (hrough x hx).1
    have heR : (remainder X x:ℝ)*(smooth X x:ℝ)=(x:ℝ) := by exact_mod_cast he
    by_cases hu : smooth X x=1
    · apply Finset.mem_union_left
      have hxrem : remainder X x=x := by simpa [hu] using he
      rw [hxrem]
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr
        ((Nat.le_floor_iff hA).mpr (hbound x hx).2)),by simpa [hxrem] using remainder_rough X x,(hbound x hx).1⟩
    · apply Finset.mem_union_right
      have hy := smooth_ge_of_rough (hrough x hx) hu
      have hle : (remainder X x:ℝ)≤A/(Y+1:ℝ) := by
        apply (le_div_iff₀ (by positivity)).mpr
        have hh := mul_le_mul_of_nonneg_left (by exact_mod_cast hy : (Y+1:ℝ)≤smooth X x)
          (Nat.cast_nonneg (remainder X x): (0:ℝ)≤_)
        exact hh.trans (heR.le.trans (hbound x hx).2)
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr
        ((Nat.le_floor_iff (by positivity)).mpr hle)),remainder_rough X x,by exact_mod_cast remainder_pos X x⟩
  calc
    S.card=(S.image (remainder X)).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ ((roughIntegerInterval X U A)∪(roughIntegerInterval X 1 (A/(Y+1:ℝ)))).card := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _

/-- Fully proved unbounded asymmetric packing, with actual X-rough interval
counts and no analytic sieve hypothesis. Closed real endpoints are retained. -/
theorem asymmetric_packing (S : Finset ℕ) (Y X Z : ℕ) {P U A : ℝ}
    (hZ : 0<Z) (hX : Z^2≤X) (hP : ((X*Z:ℕ):ℝ)≤P) (hA : 0≤A)
    (hrough : ∀x∈S,rough Y x) (hbound : ∀x∈S,U≤(x:ℝ) ∧ (x:ℝ)≤A)
    (hsep : numeratorsSeparated P S) :
    (S.card:ℝ)≤(roughIntegerInterval X U A).card+
      (roughIntegerInterval X 1 (A/(Y+1:ℝ))).card+A/(Z:ℝ) := by
  let H := S.filter (fun x => A/(X:ℝ)<(remainder X x:ℝ))
  let L := S.filter (fun x => ¬A/(X:ℝ)<(remainder X x:ℝ))
  have hXpos : 0<X := lt_of_lt_of_le (pow_pos hZ _) hX
  have hXP : (X:ℝ)≤P := by
    have h1 : X≤X*Z := by nlinarith
    exact (by exact_mod_cast h1 : (X:ℝ)≤((X*Z:ℕ):ℝ)).trans hP
  have hH := high_remainder_card H Y X hXpos hXP hA
    (fun x hx => hrough x (Finset.mem_filter.mp hx).1)
    (fun x hx => hbound x (Finset.mem_filter.mp hx).1)
    (fun x hx y hy => hsep x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1)
    (fun x hx => (Finset.mem_filter.mp hx).2)
  have hL := low_remainder_card L X Z hZ hX hP hA
    (fun x hx => (hrough x (Finset.mem_filter.mp hx).1).1)
    (fun x hx => (hbound x (Finset.mem_filter.mp hx).1).2)
    (fun x hx y hy => hsep x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1)
    (fun x hx => le_of_not_gt (Finset.mem_filter.mp hx).2)
  have hc : H.card+L.card=S.card := Finset.card_filter_add_card_filter_not _
  have hcR : (S.card:ℝ)=(H.card:ℝ)+(L.card:ℝ) := by exact_mod_cast hc.symm
  have hhR : (H.card:ℝ)≤(roughIntegerInterval X U A).card+
      (roughIntegerInterval X 1 (A/(Y+1:ℝ))).card := by exact_mod_cast hH
  linarith

end LonelyRunnerNew.RoughRational.Asymmetric
