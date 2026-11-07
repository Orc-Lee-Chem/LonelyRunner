import LonelyRunnerNew.UnimodalGrid

noncomputable section
set_option autoImplicit false
open scoped BigOperators
open MeasureTheory
namespace LonelyRunnerNew.UnimodalGrid

theorem progression (g : ℝ → ℝ) {a d B M : ℝ} (ha : 0≤a) (hd : 0<d) (n : ℕ)
    (hlast : a+d*(n:ℝ)≤B) (hc : ContinuousOn g (Set.Icc a (a+d*(n:ℝ))))
    (hb : BetweenLower g 0 B) (hpos : ∀x∈Set.Icc 0 B,0≤g x)
    (hM : ∀x∈Set.Icc 0 B,g x≤M) (hInt : IntervalIntegrable g volume 0 B) :
    (∑i∈Finset.range (n+1),g (a+d*(i:ℝ)))≤(1/d)*(∫t in (0:ℝ)..B,g t)+M := by
  let f := fun t : ℝ => g (a+d*t)
  have hmap {t : ℝ} (ht : t∈Set.Icc 0 (n:ℝ)) : a+d*t∈Set.Icc a (a+d*(n:ℝ)) := by
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left ht.2 hd.le,mul_nonneg hd.le ht.1]
  have hglobal {t : ℝ} (ht : t∈Set.Icc 0 (n:ℝ)) : a+d*t∈Set.Icc 0 B := by
    have hh := hmap ht
    exact ⟨ha.trans hh.1,hh.2.trans hlast⟩
  have hfc : ContinuousOn f (Set.Icc 0 (n:ℝ)) := hc.comp
    (continuous_const.add (continuous_const.mul continuous_id)).continuousOn (fun t ht => hmap ht)
  have hfb : BetweenLower f 0 (n:ℝ) := by
    intro x hx z hz y hxy hyz
    exact hb _ (hglobal hx) _ (hglobal hz) _ (by nlinarith) (by nlinarith)
  have hfm : ∀i∈Finset.range (n+1),f (i:ℝ)≤M := by
    intro i hi
    apply hM
    apply hglobal
    have hn := Finset.mem_range.mp hi
    exact ⟨Nat.cast_nonneg _,by exact_mod_cast (by omega : i≤n)⟩
  have hu := unit_grid n f M hfc hfb hfm
  have he : (∫t in (0:ℝ)..(n:ℝ),f t)=(1/d)*(∫t in a..a+d*(n:ℝ),g t) := by
    have hh := intervalIntegral.integral_comp_add_mul (f:=g) (a:=(0:ℝ)) (b:=(n:ℝ)) hd.ne' a
    simpa only [f,mul_zero,add_zero,smul_eq_mul,one_div] using hh
  rw [he] at hu
  have hnn : a≤a+d*(n:ℝ) := by have hh := mul_nonneg hd.le (Nat.cast_nonneg n : (0:ℝ)≤n);linarith
  have hm := intervalIntegral.integral_mono_interval ha hnn hlast
    (ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx => hpos x ⟨hx.1.le,hx.2⟩)) hInt
  have hmul := mul_le_mul_of_nonneg_left hm (by positivity : (0:ℝ)≤1/d)
  exact hu.trans (by linarith)

def residue (m r : ℕ) : Finset ℕ := (Finset.Icc 1 m).filter (fun b => b%6=r)

theorem residue_image {m r : ℕ} (hr1 : 1≤r) (hr6 : r<6) (hrm : r≤m) :
    residue m r=(Finset.range ((m-r)/6+1)).image (fun i => r+6*i) := by
  ext b
  simp only [residue,Finset.mem_filter,Finset.mem_Icc,Finset.mem_image,Finset.mem_range]
  constructor
  · intro h
    refine ⟨b/6,?_,?_⟩ <;> omega
  · rintro ⟨i,hi,rfl⟩
    constructor <;> omega

theorem residue_sum (g : ℝ → ℝ) {B M : ℝ} (hB : 128≤B) (r : ℕ) (hr1 : 1≤r) (hr5 : r≤5)
    (hc : ContinuousOn g (Set.Icc (r:ℝ) B)) (hb : BetweenLower g 0 B)
    (hpos : ∀x∈Set.Icc 0 B,0≤g x) (hM : ∀x∈Set.Icc 0 B,g x≤M)
    (hInt : IntervalIntegrable g volume 0 B) :
    (∑b∈residue ⌊B⌋₊ r,g (b:ℝ))≤(1/6:ℝ)*(∫t in (0:ℝ)..B,g t)+M := by
  have hB0 : 0≤B := by linarith
  have hrm : r≤⌊B⌋₊ := (Nat.le_floor_iff hB0).mpr (by
    have hrR : (r:ℝ)≤5 := by exact_mod_cast hr5
    linarith)
  let n := (⌊B⌋₊-r)/6
  have hlastNat : r+6*n≤⌊B⌋₊ := by dsimp only [n];omega
  have hlast : (r:ℝ)+6*(n:ℝ)≤B := by
    have hh : (r:ℝ)+6*(n:ℝ)≤⌊B⌋₊ := by exact_mod_cast hlastNat
    exact hh.trans (Nat.floor_le hB0)
  have hg := progression g (a:=(r:ℝ)) (d:=6) (Nat.cast_nonneg _) (by norm_num) n hlast
    (hc.mono (by intro x hx;exact ⟨hx.1,hx.2.trans hlast⟩)) hb hpos hM hInt
  rw [residue_image hr1 (by omega) hrm,Finset.sum_image]
  · simpa only [n,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hg
  · intro i hi j hj he
    change r+6*i=r+6*j at he
    omega

theorem two_residue_sum (g : ℝ → ℝ) {B M : ℝ} (hB : 128≤B)
    (hc : ContinuousOn g (Set.Icc 1 B)) (hb : BetweenLower g 0 B)
    (hpos : ∀x∈Set.Icc 0 B,0≤g x) (hM : ∀x∈Set.Icc 0 B,g x≤M)
    (hInt : IntervalIntegrable g volume 0 B) :
    (∑b∈(Finset.Icc 1 ⌊B⌋₊).filter (fun b => b%6=1 ∨ b%6=5),g (b:ℝ))≤
      (1/3:ℝ)*(∫t in (0:ℝ)..B,g t)+2*M := by
  have h1 := residue_sum g hB 1 (by norm_num) (by norm_num) (by simpa only [Nat.cast_one] using hc) hb hpos hM hInt
  have h5 := residue_sum g hB 5 (by norm_num) (by norm_num)
    (hc.mono (by intro x hx;norm_num only [Nat.cast_ofNat] at hx;exact ⟨by linarith [hx.1],hx.2⟩)) hb hpos hM hInt
  have hd : Disjoint (residue ⌊B⌋₊ 1) (residue ⌊B⌋₊ 5) := by
    apply Finset.disjoint_left.mpr
    intro b hb1 hb5
    have h1 := (Finset.mem_filter.mp hb1).2
    have h5 := (Finset.mem_filter.mp hb5).2
    omega
  have he : (Finset.Icc 1 ⌊B⌋₊).filter (fun b => b%6=1 ∨ b%6=5)=
      (residue ⌊B⌋₊ 1)∪(residue ⌊B⌋₊ 5) := by ext b;simp [residue];tauto
  rw [he,Finset.sum_union hd]
  linarith

end LonelyRunnerNew.UnimodalGrid
