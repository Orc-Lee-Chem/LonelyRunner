import LonelyRunnerNew.PeriodicLevelDilation
import LonelyRunnerNew.ForbiddenExcess

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators
namespace LonelyRunnerNew
attribute [local instance] Classical.propDecidable

def bohrPrototypes (V : Finset ℕ) : Finset (Σ _ : ℕ,ℕ) :=
  V.sigma (fun v => Finset.range v)
def bohrCenter (ij : Σ _ : ℕ,ℕ) : ℝ := (ij.2:ℝ)/(ij.1:ℝ)
def bohrRadius (ij : Σ _ : ℕ,ℕ) : ℝ := 1/(ij.1:ℝ)
def bohrMultiplicity (V : Finset ℕ) (r x : ℝ) : ℝ :=
  ∑ v∈V,(forbidden v r).indicator (fun _ => (1:ℝ)) x

theorem prototype_forbidden {v k : ℕ} (hv : 0<v) {r x : ℝ}
    (h : x∈PeriodicArc.arc ((k:ℝ)/(v:ℝ)) (r/(v:ℝ))) : x∈forbidden v r := by
  obtain ⟨j,hj⟩ := h
  refine ⟨(k:ℤ)+(v:ℤ)*j,?_⟩
  have hvR : 0<(v:ℝ) := by exact_mod_cast hv
  have hh := (mul_le_mul_of_nonneg_left hj hvR.le)
  have he : (v:ℝ)*|x-(k:ℝ)/(v:ℝ)-(j:ℝ)|=
      |(v:ℝ)*x-((k:ℤ)+(v:ℤ)*j:ℤ)| := by
    rw [show (v:ℝ)*|x-(k:ℝ)/(v:ℝ)-(j:ℝ)|=|(v:ℝ)*(x-(k:ℝ)/(v:ℝ)-(j:ℝ))| by
      rw [abs_mul,abs_of_pos hvR]]
    congr 1
    push_cast
    field_simp
    ring
  rw [he,mul_div_cancel₀ _ hvR.ne'] at hh
  exact hh

theorem forbidden_prototype {v : ℕ} (hv : 0<v) {r x : ℝ}
    (h : x∈forbidden v r) :
    ∃ k∈Finset.range v,x∈PeriodicArc.arc ((k:ℝ)/(v:ℝ)) (r/(v:ℝ)) := by
  obtain ⟨j,hj⟩ := h
  let k := (j%(v:ℤ)).toNat
  have hvI : (0:ℤ)<v := by exact_mod_cast hv
  have hk0 := Int.emod_nonneg j hvI.ne'
  have hkv := Int.emod_lt_of_pos j hvI
  have hkcast : (k:ℤ)=j%(v:ℤ) := Int.toNat_of_nonneg hk0
  have hk : k<v := by exact_mod_cast (show (k:ℤ)<(v:ℤ) by rwa [hkcast])
  refine ⟨k,Finset.mem_range.mpr hk,j/(v:ℤ),?_⟩
  have hvR : 0<(v:ℝ) := by exact_mod_cast hv
  have heI : (v:ℤ)*(j/(v:ℤ))+(k:ℤ)=j := by
    rw [hkcast]
    exact Int.mul_ediv_add_emod j (v:ℤ)
  have heR := congrArg (fun z : ℤ => (z:ℝ)) heI
  push_cast at heR
  change |x-(k:ℝ)/(v:ℝ)-((j/(v:ℤ):ℤ):ℝ)|≤r/(v:ℝ)
  apply (le_div_iff₀ hvR).mpr
  rw [show |x-(k:ℝ)/(v:ℝ)-((j/(v:ℤ):ℤ):ℝ)| * (v:ℝ)=
      |(x-(k:ℝ)/(v:ℝ)-((j/(v:ℤ):ℤ):ℝ))*(v:ℝ)| by rw [abs_mul,abs_of_pos hvR]]
  have he : (x-(k:ℝ)/(v:ℝ)-((j/(v:ℤ):ℤ):ℝ))*(v:ℝ)=(v:ℝ)*x-(j:ℝ) := by
    field_simp
    nlinarith only [heR]
  rwa [he]

theorem prototype_unique {v k l : ℕ} (hv : 0<v) (hk : k<v) (hl : l<v)
    {r x : ℝ} (hr : r<1/2)
    (ha : x∈PeriodicArc.arc ((k:ℝ)/(v:ℝ)) (r/(v:ℝ)))
    (hb : x∈PeriodicArc.arc ((l:ℝ)/(v:ℝ)) (r/(v:ℝ))) : k=l := by
  obtain ⟨j,hj⟩ := ha
  obtain ⟨j',hj'⟩ := hb
  have hnear (z : ℕ) (a : ℤ) (hh : |x-(z:ℝ)/(v:ℝ)-(a:ℝ)|≤r/(v:ℝ)) :
      |(v:ℝ)*x-((z:ℤ)+(v:ℤ)*a:ℤ)|≤r := by
    have hvR : 0<(v:ℝ) := by exact_mod_cast hv
    have hh' := mul_le_mul_of_nonneg_left hh hvR.le
    have he : (v:ℝ)*|x-(z:ℝ)/(v:ℝ)-(a:ℝ)|=
        |(v:ℝ)*x-((z:ℤ)+(v:ℤ)*a:ℤ)| := by
      rw [show (v:ℝ)*|x-(z:ℝ)/(v:ℝ)-(a:ℝ)|=|(v:ℝ)*(x-(z:ℝ)/(v:ℝ)-(a:ℝ))| by
        rw [abs_mul,abs_of_pos hvR]]
      congr 1
      push_cast
      field_simp
      ring
    rwa [he,mul_div_cancel₀ _ hvR.ne'] at hh'
  have hq := PeriodicArc.turn_unique (x:=(v:ℝ)*x) (c:=0)
    (j:=(k:ℤ)+(v:ℤ)*j) (l:=(l:ℤ)+(v:ℤ)*j') hr
    (by simpa using hnear k j hj) (by simpa using hnear l j' hj')
  have he := congrArg (fun z : ℤ => z%(v:ℤ)) hq
  have hkI : (0:ℤ)≤k := by exact_mod_cast Nat.zero_le k
  have hlI : (0:ℤ)≤l := by exact_mod_cast Nat.zero_le l
  have hkV : (k:ℤ)<v := by exact_mod_cast hk
  have hlV : (l:ℤ)<v := by exact_mod_cast hl
  simpa [Int.add_emod,Int.mul_emod,Int.emod_eq_of_lt hkI hkV,Int.emod_eq_of_lt hlI hlV] using he

theorem prototype_indicator_sum {v : ℕ} (hv : 0<v) (r x : ℝ) (hr : r<1/2) :
    (∑ k∈Finset.range v,(PeriodicArc.arc ((k:ℝ)/(v:ℝ)) (r/(v:ℝ))).indicator (fun _ => (1:ℝ)) x)=
      (forbidden v r).indicator (fun _ => (1:ℝ)) x := by
  by_cases hx : x∈forbidden v r
  · obtain ⟨k,hk,hkx⟩ := forbidden_prototype hv hx
    rw [Set.indicator_of_mem hx]
    rw [Finset.sum_eq_single k]
    · rw [Set.indicator_of_mem hkx]
    · intro l hl hlk
      apply Set.indicator_of_notMem
      intro hlx
      exact hlk (prototype_unique hv (Finset.mem_range.mp hl) (Finset.mem_range.mp hk) hr hlx hkx)
    · exact fun h => (h hk).elim
  · rw [Set.indicator_of_notMem hx]
    apply Finset.sum_eq_zero
    intro k _
    exact Set.indicator_of_notMem (fun h => hx (prototype_forbidden hv h)) _

theorem bohrMultiplicity_eq_prototypes (V : Finset ℕ) (hV : positive V)
    (r x : ℝ) (hr : r<1/2) :
    PeriodicArc.multiplicity (bohrPrototypes V) bohrCenter (fun ij => r*bohrRadius ij) x=
      bohrMultiplicity V r x := by
  unfold PeriodicArc.multiplicity bohrPrototypes bohrMultiplicity
  rw [Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro v hv
  simpa [bohrCenter,bohrRadius,div_eq_mul_inv] using prototype_indicator_sum (hV v hv) r x hr

theorem bohr_level_dilation (V : Finset ℕ) (hV : positive V) (k : ℕ) {s t : ℝ}
    (hs : 0<s) (hst : s≤t) (ht : t<1/2) :
    (∫ x in (0:ℝ)..1,IntervalCoverage.tail (bohrMultiplicity V s x) k)/s≤
      (∫ x in (0:ℝ)..1,IntervalCoverage.tail (bohrMultiplicity V t x) k)/t := by
  have hrad : ∀ ij∈bohrPrototypes V,0<bohrRadius ij ∧ bohrRadius ij≤1 := by
    intro ij hij
    have hv := hV ij.1 (Finset.mem_sigma.mp hij).1
    have hvR : (1:ℝ) ≤ ij.1 := by exact_mod_cast hv
    exact ⟨one_div_pos.mpr (lt_of_lt_of_le zero_lt_one hvR),by
      simpa [bohrRadius] using one_div_le_one_div_of_le zero_lt_one hvR⟩
  have hcent : ∀ ij∈bohrPrototypes V,0≤bohrCenter ij ∧ bohrCenter ij<1 := by
    intro ij hij
    obtain ⟨hi,hj⟩ := Finset.mem_sigma.mp hij
    have hvR : (0:ℝ) < ij.1 := by exact_mod_cast hV ij.1 hi
    exact ⟨div_nonneg (Nat.cast_nonneg _) hvR.le,(div_lt_one hvR).mpr (by exact_mod_cast Finset.mem_range.mp hj)⟩
  have hsmall : ∀ ij∈bohrPrototypes V,t*bohrRadius ij<1/2 := fun ij hij =>
    (mul_le_of_le_one_right (hs.trans_le hst).le (hrad ij hij).2).trans_lt ht
  have heq (a : ℝ) (ha : a<1/2) :
      PeriodicArc.level (bohrPrototypes V) bohrCenter (fun ij => a*bohrRadius ij) k=
        fun x => IntervalCoverage.tail (bohrMultiplicity V a x) k := by
    funext x
    rw [PeriodicArc.level,bohrMultiplicity_eq_prototypes V hV a x ha]
  have hh := PeriodicArc.level_dilation (bohrPrototypes V) bohrCenter bohrRadius k hs hst hcent
    (fun ij hij => (hrad ij hij).1.le) hsmall
  rwa [heq s (hst.trans_lt ht),heq t ht] at hh

end LonelyRunnerNew
