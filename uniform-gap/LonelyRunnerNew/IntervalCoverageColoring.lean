import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Finset.Image
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Push

noncomputable section
set_option autoImplicit false
namespace LonelyRunnerNew.IntervalCoverage
variable {ι : Type*} [DecidableEq ι] {k : ℕ}

/-- A repeated color at a point forces every color to cover that point.
This stronger invariant implies the required min(N,k) coverage identity. -/
def PairBalanced (F : Finset ι) (L R : ι → ℝ) (col : ι → Fin k) : Prop :=
  ∀ u∈F,∀ v∈F,u≠v → col u=col v → ∀ t,
    t∈Set.Icc (L u) (R u) → t∈Set.Icc (L v) (R v) →
    ∀ d : Fin k,∃ j∈F,col j=d ∧ t∈Set.Icc (L j) (R j)

theorem balanced_insert (F : Finset ι) (a : ι) (ha : a∉F) (L R : ι → ℝ)
    (hL : ∀ u∈F,L u≤L a) (col : ι → Fin k) (hc : PairBalanced F L R col) (c : Fin k)
    (hnew : ∀ u∈F,col u=c → ∀ d : Fin k,∃ j∈F,col j=d ∧ R u≤R j) :
    PairBalanced (insert a F) L R (Function.update col a c) := by
  classical
  have hold (u : ι) (hu : u∈F) : Function.update col a c u=col u := by
    have hua : u≠a := by intro he;subst u;exact ha hu
    simp [Function.update_apply,hua]
  have hnewcolor : Function.update col a c a=c := by simp
  intro u hu v hv hne heq t htu htv d
  by_cases hua : u=a
  · subst u
    have hvF : v∈F := (Finset.mem_insert.mp hv).resolve_left hne.symm
    have hcv : col v=c := by rw [hnewcolor,hold v hvF] at heq;exact heq.symm
    obtain ⟨j,hj,hcol,hR⟩ := hnew v hvF hcv d
    refine ⟨j,Finset.mem_insert_of_mem hj,?_,?_⟩
    · rw [hold j hj];exact hcol
    · exact ⟨(hL j hj).trans htu.1,htv.2.trans hR⟩
  · have huF : u∈F := (Finset.mem_insert.mp hu).resolve_left hua
    by_cases hva : v=a
    · subst v
      have hcu : col u=c := by rw [hold u huF,hnewcolor] at heq;exact heq
      obtain ⟨j,hj,hcol,hR⟩ := hnew u huF hcu d
      refine ⟨j,Finset.mem_insert_of_mem hj,?_,?_⟩
      · rw [hold j hj];exact hcol
      · exact ⟨(hL j hj).trans htv.1,htu.2.trans hR⟩
    · have hvF : v∈F := (Finset.mem_insert.mp hv).resolve_left hva
      have hcv : col u=col v := by rwa [hold u huF,hold v hvF] at heq
      obtain ⟨j,hj,hcol,ht⟩ := hc u huF v hvF hne hcv t htu htv d
      exact ⟨j,Finset.mem_insert_of_mem hj,(hold j hj).trans hcol,ht⟩

/-- A greedy color extension: an unused color, or a color whose current
farthest right endpoint is smallest. No integral-flow theorem is assumed. -/
theorem exists_balanced_insert (F : Finset ι) (a : ι) (ha : a∉F) (L R : ι → ℝ)
    (hL : ∀ u∈F,L u≤L a) (hk : 0<k)
    (col : ι → Fin k) (hc : PairBalanced F L R col) :
    ∃ col' : ι → Fin k,PairBalanced (insert a F) L R col' := by
  classical
  by_cases hunused : ∃ c : Fin k,∀ u∈F,col u≠c
  · obtain ⟨c,hc0⟩ := hunused
    refine ⟨Function.update col a c,balanced_insert F a ha L R hL col hc c ?_⟩
    intro u hu huc d
    exact (hc0 u hu huc).elim
  · have heach : ∀ d : Fin k,∃ u∈F,col u=d := by
      simpa only [not_exists,not_forall,not_imp,not_not,exists_prop] using hunused
    have htop : ∀ d : Fin k,∃ j∈F,col j=d ∧ ∀ u∈F,col u=d → R u≤R j := by
      intro d
      obtain ⟨u,hu,huc⟩ := heach d
      have hne : (F.filter (fun u => col u=d)).Nonempty := ⟨u,Finset.mem_filter.mpr ⟨hu,huc⟩⟩
      obtain ⟨j,hj,hr⟩ := Finset.exists_max_image (F.filter (fun u => col u=d)) R hne
      have hj' := Finset.mem_filter.mp hj
      exact ⟨j,hj'.1,hj'.2,fun u hu he => hr u (Finset.mem_filter.mpr ⟨hu,he⟩)⟩
    choose top htop using htop
    have hfin : (Finset.univ : Finset (Fin k)).Nonempty := ⟨⟨0,hk⟩,Finset.mem_univ _⟩
    obtain ⟨c,hcU,hcmin⟩ := Finset.exists_min_image Finset.univ (fun d => R (top d)) hfin
    refine ⟨Function.update col a c,balanced_insert F a ha L R hL col hc c ?_⟩
    intro u hu huc d
    exact ⟨top d,(htop d).1,(htop d).2.1,
      ((htop c).2.2 u hu huc).trans (hcmin d (Finset.mem_univ _))⟩

theorem exists_pair_balanced (F : Finset ι) (L R : ι → ℝ) (hk : 0<k) :
    ∃ col : ι → Fin k,PairBalanced F L R col := by
  classical
  refine Finset.strongInductionOn F ?_
  intro F ih
  by_cases hF : F.Nonempty
  · obtain ⟨a,ha,hmax⟩ := Finset.exists_max_image F L hF
    obtain ⟨col,hcol⟩ := ih (F.erase a) (Finset.erase_ssubset ha)
    obtain ⟨col',hcol'⟩ := exists_balanced_insert (F.erase a) a (Finset.notMem_erase a F) L R
      (fun u hu => hmax u (Finset.mem_of_mem_erase hu)) hk col hcol
    rw [Finset.insert_erase ha] at hcol'
    exact ⟨col',hcol'⟩
  · have he : F=∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    subst F
    exact ⟨fun _ => ⟨0,hk⟩,by intro u hu;simpa using hu⟩

def active (F : Finset ι) (L R : ι → ℝ) (t : ℝ) : Finset ι :=
  F.filter (fun i => t∈Set.Icc (L i) (R i))

theorem colors_card (F : Finset ι) (L R : ι → ℝ) (col : ι → Fin k)
    (hc : PairBalanced F L R col) (t : ℝ) :
    ((active F L R t).image col).card=min (active F L R t).card k := by
  classical
  let A := active F L R t
  let C := A.image col
  have hC : C.card≤k := by simpa using Finset.card_le_card (Finset.subset_univ C)
  by_cases hfull : C=Finset.univ
  · have he : C.card=k := by simp [hfull]
    have hn : k≤A.card := he.symm ▸ Finset.card_image_le
    change C.card=min A.card k
    rw [he,min_eq_right hn]
  · have hmiss : ∃ d : Fin k,d∉C := by
      by_contra h
      push Not at h
      apply hfull
      exact Finset.eq_univ_iff_forall.mpr h
    obtain ⟨d,hd⟩ := hmiss
    have hinj : Set.InjOn col (A:Set ι) := by
      intro u hu v hv he
      by_contra hne
      have hu' := Finset.mem_filter.mp hu
      have hv' := Finset.mem_filter.mp hv
      obtain ⟨j,hj,hcol,ht⟩ := hc u hu'.1 v hv'.1 hne he t hu'.2 hv'.2 d
      exact hd (Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨hj,ht⟩,hcol⟩)
    have he : C.card=A.card := Finset.card_image_of_injOn hinj
    have hn : A.card≤k := he ▸ hC
    change C.card=min A.card k
    rw [he,min_eq_left hn]

theorem exists_coverage_coloring (F : Finset ι) (L R : ι → ℝ) (hk : 0<k) :
    ∃ col : ι → Fin k,∀ t,
      ((active F L R t).image col).card=min (active F L R t).card k := by
  obtain ⟨col,hcol⟩ := exists_pair_balanced F L R hk
  exact ⟨col,colors_card F L R col hcol⟩

end LonelyRunnerNew.IntervalCoverage
