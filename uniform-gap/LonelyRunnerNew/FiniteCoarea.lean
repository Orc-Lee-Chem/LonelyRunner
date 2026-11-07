import LonelyRunnerNew.FiniteMedian

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew.FiniteCore
set_option maxHeartbeats 2000000
variable {V : Type*} [DecidableEq V]

def cross (F : Finset V) (omega : V → V → ℝ) (S : Finset V) : ℝ :=
  ∑ v∈F,∑ u∈F,if v∈S ∧ u∉S then omega v u else 0

theorem mass_complement (F : Finset V) (pi : V → ℝ) (S : Finset V)
    (hs : (∑ v∈F,pi v)=1) : mass F pi S+mass F pi (F\S)=1 := by
  rw [← hs]
  unfold mass
  simp only [Finset.sum_filter,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hm : v∈S <;> simp [hv,hm]

theorem filtered_sum_mono (F : Finset V) (pi : V → ℝ) (hpi : ∀ v∈F,0≤pi v)
    (P Q : V → Prop) [DecidablePred P] [DecidablePred Q] (hPQ : ∀ v∈F,P v → Q v) :
    (∑ v∈F.filter P,pi v)≤∑ v∈F.filter Q,pi v := by
  simp only [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro v hv
  by_cases hp : P v <;> by_cases hq : Q v
  · simp [hp,hq]
  · exact False.elim (hq (hPQ v hv hp))
  · simpa [hp,hq] using hpi v hv
  · simp [hp,hq]

theorem indicator_cross (F : Finset V) (omega : V → V → ℝ)
    (hsym : ∀ v u,omega v u=omega u v) (S : Finset V) :
    (∑ v∈F,∑ u∈F,omega v u*|(if v∈S then (1:ℝ) else 0)-(if u∈S then (1:ℝ) else 0)|)=
      2*cross F omega S := by
  have he : (∑ v∈F,∑ u∈F,if u∈S ∧ v∉S then omega v u else 0)=cross F omega S := by
    rw [Finset.sum_comm]
    unfold cross
    apply Finset.sum_congr rfl
    intro v hv
    apply Finset.sum_congr rfl
    intro u hu
    rw [hsym u v]
  have hp (v u : V) : omega v u*|(if v∈S then (1:ℝ) else 0)-(if u∈S then (1:ℝ) else 0)| =
      (if v∈S ∧ u∉S then omega v u else 0)+(if u∈S ∧ v∉S then omega v u else 0) := by
    by_cases hv : v∈S <;> by_cases hu : u∈S <;> simp [hv,hu]
  simp_rw [hp,Finset.sum_add_distrib]
  rw [he]
  change cross F omega S+cross F omega S=2*cross F omega S
  ring

theorem level_mass_min (F : Finset V) (pi : V → ℝ) (f : V → ℕ)
    (hpi : ∀ v∈F,0≤pi v) (hs : (∑ v∈F,pi v)=1) (m k : ℕ)
    (hmlo : (∑ v∈F.filter (fun v => f v<m),pi v)≤1/2)
    (hmhi : (∑ v∈F.filter (fun v => m<f v),pi v)≤1/2) :
    (∑ v∈F,pi v*|levelIndicator k (f v)-levelIndicator k m|)=
      min (mass F pi (F.filter (fun v => k<f v)))
        (mass F pi (F\F.filter (fun v => k<f v))) := by
  let S := F.filter (fun v => k<f v)
  have he : F\S=F.filter (fun v => f v≤k) := by
    ext v
    by_cases hv : v∈F <;> simp [S,hv,not_lt]
  have hpart := mass_complement F pi S hs
  have hS : mass F pi S=∑ v∈F.filter (fun v => k<f v),pi v := mass_filter F pi _
  have hc : mass F pi (F\S)=∑ v∈F.filter (fun v => f v≤k),pi v := by rw [he,mass_filter]
  change _=min (mass F pi S) (mass F pi (F\S))
  by_cases hk : k<m
  · have hh : mass F pi (F\S)≤1/2 := by
      rw [hc]
      exact (filtered_sum_mono F pi hpi (fun v => f v≤k) (fun v => f v<m) (fun v _ h => by omega)).trans hmlo
    rw [min_eq_right (by linarith only [hpart,hh]),hc]
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro v hv
    unfold levelIndicator
    by_cases hf : k<f v <;> simp [hk,hf,show f v≤k ↔ ¬k<f v by omega]
  · have hh : mass F pi S≤1/2 := by
      rw [hS]
      exact (filtered_sum_mono F pi hpi (fun v => k<f v) (fun v => m<f v) (fun v _ h => by omega)).trans hmhi
    rw [min_eq_left (by linarith only [hpart,hh]),hS]
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro v hv
    unfold levelIndicator
    by_cases hf : k<f v <;> simp [hk,hf]

/-- Finite coarea for natural-valued functions, with no bound supplied by the
caller: a finite threshold range is derived from the actual finite image. -/
theorem nat_median_coarea (F : Finset V) (pi : V → ℝ) (omega : V → V → ℝ)
    (hpi : ∀ v∈F,0≤pi v) (hs : (∑ v∈F,pi v)=1)
    (hsym : ∀ v u,omega v u=omega u v)
    (hcut : ∀ S,cutConstant*min (mass F pi S) (mass F pi (F\S))≤cross F omega S)
    (f : V → ℕ) (m : ℕ)
    (hmlo : (∑ v∈F.filter (fun v => f v<m),pi v)≤1/2)
    (hmhi : (∑ v∈F.filter (fun v => m<f v),pi v)≤1/2) :
    (∑ v∈F,pi v*|(f v:ℝ)-(m:ℝ)|)≤
      coareaConstant*(∑ v∈F,∑ u∈F,omega v u*|(f v:ℝ)-(f u:ℝ)|) := by
  let N := max (F.sup f) m
  have hf : ∀ v∈F,f v≤N := fun v hv => (Finset.le_sup hv).trans (le_max_left _ _)
  have hm : m≤N := le_max_right _ _
  let S := fun k => F.filter (fun v => k<f v)
  have hL : (∑ v∈F,pi v*|(f v:ℝ)-(m:ℝ)|)=
      ∑ k∈Finset.range N,min (mass F pi (S k)) (mass F pi (F\S k)) := by
    calc
      _ = ∑ v∈F,pi v*(∑ k∈Finset.range N,|levelIndicator k (f v)-levelIndicator k m|) := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [levelIndicator_distance N _ _ (hf v hv) hm]
      _ = ∑ k∈Finset.range N,∑ v∈F,pi v*|levelIndicator k (f v)-levelIndicator k m| := by
        simp_rw [Finset.mul_sum]
        exact Finset.sum_comm
      _ = _ := Finset.sum_congr rfl (fun k _ => level_mass_min F pi f hpi hs m k hmlo hmhi)
  have hE : (∑ v∈F,∑ u∈F,omega v u*|(f v:ℝ)-(f u:ℝ)|)=
      2*(∑ k∈Finset.range N,cross F omega (S k)) := by
    calc
      _ = ∑ v∈F,∑ u∈F,omega v u*(∑ k∈Finset.range N,|levelIndicator k (f v)-levelIndicator k (f u)|) := by
        apply Finset.sum_congr rfl
        intro v hv
        apply Finset.sum_congr rfl
        intro u hu
        rw [levelIndicator_distance N _ _ (hf v hv) (hf u hu)]
      _ = ∑ v∈F,∑ k∈Finset.range N,∑ u∈F,omega v u*|levelIndicator k (f v)-levelIndicator k (f u)| := by
        simp_rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
      _ = ∑ k∈Finset.range N,∑ v∈F,∑ u∈F,omega v u*|levelIndicator k (f v)-levelIndicator k (f u)| := Finset.sum_comm
      _ = ∑ k∈Finset.range N,2*cross F omega (S k) := by
        apply Finset.sum_congr rfl
        intro k hk
        have he (v : V) (hv : v∈F) : levelIndicator k (f v)=(if v∈S k then (1:ℝ) else 0) := by
          simp [levelIndicator,S,hv]
        have hh := indicator_cross F omega hsym (S k)
        convert hh using 1
        apply Finset.sum_congr rfl
        intro v hv
        apply Finset.sum_congr rfl
        intro u hu
        rw [he v hv,he u hu]
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hsum : cutConstant*(∑ v∈F,pi v*|(f v:ℝ)-(m:ℝ)|)≤∑ k∈Finset.range N,cross F omega (S k) := by
    rw [hL,Finset.mul_sum]
    exact Finset.sum_le_sum (fun k _ => hcut (S k))
  have hh : 2*cutConstant*(∑ v∈F,pi v*|(f v:ℝ)-(m:ℝ)|)≤
      ∑ v∈F,∑ u∈F,omega v u*|(f v:ℝ)-(f u:ℝ)| := by rw [hE];linarith only [hsum]
  have hC : 0≤coareaConstant := by unfold coareaConstant;positivity
  have hhC := mul_le_mul_of_nonneg_left hh hC
  have he : coareaConstant*(2*cutConstant*(∑ v∈F,pi v*|(f v:ℝ)-(m:ℝ)|))=
      ∑ v∈F,pi v*|(f v:ℝ)-(m:ℝ)| := by
    have hx := congrArg (fun t : ℝ => t*(∑ v∈F,pi v*|(f v:ℝ)-(m:ℝ)|)) coareaConstant_identity
    nlinarith only [hx]
  rwa [he] at hhC

end LonelyRunnerNew.FiniteCore
