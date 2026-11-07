import LonelyRunnerNew.DyadicGraphSelection
import LonelyRunnerNew.DyadicKernelCertificate
import LonelyRunnerNew.OriginalRoughLC
import LonelyRunnerNew.SeparatedEstimates
import LonelyRunnerNew.Certificates
import LonelyRunnerNew.OuterAssembly
import LonelyRunnerNew.SpecificationAdapter
import LonelyRunnerNew.DyadicRetainedChoice

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew.TaggedState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

theorem dyadic_physical_of_roughBlockInput (hA : roughBlockInput) (s : TaggedState Label n)
    (G : Finset (Label × Label)) (hG : G⊆s.edges) {ell : ℝ} (hell : 4096≤ell)
    (hL : ∀ x∈s.left,rough 142 (s.leftValue x)) (hR : ∀ y∈s.right,rough 142 (s.rightValue y))
    (hsep : separated (Real.exp ell) s) (i j : ℕ) (hi : i∈s.leftBlockCodes) (hj : j∈s.rightBlockCodes) :
    s.dyadicPhysicalQ G hG i j hi hj≤roughConstant ell n := by
  let t := s.dyadicState G hG i j hi hj
  let U := t.left.image t.leftValue
  let Z := t.right.image t.rightValue
  let E := t.valueEdges t.edges
  let A := s.blockA i
  let B := s.blockB j
  let D := blockScale s.a s.b A B
  have hU : ∀ u∈U,rough 142 u ∧ A≤(u:ℝ) ∧ (u:ℝ)<2*A := by
    intro u hu
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hu
    exact ⟨hL x (Finset.mem_filter.mp hx).1,s.leftBlock_bounds hx⟩
  have hZ : ∀ u∈Z,rough 142 u ∧ B≤(u:ℝ) ∧ (u:ℝ)<2*B := by
    intro u hu
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hu
    exact ⟨hR x (Finset.mem_filter.mp hx).1,s.rightBlock_bounds hx⟩
  have hSepU : LonelyRunnerNew.separated (Real.exp ell) U := by
    intro u hu v hv huv
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hv
    exact hsep.1 x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 (by intro he;subst y;exact huv rfl)
  have hSepZ : LonelyRunnerNew.separated (Real.exp ell) Z := by
    intro u hu v hv huv
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hv
    exact hsep.2 x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 (by intro he;subst y;exact huv rfl)
  have hcardU : U.card=t.left.card := Finset.card_image_iff.mpr t.left_injective
  have hcardZ : Z.card=t.right.card := Finset.card_image_iff.mpr t.right_injective
  have hp := hA n U Z E A B D ell (by exact_mod_cast t.ambient_pos)
    (t.left_nonempty.image _) (t.right_nonempty.image _) (hcardU.trans_le t.left_budget)
    (hcardZ.trans_le t.right_budget) (t.valueEdges_subset t.edges (Finset.Subset.refl _))
    (s.blockA_pos i) (s.blockB_pos j) (blockScale_pos (b := s.b) (B := B) s.a_positive (s.blockA_pos i))
    hell hU hZ hSepU hSepZ
  rw [hcardU,hcardZ] at hp
  change (physicalDensity U Z E D)^q*t.area/(A*B/D^2)*(t.area/(n:ℝ)^2)^sigma≤_ at hp
  unfold dyadicPhysicalQ
  change (physicalDensity U Z E D)^q*t.area*(D^2/(A*B))*(t.area/(n:ℝ)^2)^sigma≤_
  rw [physical_score_factor_form]
  exact hp

theorem rough_quality_of_roughBlockInput (hA : roughBlockInput) (s : TaggedState Label n)
    (hM : 0<s.edgeMass) {ell : ℝ} (hell : 4096≤ell)
    (hL : ∀ x∈s.left,rough 142 (s.leftValue x)) (hR : ∀ y∈s.right,rough 142 (s.rightValue y))
    (hsep : separated (Real.exp ell) s) :
    s.quality≤(Certificate.Bbar:ℝ)^q*roughConstant ell n := by
  have hfull : s.keepEdges s.edges (Finset.Subset.refl _)=s := rfl
  obtain ⟨i,hi,j,hj,_,hb⟩ := s.select_ordinary_physical_block s.edges (Finset.Subset.refl _)
    (by simpa only [hfull] using hM)
  rw [hfull] at hb
  have hphys := s.dyadic_physical_of_roughBlockInput hA s.edges (Finset.Subset.refl _) hell hL hR hsep i j hi hj
  have hK := DyadicPhysical.kernelN_ge_one (DyadicPhysical.lambda_pos q)
    (DyadicPhysical.lambda_lt_one (by norm_num [q] : 0<q))
  have hK0 : 0≤kernelN (DyadicPhysical.lambda q) := by linarith
  have hp := mul_le_mul_of_nonneg_left hphys (Real.rpow_nonneg hK0 q)
  have hconst : 0≤roughConstant ell n := by
    unfold roughConstant
    exact add_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (mul_nonneg (by norm_num) (Real.rpow_nonneg (div_nonneg (by norm_num) (by positivity)) _))
  have hnum := Real.rpow_le_rpow hK0 DyadicPhysical.dyadic_kernel_le_Bbar (by norm_num [q] : 0≤q)
  exact hb.trans (hp.trans (mul_le_mul_of_nonneg_right hnum hconst))

end LonelyRunnerNew.TaggedState

namespace LonelyRunnerNew

/-- Unconditional block choice within the explicitly separated original-speed
branch. There is no roughBlockInput or RC premise in this theorem. -/
theorem original_ordinary_physical_choice (V : Finset ℕ) (hV : valid V)
    (hsep : separated (Real.exp 6880) V) :
    ∃ t : TaggedState ℕ V.card,
      (∀ u,TaggedState.Step t u → u.quality≤t.quality) ∧ 0<t.edgeMass ∧
      (∀ x∈t.left,rough 142 (t.leftValue x)) ∧ (∀ y∈t.right,rough 142 (t.rightValue y)) ∧
      TaggedState.separated (Real.exp 4130) t ∧
      ∃ (i : ℕ) (hi : i∈t.leftBlockCodes) (j : ℕ) (hj : j∈t.rightBlockCodes),
        0<(t.dyadicState t.edges (Finset.Subset.refl _) i j hi hj).edgeMass ∧
        (Certificate.tbar:ℝ)^q*((W V)^q/4)≤(Certificate.Bbar:ℝ)^q*
          t.dyadicPhysicalQ t.edges (Finset.Subset.refl _) i j hi hj := by
  obtain ⟨s,r,t,centers,hpath,hs,hps,hM,hrL,hrR,hrE,hrvL,hrvR,hra,hrb,hrpos,
    htpath,htQ,htstable,htM,htL,htR,htsep,htLV,htRV,htEV,hParent,hInit,rest⟩ :=
      original_ordinary_stable_rough_LC V hV hsep
  have hfull : t.keepEdges t.edges (Finset.Subset.refl _)=t := rfl
  obtain ⟨i,hi,j,hj,hm,hb⟩ := t.select_ordinary_physical_block_Bbar t.edges (Finset.Subset.refl _)
    (by simpa only [hfull] using htM)
  rw [hfull] at hb
  rw [initialTaggedState_quality] at hInit
  exact ⟨t,htstable,htM,htL,htR,htsep,i,hi,j,hj,hm,hInit.trans hb⟩

theorem original_universal_retained_physical_choice (V : Finset ℕ) (hV : valid V)
    (hsep : separated (Real.exp 6880) V) :
    ∃ (t : TaggedState ℕ V.card) (centers : ℕ → ℕ),
      (∀ u,TaggedState.Step t u → u.universalQuality≤t.universalQuality) ∧ 0<t.edgeMass ∧
      (∀ x∈t.left,rough 142 (t.leftValue x)) ∧ (∀ y∈t.right,rough 142 (t.rightValue y)) ∧
      TaggedState.separated (Real.exp 4130) t ∧
      (27/50:ℝ)≤∑ e∈t.retainedLargeEdges centers,t.edgeProbability e ∧
      (∀ e∈t.retainedLargeEdges centers,∀ p,Nat.Prime p → t.centerBrackets p (centers p) e) ∧
      ∃ (i : ℕ) (hi : i∈t.leftBlockCodes) (j : ℕ) (hj : j∈t.rightBlockCodes),
        0<(t.dyadicState (t.retainedLargeEdges centers) (t.retainedLargeEdges_subset centers) i j hi hj).edgeMass ∧
        (27/50:ℝ)^4*((Certificate.tbar:ℝ)^4*(initialTaggedState V hV).universalQuality)≤
          (Certificate.Bbar:ℝ)^4*t.dyadicPhysicalQ4 (t.retainedLargeEdges centers)
            (t.retainedLargeEdges_subset centers) i j hi hj := by
  obtain ⟨s,r,t,c,hpath,hs,hps,hM,hrL,hrR,hrE,hrvL,hrvR,hra,hrb,hrpos,
    htpath,htQ,htstable,htM,htL,htR,htsep,htLV,htRV,htEV,hParent,hInit,rest⟩ :=
      original_universal_stable_rough_LC V hV hsep
  obtain ⟨hoff,hG,hprob,hraw,hall,hN,hden⟩ := rest
  obtain ⟨hmass,_,hkeep⟩ := t.keepEdges_score_bounds (t.retainedLargeEdges c) hG htM
    (by norm_num : (0:ℝ)≤27/50) hprob
  have hp : 0<(t.keepEdges (t.retainedLargeEdges c) hG).edgeMass :=
    (mul_pos (by norm_num : (0:ℝ)<27/50) htM).trans_le hmass
  obtain ⟨i,hi,j,hj,hm,hb⟩ := t.select_universal_physical_block_Bbar (t.retainedLargeEdges c) hG hp
  have hl := mul_le_mul_of_nonneg_left hInit (by norm_num : (0:ℝ)≤(27/50:ℝ)^4)
  exact ⟨t,c,htstable,htM,htL,htR,htsep,hprob,hall,i,hi,j,hj,hm,hl.trans (hkeep.trans hb)⟩

theorem real_rational_endgame :
    4*(Certificate.Cbar:ℝ)*(Certificate.Bbar:ℝ)^q<((Certificate.wbar:ℝ)*(Certificate.tbar:ℝ))^q := by
  have hc : (0:ℝ)≤4*(Certificate.Cbar:ℝ) := by norm_num [Certificate.Cbar]
  have hb : (0:ℝ)≤(Certificate.Bbar:ℝ) := by norm_num [Certificate.Bbar]
  have hw : (0:ℝ)≤(Certificate.wbar:ℝ)*(Certificate.tbar:ℝ) := by norm_num [Certificate.wbar,Certificate.tbar,Certificate.Dbar]
  have he : (4*(Certificate.Cbar:ℝ))^50*(Certificate.Bbar:ℝ)^201<
      ((Certificate.wbar:ℝ)*(Certificate.tbar:ℝ))^201 := by
    exact_mod_cast rational_endgame
  have h := Real.rpow_lt_rpow (mul_nonneg (pow_nonneg hc _) (pow_nonneg hb _)) he (by norm_num : (0:ℝ)<1/50)
  rw [Real.mul_rpow (pow_nonneg hc _) (pow_nonneg hb _),
    ← Real.rpow_natCast_mul hc 50 (1/50),← Real.rpow_natCast_mul hb 201 (1/50),
    ← Real.rpow_natCast_mul hw 201 (1/50)] at h
  norm_num only [Nat.cast_ofNat] at h
  convert h using 1 <;> norm_num [q]

/-- Existing roughBlockInput remains an explicit, unproved analytic input.
All global localization, dyadic losses and frozen numerical comparisons are
proved here; kernelInput is no longer an additional premise. -/
theorem separated_control_of_roughBlockInput (hA : roughBlockInput) :
    separatedControl (Real.exp 6880) (17/100) := by
  intro V hV hsep
  by_cases hsmall : (V.card:ℝ)<(1/20:ℝ)*Real.exp 6880/2
  · have h := small_n (Real.exp_pos _) V (valid_card_pos hV) hsep hsmall
    exact h.le.trans (by norm_num)
  · have hlarge : (1/20:ℝ)*Real.exp 6880/2≤(V.card:ℝ) := le_of_not_gt hsmall
    obtain ⟨s,r,t,centers,hpath,hs,hps,hM,hrL,hrR,hrE,hrvL,hrvR,hra,hrb,hrpos,
      htpath,htQ,htstable,htM,htL,htR,htsep,htLV,htRV,htEV,hParent,hInit,rest⟩ :=
        original_ordinary_stable_rough_LC V hV hsep
    have hrough := t.rough_quality_of_roughBlockInput hA htM (by norm_num : (4096:ℝ)≤4130) htL htR htsep
    have hC := (roughConstant_le_largeNConstant V.card hlarge).trans_lt Endgame.largeNConstant_lt_Cbar
    have hbpos : 0<(Certificate.Bbar:ℝ)^q := Real.rpow_pos_of_pos (by norm_num [Certificate.Bbar]) _
    have hstrict := hrough.trans_lt (mul_lt_mul_of_pos_left hC hbpos)
    rw [initialTaggedState_quality] at hInit
    change (Certificate.tbar:ℝ)^q*((W V)^q/4)≤t.quality at hInit
    have hW : W V<(Certificate.wbar:ℝ) := by
      by_contra hn
      have hwW := le_of_not_gt hn
      have hw0 : (0:ℝ)≤Certificate.wbar := by norm_num [Certificate.wbar]
      have ht0 : (0:ℝ)≤Certificate.tbar := by norm_num [Certificate.tbar,Certificate.Dbar]
      have hpW := Real.rpow_le_rpow hw0 hwW (by norm_num [q] : 0≤q)
      have hp := mul_le_mul_of_nonneg_left hpW (Real.rpow_nonneg ht0 q)
      have hend := real_rational_endgame
      rw [Real.mul_rpow hw0 ht0] at hend
      nlinarith only [hInit,hstrict,hp,hend]
    exact hW.le.trans Certificate.wbar_lt_delta.le

theorem main_of_roughBlockInput_spillover_forest (hA : roughBlockInput)
    (hS : spilloverInput) (hF : forestInput) : mainStatement :=
  main_of_separated_control hS hF (separated_control_of_roughBlockInput hA)

theorem separatedTarget_proved : separatedTarget := by
  intro hA _
  exact separated_control_of_roughBlockInput hA

theorem conditionalTarget_proved : conditionalTarget := by
  intro hA _ hS hF
  exact main_of_roughBlockInput_spillover_forest hA hS hF

/-- An explicit conditional adapter, not an unconditional final theorem. -/
theorem frozen_of_rough_block_spillover_forest (hA : roughBlockInput)
    (hS : spilloverInput) (hF : forestInput) : LonelyRunnerSpec.V1.Statement :=
  internalStatement_iff_frozen.mp (main_of_roughBlockInput_spillover_forest hA hS hF)

end LonelyRunnerNew
