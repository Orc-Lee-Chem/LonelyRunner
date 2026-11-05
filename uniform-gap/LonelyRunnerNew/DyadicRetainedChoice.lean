import LonelyRunnerNew.DyadicUniformSelection

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew.TaggedState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

/-- One global LC selection, followed by a uniform physical block choice.
The 27/50 loss is global and is explicitly raised to q. -/
theorem ordinary_retained_physical_choice (s : TaggedState Label n)
    (hs : ∀ t,Step s t → t.quality≤s.quality) (hM : 0<s.edgeMass)
    (hL : ∀ x∈s.left,rough 142 (s.leftValue x)) (hR : ∀ y∈s.right,rough 142 (s.rightValue y)) :
    ∃ (centers : ℕ → ℕ) (i : ℕ) (hi : i∈s.leftBlockCodes) (j : ℕ) (hj : j∈s.rightBlockCodes),
      (27/50:ℝ)≤∑ e∈s.retainedLargeEdges centers,s.edgeProbability e ∧
      (∀ e∈s.retainedLargeEdges centers,∀ p,Nat.Prime p → s.centerBrackets p (centers p) e) ∧
      0<(s.dyadicState (s.retainedLargeEdges centers) (s.retainedLargeEdges_subset centers) i j hi hj).edgeMass ∧
      (27/50:ℝ)^q*s.quality≤(Certificate.Bbar:ℝ)^q*
        s.dyadicPhysicalQ (s.retainedLargeEdges centers) (s.retainedLargeEdges_subset centers) i j hi hj := by
  obtain ⟨centers,_,hG,hprob,hall⟩ := s.stable_rough_all_prime_retention hs hM hL hR
  obtain ⟨hm,hq,_⟩ := s.keepEdges_score_bounds _ hG hM (by norm_num : (0:ℝ)≤27/50) hprob
  have hp : 0<(s.keepEdges (s.retainedLargeEdges centers) hG).edgeMass :=
    (mul_pos (by norm_num : (0:ℝ)<27/50) hM).trans_le hm
  obtain ⟨i,hi,j,hj,hblock,hbound⟩ := s.select_ordinary_physical_block_Bbar _ hG hp
  exact ⟨centers,i,hi,j,hj,hprob,hall,hblock,hq.trans hbound⟩

theorem universal_retained_physical_choice (s : TaggedState Label n)
    (hs : ∀ t,Step s t → t.universalQuality≤s.universalQuality) (hM : 0<s.edgeMass)
    (hL : ∀ x∈s.left,rough 142 (s.leftValue x)) (hR : ∀ y∈s.right,rough 142 (s.rightValue y)) :
    ∃ (centers : ℕ → ℕ) (i : ℕ) (hi : i∈s.leftBlockCodes) (j : ℕ) (hj : j∈s.rightBlockCodes),
      (27/50:ℝ)≤∑ e∈s.retainedLargeEdges centers,s.edgeProbability e ∧
      (∀ e∈s.retainedLargeEdges centers,∀ p,Nat.Prime p → s.centerBrackets p (centers p) e) ∧
      0<(s.dyadicState (s.retainedLargeEdges centers) (s.retainedLargeEdges_subset centers) i j hi hj).edgeMass ∧
      (27/50:ℝ)^4*s.universalQuality≤(Certificate.Bbar:ℝ)^4*
        s.dyadicPhysicalQ4 (s.retainedLargeEdges centers) (s.retainedLargeEdges_subset centers) i j hi hj := by
  obtain ⟨centers,_,hG,hprob,hall⟩ := s.universal_rough_all_prime_retention hs hM hL hR
  obtain ⟨hm,_,hq⟩ := s.keepEdges_score_bounds _ hG hM (by norm_num : (0:ℝ)≤27/50) hprob
  have hp : 0<(s.keepEdges (s.retainedLargeEdges centers) hG).edgeMass :=
    (mul_pos (by norm_num : (0:ℝ)<27/50) hM).trans_le hm
  obtain ⟨i,hi,j,hj,hblock,hbound⟩ := s.select_universal_physical_block_Bbar _ hG hp
  exact ⟨centers,i,hi,j,hj,hprob,hall,hblock,hq.trans hbound⟩

end LonelyRunnerNew.TaggedState
