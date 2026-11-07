import LonelyRunnerNew.DyadicGraphSelection
import LonelyRunnerNew.DyadicKernelCertificate

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew.TaggedState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

theorem dyadicPhysicalQ_nonneg (s : TaggedState Label n) (G : Finset (Label × Label)) (hG : G⊆s.edges)
    (i j : ℕ) (hi : i∈s.leftBlockCodes) (hj : j∈s.rightBlockCodes) : 0≤s.dyadicPhysicalQ G hG i j hi hj := by
  let t := s.dyadicState G hG i j hi hj
  have hD : 0<blockScale s.a s.b (s.blockA i) (s.blockB j) := blockScale_pos s.a_positive (s.blockA_pos i)
  have hd : 0≤physicalDensity (t.left.image t.leftValue) (t.right.image t.rightValue)
      (t.valueEdges t.edges) (blockScale s.a s.b (s.blockA i) (s.blockB j)) := by
    exact div_nonneg (Finset.sum_nonneg (fun e _ => le_min (by norm_num) (div_nonneg (Nat.cast_nonneg _) hD.le)))
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  exact mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hd _) t.area_pos.le)
    (div_nonneg (sq_nonneg _) (mul_pos (s.blockA_pos i) (s.blockB_pos j)).le))
    (Real.rpow_nonneg (div_nonneg t.area_pos.le (sq_nonneg _)) _)

theorem dyadicPhysicalQ4_nonneg (s : TaggedState Label n) (G : Finset (Label × Label)) (hG : G⊆s.edges)
    (i j : ℕ) (hi : i∈s.leftBlockCodes) (hj : j∈s.rightBlockCodes) : 0≤s.dyadicPhysicalQ4 G hG i j hi hj := by
  let t := s.dyadicState G hG i j hi hj
  exact mul_nonneg (mul_nonneg (by positivity) t.area_pos.le)
    (div_nonneg (sq_nonneg _) (mul_pos (s.blockA_pos i) (s.blockB_pos j)).le)

theorem select_ordinary_physical_block_Bbar (s : TaggedState Label n) (G : Finset (Label × Label))
    (hG : G⊆s.edges) (hM : 0<(s.keepEdges G hG).edgeMass) :
    ∃ (i : ℕ) (hi : i∈s.leftBlockCodes) (j : ℕ) (hj : j∈s.rightBlockCodes),
      0<(s.dyadicState G hG i j hi hj).edgeMass ∧
      (s.keepEdges G hG).quality≤(Certificate.Bbar:ℝ)^q*s.dyadicPhysicalQ G hG i j hi hj := by
  obtain ⟨i,hi,j,hj,hm,hb⟩ := s.select_ordinary_physical_block G hG hM
  have hk := Real.rpow_le_rpow (show 0≤kernelN (DyadicPhysical.lambda q) from
    le_trans (by norm_num) (DyadicPhysical.kernelN_ge_one (DyadicPhysical.lambda_pos q)
      (DyadicPhysical.lambda_lt_one (by norm_num [q] : 0<q)))) DyadicPhysical.dyadic_kernel_le_Bbar
      (by norm_num [q] : 0≤q)
  exact ⟨i,hi,j,hj,hm,hb.trans (mul_le_mul_of_nonneg_right hk (s.dyadicPhysicalQ_nonneg G hG i j hi hj))⟩

/-- q=4 uses its own quartic score. The dyadic convolution is dominated
pointwise by the proved q-kernel; monotonicity of kernelN is not needed. -/
theorem select_universal_physical_block_Bbar (s : TaggedState Label n) (G : Finset (Label × Label))
    (hG : G⊆s.edges) (hM : 0<(s.keepEdges G hG).edgeMass) :
    ∃ (i : ℕ) (hi : i∈s.leftBlockCodes) (j : ℕ) (hj : j∈s.rightBlockCodes),
      0<(s.dyadicState G hG i j hi hj).edgeMass ∧
      (s.keepEdges G hG).universalQuality≤(Certificate.Bbar:ℝ)^4*s.dyadicPhysicalQ4 G hG i j hi hj := by
  have hq : 0<q := by norm_num [q]
  obtain ⟨i,hi,j,hj,hm,hb⟩ := s.select_dyadic_normalized G hG hM
    (DyadicPhysical.lambda_pos q) (DyadicPhysical.lambda_lt_one hq)
  let t := s.dyadicState G hG i j hi hj
  let d := DyadicPhysical.gap i j
  have hK : 0≤kernelN (DyadicPhysical.lambda q) := le_trans (by norm_num)
    (DyadicPhysical.kernelN_ge_one (DyadicPhysical.lambda_pos q) (DyadicPhysical.lambda_lt_one hq))
  have hp := pow_le_pow_left₀ (div_nonneg (s.keepEdges G hG).edgeMass_nonneg (Real.rpow_pos_of_pos s.area_pos _).le) hb 4
  rw [mul_pow] at hp
  have hlam : DyadicPhysical.lambda 4≤DyadicPhysical.lambda q :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) (by norm_num [q])
  have hden := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (DyadicPhysical.lambda_pos 4).le hlam d)
    (Real.rpow_pos_of_pos t.area_pos (3/4:ℝ)).le
  have hratio := div_le_div_of_nonneg_left t.edgeMass_nonneg
    (mul_pos (pow_pos (DyadicPhysical.lambda_pos 4) _) (Real.rpow_pos_of_pos t.area_pos _)) hden
  have hratio0 : 0≤t.edgeMass/((DyadicPhysical.lambda q)^d*t.area^(3/4:ℝ)) :=
    div_nonneg t.edgeMass_nonneg (mul_pos (pow_pos (DyadicPhysical.lambda_pos q) _) (Real.rpow_pos_of_pos t.area_pos _)).le
  have hrpow := pow_le_pow_left₀ hratio0 hratio 4
  have he := DyadicPhysical.normalized_ratio_rpow (by norm_num : (0:ℝ)<4) t.edgeMass_nonneg t.area_pos d
  norm_num only [Real.rpow_ofNat] at he
  rw [he] at hrpow
  have hp' := hp.trans (mul_le_mul_of_nonneg_left hrpow (pow_nonneg hK 4))
  have hh := mul_le_mul_of_nonneg_right hp' (mul_pos s.a_positive s.b_positive).le
  have hscore : (s.keepEdges G hG).universalQuality≤(kernelN (DyadicPhysical.lambda q))^4*(2:ℝ)^d*t.universalQuality := by
    rw [(s.keepEdges G hG).universalQuality_eq_normalized,t.universalQuality_eq_normalized]
    change ((s.keepEdges G hG).edgeMass/s.area^(3/4:ℝ))^4*(s.a*s.b)≤
      (kernelN (DyadicPhysical.lambda q))^4*(2:ℝ)^d*((t.edgeMass/t.area^(3/4:ℝ))^4*(s.a*s.b))
    convert hh using 1 <;> ring
  have hphys := mul_le_mul_of_nonneg_left (s.dyadic_universal_physical G hG i j hi hj) (pow_nonneg hK 4)
  have hk := pow_le_pow_left₀ hK DyadicPhysical.dyadic_kernel_le_Bbar 4
  have hscore' : (s.keepEdges G hG).universalQuality≤
      (kernelN (DyadicPhysical.lambda q))^4*s.dyadicPhysicalQ4 G hG i j hi hj :=
    hscore.trans (by simpa only [mul_assoc] using hphys)
  exact ⟨i,hi,j,hj,hm,hscore'.trans
    (mul_le_mul_of_nonneg_right hk (s.dyadicPhysicalQ4_nonneg G hG i j hi hj))⟩

end LonelyRunnerNew.TaggedState
