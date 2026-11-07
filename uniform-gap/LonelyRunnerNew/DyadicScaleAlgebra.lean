import LonelyRunnerNew.DyadicPhysicalPartition

noncomputable section
set_option autoImplicit false
namespace LonelyRunnerNew.DyadicPhysical

def lambda (eta : ℝ) : ℝ := (2:ℝ)^(-1/eta)
theorem lambda_pos (eta : ℝ) : 0<lambda eta := Real.rpow_pos_of_pos (by norm_num) _
theorem lambda_lt_one {eta : ℝ} (heta : 0<eta) : lambda eta<1 := by
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (div_neg_of_neg_of_pos (by norm_num) heta)

theorem lambda_rpow {eta : ℝ} (heta : 0<eta) : (lambda eta)^eta=(1/2:ℝ) := by
  rw [lambda,← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
  have h : (-1/eta)*eta=(-1:ℝ) := by field_simp
  rw [h]
  norm_num

theorem lambda_gap_rpow {eta : ℝ} (heta : 0<eta) (d : ℕ) :
    ((lambda eta)^d)^eta=1/(2:ℝ)^d := by
  rw [← Real.rpow_pow_comm (lambda_pos eta).le eta d,lambda_rpow heta,div_pow,one_pow]

theorem normalized_ratio_rpow {eta m A : ℝ} (heta : 0<eta) (hm : 0≤m) (hA : 0<A) (d : ℕ) :
    (m/((lambda eta)^d*A^(3/4:ℝ)))^eta=(2:ℝ)^d*(m/A^(3/4:ℝ))^eta := by
  have he : m/((lambda eta)^d*A^(3/4:ℝ))=(m/A^(3/4:ℝ))/((lambda eta)^d) := by ring
  rw [he,Real.div_rpow (div_nonneg hm (Real.rpow_pos_of_pos hA _).le) (pow_pos (lambda_pos eta) _).le,
    lambda_gap_rpow heta]
  rw [div_div_eq_mul_div,div_one]
  ring

end LonelyRunnerNew.DyadicPhysical

namespace LonelyRunnerNew.TaggedState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

theorem dyadic_block_scale_factor (s : TaggedState Label n) (i j : ℕ) :
    (blockScale s.a s.b (s.blockA i) (s.blockB j))^2/(s.blockA i*s.blockB j)=
      (s.a*s.b)*(2:ℝ)^(DyadicPhysical.gap i j) := by
  have hA : s.a*s.blockA i=s.blockUnit*(2:ℝ)^i := by unfold blockA;field_simp [s.a_positive.ne']
  have hB : s.b*s.blockB j=s.blockUnit*(2:ℝ)^j := by unfold blockB;field_simp [s.b_positive.ne']
  unfold blockScale
  rw [hA,hB]
  rcases le_total i j with hij | hji
  · have hp : (2:ℝ)^i≤(2:ℝ)^j := pow_le_pow_right₀ (by norm_num) hij
    rw [max_eq_right (mul_le_mul_of_nonneg_left hp s.blockUnit_pos.le)]
    have hgap : DyadicPhysical.gap i j=j-i := Int.natAbs_natCast_sub_natCast_of_le hij
    rw [hgap]
    have he : (2:ℝ)^j=(2:ℝ)^i*(2:ℝ)^(j-i) := by rw [← pow_add,Nat.add_sub_of_le hij]
    unfold blockA blockB
    rw [he]
    field_simp [s.a_positive.ne',s.b_positive.ne',s.blockUnit_pos.ne']
    <;> ring
  · have hp : (2:ℝ)^j≤(2:ℝ)^i := pow_le_pow_right₀ (by norm_num) hji
    rw [max_eq_left (mul_le_mul_of_nonneg_left hp s.blockUnit_pos.le)]
    have hgap : DyadicPhysical.gap i j=i-j := Int.natAbs_natCast_sub_natCast_of_ge hji
    rw [hgap]
    have he : (2:ℝ)^i=(2:ℝ)^j*(2:ℝ)^(i-j) := by rw [← pow_add,Nat.add_sub_of_le hji]
    unfold blockA blockB
    rw [he]
    field_simp [s.a_positive.ne',s.b_positive.ne',s.blockUnit_pos.ne']
    <;> ring

end LonelyRunnerNew.TaggedState
