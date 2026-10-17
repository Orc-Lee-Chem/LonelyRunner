import LonelyRunner.BedertCompressionStep
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Bedert 迭代模型的数值工具

论文 `prop:bedert` 的模型构造：固定高度门槛、取整根及望远镜势函数。
-/

namespace LonelyRunner

/-- 本轮固定的自然数高度门槛。 -/
def bedertModelThreshold (m d : ℕ) : ℕ := (32 * m * d) ^ (204 * d)

/-- 望远镜势函数，指数和除法均在实数中。 -/
noncomputable def bedertModelPotential (d : ℕ) (x : ℝ) : ℝ :=
  32 * (d : ℝ)^2 * x ^ (-(2 * (d : ℝ))⁻¹)

/-- 正维数时势函数在正实轴上非负且单调递减。 -/
theorem bedertModelPotential_antitone (d : ℕ) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    bedertModelPotential d y ≤ bedertModelPotential d x := by
  unfold bedertModelPotential
  apply mul_le_mul_of_nonneg_left
  · exact Real.rpow_le_rpow_of_nonpos hx hxy (neg_nonpos.mpr (by positivity))
  · positivity

/-- 当当前高度超过两倍门槛时，实际向下取整的根满足单步压缩条件，
并给出单步误差 `≤8d M^(-1/(2d))`。 -/
theorem bedertModel_floor_root (m d M : ℕ) (hm : 2 ≤ m) (hd : 1 ≤ d)
    (hM : 2 * bedertModelThreshold m d < M) :
    let L := ⌊(M : ℝ) ^ ((2 * (d : ℝ))⁻¹)⌋₊
    16 * m * d ≤ L ∧ L ^ (2 * d) < 2 * M ∧
      4 * (d : ℝ) / (L : ℝ) ≤
        8 * (d : ℝ) * (M : ℝ) ^ (-(2 * (d : ℝ))⁻¹) := by
  intro L
  have hbase : 1 ≤ 32 * m * d := by nlinarith
  have hHpos : 0 < bedertModelThreshold m d := pow_pos (by omega) _
  have hMpos : 0 < M := by omega
  have hMR : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hpowBase : (32 * m * d) ^ (2 * d) ≤ M := by
    have hHM : bedertModelThreshold m d ≤ M := by omega
    exact (pow_le_pow_right' hbase (by omega : 2 * d ≤ 204 * d)).trans hHM
  have hroot : (32 : ℝ) * (m : ℝ) * (d : ℝ) ≤
      (M : ℝ) ^ ((2 * (d : ℝ))⁻¹) := by
    have hpowReal : (((32 * m * d : ℕ) : ℝ)^(2*d)) ≤ (M : ℝ) := by exact_mod_cast hpowBase
    have hh := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ ((32 * m * d : ℕ) : ℝ)^(2*d))
      hpowReal (by positivity : (0 : ℝ) ≤ (2 * (d : ℝ))⁻¹)
    have heq := Real.pow_rpow_inv_natCast
      (by positivity : (0 : ℝ) ≤ ((32 * m * d : ℕ) : ℝ)) (by omega : 2 * d ≠ 0)
    have heq' : (((32 * m * d : ℕ) : ℝ)^(2*d))^((2 * (d : ℝ))⁻¹) =
        ((32 * m * d : ℕ) : ℝ) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using heq
    rw [heq'] at hh
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hh
  have hL : 16 * m * d ≤ L := by
    apply (Nat.le_floor_iff (Real.rpow_nonneg hMR.le _)).2
    push_cast
    nlinarith
  have hLpos : 0 < L := by nlinarith
  have hLR : (0 : ℝ) < L := by exact_mod_cast hLpos
  have hfloor : (L : ℝ) ≤ (M : ℝ) ^ ((2 * (d : ℝ))⁻¹) := Nat.floor_le (by positivity)
  have hpowR : (L : ℝ) ^ (2 * d) ≤ M := by
    have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ L) hfloor (2 * d)
    have heq := Real.rpow_inv_natCast_pow hMR.le (by omega : 2 * d ≠ 0)
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hh.trans_eq (by simpa using heq)
  have hpowNat : L ^ (2 * d) < 2 * M := by
    have hh : L ^ (2 * d) ≤ M := by exact_mod_cast hpowR
    omega
  have hfloorhalf : (M : ℝ) ^ ((2 * (d : ℝ))⁻¹) / 2 ≤ L := by
    have hf := Nat.sub_one_lt_floor ((M : ℝ) ^ ((2 * (d : ℝ))⁻¹))
    have hlarge : (2 : ℝ) ≤ (M : ℝ) ^ ((2 * (d : ℝ))⁻¹) := by
      have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
      have hd1R : (1 : ℝ) ≤ d := by exact_mod_cast hd
      nlinarith
    change _ ≤ (⌊(M : ℝ) ^ ((2 * (d : ℝ))⁻¹)⌋₊ : ℝ)
    nlinarith
  refine ⟨hL, hpowNat, ?_⟩
  rw [Real.rpow_neg hMR.le, ← div_eq_mul_inv]
  apply (div_le_div_iff₀ hLR (Real.rpow_pos_of_pos hMR _)).mpr
  nlinarith

/-- 高度至少减半时，势函数的增加足以支付单步误差。
实际使用 `exp x≥1+x` 以及 `log 2>1/2`，不假设几何级数误差界。 -/
theorem bedertModel_potential_gap (d : ℕ) (hd : 1 ≤ d) {N M : ℝ}
    (hN : 0 < N) (hhalf : N ≤ M / 2) :
    8 * (d : ℝ) * M ^ (-(2 * (d : ℝ))⁻¹) ≤
      bedertModelPotential d N - bedertModelPotential d M := by
  have hM : 0 < M := by linarith
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  let s : ℝ := (2 * (d : ℝ))⁻¹
  have hs : 0 < s := by dsimp [s]; positivity
  have hds : (d : ℝ) * s = 1 / 2 := by dsimp [s]; field_simp
  have htwo : 1 + s / 2 ≤ (2 : ℝ)^s := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    have hh := Real.add_one_le_exp (Real.log 2 * s)
    have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    nlinarith [mul_le_mul_of_nonneg_right hlog hs.le]
  have hratio : (M / 2) ^ (-s) = M ^ (-s) * (2 : ℝ)^s := by
    rw [Real.div_rpow hM.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
      div_inv_eq_mul]
  have hanti : (M / 2)^(-s) ≤ N^(-s) :=
    Real.rpow_le_rpow_of_nonpos hN hhalf (by linarith)
  rw [hratio] at hanti
  have hpow := Real.rpow_pos_of_pos hM (-s)
  have hmul := mul_le_mul_of_nonneg_left htwo hpow.le
  have hgain : M^(-s) * (s / 2) ≤ N^(-s) - M^(-s) := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hgain (show (0 : ℝ) ≤ 32 * (d : ℝ)^2 by positivity)
  have hcoef : 32 * (d : ℝ)^2 * (s / 2) = 8 * (d : ℝ) := by
    nlinarith [congrArg (fun x : ℝ => (d : ℝ) * x) hds]
  have hpay : 32 * (d : ℝ)^2 * (M^(-s) * (s / 2)) = 8 * (d : ℝ) * M^(-s) := by
    calc
      _ = (32 * (d : ℝ)^2 * (s / 2)) * M^(-s) := by ring
      _ = _ := by rw [hcoef]
  rw [hpay] at hh
  unfold bedertModelPotential
  change 8 * (d : ℝ) * M ^ (-s) ≤ 32 * (d : ℝ)^2 * N ^ (-s) -
    32 * (d : ℝ)^2 * M ^ (-s)
  nlinarith

/-- 固定门槛的势函数足够小：精确计算指数为 `-102`，再比较有限整数幂。 -/
theorem bedertModel_threshold_error (m d : ℕ) (hm : 2 ≤ m) (hd : 1 ≤ d) :
    bedertModelPotential d (bedertModelThreshold m d : ℝ) ≤ (m : ℝ)^(-100 : ℝ) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  let a : ℝ := 32 * (m : ℝ) * (d : ℝ)
  have ha : 0 < a := by dsimp [a]; positivity
  have hmpos : (0 : ℝ) < m := by linarith
  have hroot : (bedertModelThreshold m d : ℝ)^(-(2 * (d : ℝ))⁻¹) = a^(-102 : ℝ) := by
    rw [bedertModelThreshold, Nat.cast_pow]
    change (((32 * m * d : ℕ) : ℝ)^(204*d))^(-(2 * (d : ℝ))⁻¹) = _
    rw [← Real.rpow_natCast_mul (by positivity)]
    push_cast
    change a^((204 * (d : ℝ)) * (-(2 * (d : ℝ))⁻¹)) = _
    congr 1
    field_simp
    <;> ring
  have haM : (m : ℝ) ≤ a := by dsimp [a]; nlinarith
  have haD : 32 * (d : ℝ) ≤ a := by dsimp [a]; nlinarith
  have ha2 : 32 * (d : ℝ)^2 ≤ a^2 := by
    have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 32 * (d : ℝ)) haD 2
    nlinarith [sq_nonneg (d : ℝ)]
  have h100 : (m : ℝ)^100 ≤ a^100 := pow_le_pow_left₀ hmpos.le haM 100
  have hden : 32 * (d : ℝ)^2 * (m : ℝ)^100 ≤ a^102 := by
    calc
      _ ≤ a^2 * a^100 := mul_le_mul ha2 h100 (by positivity) (by positivity)
      _ = _ := by rw [← pow_add]
  unfold bedertModelPotential
  rw [hroot, Real.rpow_neg ha.le, Real.rpow_neg hmpos.le]
  norm_num only [Real.rpow_ofNat]
  rw [← div_eq_mul_inv, ← one_div]
  exact (div_le_div_iff₀ (pow_pos ha _) (pow_pos hmpos _)).mpr (by simpa using hden)

/-- 最终高度 `T=2H` 的对数界，常数完全显式。
使用 `d≤m`；没有以最终模型界作为输入。 -/
theorem bedertModel_threshold_log (m d : ℕ) (hm : 2 ≤ m) (hd : 1 ≤ d) (hdm : d ≤ m) :
    Real.log ((2 * bedertModelThreshold m d : ℕ) : ℝ) ≤
      2048 * (d : ℝ) * Real.log (2 * (m : ℝ)) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hmpos : (0 : ℝ) < m := by linarith
  have hdpos : (0 : ℝ) < d := by linarith
  have hdmR : (d : ℝ) ≤ m := by exact_mod_cast hdm
  have hlogm : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hmR
  have hlogd : Real.log (d : ℝ) ≤ Real.log (m : ℝ) := Real.log_le_log hdpos hdmR
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog32 : Real.log (32 : ℝ) = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = 2^5 by norm_num, Real.log_pow]
    norm_num
  have hlogbase : Real.log (32 * (m : ℝ) * (d : ℝ)) ≤ 5 * Real.log (2 * (m : ℝ)) := by
    rw [Real.log_mul (by positivity) hdpos.ne', Real.log_mul (by norm_num) hmpos.ne',
      Real.log_mul (by norm_num) hmpos.ne', hlog32]
    linarith
  have hlogtotal : Real.log ((2 * bedertModelThreshold m d : ℕ) : ℝ) =
      Real.log 2 + (204 * (d : ℝ)) * Real.log (32 * (m : ℝ) * (d : ℝ)) := by
    simp only [bedertModelThreshold, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast
    ring
  have hlog2m : 0 ≤ Real.log (2 * (m : ℝ)) := Real.log_nonneg (by nlinarith)
  have hlog2le : Real.log 2 ≤ Real.log (2 * (m : ℝ)) :=
    Real.log_le_log (by norm_num) (by nlinarith)
  have hlog2d : Real.log 2 ≤ (d : ℝ) * Real.log (2 * (m : ℝ)) := by
    nlinarith [mul_le_mul_of_nonneg_right hdR hlog2m]
  rw [hlogtotal]
  nlinarith [mul_le_mul_of_nonneg_left hlogbase (show (0 : ℝ) ≤ 204 * (d : ℝ) by positivity)]

#print axioms bedertModel_floor_root
#print axioms bedertModel_potential_gap
#print axioms bedertModel_threshold_error
#print axioms bedertModel_threshold_log

end LonelyRunner
