import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# 平方自由整数上的调和和

使用 Mathlib 的 `Squarefree`、`Nat.totient` 与实际平方自由分解。
证明只涉及有限正项求和及有限望远镜求和，包含 `z=1`。
-/

namespace LonelyRunner

/-- 求和指标精确为 `1≤d≤z` 的平方自由自然数。 -/
def squarefreeHarmonicIndices (z : ℕ) : Finset ℕ :=
  (Finset.Icc 1 z).filter Squarefree

/-- `S(z)`：分母先转为实数，再取倒数。 -/
noncomputable def squarefreeHarmonicSum (z : ℕ) : ℝ :=
  ∑ d ∈ squarefreeHarmonicIndices z, (d : ℝ)⁻¹

/-- `G(z)`：沿用 Mathlib 的 Euler 函数，分母在实数中取倒数。 -/
noncomputable def squarefreeTotientSum (z : ℕ) : ℝ :=
  ∑ d ∈ squarefreeHarmonicIndices z, (Nat.totient d : ℝ)⁻¹

private theorem squarefreeFactorPair_exists (n : ℕ) :
    ∃ p : ℕ × ℕ, Squarefree p.1 ∧ n = p.1 * p.2 ^ 2 := by
  obtain ⟨b, d, heq, hd⟩ := exists_sq_mul_squarefree n
  exact ⟨(d, b), hd, by simpa [Nat.mul_comm] using heq.symm⟩

/-- 对每个整数固定一次平方自由分解。后续单射不需要分解唯一性。 -/
noncomputable def squarefreeFactorPair (n : ℕ) : ℕ × ℕ :=
  Classical.choose (squarefreeFactorPair_exists n)

theorem squarefreeFactorPair_spec (n : ℕ) :
    Squarefree (squarefreeFactorPair n).1 ∧
      n = (squarefreeFactorPair n).1 * (squarefreeFactorPair n).2 ^ 2 :=
  Classical.choose_spec (squarefreeFactorPair_exists n)

/-- 编码可恢复原整数 `n=db²`，因此实际选定的分解映射是单射。 -/
theorem squarefreeFactorPair_injective : Function.Injective squarefreeFactorPair := by
  intro n n' heq
  calc
    n = (squarefreeFactorPair n).1 * (squarefreeFactorPair n).2 ^ 2 :=
      (squarefreeFactorPair_spec n).2
    _ = (squarefreeFactorPair n').1 * (squarefreeFactorPair n').2 ^ 2 :=
      congrArg (fun p : ℕ × ℕ => p.1 * p.2 ^ 2) heq
    _ = n' := (squarefreeFactorPair_spec n').2.symm

/-- 正整数 `n≤z` 的选定分解满足 `1≤d,b≤z`，故落入实际有限求和矩形。 -/
theorem squarefreeFactorPair_mem (n z : ℕ) (hn : n ∈ Finset.Icc 1 z) :
    squarefreeFactorPair n ∈ squarefreeHarmonicIndices z ×ˢ Finset.Icc 1 z := by
  obtain ⟨hnpos, hnz⟩ := Finset.mem_Icc.mp hn
  have hn0 : 0 < n := by omega
  obtain ⟨hd, heq⟩ := squarefreeFactorPair_spec n
  have hdpos : 0 < (squarefreeFactorPair n).1 := Nat.pos_of_ne_zero hd.ne_zero
  have hbpos : 0 < (squarefreeFactorPair n).2 := by
    by_contra hbad
    have hb : (squarefreeFactorPair n).2 = 0 := by omega
    simp [hb] at heq
    omega
  have hdvd : (squarefreeFactorPair n).1 ∣ n := ⟨(squarefreeFactorPair n).2 ^ 2, heq⟩
  have hbvd : (squarefreeFactorPair n).2 ∣ n := by
    refine ⟨(squarefreeFactorPair n).1 * (squarefreeFactorPair n).2, ?_⟩
    calc
      n = (squarefreeFactorPair n).1 * (squarefreeFactorPair n).2 ^ 2 := heq
      _ = (squarefreeFactorPair n).2 *
          ((squarefreeFactorPair n).1 * (squarefreeFactorPair n).2) := by ring
  exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨hdpos, (Nat.le_of_dvd hn0 hdvd).trans hnz⟩, hd⟩,
    Finset.mem_Icc.mpr ⟨hbpos, (Nat.le_of_dvd hn0 hbvd).trans hnz⟩⟩

/-- 对单射编码的像求和，再用非负性补齐矩形，得到有限调和和的乘积上界。 -/
theorem harmonic_le_squarefree_mul_square_sum (z : ℕ) :
    (∑ n ∈ Finset.Icc 1 z, (n : ℝ)⁻¹) ≤
      squarefreeHarmonicSum z * (∑ b ∈ Finset.Icc 1 z, ((b : ℝ)^2)⁻¹) := by
  classical
  let f : ℕ × ℕ → ℝ := fun p => (p.1 : ℝ)⁻¹ * ((p.2 : ℝ)^2)⁻¹
  have hsub : (Finset.Icc 1 z).image squarefreeFactorPair ⊆
      squarefreeHarmonicIndices z ×ˢ Finset.Icc 1 z := by
    intro p hp
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hp
    exact squarefreeFactorPair_mem n z hn
  calc
    (∑ n ∈ Finset.Icc 1 z, (n : ℝ)⁻¹) =
        ∑ n ∈ Finset.Icc 1 z, f (squarefreeFactorPair n) := by
      apply Finset.sum_congr rfl
      intro n hn
      have heq : (n : ℝ) = ((squarefreeFactorPair n).1 : ℝ) *
          ((squarefreeFactorPair n).2 : ℝ)^2 := by
        exact_mod_cast (squarefreeFactorPair_spec n).2
      simp only [heq, mul_inv_rev, f]
      ring
    _ = ∑ p ∈ (Finset.Icc 1 z).image squarefreeFactorPair, f p :=
      (Finset.sum_image (fun n hn n' hn' h => squarefreeFactorPair_injective h)).symm
    _ ≤ ∑ p ∈ squarefreeHarmonicIndices z ×ˢ Finset.Icc 1 z, f p :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp hnot => by dsimp [f]; positivity)
    _ = squarefreeHarmonicSum z * (∑ b ∈ Finset.Icc 1 z, ((b : ℝ)^2)⁻¹) := by
      rw [Finset.sum_product]
      exact (Finset.sum_mul_sum (squarefreeHarmonicIndices z) (Finset.Icc 1 z)
        (fun d => (d : ℝ)⁻¹) (fun b => ((b : ℝ)^2)⁻¹)).symm

/-- 有限望远镜估计的单步：对 `x>0`，`1/(x+1)²≤1/x−1/(x+1)`。 -/
theorem squareReciprocal_telescope_step (x : ℝ) (hx : 0 < x) :
    ((x + 1)^2)⁻¹ ≤ x⁻¹ - (x + 1)⁻¹ := by
  calc
    ((x + 1)^2)⁻¹ ≤ (x * (x + 1))⁻¹ := by
      have h := one_div_le_one_div_of_le (by positivity : 0 < x * (x + 1))
        (by nlinarith : x * (x + 1) ≤ (x + 1)^2)
      simpa only [one_div] using h
    _ = x⁻¹ - (x + 1)⁻¹ := by field_simp; ring

/-- 实际有限望远镜归纳：平方倒数和不超过 `2−1/z`。 -/
theorem squareReciprocal_sum_le_sub (z : ℕ) (hz : 1 ≤ z) :
    (∑ b ∈ Finset.Icc 1 z, ((b : ℝ)^2)⁻¹) ≤ 2 - (z : ℝ)⁻¹ := by
  induction z, hz using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hIcc : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
      ext b
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot : n + 1 ∉ Finset.Icc 1 n := by simp
    have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    rw [hIcc, Finset.sum_insert hnot]
    have hstep := squareReciprocal_telescope_step (n : ℝ) hnR
    push_cast
    linarith [ih, hstep]

/-- 不需要无限级数：所有 `z≥1` 的有限平方倒数和至多为二。 -/
theorem squareReciprocal_sum_le_two (z : ℕ) (hz : 1 ≤ z) :
    (∑ b ∈ Finset.Icc 1 z, ((b : ℝ)^2)⁻¹) ≤ 2 :=
  (squareReciprocal_sum_le_sub z hz).trans (by
    have h : 0 ≤ (z : ℝ)⁻¹ := by positivity
    linarith)

/-- 从选定平方自由分解及有限平方倒数和得到 `H_z≤2S(z)`。 -/
theorem harmonic_le_two_squarefreeHarmonicSum (z : ℕ) (hz : 1 ≤ z) :
    (∑ n ∈ Finset.Icc 1 z, (n : ℝ)⁻¹) ≤ 2 * squarefreeHarmonicSum z := by
  have hS : 0 ≤ squarefreeHarmonicSum z := Finset.sum_nonneg (fun d hd => by positivity)
  calc
    _ ≤ squarefreeHarmonicSum z * (∑ b ∈ Finset.Icc 1 z, ((b : ℝ)^2)⁻¹) :=
      harmonic_le_squarefree_mul_square_sum z
    _ ≤ squarefreeHarmonicSum z * 2 :=
      mul_le_mul_of_nonneg_left (squareReciprocal_sum_le_two z hz) hS
    _ = _ := by ring

/-- 调用 Mathlib 已证调和和下界，得到 `log(z+1)/2≤S(z)`。 -/
theorem squarefreeHarmonicSum_log_lower (z : ℕ) (hz : 1 ≤ z) :
    (1 / 2 : ℝ) * Real.log ((z : ℝ) + 1) ≤ squarefreeHarmonicSum z := by
  have hlog : Real.log ((z : ℝ) + 1) ≤ ∑ n ∈ Finset.Icc 1 z, (n : ℝ)⁻¹ := by
    simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
      Nat.cast_add, Nat.cast_one] using log_add_one_le_harmonic z
  have h := harmonic_le_two_squarefreeHarmonicSum z hz
  linarith

/-- `0<φ(d)≤d` 在实数倒数下给出 `S(z)≤G(z)`。 -/
theorem squarefreeHarmonicSum_le_totientSum (z : ℕ) :
    squarefreeHarmonicSum z ≤ squarefreeTotientSum z := by
  apply Finset.sum_le_sum
  intro d hd
  have hdpos : 0 < d := by have h := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1; omega
  have hphi : (0 : ℝ) < Nat.totient d := by exact_mod_cast Nat.totient_pos.mpr hdpos
  have hphid : (Nat.totient d : ℝ) ≤ d := by exact_mod_cast Nat.totient_le d
  simpa only [one_div] using one_div_le_one_div_of_le hphi hphid

/-- `1` 是平方自由数且 `φ(1)=1`，所以即使 `z=1` 也有 `G(z)≥1>0`。 -/
theorem squarefreeTotientSum_pos (z : ℕ) (hz : 1 ≤ z) : 0 < squarefreeTotientSum z := by
  have hmem : 1 ∈ squarefreeHarmonicIndices z :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, hz⟩, squarefree_one⟩
  have hle := Finset.single_le_sum (f := fun d : ℕ => (Nat.totient d : ℝ)⁻¹)
    (fun d hd => by positivity) hmem
  norm_num at hle
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hle

/-- 所需平方自由调和和结论，分母与对数均在实数中解释，包含 `z=1`。 -/
theorem squarefreeHarmonic_bounds (z : ℕ) (hz : 1 ≤ z) :
    (1 / 2 : ℝ) * Real.log ((z : ℝ) + 1) ≤ squarefreeHarmonicSum z ∧
      squarefreeHarmonicSum z ≤ squarefreeTotientSum z ∧ 0 < squarefreeTotientSum z :=
  ⟨squarefreeHarmonicSum_log_lower z hz, squarefreeHarmonicSum_le_totientSum z,
    squarefreeTotientSum_pos z hz⟩

/-- 最小边界：`S(1)=G(1)=1`。 -/
theorem squarefreeHarmonic_at_one : squarefreeHarmonicSum 1 = 1 ∧ squarefreeTotientSum 1 = 1 := by
  have hidx : squarefreeHarmonicIndices 1 = {1} := by
    ext d
    simp only [squarefreeHarmonicIndices, Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
    constructor
    · intro hd
      omega
    · rintro rfl
      exact ⟨⟨le_rfl, le_rfl⟩, squarefree_one⟩
  simp [squarefreeHarmonicSum, squarefreeTotientSum, hidx]

#print axioms squarefreeFactorPair_injective
#print axioms harmonic_le_squarefree_mul_square_sum
#print axioms squareReciprocal_sum_le_two
#print axioms squarefreeHarmonic_bounds
#print axioms squarefreeHarmonic_at_one

end LonelyRunner
