import LonelyRunner.SquarefreeHarmonic
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SelbergSieve

/-!
# 区间筛的有限 Selberg 权重

`P` 直接采用 Mathlib 的 `primorial z`，即所有 `p≤z` 的素数之积。
本文件只处理权重、有限反演及二次型，不包含区间素数计数。
-/

namespace LonelyRunner
open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-- 实际素数乘积平方自由；当 `z=1` 时空乘积为一。 -/
theorem selbergIntervalProduct_squarefree (z : ℕ) : Squarefree (primorial z) :=
  squarefree_primorial z

/-- 截断的正约数集精确等于正平方自由整数集。 -/
theorem selbergInterval_divisors_eq (z : ℕ) :
    ((primorial z).divisors.filter (fun l => l ≤ z)) = squarefreeHarmonicIndices z := by
  ext l
  simp only [mem_filter, Nat.mem_divisors, squarefreeHarmonicIndices, mem_Icc]
  constructor
  · rintro ⟨⟨hl, hP⟩, hlz⟩
    have hs := (selbergIntervalProduct_squarefree z).squarefree_of_dvd hl
    exact ⟨⟨by have := hs.ne_zero; omega, hlz⟩, hs⟩
  · rintro ⟨⟨hl1, hlz⟩, hs⟩
    exact ⟨⟨hs.dvd_primorial.trans (primorial_dvd_primorial hlz), primorial_ne_zero z⟩, hlz⟩

/-- 题述的 `y_l`，所有除法都在实数中进行。 -/
noncomputable def selbergIntervalY (z l : ℕ) : ℝ :=
  if l ≤ z then (μ l : ℝ) / ((Nat.totient l : ℝ) * squarefreeTotientSum z) else 0

/-- 题述的有限权重；非 `P` 的约数处明确取零。 -/
noncomputable def selbergIntervalWeight (z d : ℕ) : ℝ :=
  if d ∣ primorial z then (d : ℝ) *
    ∑ l ∈ (primorial z).divisors with d ∣ l, (μ (l / d) : ℝ) * selbergIntervalY z l else 0

/-- 在非零整数的约数上，取互补约数将倍数方向求和变为普通约数求和。 -/
theorem selberg_divisor_multiples_sum (P d : ℕ) (hP : P ≠ 0) (hd : d ∣ P) (f : ℕ → ℝ) :
    (∑ l ∈ P.divisors with d ∣ l, f l) = ∑ b ∈ (P / d).divisors, f (P / b) := by
  classical
  rw [sum_filter, ← Nat.sum_div_divisors P (fun l => if d ∣ l then f l else 0)]
  have hdcomp : P / d ∣ P := Nat.div_dvd_of_dvd hd
  have heq (b : ℕ) (hb : b ∈ P.divisors) : d ∣ P / b ↔ b ∣ P / d := by
    rw [Nat.dvd_div_iff_mul_dvd (Nat.dvd_of_mem_divisors hb), Nat.dvd_div_iff_mul_dvd hd]
    rw [Nat.mul_comm b d]
  rw [← Nat.divisors_filter_dvd_of_dvd hP hdcomp, sum_filter]
  exact sum_congr rfl (fun b hb => by simp only [heq b hb])

/-- 互补约数将题述的 Möbius 系数变为标准 Möbius 变换。 -/
theorem selberg_upper_moebius_complement (P d : ℕ) (hP : P ≠ 0)
    (hd : d ∣ P) (y : ℕ → ℝ) :
    (∑ l ∈ P.divisors with d ∣ l, (μ (l / d) : ℝ) * y l) =
      ∑ b ∈ (P / d).divisors, (μ ((P / d) / b) : ℝ) * y (P / b) := by
  rw [selberg_divisor_multiples_sum P d hP hd]
  apply sum_congr rfl
  intro b hb
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm b d]

/-- 实际有限上 Möbius 反演：先在互补约数上调用 Mathlib 反演，再换回倍数方向。 -/
theorem selberg_upper_moebius_inversion (P : ℕ) (hP : P ≠ 0) (y : ℕ → ℝ)
    (l : ℕ) (hl : l ∣ P) :
    (∑ d ∈ P.divisors with l ∣ d,
      ∑ a ∈ P.divisors with d ∣ a, (μ (a / d) : ℝ) * y a) = y l := by
  classical
  let a : ℕ → ℝ := fun d => ∑ h ∈ P.divisors with d ∣ h, (μ (h / d) : ℝ) * y h
  let f : ℕ → ℝ := fun n => a (P / n)
  let g : ℕ → ℝ := fun n => y (P / n)
  have htransform : ∀ n > 0, n ∣ P →
      (∑ x ∈ n.divisorsAntidiagonal, (μ x.1 : ℝ) * g x.2) = f n := by
    intro n hn hnP
    have hcomp : P / (P / n) = n := Nat.div_div_self hnP hP
    have hdP : P / n ∣ P := Nat.div_dvd_of_dvd hnP
    dsimp [f, a]
    rw [selberg_upper_moebius_complement P (P / n) hP hdP, hcomp]
    simpa only [g] using (Nat.sum_divisorsAntidiagonal' (n := n)
      (f := fun x b => (μ x : ℝ) * g b))
  have hsum := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq_on
    (f := f) (g := g) {n : ℕ | n ∣ P}
    (fun m n hmn hn => hmn.trans hn)).mpr htransform
  have hnP : P / l ∣ P := Nat.div_dvd_of_dvd hl
  have hnpos : 0 < P / l := Nat.pos_of_dvd_of_pos hnP (Nat.pos_of_ne_zero hP)
  have h := hsum (P / l) hnpos hnP
  change (∑ n ∈ (P / l).divisors, a (P / n)) = y (P / (P / l)) at h
  rw [Nat.div_div_self hl hP] at h
  change (∑ d ∈ P.divisors with l ∣ d, a d) = y l
  rw [selberg_divisor_multiples_sum P l hP hl]
  exact h

/-- 权重在正约数上的有限反演恒等式；除以 `d` 前先证明 `d>0`。 -/
theorem selbergIntervalWeight_inversion (z l : ℕ) (hl : l ∣ primorial z) :
    (∑ d ∈ (primorial z).divisors with l ∣ d,
      selbergIntervalWeight z d / (d : ℝ)) = selbergIntervalY z l := by
  calc
    _ = ∑ d ∈ (primorial z).divisors with l ∣ d,
        ∑ a ∈ (primorial z).divisors with d ∣ a,
          (μ (a / d) : ℝ) * selbergIntervalY z a := by
      apply sum_congr rfl
      intro d hd
      have hdmem := (mem_filter.mp hd).1
      have hddvd := Nat.dvd_of_mem_divisors hdmem
      have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hdmem).ne'
      simp [selbergIntervalWeight, hddvd, hd0]
    _ = _ := selberg_upper_moebius_inversion (primorial z) (primorial_ne_zero z)
      (selbergIntervalY z) l hl

/-- 截断约数上的 `1/φ` 求和就是此前已经定义并证明为正的 `G`。 -/
theorem selbergInterval_reciprocal_sum (z : ℕ) :
    (∑ l ∈ (primorial z).divisors, if l ≤ z then (Nat.totient l : ℝ)⁻¹ else 0) =
      squarefreeTotientSum z := by
  rw [← sum_filter, selbergInterval_divisors_eq]
  rfl

/-- 每个正约数平方自由，故 `|μ(l)|=1`，明确计算 `|y_l|`。 -/
theorem selbergIntervalY_abs (z l : ℕ) (hz : 1 ≤ z) (hl : l ∈ (primorial z).divisors) :
    |selbergIntervalY z l| = if l ≤ z then (Nat.totient l : ℝ)⁻¹ / squarefreeTotientSum z else 0 := by
  have hlpos := Nat.pos_of_mem_divisors hl
  have hphi : (0 : ℝ) < Nat.totient l := by exact_mod_cast Nat.totient_pos.mpr hlpos
  have hG := squarefreeTotientSum_pos z hz
  have hsq := (selbergIntervalProduct_squarefree z).squarefree_of_dvd (Nat.dvd_of_mem_divisors hl)
  have hmu : |(μ l : ℝ)| = 1 := by exact_mod_cast abs_moebius_eq_one_of_squarefree hsq
  by_cases hlz : l ≤ z
  · rw [selbergIntervalY, ite_eq_left hlz, ite_eq_left hlz, abs_div,
      abs_of_pos (mul_pos hphi hG), hmu]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  · simp [selbergIntervalY, hlz]

/-- 题述的归一化条件：`∑|y_l|=1`。 -/
theorem selbergIntervalY_abs_sum (z : ℕ) (hz : 1 ≤ z) :
    (∑ l ∈ (primorial z).divisors, |selbergIntervalY z l|) = 1 := by
  have hG := squarefreeTotientSum_pos z hz
  calc
    _ = ∑ l ∈ (primorial z).divisors,
        (if l ≤ z then (Nat.totient l : ℝ)⁻¹ else 0) / squarefreeTotientSum z := by
      apply sum_congr rfl
      intro l hl
      rw [selbergIntervalY_abs z l hz hl]
      split_ifs <;> simp
    _ = (∑ l ∈ (primorial z).divisors,
        if l ≤ z then (Nat.totient l : ℝ)⁻¹ else 0) / squarefreeTotientSum z := by
      rw [sum_div]
    _ = 1 := by rw [selbergInterval_reciprocal_sum, div_self hG.ne']

theorem selbergIntervalY_moebius_mul (z l : ℕ) (hz : 1 ≤ z)
    (hl : l ∈ (primorial z).divisors) :
    (μ l : ℝ) * selbergIntervalY z l = |selbergIntervalY z l| := by
  have hsq := (selbergIntervalProduct_squarefree z).squarefree_of_dvd (Nat.dvd_of_mem_divisors hl)
  have hmu : (μ l : ℝ)^2 = 1 := by exact_mod_cast moebius_sq_eq_one_of_squarefree hsq
  rw [selbergIntervalY_abs z l hz hl]
  by_cases hlz : l ≤ z
  · rw [selbergIntervalY, ite_eq_left hlz, ite_eq_left hlz]
    calc
      _ = (μ l : ℝ)^2 / ((Nat.totient l : ℝ) * squarefreeTotientSum z) := by ring
      _ = _ := by rw [hmu]; simp [div_eq_mul_inv, mul_inv_rev, mul_comm]
  · simp [selbergIntervalY, hlz]

/-- 实际取得 `w₁=1`，没有把归一化作为假设。 -/
theorem selbergIntervalWeight_one (z : ℕ) (hz : 1 ≤ z) : selbergIntervalWeight z 1 = 1 := by
  classical
  simp only [selbergIntervalWeight, one_dvd, ite_true, Nat.cast_one, one_mul, Nat.div_one,
    filter_true_of_mem (fun _ _ => True.intro)]
  calc
    _ = ∑ l ∈ (primorial z).divisors, |selbergIntervalY z l| :=
      sum_congr rfl (fun l hl => selbergIntervalY_moebius_mul z l hz hl)
    _ = 1 := selbergIntervalY_abs_sum z hz

/-- 非约数处权重为零。 -/
theorem selbergIntervalWeight_of_not_dvd (z d : ℕ) (hd : ¬ d ∣ primorial z) :
    selbergIntervalWeight z d = 0 := by simp [selbergIntervalWeight, hd]

/-- 权重严格支撑于 `d≤z`：若 `d>z`，每个可能的倍数指标都被截断。 -/
theorem selbergIntervalWeight_above (z d : ℕ) (hdz : z < d) : selbergIntervalWeight z d = 0 := by
  classical
  by_cases hd : d ∣ primorial z
  · rw [selbergIntervalWeight, ite_eq_left hd]
    have hzero : (∑ l ∈ (primorial z).divisors with d ∣ l,
        (μ (l / d) : ℝ) * selbergIntervalY z l) = 0 := by
      apply sum_eq_zero
      intro l hl
      obtain ⟨hlP, hdl⟩ := mem_filter.mp hl
      have hdlle := Nat.le_of_dvd (Nat.pos_of_mem_divisors hlP) hdl
      have hlz : ¬ l ≤ z := by omega
      simp [selbergIntervalY, hlz]
    rw [hzero, mul_zero]
  · exact selbergIntervalWeight_of_not_dvd z d hd

/-- 利用 `|μ|≤1`、有限三角不等式及 `∑|y|=1` 得到 `|w_d|≤d`。 -/
theorem selbergIntervalWeight_abs_le (z d : ℕ) (hz : 1 ≤ z) (hd : d ∣ primorial z) :
    |selbergIntervalWeight z d| ≤ (d : ℝ) := by
  classical
  have hsum : |∑ l ∈ (primorial z).divisors with d ∣ l,
      (μ (l / d) : ℝ) * selbergIntervalY z l| ≤ 1 := by
    calc
      _ ≤ ∑ l ∈ (primorial z).divisors with d ∣ l,
          |(μ (l / d) : ℝ) * selbergIntervalY z l| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ l ∈ (primorial z).divisors with d ∣ l, |selbergIntervalY z l| := by
        apply sum_le_sum
        intro l hl
        have hmu : |(μ (l / d) : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one (n := l / d)
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_right hmu (abs_nonneg _)).trans_eq (one_mul _)
      _ ≤ ∑ l ∈ (primorial z).divisors, |selbergIntervalY z l| :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => abs_nonneg _)
      _ = 1 := selbergIntervalY_abs_sum z hz
  rw [selbergIntervalWeight, ite_eq_left hd, abs_mul, abs_of_nonneg (Nat.cast_nonneg d)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg d)

/-- 实际截断支撑后求和，得到 `∑_{d|P}|w_d|≤z²`。 -/
theorem selbergIntervalWeight_abs_sum (z : ℕ) (hz : 1 ≤ z) :
    (∑ d ∈ (primorial z).divisors, |selbergIntervalWeight z d|) ≤ (z : ℝ)^2 := by
  classical
  have htruncate : (∑ d ∈ (primorial z).divisors, |selbergIntervalWeight z d|) =
      ∑ d ∈ (primorial z).divisors with d ≤ z, |selbergIntervalWeight z d| := by
    symm
    apply sum_subset (filter_subset _ _)
    intro d hd hnot
    have hdz : z < d := by
      by_contra h
      exact hnot (mem_filter.mpr ⟨hd, by omega⟩)
    rw [selbergIntervalWeight_above z d hdz, abs_zero]
  rw [htruncate, selbergInterval_divisors_eq]
  have hcard : (squarefreeHarmonicIndices z).card ≤ z := by
    calc
      _ ≤ (Icc 1 z).card := card_filter_le _ _
      _ = z := by simp
  calc
    _ ≤ ∑ d ∈ squarefreeHarmonicIndices z, (d : ℝ) := by
      apply sum_le_sum
      intro d hd
      have hP : d ∣ primorial z := by
        have hh : d ∈ (primorial z).divisors.filter (fun d => d ≤ z) :=
          by rw [selbergInterval_divisors_eq]; exact hd
        exact Nat.dvd_of_mem_divisors (mem_filter.mp hh).1
      exact selbergIntervalWeight_abs_le z d hz hP
    _ ≤ ∑ _d ∈ squarefreeHarmonicIndices z, (z : ℝ) := by
      apply sum_le_sum
      intro d hd
      exact_mod_cast (mem_Icc.mp (mem_filter.mp hd).1).2
    _ = ((squarefreeHarmonicIndices z).card : ℝ) * (z : ℝ) := by simp
    _ ≤ (z : ℝ)^2 := by
      have hc : ((squarefreeHarmonicIndices z).card : ℝ) ≤ z := by exact_mod_cast hcard
      nlinarith

/-- 适配 Mathlib 筛接口的真实算术函数 `ν(d)=1/d`，包括 `ν(0)=0`。 -/
noncomputable def selbergIntervalNu : ArithmeticFunction ℝ :=
  ⟨fun d => (d : ℝ)⁻¹, by simp⟩

theorem selbergIntervalNu_mult : selbergIntervalNu.IsMultiplicative := by
  constructor
  · norm_num [selbergIntervalNu]
  · intro a b hab
    simp [selbergIntervalNu, Nat.cast_mul, mul_inv_rev, mul_comm]

/-- 为对角化实际构造 `BoundingSieve`：支撑、质量取零，仅有限代数结构参与证明。
`ν` 的乘法性及素数上的严格正性、严格小于一均已验证。 -/
noncomputable def selbergIntervalSieve (z : ℕ) : BoundingSieve where
  support := ∅
  prodPrimes := primorial z
  prodPrimes_squarefree := selbergIntervalProduct_squarefree z
  weights := fun _ => 0
  weights_nonneg := fun _ => le_rfl
  totalMass := 0
  nu := selbergIntervalNu
  nu_mult := selbergIntervalNu_mult
  nu_pos_of_prime := by
    intro p hp hpd
    change (0 : ℝ) < (p : ℝ)⁻¹
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
    positivity
  nu_lt_one_of_prime := by
    intro p hp hpd
    change (p : ℝ)⁻¹ < 1
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
    rw [inv_lt_one₀ hpR]
    exact_mod_cast hp.one_lt

@[simp] theorem selbergIntervalSieve_nu (z n : ℕ) :
    (selbergIntervalSieve z).nu n = (n : ℝ)⁻¹ := rfl

/-- 由 `∑_{d|n}φ(d)=n` 和已证 Möbius 反演，识别 Mathlib 的对角系数为 `φ(l)`。 -/
theorem selbergIntervalSieve_diagonalCoeff (z l : ℕ) (hl : l ∣ primorial z) :
    ((selbergIntervalSieve z).selbergTerms l)⁻¹ = (Nat.totient l : ℝ) := by
  have hlpos : 0 < l := Nat.pos_of_dvd_of_pos hl (primorial_pos z)
  have hphiSum : ∀ n : ℕ, n > 0 → (∑ d ∈ n.divisors, (Nat.totient d : ℝ)) = (n : ℝ) := by
    intro n hn
    exact_mod_cast Nat.sum_totient n
  have hinv := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := fun d => (Nat.totient d : ℝ)) (g := fun n => (n : ℝ))).mp hphiSum l hlpos
  have hsq := (selbergIntervalProduct_squarefree z).squarefree_of_dvd hl
  have hnu : (selbergIntervalSieve z).nu l ≠ 0 := by
    rw [selbergIntervalSieve_nu]
    exact inv_ne_zero (by exact_mod_cast hlpos.ne')
  have h := BoundingSieve.inv_selbergTerms_eq_sum_divisors_moebius_nu
    (s := selbergIntervalSieve z) hsq hnu
  simp only [selbergIntervalSieve_nu, inv_inv] at h
  exact h.trans hinv

/-- 将 Mathlib 的主二次型精确识别为题述的 `w_d w_e / lcm(d,e)`。 -/
theorem selbergIntervalSieve_mainSum (z : ℕ) (w : ℕ → ℝ) :
    (selbergIntervalSieve z).mainSum (BoundingSieve.lambdaSquared w) =
      ∑ d ∈ (primorial z).divisors, ∑ e ∈ (primorial z).divisors,
        w d * w e / (Nat.lcm d e : ℝ) := by
  rw [BoundingSieve.mainSum_lambdaSquared_eq_sum_sum_mul]
  apply sum_congr rfl
  intro d hd
  apply sum_congr rfl
  intro e he
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  have heR : (e : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors he).ne'
  have hlR : (Nat.lcm d e : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.lcm_pos (Nat.pos_of_mem_divisors hd) (Nat.pos_of_mem_divisors he)).ne'
  have hprod : (Nat.gcd d e : ℝ) * (Nat.lcm d e : ℝ) = (d : ℝ) * (e : ℝ) := by
    exact_mod_cast Nat.gcd_mul_lcm d e
  have hscalar : (d : ℝ)⁻¹ * (e : ℝ)⁻¹ * (Nat.gcd d e : ℝ) = 1 / (Nat.lcm d e : ℝ) := by
    apply (eq_div_iff hlR).2
    calc
      _ = ((d : ℝ)⁻¹ * (e : ℝ)⁻¹) * ((Nat.gcd d e : ℝ) * (Nat.lcm d e : ℝ)) := by ring
      _ = ((d : ℝ)⁻¹ * (e : ℝ)⁻¹) * ((d : ℝ) * (e : ℝ)) := by rw [hprod]
      _ = 1 := by field_simp
  simp only [selbergIntervalSieve_nu, inv_inv]
  calc
    _ = (w d * w e) * ((d : ℝ)⁻¹ * (e : ℝ)⁻¹ * (Nat.gcd d e : ℝ)) := by ring
    _ = _ := by rw [hscalar]; ring

/-- 实际调用 Mathlib 的二次型对角化，并用已证明的权重反演消去内层求和。 -/
theorem selbergIntervalWeight_diagonalization (z : ℕ) :
    (∑ d ∈ (primorial z).divisors, ∑ e ∈ (primorial z).divisors,
      selbergIntervalWeight z d * selbergIntervalWeight z e / (Nat.lcm d e : ℝ)) =
      ∑ l ∈ (primorial z).divisors, (Nat.totient l : ℝ) * selbergIntervalY z l ^ 2 := by
  calc
    _ = (selbergIntervalSieve z).mainSum
        (BoundingSieve.lambdaSquared (selbergIntervalWeight z)) :=
      (selbergIntervalSieve_mainSum z (selbergIntervalWeight z)).symm
    _ = ∑ l ∈ (primorial z).divisors,
        ((selbergIntervalSieve z).selbergTerms l)⁻¹ *
          (∑ d ∈ (primorial z).divisors,
            if l ∣ d then (selbergIntervalSieve z).nu d * selbergIntervalWeight z d else 0)^2 :=
      BoundingSieve.mainSum_lambdaSquared_eq_sum_mul_sum_sq _
    _ = _ := by
      apply sum_congr rfl
      intro l hl
      rw [selbergIntervalSieve_diagonalCoeff z l (Nat.dvd_of_mem_divisors hl)]
      have hinner : (∑ d ∈ (primorial z).divisors,
          if l ∣ d then (selbergIntervalSieve z).nu d * selbergIntervalWeight z d else 0) =
          selbergIntervalY z l := by
        rw [← sum_filter]
        calc
          _ = ∑ d ∈ (primorial z).divisors with l ∣ d,
              selbergIntervalWeight z d / (d : ℝ) := by
            apply sum_congr rfl
            intro d hd
            rw [selbergIntervalSieve_nu]
            ring
          _ = _ := selbergIntervalWeight_inversion z l (Nat.dvd_of_mem_divisors hl)
      rw [hinner]

/-- 平方自由性使 `μ(l)²=1`，从而每个对角项等于 `|y_l|/G`。 -/
theorem selbergIntervalY_diagonal_term (z l : ℕ) (hz : 1 ≤ z)
    (hl : l ∈ (primorial z).divisors) :
    (Nat.totient l : ℝ) * selbergIntervalY z l ^ 2 = |selbergIntervalY z l| / squarefreeTotientSum z := by
  have hlpos := Nat.pos_of_mem_divisors hl
  have hphi : (0 : ℝ) < Nat.totient l := by exact_mod_cast Nat.totient_pos.mpr hlpos
  have hG := squarefreeTotientSum_pos z hz
  have hsq := (selbergIntervalProduct_squarefree z).squarefree_of_dvd (Nat.dvd_of_mem_divisors hl)
  have hmu : (μ l : ℝ)^2 = 1 := by exact_mod_cast moebius_sq_eq_one_of_squarefree hsq
  rw [selbergIntervalY_abs z l hz hl]
  by_cases hlz : l ≤ z
  · rw [selbergIntervalY, ite_eq_left hlz, ite_eq_left hlz]
    calc
      _ = (μ l : ℝ)^2 / ((Nat.totient l : ℝ) * squarefreeTotientSum z ^ 2) := by
        field_simp
      _ = _ := by rw [hmu]; simp [div_eq_mul_inv, mul_inv_rev, pow_two]; ring
  · simp [selbergIntervalY, hlz]

/-- 题述二次型的精确值为 `1/G`，包括 `z=1`、`P=1`。 -/
theorem selbergIntervalWeight_quadratic (z : ℕ) (hz : 1 ≤ z) :
    (∑ d ∈ (primorial z).divisors, ∑ e ∈ (primorial z).divisors,
      selbergIntervalWeight z d * selbergIntervalWeight z e / (Nat.lcm d e : ℝ)) =
      (∑ l ∈ (primorial z).divisors, (Nat.totient l : ℝ) * selbergIntervalY z l ^ 2) ∧
    (∑ l ∈ (primorial z).divisors, (Nat.totient l : ℝ) * selbergIntervalY z l ^ 2) =
      1 / squarefreeTotientSum z := by
  refine ⟨selbergIntervalWeight_diagonalization z, ?_⟩
  calc
    _ = ∑ l ∈ (primorial z).divisors, |selbergIntervalY z l| / squarefreeTotientSum z :=
      sum_congr rfl (fun l hl => selbergIntervalY_diagonal_term z l hz hl)
    _ = (∑ l ∈ (primorial z).divisors, |selbergIntervalY z l|) / squarefreeTotientSum z := by
      rw [sum_div]
    _ = _ := by rw [selbergIntervalY_abs_sum z hz]

/-- 最小边界 `z=1`：`P=1` 且唯一非零权重为 `w₁=1`。 -/
theorem selbergIntervalWeight_at_one (d : ℕ) :
    primorial 1 = 1 ∧ selbergIntervalWeight 1 d = if d = 1 then 1 else 0 := by
  refine ⟨primorial_one, ?_⟩
  by_cases hd : d = 1
  · subst d
    simp [selbergIntervalWeight_one 1 le_rfl]
  · have hnot : ¬ d ∣ primorial 1 := by simpa only [primorial_one, Nat.dvd_one] using hd
    simp [selbergIntervalWeight_of_not_dvd 1 d hnot, hd]

#print axioms selbergInterval_divisors_eq
#print axioms selbergIntervalWeight_one
#print axioms selbergIntervalWeight_abs_sum
#print axioms selbergIntervalWeight_inversion
#print axioms selbergIntervalWeight_quadratic
#print axioms selbergIntervalWeight_at_one

end LonelyRunner
