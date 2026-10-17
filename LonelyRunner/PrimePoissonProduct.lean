import LonelyRunner.CirclePoisson
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.PSeries

/-!
# 有限素数 Poisson 核乘积

沿用 `CirclePoisson` 的单圆周核与 `circleHaar`，为后续 GCD 积分表示准备
独立圆周坐标的乘积概率测度。本文件只证明有限乘积与统一矩界。
-/

open MeasureTheory
open scoped Real

namespace LonelyRunner


/-- 有限个圆周的独立 Haar 概率测度。 -/
noncomputable def circleProductHaar (ι : Type*) [Fintype ι] : Measure (ι → UnitAddCircle) :=
  Measure.pi (fun _ : ι => circleHaar)

instance (ι : Type*) [Fintype ι] : IsProbabilityMeasure (circleProductHaar ι) := by
  unfold circleProductHaar
  infer_instance

/-- 有限坐标函数乘积可积；直接调用 Mathlib 的有限乘积可积性定理。 -/
theorem circleProduct_integrable {ι : Type*} [Fintype ι]
    (f : ι → UnitAddCircle → ℝ) (hf : ∀ i, Integrable (f i) circleHaar) :
    Integrable (fun t : ι → UnitAddCircle => ∏ i, f i (t i)) (circleProductHaar ι) := by
  unfold circleProductHaar
  exact Integrable.fintype_prod hf

/-- 有限坐标乘积的积分等于各坐标积分的乘积。 -/
theorem circleProduct_integral {ι : Type*} [Fintype ι]
    (f : ι → UnitAddCircle → ℝ) :
    (∫ t : ι → UnitAddCircle, (∏ i, f i (t i)) ∂circleProductHaar ι) =
      ∏ i, ∫ t : UnitAddCircle, f i t ∂circleHaar := by
  unfold circleProductHaar
  exact integral_fintype_prod_eq_prod f

/-- 有限素数集的 Poisson 核乘积。 -/
noncomputable def primePoissonProduct (σ : ℝ) (F : Finset ℕ)
    (t : F → UnitAddCircle) : ℝ :=
  ∏ p : F, circlePoisson ((p.val : ℝ) ^ (-σ)) (t p)

/-- 每个素数对应的半径严格为正且不超过 `3/4`。 -/
theorem primePoisson_rate (σ : ℝ) (hσ : 1 / 2 < σ)
    {p : ℕ} (hp : p.Prime) :
    0 < (p : ℝ) ^ (-σ) ∧ (p : ℝ) ^ (-σ) ≤ 3 / 4 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have h1 : (p : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith)
  have h2 : (2 : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hsqrt : (4 / 3 : ℝ) ≤ Real.sqrt 2 := by
    have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith
  have h3 : (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 3 / 4 := by
    rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
    have hspos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    apply (inv_le_comm₀ hspos (by norm_num)).2
    nlinarith [hsqrt]
  exact ⟨Real.rpow_pos_of_pos hp0 _, (h1.trans h2).trans h3⟩

/-- 有限素数核乘积连续。 -/
theorem primePoissonProduct_continuous (σ : ℝ) (hσ : 1 / 2 < σ)
    (F : Finset ℕ) (hF : ∀ p ∈ F, p.Prime) :
    Continuous (primePoissonProduct σ F) := by
  unfold primePoissonProduct
  apply continuous_finsetProd
  intro p hp
  have hr := primePoisson_rate σ hσ (hF p.val p.property)
  exact (circlePoisson_continuous _ hr.1.le (lt_of_le_of_lt hr.2 (by norm_num))).comp
    (continuous_apply p)

/-- 有限素数核乘积逐点非负。 -/
theorem primePoissonProduct_nonneg (σ : ℝ) (hσ : 1 / 2 < σ)
    (F : Finset ℕ) (hF : ∀ p ∈ F, p.Prime)
    (t : F → UnitAddCircle) : 0 ≤ primePoissonProduct σ F t := by
  unfold primePoissonProduct
  exact Finset.prod_nonneg fun p hp => by
    have hr := primePoisson_rate σ hσ (hF p.val p.property)
    exact circlePoisson_nonneg _ hr.1.le (lt_of_le_of_lt hr.2 (by norm_num)) _

/-- 有限素数核乘积对乘积 Haar 概率测度可积。 -/
theorem primePoissonProduct_integrable (σ : ℝ) (hσ : 1 / 2 < σ)
    (F : Finset ℕ) (hF : ∀ p ∈ F, p.Prime) :
    Integrable (primePoissonProduct σ F) (circleProductHaar F) := by
  unfold primePoissonProduct
  apply circleProduct_integrable
  intro p
  have hr := primePoisson_rate σ hσ (hF p.val p.property)
  exact circlePoisson_integrable _ hr.1.le (lt_of_le_of_lt hr.2 (by norm_num))

/-- 有限素数核乘积的积分为一；空乘积也适用。 -/
theorem primePoissonProduct_integral_one (σ : ℝ) (hσ : 1 / 2 < σ)
    (F : Finset ℕ) (hF : ∀ p ∈ F, p.Prime) :
    (∫ t : F → UnitAddCircle, primePoissonProduct σ F t ∂circleProductHaar F) = 1 := by
  change (∫ t : F → UnitAddCircle,
    (∏ p : F, circlePoisson ((p.val : ℝ) ^ (-σ)) (t p)) ∂circleProductHaar F) = 1
  rw [circleProduct_integral]
  apply Finset.prod_eq_one
  intro p hp
  have hr := primePoisson_rate σ hσ (hF p.val p.property)
  exact circlePoisson_integral_one _ hr.1.le (lt_of_le_of_lt hr.2 (by norm_num))

/-- 有限素数核乘积的任意自然数次幂可积。 -/
theorem primePoissonProduct_pow_integrable (σ : ℝ) (hσ : 1 / 2 < σ)
    (F : Finset ℕ) (hF : ∀ p ∈ F, p.Prime) (k : ℕ) :
    Integrable (fun t => (primePoissonProduct σ F t) ^ k) (circleProductHaar F) := by
  have hc := primePoissonProduct_continuous σ hσ F hF
  have hf : Continuous (fun t : F → UnitAddCircle => (primePoissonProduct σ F t) ^ k) :=
    hc.pow k
  obtain ⟨M, hM⟩ := (isCompact_range hf).isBounded.exists_norm_le
  apply Integrable.of_bound hf.aestronglyMeasurable M
  filter_upwards [] with t
  exact hM _ ⟨t, rfl⟩

/-- `k` 次矩精确分解成各个素数坐标的矩。 -/
theorem primePoissonProduct_pow_integral (σ : ℝ) (F : Finset ℕ) (k : ℕ) :
    (∫ t : F → UnitAddCircle, (primePoissonProduct σ F t) ^ k ∂circleProductHaar F) =
      ∏ p : F, (∫ t : UnitAddCircle, (circlePoisson ((p.val : ℝ) ^ (-σ)) t) ^ k ∂circleHaar) := by
  change (∫ t : F → UnitAddCircle,
    (∏ p : F, circlePoisson ((p.val : ℝ) ^ (-σ)) (t p)) ^ k ∂circleProductHaar F) = _
  have hprod (t : F → UnitAddCircle) :
      (∏ p : F, circlePoisson ((p.val : ℝ) ^ (-σ)) (t p)) ^ k =
        ∏ p : F, (circlePoisson ((p.val : ℝ) ^ (-σ)) (t p)) ^ k := by
    simpa only using
      (Finset.prod_pow (Finset.univ : Finset F) k
        (fun p : F => circlePoisson ((p.val : ℝ) ^ (-σ)) (t p))).symm
  simp_rw [hprod]
  exact circleProduct_integral (fun p : F => fun t => (circlePoisson ((p.val : ℝ) ^ (-σ)) t) ^ k)

/-- 空素数集的核恒为一，任意自然数次矩亦为一。 -/
theorem primePoissonProduct_empty (σ : ℝ) (k : ℕ) :
    (∀ t : (∅ : Finset ℕ) → UnitAddCircle, primePoissonProduct σ ∅ t = 1) ∧
    (∫ t : (∅ : Finset ℕ) → UnitAddCircle,
      (primePoissonProduct σ ∅ t) ^ k ∂circleProductHaar (∅ : Finset ℕ)) = 1 := by
  constructor
  · intro t
    simp [primePoissonProduct]
  · simp [primePoissonProduct]

/-- `σ>1/2` 时，`k≥2` 的所有有限素数乘积矩由仅依赖 `σ,k` 的正常数统一控制。 -/
theorem primePoissonProduct_uniform_moment (σ : ℝ) (hσ : 1 / 2 < σ)
    (k : ℕ) (hk : 2 ≤ k) :
    ∃ B : ℝ, 0 < B ∧ ∀ (F : Finset ℕ), (∀ p ∈ F, p.Prime) →
      (∫ t : F → UnitAddCircle, (primePoissonProduct σ F t) ^ k
        ∂circleProductHaar F) ≤ B := by
  obtain ⟨Ck, hCk, hmoment⟩ := circlePoisson_moment_bound k hk
  let S : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-(2 * σ))
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (-(2 * σ))) := by
    have heq (n : ℕ) : (n : ℝ) ^ (-(2 * σ)) = 1 / (n : ℝ) ^ (2 * σ) := by
      rw [Real.rpow_neg (Nat.cast_nonneg _), one_div]
    simpa only [heq] using
      (Real.summable_one_div_nat_rpow.mpr (by linarith : 1 < 2 * σ))
  refine ⟨Real.exp (Ck * S), Real.exp_pos _, ?_⟩
  intro F hF
  have hfin : (∑ p : F, (p.val : ℝ) ^ (-(2 * σ))) ≤ S := by
    change (∑ p : F, (p.val : ℝ) ^ (-(2 * σ))) ≤
      ∑' n : ℕ, (n : ℝ) ^ (-(2 * σ))
    have h := hsum.sum_le_tsum F
      (fun n hn => Real.rpow_nonneg (by positivity) _)
    rw [← Finset.sum_attach, Finset.attach_eq_univ] at h
    exact h
  rw [primePoissonProduct_pow_integral]
  calc
    (∏ p : F, (∫ t : UnitAddCircle,
      (circlePoisson ((p.val : ℝ) ^ (-σ)) t) ^ k ∂circleHaar))
      ≤ ∏ p : F, (1 + Ck * (p.val : ℝ) ^ (-(2 * σ))) := by
        apply Finset.prod_le_prod₀
        · intro p hp
          exact integral_nonneg fun t => pow_nonneg
            (circlePoisson_nonneg _
              (primePoisson_rate σ hσ (hF p.val p.property)).1.le
              (lt_of_le_of_lt (primePoisson_rate σ hσ (hF p.val p.property)).2
                (by norm_num)) t) _
        · intro p hp
          have hr := primePoisson_rate σ hσ (hF p.val p.property)
          have h := hmoment _ hr.1.le hr.2
          have hp0 : (0 : ℝ) ≤ p.val := by positivity
          have heq : ((p.val : ℝ) ^ (-σ)) ^ 2 =
              (p.val : ℝ) ^ (-(2 * σ)) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hp0]
            congr 1
            ring
          rwa [heq] at h
    _ ≤ Real.exp (∑ p : F, Ck * (p.val : ℝ) ^ (-(2 * σ))) := by
      simpa only using
        Real.prod_one_add_le_exp_sum (Finset.univ : Finset F)
          (fun p : F => mul_nonneg hCk.le (Real.rpow_nonneg (by positivity) _))
    _ ≤ Real.exp (Ck * S) := by
      rw [← Finset.mul_sum]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hfin hCk.le)

end LonelyRunner
