import LonelyRunner.GcdPoissonRepresentation

/-!
# GCD 和的无条件弱幂次界

利用有限 Poisson 乘积的统一矩界及精确积分表示，得到对任意正速度有限集
`S₂(V) ≪_η |V|^(1+η)`。不涉及 Bondarenko–Seip 的精细指数。
-/

open MeasureTheory
open scoped Real

namespace LonelyRunner

private theorem truncation_pointwise (k : ℕ) (hk : 2 ≤ k)
    (m T z d : ℝ) (hm : 1 ≤ m) (hT : 0 < T) (hzk : 0 ≤ z)
    (hd : 0 ≤ d) (hdm : d ≤ m) :
    z * d ^ 2 ≤ T * d ^ 2 + T ^ (1 - (k : ℝ)) * z ^ k * m ^ 2 := by
  by_cases hzT : z ≤ T
  · have hmain := mul_le_mul_of_nonneg_right hzT (sq_nonneg d)
    have hextra : 0 ≤ T ^ (1 - (k : ℝ)) * z ^ k * m ^ 2 := by positivity
    linarith
  · have hzT' : T ≤ z := le_of_lt (lt_of_not_ge hzT)
    have hpow : T ^ (k - 1) ≤ z ^ (k - 1) :=
      pow_le_pow_left₀ hT.le hzT' _
    have hzk' : T ^ (k - 1) * z ≤ z ^ k := by
      have h := mul_le_mul_of_nonneg_right hpow hzk
      calc
        _ ≤ z ^ (k - 1) * z := h
        _ = z ^ k := by
          rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ k)]
    have hexp : 1 - (k : ℝ) + ((k - 1 : ℕ) : ℝ) = 0 := by
      have hk1 : 1 ≤ k := by omega
      rw [Nat.cast_sub hk1]
      push_cast
      ring
    have hcancel : T ^ (1 - (k : ℝ)) * T ^ (k - 1) = 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hT, hexp, Real.rpow_zero]
    have hbound : z ≤ T ^ (1 - (k : ℝ)) * z ^ k := by
      have h := mul_le_mul_of_nonneg_left hzk'
        (Real.rpow_nonneg hT.le (1 - (k : ℝ)))
      nlinarith [hcancel]
    have hd2 : d ^ 2 ≤ m ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hdm)
        (add_nonneg hd (le_trans zero_le_one hm))]
    have h1 := mul_le_mul_of_nonneg_right hbound (sq_nonneg d)
    have h2 : T ^ (1 - (k : ℝ)) * z ^ k * d ^ 2 ≤
        T ^ (1 - (k : ℝ)) * z ^ k * m ^ 2 :=
      mul_le_mul_of_nonneg_left hd2
        (mul_nonneg (Real.rpow_nonneg hT.le _) (pow_nonneg hzk k))
    nlinarith [h1, h2]

private theorem truncation_scale (k : ℕ) (hk : 2 ≤ k)
    (m : ℝ) (hm : 1 ≤ m) :
    let T := m ^ (1 / (k : ℝ))
    0 < T ∧ T * m = m ^ (1 + 1 / (k : ℝ)) ∧
      T ^ (1 - (k : ℝ)) * m ^ 2 = m ^ (1 + 1 / (k : ℝ)) := by
  dsimp
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hT : 0 < m ^ (1 / (k : ℝ)) := Real.rpow_pos_of_pos hm0 _
  refine ⟨hT, ?_, ?_⟩
  · calc
      m ^ (1 / (k : ℝ)) * m = m ^ (1 / (k : ℝ)) * m ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = m ^ (1 / (k : ℝ) + 1) := (Real.rpow_add hm0 _ _).symm
      _ = m ^ (1 + 1 / (k : ℝ)) := by ring
  · calc
      (m ^ (1 / (k : ℝ))) ^ (1 - (k : ℝ)) * m ^ 2 =
          m ^ ((1 / (k : ℝ)) * (1 - (k : ℝ))) * m ^ (2 : ℝ) := by
            rw [← Real.rpow_mul hm0.le, Real.rpow_two]
      _ = m ^ ((1 / (k : ℝ)) * (1 - (k : ℝ)) + 2) :=
        (Real.rpow_add hm0 _ _).symm
      _ = m ^ (1 + 1 / (k : ℝ)) := by
        congr 1
        field_simp
        ring

/-- 固定 `σ>1/2` 与 `k≥2` 时，GCD 核和由 `m^(1+1/k)` 统一控制。 -/
theorem gcdKernel_sum_subpower (σ : ℝ) (hσ : 1 / 2 < σ)
    (k : ℕ) (hk : 2 ≤ k) :
    ∃ A : ℝ, 0 < A ∧ ∀ (V : Finset ℕ),
      (∀ n ∈ V, 0 < n) → 1 ≤ V.card →
        (∑ a ∈ V, ∑ b ∈ V, gcdKernel σ a b) ≤
          A * (V.card : ℝ) ^ (1 + 1 / (k : ℝ)) := by
  obtain ⟨B, hB, hmoment⟩ := primePoissonProduct_uniform_moment σ hσ k hk
  refine ⟨1 + B, by positivity, ?_⟩
  intro V hV hcard
  let F := gcdPrimeSet V
  let m : ℝ := V.card
  let T : ℝ := m ^ (1 / (k : ℝ))
  have hm : 1 ≤ m := by
    change (1 : ℝ) ≤ (V.card : ℝ)
    exact_mod_cast hcard
  obtain ⟨hT, hTm, hTtail⟩ := truncation_scale k hk m hm
  have hZcont := primePoissonProduct_continuous σ hσ F
    (fun p hp => gcdPrimeSet_prime V hp)
  have hDcont := gcdCharacterSum_continuous V
  have hLcont : Continuous (fun t : F → UnitAddCircle =>
      primePoissonProduct σ F t * ‖gcdCharacterSum V t‖ ^ 2) :=
    hZcont.mul (hDcont.norm.pow 2)
  have hLint : Integrable (fun t : F → UnitAddCircle =>
      primePoissonProduct σ F t * ‖gcdCharacterSum V t‖ ^ 2)
      (circleProductHaar F) := by
    obtain ⟨M, hM⟩ := (isCompact_range hLcont).isBounded.exists_norm_le
    apply Integrable.of_bound hLcont.aestronglyMeasurable M
    filter_upwards [] with t
    exact hM _ ⟨t, rfl⟩
  have hDint : Integrable (fun t : F → UnitAddCircle =>
      ‖gcdCharacterSum V t‖ ^ 2) (circleProductHaar F) :=
    gcdCharacterSum_normSq_integrable V
  have hZint : Integrable (fun t : F → UnitAddCircle =>
      (primePoissonProduct σ F t) ^ k) (circleProductHaar F) :=
    primePoissonProduct_pow_integrable σ hσ F
      (fun p hp => gcdPrimeSet_prime V hp) k
  have hTailInt : Integrable (fun t : F → UnitAddCircle =>
      T ^ (1 - (k : ℝ)) * m ^ 2 * (primePoissonProduct σ F t) ^ k)
        (circleProductHaar F) := hZint.const_mul _
  have hRint : Integrable (fun t : F → UnitAddCircle =>
      T * ‖gcdCharacterSum V t‖ ^ 2 +
        T ^ (1 - (k : ℝ)) * m ^ 2 * (primePoissonProduct σ F t) ^ k)
        (circleProductHaar F) := (hDint.const_mul T).add hTailInt
  have hpoint (t : F → UnitAddCircle) :
      primePoissonProduct σ F t * ‖gcdCharacterSum V t‖ ^ 2 ≤
        T * ‖gcdCharacterSum V t‖ ^ 2 +
          T ^ (1 - (k : ℝ)) * m ^ 2 * (primePoissonProduct σ F t) ^ k := by
    have hz := primePoissonProduct_nonneg σ hσ F
      (fun p hp => gcdPrimeSet_prime V hp) t
    have hd := gcdCharacterSum_norm_le V t
    have h := truncation_pointwise k hk m T
      (primePoissonProduct σ F t) ‖gcdCharacterSum V t‖
      hm hT hz (norm_nonneg _) (by simpa [m] using hd)
    nlinarith [h]
  have hInt := integral_mono_ae hLint hRint (Filter.Eventually.of_forall hpoint)
  have hIntEq :
      (∫ t : F → UnitAddCircle,
        (T * ‖gcdCharacterSum V t‖ ^ 2 +
          T ^ (1 - (k : ℝ)) * m ^ 2 * (primePoissonProduct σ F t) ^ k)
          ∂circleProductHaar F) =
        T * m + T ^ (1 - (k : ℝ)) * m ^ 2 *
          (∫ t : F → UnitAddCircle,
            (primePoissonProduct σ F t) ^ k ∂circleProductHaar F) := by
    rw [integral_add (hDint.const_mul T) hTailInt]
    rw [integral_const_mul, integral_const_mul,
      gcdCharacterSum_integral_normSq V hV]
  have hB' := hmoment F (fun p hp => gcdPrimeSet_prime V hp)
  rw [gcdPoisson_integral_normSq σ hσ V hV] at hInt
  rw [hIntEq] at hInt
  have hCoeff : 0 ≤ T ^ (1 - (k : ℝ)) * m ^ 2 := by positivity
  have hBound := mul_le_mul_of_nonneg_left hB' hCoeff
  change (∑ a ∈ V, ∑ b ∈ V, gcdKernel σ a b) ≤
    (1 + B) * m ^ (1 + 1 / (k : ℝ))
  nlinarith [hInt, hBound, hTm, hTtail]

private theorem halfKernel_pointwise (α m x : ℝ)
    (hα : 1 < α) (hm : 1 ≤ m) (hx : 0 ≤ x) :
    x ≤ 1 / m + m ^ (α - 1) * x ^ α := by
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hmexp : 0 < m ^ (α - 1) := Real.rpow_pos_of_pos hm0 _
  by_cases hsmall : x ≤ 1 / m
  · have hterm : 0 ≤ m ^ (α - 1) * x ^ α := by positivity
    linarith
  · have hxpos : 0 < x := lt_of_le_of_lt (by positivity : 0 ≤ (1 / m : ℝ))
        (lt_of_not_ge hsmall)
    have hbase : 1 / m ≤ x := le_of_lt (lt_of_not_ge hsmall)
    have hpow : (1 / m) ^ (α - 1) ≤ x ^ (α - 1) :=
      Real.rpow_le_rpow (by positivity) hbase (by linarith)
    have hscale : m ^ (α - 1) * (1 / m) ^ (α - 1) = 1 := by
      rw [← Real.mul_rpow (by positivity) (by positivity), mul_one_div_cancel hm0.ne',
        Real.one_rpow]
    have h1 := mul_le_mul_of_nonneg_left hpow hmexp.le
    have h2 := mul_le_mul_of_nonneg_left h1 hx
    have hident : x * (m ^ (α - 1) * x ^ (α - 1)) =
        m ^ (α - 1) * x ^ α := by
      calc
        x * (m ^ (α - 1) * x ^ (α - 1)) =
            m ^ (α - 1) * (x ^ (1 : ℝ) * x ^ (α - 1)) := by
              rw [Real.rpow_one]; ring
        _ = m ^ (α - 1) * x ^ α := by
          rw [← Real.rpow_add hxpos]
          ring
    rw [hscale] at h2
    rw [hident] at h2
    simp only [mul_one] at h2
    have hInv : 0 ≤ 1 / m := by positivity
    linarith

/-- 从一般 `σ` 核的界返回半次核，明确保留首项 `m`。 -/
theorem gcdKernel_half_sum_bound (σ : ℝ) (hσ : 1 / 2 < σ)
    (k : ℕ) (hk : 2 ≤ k) :
    ∃ A : ℝ, 0 < A ∧ ∀ (V : Finset ℕ),
      (∀ n ∈ V, 0 < n) → 1 ≤ V.card →
        (∑ a ∈ V, ∑ b ∈ V, gcdKernel ((1 : ℝ) / 2) a b) ≤
          (V.card : ℝ) +
            A * (V.card : ℝ) ^ (2 * σ + 1 / (k : ℝ)) := by
  obtain ⟨A, hA, hbound⟩ := gcdKernel_sum_subpower σ hσ k hk
  refine ⟨A, hA, ?_⟩
  intro V hV hcard
  let m : ℝ := V.card
  have hm : 1 ≤ m := by
    change (1 : ℝ) ≤ (V.card : ℝ)
    exact_mod_cast hcard
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hpoint (a b : ℕ) (ha : a ∈ V) (hb : b ∈ V) :
      gcdKernel ((1 : ℝ) / 2) a b ≤
        1 / m + m ^ (2 * σ - 1) * gcdKernel σ a b := by
    have hx := (gcdKernel_pos_le_one ((1 : ℝ) / 2) (by norm_num)
      a b (hV a ha) (hV b hb)).1.le
    have h := halfKernel_pointwise (2 * σ) m
      (gcdKernel ((1 : ℝ) / 2) a b) (by linarith) hm hx
    rwa [← gcdKernel_eq_half_rpow σ (by linarith) a b (hV a ha) (hV b hb)] at h
  have hsum :
      (∑ a ∈ V, ∑ b ∈ V, gcdKernel ((1 : ℝ) / 2) a b) ≤
        ∑ a ∈ V, ∑ b ∈ V, (1 / m + m ^ (2 * σ - 1) * gcdKernel σ a b) := by
    apply Finset.sum_le_sum
    intro a ha
    apply Finset.sum_le_sum
    intro b hb
    exact hpoint a b ha hb
  have hsumEq :
      (∑ a ∈ V, ∑ b ∈ V, (1 / m + m ^ (2 * σ - 1) * gcdKernel σ a b)) =
        m + m ^ (2 * σ - 1) *
          (∑ a ∈ V, ∑ b ∈ V, gcdKernel σ a b) := by
    simp [Finset.sum_add_distrib, ← Finset.mul_sum, m] <;> field_simp
  have hgeneral := hbound V hV hcard
  have hcoeff : 0 ≤ m ^ (2 * σ - 1) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hgeneral hcoeff
  have hexp : m ^ (2 * σ - 1) * m ^ (1 + 1 / (k : ℝ)) =
      m ^ (2 * σ + 1 / (k : ℝ)) := by
    rw [← Real.rpow_add hm0]
    congr 1
    ring
  rw [hsumEq] at hsum
  change (∑ a ∈ V, ∑ b ∈ V, gcdKernel ((1 : ℝ) / 2) a b) ≤
    m + A * m ^ (2 * σ + 1 / (k : ℝ))
  nlinarith [hsum, hmul, hexp]

/-- 对任意 `η>0`，原有 `S₂(V)` 对所有正速度有限集满足无高度限制的弱幂次界。 -/
theorem inversePairGcdSum_subpower (η : ℝ) (hη : 0 < η) :
    ∃ Cη : ℝ, 0 < Cη ∧ ∀ (V : Finset ℕ),
      (∀ v ∈ V, 0 < v) →
        inversePairGcdSum V ≤ Cη * (V.card : ℝ) ^ (1 + η) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (4 / η)
  let k : ℕ := max 2 N
  have hk : 2 ≤ k := le_max_left 2 N
  have hkN : N ≤ k := le_max_right 2 N
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hkInv : 1 / (k : ℝ) ≤ η / 4 := by
    have hN' : (4 : ℝ) / η ≤ (k : ℝ) :=
      (le_of_lt hN).trans (by exact_mod_cast hkN)
    have hmul : (4 : ℝ) ≤ η * (k : ℝ) :=
      by simpa [mul_comm] using (div_le_iff₀ hη).mp hN'
    apply (div_le_iff₀ hk0).2
    nlinarith
  let σ : ℝ := 1 / 2 + η / 8
  have hσ : 1 / 2 < σ := by dsimp [σ]; linarith
  obtain ⟨A, hA, hhalf⟩ := gcdKernel_half_sum_bound σ hσ k hk
  refine ⟨1 + A, by positivity, ?_⟩
  intro V hV
  by_cases hEmpty : V = ∅
  · subst V
    simp [inversePairGcdSum, Real.zero_rpow (by linarith : (1 + η) ≠ 0)]
  have hcard : 1 ≤ V.card := by
    have hne : V.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
    exact Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero.mpr hne)
  let m : ℝ := V.card
  have hm : 1 ≤ m := by
    change (1 : ℝ) ≤ (V.card : ℝ)
    exact_mod_cast hcard
  have hexp : 2 * σ + 1 / (k : ℝ) ≤ 1 + η := by
    dsimp [σ]
    linarith
  have hpow1 : m ≤ m ^ (1 + η) := by
    calc
      m = m ^ (1 : ℝ) := (Real.rpow_one m).symm
      _ ≤ m ^ (1 + η) := Real.rpow_le_rpow_of_exponent_le hm (by linarith)
  have hpow2 : m ^ (2 * σ + 1 / (k : ℝ)) ≤ m ^ (1 + η) :=
    Real.rpow_le_rpow_of_exponent_le hm hexp
  have hbase := inversePairGcdSum_le_kernel_half V hV
  have hhalf' := hhalf V hV hcard
  change inversePairGcdSum V ≤ (1 + A) * m ^ (1 + η)
  nlinarith [mul_le_mul_of_nonneg_left hpow2 hA.le, hbase, hhalf', hpow1]

end LonelyRunner
