import LonelyRunner.GcdKernel
import LonelyRunner.PrimePoissonProduct

/-!
# GCD 核的有限 Poisson 积分表示

论文中 GCD 和估计的积分表示步骤；此处只涉及实际素因子和有限和。
-/

open MeasureTheory
open scoped Real ComplexConjugate

namespace LonelyRunner


/-- 有限正整数集的实际素因子并集。 -/
def gcdPrimeSet (V : Finset ℕ) : Finset ℕ :=
  V.biUnion Nat.primeFactors

/-- 并集内的每一个整数都是素数。 -/
theorem gcdPrimeSet_prime (V : Finset ℕ) {p : ℕ} (hp : p ∈ gcdPrimeSet V) :
    p.Prime := by
  obtain ⟨n, hn, hpn⟩ := Finset.mem_biUnion.mp hp
  exact Nat.prime_of_mem_primeFactors hpn

/-- 每个速度的全部素因子都包含在实际素数并集中。 -/
theorem primeFactors_subset_gcdPrimeSet (V : Finset ℕ) {n : ℕ} (hn : n ∈ V) :
    n.primeFactors ⊆ gcdPrimeSet V := by
  intro p hp
  exact Finset.mem_biUnion.mpr ⟨n, hn, hp⟩

private theorem factorization_zero_outside (V : Finset ℕ) (n : ℕ) (hn : n ∈ V)
    (p : ℕ) (hp : p ∉ gcdPrimeSet V) : n.factorization p = 0 := by
  have hpn : p ∉ n.primeFactors := fun h => hp (primeFactors_subset_gcdPrimeSet V hn h)
  exact Finsupp.notMem_support_iff.mp (by simpa [Nat.support_factorization] using hpn)

/-- 正速度若不同，则并集中的某个素因子指数不同。 -/
theorem gcdPrimeSet_separates (V : Finset ℕ) (hV : ∀ n ∈ V, 0 < n)
    {a b : ℕ} (ha : a ∈ V) (hb : b ∈ V) (hab : a ≠ b) :
    ∃ p : gcdPrimeSet V, a.factorization p.val ≠ b.factorization p.val := by
  classical
  by_contra h
  push Not at h
  apply hab
  apply Nat.eq_of_factorization_eq (Nat.ne_of_gt (hV a ha))
    (Nat.ne_of_gt (hV b hb))
  intro p
  by_cases hp : p ∈ gcdPrimeSet V
  · exact h ⟨p, hp⟩
  · rw [factorization_zero_outside V a ha p hp,
      factorization_zero_outside V b hb p hp]

/-- 实际素数坐标上的有限 Fourier 角色。 -/
noncomputable def gcdCharacter (V : Finset ℕ) (n : ℕ)
    (t : gcdPrimeSet V → UnitAddCircle) : ℂ :=
  ∏ p : gcdPrimeSet V, fourier (n.factorization p.val : ℤ) (t p)

/-- 有限 Fourier 角色连续。 -/
theorem gcdCharacter_continuous (V : Finset ℕ) (n : ℕ) :
    Continuous (gcdCharacter V n) := by
  unfold gcdCharacter
  apply continuous_finsetProd
  intro p hp
  exact (fourier (n.factorization p.val : ℤ)).continuous.comp (continuous_apply p)

/-- 每个 Fourier 角色的复模长等于一。 -/
theorem gcdCharacter_norm (V : Finset ℕ) (n : ℕ)
    (t : gcdPrimeSet V → UnitAddCircle) : ‖gcdCharacter V n t‖ = 1 := by
  unfold gcdCharacter
  have h (s : Finset (gcdPrimeSet V)) :
      ‖∏ p ∈ s, fourier (n.factorization p.val : ℤ) (t p)‖ = 1 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert p s hp ih =>
      rw [Finset.prod_insert hp, norm_mul, ih, mul_one]
      rw [fourier_apply]
      exact Circle.norm_coe _
  exact h Finset.univ

private theorem gcdCharacter_pair (V : Finset ℕ) (a b : ℕ)
    (t : gcdPrimeSet V → UnitAddCircle) :
    gcdCharacter V a t * conj (gcdCharacter V b t) =
      ∏ p : gcdPrimeSet V,
        fourier ((a.factorization p.val : ℤ) - (b.factorization p.val : ℤ)) (t p) := by
  change (∏ p : gcdPrimeSet V, fourier (a.factorization p.val : ℤ) (t p)) *
      conj (∏ p : gcdPrimeSet V, fourier (b.factorization p.val : ℤ) (t p)) = _
  have hconj : conj (∏ p : gcdPrimeSet V, fourier (b.factorization p.val : ℤ) (t p)) =
      ∏ p : gcdPrimeSet V, conj (fourier (b.factorization p.val : ℤ) (t p)) := by
    exact map_prod (starRingEnd ℂ) _ Finset.univ
  rw [hconj, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  rw [sub_eq_add_neg, fourier_add, fourier_neg]

/-- 不加权角色的两两正交性，速度 `1` 和空集亦包含。 -/
theorem gcdCharacter_orthogonal (V : Finset ℕ) (hV : ∀ n ∈ V, 0 < n)
    {a b : ℕ} (ha : a ∈ V) (hb : b ∈ V) :
    (∫ t : gcdPrimeSet V → UnitAddCircle,
      gcdCharacter V a t * conj (gcdCharacter V b t)
        ∂circleProductHaar (gcdPrimeSet V)) =
      if a = b then 1 else 0 := by
  simp_rw [gcdCharacter_pair]
  rw [show (∫ t : gcdPrimeSet V → UnitAddCircle,
      (∏ p : gcdPrimeSet V,
        fourier ((a.factorization p.val : ℤ) - (b.factorization p.val : ℤ)) (t p))
        ∂circleProductHaar (gcdPrimeSet V)) =
      ∏ p : gcdPrimeSet V,
        (∫ t : UnitAddCircle,
          fourier ((a.factorization p.val : ℤ) - (b.factorization p.val : ℤ)) t
            ∂circleHaar) from by
        unfold circleProductHaar
        exact integral_fintype_prod_eq_prod _]
  simp_rw [integral_circleFourier]
  by_cases hab : a = b
  · subst b
    simp
  · obtain ⟨p, hp⟩ := gcdPrimeSet_separates V hV ha hb hab
    have hne : (a.factorization p.val : ℤ) - (b.factorization p.val : ℤ) ≠ 0 := by
      apply sub_ne_zero.mpr
      exact_mod_cast hp
    have hpz : (if (a.factorization p.val : ℤ) - (b.factorization p.val : ℤ) = 0
        then (1 : ℂ) else 0) = 0 := by
      simp [hne]
    simp only [if_neg hab]
    exact Finset.prod_eq_zero (Finset.mem_univ p) hpz

private theorem factor_abs_cast (x y : ℕ) :
    (((x : ℤ) - (y : ℤ)).natAbs : ℝ) = |(x : ℝ) - (y : ℝ)| := by
  let z : ℤ := (x : ℤ) - (y : ℤ)
  have h : ((z.natAbs : ℤ) : ℝ) = ((|z| : ℤ) : ℝ) :=
    congrArg (fun w : ℤ => (w : ℝ)) (Int.natCast_natAbs z)
  simpa [z] using h

private theorem gcdKernel_factorization_on_set (σ : ℝ) (hσ : 0 < σ)
    (V : Finset ℕ) (hV : ∀ n ∈ V, 0 < n)
    {a b : ℕ} (ha : a ∈ V) (hb : b ∈ V) :
    gcdKernel σ a b =
      ∏ p : gcdPrimeSet V,
        (p.val : ℝ) ^ (-σ *
          |((a.factorization p.val : ℝ) - (b.factorization p.val : ℝ))|) := by
  let S := (a * b).primeFactors
  have ha0 := Nat.ne_of_gt (hV a ha)
  have hb0 := Nat.ne_of_gt (hV b hb)
  have hsub : S ⊆ gcdPrimeSet V := by
    intro p hp
    change p ∈ (a * b).primeFactors at hp
    rw [Nat.primeFactors_mul ha0 hb0] at hp
    rcases Finset.mem_union.mp hp with hpa | hpb
    · exact primeFactors_subset_gcdPrimeSet V ha hpa
    · exact primeFactors_subset_gcdPrimeSet V hb hpb
  rw [gcdKernel_factorization σ hσ a b (hV a ha) (hV b hb)]
  have hattach :
      (∏ p : gcdPrimeSet V,
        (p.val : ℝ) ^ (-σ *
          |((a.factorization p.val : ℝ) - (b.factorization p.val : ℝ))|)) =
      ∏ p ∈ gcdPrimeSet V,
        (p : ℝ) ^ (-σ *
          |((a.factorization p : ℝ) - (b.factorization p : ℝ))|) := by
    simpa only [Finset.univ_eq_attach] using
      (Finset.prod_attach (gcdPrimeSet V) (fun p : ℕ =>
        (p : ℝ) ^ (-σ * |((a.factorization p : ℝ) - (b.factorization p : ℝ))|)))
  rw [hattach]
  apply Finset.prod_subset hsub
  intro p hpF hpS
  have hpa : p ∉ a.primeFactors := by
    intro h
    apply hpS
    change p ∈ (a * b).primeFactors
    rw [Nat.primeFactors_mul ha0 hb0]
    exact Finset.mem_union_left _ h
  have hpb : p ∉ b.primeFactors := by
    intro h
    apply hpS
    change p ∈ (a * b).primeFactors
    rw [Nat.primeFactors_mul ha0 hb0]
    exact Finset.mem_union_right _ h
  have hza : a.factorization p = 0 :=
    Finsupp.notMem_support_iff.mp (by simpa [Nat.support_factorization] using hpa)
  have hzb : b.factorization p = 0 :=
    Finsupp.notMem_support_iff.mp (by simpa [Nat.support_factorization] using hpb)
  simp [hza, hzb]

private theorem poisson_factor_rate (σ : ℝ) (p x y : ℕ) :
    ((p : ℝ) ^ (-σ)) ^ (((x : ℤ) - (y : ℤ)).natAbs) =
      (p : ℝ) ^ (-σ * |((x : ℝ) - (y : ℝ))|) := by
  have hp0 : (0 : ℝ) ≤ p := by positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul hp0, factor_abs_cast]

private theorem gcdPoisson_pair_pointwise (σ : ℝ) (V : Finset ℕ)
    (a b : ℕ) (t : gcdPrimeSet V → UnitAddCircle) :
    (primePoissonProduct σ (gcdPrimeSet V) t : ℂ) *
        gcdCharacter V a t * conj (gcdCharacter V b t) =
      ∏ p : gcdPrimeSet V,
        ((circlePoisson ((p.val : ℝ) ^ (-σ)) (t p) : ℂ) *
          fourier ((a.factorization p.val : ℤ) - (b.factorization p.val : ℤ)) (t p)) := by
  rw [mul_assoc, gcdCharacter_pair]
  change ((∏ p : gcdPrimeSet V,
    circlePoisson ((p.val : ℝ) ^ (-σ)) (t p) : ℝ) : ℂ) *
      (∏ p : gcdPrimeSet V,
        fourier ((a.factorization p.val : ℤ) - (b.factorization p.val : ℤ)) (t p)) = _
  have hcast : ((∏ p : gcdPrimeSet V,
      circlePoisson ((p.val : ℝ) ^ (-σ)) (t p) : ℝ) : ℂ) =
      ∏ p : gcdPrimeSet V,
        (circlePoisson ((p.val : ℝ) ^ (-σ)) (t p) : ℂ) := by
    exact map_prod (Complex.ofRealHom) _ Finset.univ
  rw [hcast, ← Finset.prod_mul_distrib]

/-- Poisson 加权角色积分精确等于实际正整数的 GCD 核。 -/
theorem gcdPoisson_pair_integral (σ : ℝ) (hσ : 1 / 2 < σ)
    (V : Finset ℕ) (hV : ∀ n ∈ V, 0 < n)
    {a b : ℕ} (ha : a ∈ V) (hb : b ∈ V) :
    (∫ t : gcdPrimeSet V → UnitAddCircle,
      (primePoissonProduct σ (gcdPrimeSet V) t : ℂ) *
        gcdCharacter V a t * conj (gcdCharacter V b t)
          ∂circleProductHaar (gcdPrimeSet V)) =
      (gcdKernel σ a b : ℂ) := by
  simp_rw [gcdPoisson_pair_pointwise]
  rw [show (∫ t : gcdPrimeSet V → UnitAddCircle,
    (∏ p : gcdPrimeSet V,
      (circlePoisson ((p.val : ℝ) ^ (-σ)) (t p) : ℂ) *
        fourier ((a.factorization p.val : ℤ) - (b.factorization p.val : ℤ)) (t p))
      ∂circleProductHaar (gcdPrimeSet V)) =
    ∏ p : gcdPrimeSet V,
      (∫ t : UnitAddCircle,
        (circlePoisson ((p.val : ℝ) ^ (-σ)) t : ℂ) *
          fourier ((a.factorization p.val : ℤ) - (b.factorization p.val : ℤ)) t
            ∂circleHaar) from by
      unfold circleProductHaar
      exact integral_fintype_prod_eq_prod
        (μ := fun _ : gcdPrimeSet V => circleHaar)
        (fun p : gcdPrimeSet V => fun t : UnitAddCircle =>
          (circlePoisson ((p.val : ℝ) ^ (-σ)) t : ℂ) *
            fourier ((a.factorization p.val : ℤ) - (b.factorization p.val : ℤ)) t)]
  have hfactors (p : gcdPrimeSet V) :
      (∫ t : UnitAddCircle,
        (circlePoisson ((p.val : ℝ) ^ (-σ)) t : ℂ) *
          fourier ((a.factorization p.val : ℤ) - (b.factorization p.val : ℤ)) t
            ∂circleHaar) =
      (((p.val : ℝ) ^ (-σ) : ℝ) : ℂ) ^
        (((a.factorization p.val : ℤ) - (b.factorization p.val : ℤ)).natAbs) := by
    have hr := primePoisson_rate σ hσ (gcdPrimeSet_prime V p.property)
    exact circlePoisson_integral_fourier _ hr.1.le
      (lt_of_le_of_lt hr.2 (by norm_num)) _
  simp_rw [hfactors]
  have hreal :
      (∏ p : gcdPrimeSet V,
        ((p.val : ℝ) ^ (-σ)) ^
          (((a.factorization p.val : ℤ) - (b.factorization p.val : ℤ)).natAbs)) =
        gcdKernel σ a b := by
    simp_rw [poisson_factor_rate]
    exact (gcdKernel_factorization_on_set σ (by linarith) V hV ha hb).symm
  exact_mod_cast hreal

/-- 实际速度的 Fourier 角色有限和。 -/
noncomputable def gcdCharacterSum (V : Finset ℕ)
    (t : gcdPrimeSet V → UnitAddCircle) : ℂ :=
  ∑ n ∈ V, gcdCharacter V n t

/-- 角色有限和连续。 -/
theorem gcdCharacterSum_continuous (V : Finset ℕ) :
    Continuous (gcdCharacterSum V) := by
  unfold gcdCharacterSum
  apply continuous_finsetSum
  intro n hn
  exact gcdCharacter_continuous V n

/-- 角色有限和的绝对值逐点至多为速度数。 -/
theorem gcdCharacterSum_norm_le (V : Finset ℕ)
    (t : gcdPrimeSet V → UnitAddCircle) :
    ‖gcdCharacterSum V t‖ ≤ V.card := by
  unfold gcdCharacterSum
  calc
    ‖∑ n ∈ V, gcdCharacter V n t‖ ≤
        ∑ n ∈ V, ‖gcdCharacter V n t‖ := norm_sum_le _ _
    _ = V.card := by simp [gcdCharacter_norm]

private theorem gcdProduct_integrable {F : Finset ℕ}
    {f : (F → UnitAddCircle) → ℂ} (hf : Continuous f) :
    Integrable f (circleProductHaar F) := by
  obtain ⟨M, hM⟩ := (isCompact_range hf).isBounded.exists_norm_le
  apply Integrable.of_bound hf.aestronglyMeasurable M
  filter_upwards [] with t
  exact hM _ ⟨t, rfl⟩

private theorem gcdCharacter_pair_integrable (V : Finset ℕ) (a b : ℕ) :
    Integrable (fun t : gcdPrimeSet V → UnitAddCircle =>
      gcdCharacter V a t * conj (gcdCharacter V b t))
        (circleProductHaar (gcdPrimeSet V)) :=
  gcdProduct_integrable
    ((gcdCharacter_continuous V a).mul
      (Complex.continuous_conj.comp (gcdCharacter_continuous V b)))

private theorem gcdPoisson_pair_integrable (σ : ℝ) (hσ : 1 / 2 < σ)
    (V : Finset ℕ) (a b : ℕ) :
    Integrable (fun t : gcdPrimeSet V → UnitAddCircle =>
      (primePoissonProduct σ (gcdPrimeSet V) t : ℂ) *
        gcdCharacter V a t * conj (gcdCharacter V b t))
        (circleProductHaar (gcdPrimeSet V)) := by
  have hc := primePoissonProduct_continuous σ hσ (gcdPrimeSet V)
    (fun p hp => gcdPrimeSet_prime V hp)
  exact gcdProduct_integrable
    (((Complex.continuous_ofReal.comp hc).mul (gcdCharacter_continuous V a)).mul
      (Complex.continuous_conj.comp (gcdCharacter_continuous V b)))

private theorem gcdCharacterSum_normSq (V : Finset ℕ)
    (t : gcdPrimeSet V → UnitAddCircle) :
    ((‖gcdCharacterSum V t‖ ^ 2 : ℝ) : ℂ) =
      ∑ a ∈ V, ∑ b ∈ V,
        gcdCharacter V a t * conj (gcdCharacter V b t) := by
  have hnorm : ((‖gcdCharacterSum V t‖ ^ 2 : ℝ) : ℂ) =
      gcdCharacterSum V t * conj (gcdCharacterSum V t) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hnorm]
  change (∑ a ∈ V, gcdCharacter V a t) *
      conj (∑ b ∈ V, gcdCharacter V b t) = _
  rw [map_sum]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]

/-- 有限角色和的平方可积。 -/
theorem gcdCharacterSum_normSq_integrable (V : Finset ℕ) :
    Integrable (fun t : gcdPrimeSet V → UnitAddCircle =>
      ‖gcdCharacterSum V t‖ ^ 2) (circleProductHaar (gcdPrimeSet V)) := by
  have hc : Continuous (fun t : gcdPrimeSet V → UnitAddCircle =>
      ‖gcdCharacterSum V t‖ ^ 2) := (gcdCharacterSum_continuous V).norm.pow 2
  obtain ⟨M, hM⟩ := (isCompact_range hc).isBounded.exists_norm_le
  apply Integrable.of_bound hc.aestronglyMeasurable M
  filter_upwards [] with t
  exact hM _ ⟨t, rfl⟩

/-- 不加权角色和的二次矩正好为速度数。 -/
theorem gcdCharacterSum_integral_normSq (V : Finset ℕ) (hV : ∀ n ∈ V, 0 < n) :
    (∫ t : gcdPrimeSet V → UnitAddCircle,
      ‖gcdCharacterSum V t‖ ^ 2 ∂circleProductHaar (gcdPrimeSet V)) = V.card := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [gcdCharacterSum_normSq]
  rw [integral_finsetSum V (fun a ha => by
    apply gcdProduct_integrable
    apply continuous_finsetSum
    intro b hb
    exact (gcdCharacter_continuous V a).mul
      (Complex.continuous_conj.comp (gcdCharacter_continuous V b)))]
  calc
    (∑ a ∈ V, ∫ t : gcdPrimeSet V → UnitAddCircle,
      (∑ b ∈ V, gcdCharacter V a t * conj (gcdCharacter V b t))
        ∂circleProductHaar (gcdPrimeSet V)) =
        ∑ a ∈ V, ∑ b ∈ V,
          (∫ t : gcdPrimeSet V → UnitAddCircle,
            gcdCharacter V a t * conj (gcdCharacter V b t)
              ∂circleProductHaar (gcdPrimeSet V)) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [integral_finsetSum V (fun b hb => gcdCharacter_pair_integrable V a b)]
    _ = ∑ a ∈ V, ∑ b ∈ V, (if a = b then (1 : ℂ) else 0) := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      exact gcdCharacter_orthogonal V hV ha hb
    _ = (V.card : ℂ) := by simp

/-- Poisson 加权角色和的二次矩正好为 GCD 核的有序双重和。 -/
theorem gcdPoisson_integral_normSq (σ : ℝ) (hσ : 1 / 2 < σ)
    (V : Finset ℕ) (hV : ∀ n ∈ V, 0 < n) :
    (∫ t : gcdPrimeSet V → UnitAddCircle,
      primePoissonProduct σ (gcdPrimeSet V) t * ‖gcdCharacterSum V t‖ ^ 2
        ∂circleProductHaar (gcdPrimeSet V)) =
      ∑ a ∈ V, ∑ b ∈ V, gcdKernel σ a b := by
  have hcont : Continuous (fun t : gcdPrimeSet V → UnitAddCircle =>
      primePoissonProduct σ (gcdPrimeSet V) t * ‖gcdCharacterSum V t‖ ^ 2) :=
    (primePoissonProduct_continuous σ hσ (gcdPrimeSet V)
      (fun p hp => gcdPrimeSet_prime V hp)).mul
      ((gcdCharacterSum_continuous V).norm.pow 2)
  have hrealInt : Integrable (fun t : gcdPrimeSet V → UnitAddCircle =>
      primePoissonProduct σ (gcdPrimeSet V) t * ‖gcdCharacterSum V t‖ ^ 2)
        (circleProductHaar (gcdPrimeSet V)) := by
    obtain ⟨M, hM⟩ := (isCompact_range hcont).isBounded.exists_norm_le
    apply Integrable.of_bound hcont.aestronglyMeasurable M
    filter_upwards [] with t
    exact hM _ ⟨t, rfl⟩
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  have hpoint (t : gcdPrimeSet V → UnitAddCircle) :
      ((primePoissonProduct σ (gcdPrimeSet V) t *
          ‖gcdCharacterSum V t‖ ^ 2 : ℝ) : ℂ) =
        ∑ a ∈ V, ∑ b ∈ V,
          (primePoissonProduct σ (gcdPrimeSet V) t : ℂ) *
            gcdCharacter V a t * conj (gcdCharacter V b t) := by
    rw [Complex.ofReal_mul, gcdCharacterSum_normSq]
    simp only [Finset.mul_sum, mul_assoc]
  simp_rw [hpoint]
  calc
    (∫ t : gcdPrimeSet V → UnitAddCircle,
      (∑ a ∈ V, ∑ b ∈ V,
        (primePoissonProduct σ (gcdPrimeSet V) t : ℂ) *
          gcdCharacter V a t * conj (gcdCharacter V b t))
          ∂circleProductHaar (gcdPrimeSet V)) =
      ∑ a ∈ V, ∑ b ∈ V,
        (∫ t : gcdPrimeSet V → UnitAddCircle,
          (primePoissonProduct σ (gcdPrimeSet V) t : ℂ) *
            gcdCharacter V a t * conj (gcdCharacter V b t)
              ∂circleProductHaar (gcdPrimeSet V)) := by
        rw [integral_finsetSum V (fun a ha => by
          apply gcdProduct_integrable
          apply continuous_finsetSum
          intro b hb
          have hc := primePoissonProduct_continuous σ hσ (gcdPrimeSet V)
            (fun p hp => gcdPrimeSet_prime V hp)
          exact (((Complex.continuous_ofReal.comp hc).mul
            (gcdCharacter_continuous V a)).mul
              (Complex.continuous_conj.comp (gcdCharacter_continuous V b))) )]
        apply Finset.sum_congr rfl
        intro a ha
        rw [integral_finsetSum V (fun b hb => gcdPoisson_pair_integrable σ hσ V a b)]
    _ = ∑ a ∈ V, ∑ b ∈ V, (gcdKernel σ a b : ℂ) := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      exact gcdPoisson_pair_integral σ hσ V hV ha hb
    _ = ((∑ a ∈ V, ∑ b ∈ V, gcdKernel σ a b : ℝ) : ℂ) := by
      push_cast
      rfl

end LonelyRunner
