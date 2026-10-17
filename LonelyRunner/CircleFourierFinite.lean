import LonelyRunner.CircleFejer

namespace LonelyRunner

open MeasureTheory



/-- 论文式 (eq:orthogonality)、引理 `lem:triple` 与 `lem:separation`：有限频率三角多项式。 -/
noncomputable def circleFourierPoly (S : Finset ℤ) (coeff : ℤ → ℂ)
    (t : UnitAddCircle) : ℂ :=
  ∑ k ∈ S, coeff k * fourier k t

/-- 论文 `lem:triple`：有限三角多项式对圆周 Haar 概率测度可积。 -/
theorem circleFourierPoly_integrable (S : Finset ℤ) (coeff : ℤ → ℂ) :
    Integrable (circleFourierPoly S coeff) circleHaar := by
  unfold circleFourierPoly
  exact integrable_finsetSum S (fun k hk => (circleFourier_integrable k).const_mul (coeff k))

/-- 论文式 (eq:orthogonality)：有限 Fourier 多项式的积分等于其零频率系数。 -/
theorem circleFourierPoly_integral (S : Finset ℤ) (coeff : ℤ → ℂ) :
    (∫ t : UnitAddCircle, circleFourierPoly S coeff t ∂circleHaar) =
      if (0 : ℤ) ∈ S then coeff 0 else 0 := by
  unfold circleFourierPoly
  rw [integral_finsetSum S (fun k hk => (circleFourier_integrable k).const_mul (coeff k))]
  simp_rw [integral_const_mul, integral_circleFourier]
  simp [Finset.sum_ite_eq']

private theorem circleFourier_nsmul (v : ℕ) (k : ℤ) (t : UnitAddCircle) :
    fourier k (v • t) = fourier ((v : ℤ) * k) t := by
  simp only [fourier_apply]
  congr 1
  rw [← natCast_zsmul, mul_comm (v : ℤ) k, mul_zsmul]

/-- 论文 `lem:triple`：代入正整数倍后，每个频率 `k` 变为 `vk`。 -/
theorem circleFourierPoly_nsmul (S : Finset ℤ) (coeff : ℤ → ℂ)
    (v : ℕ) (t : UnitAddCircle) :
    circleFourierPoly S coeff (v • t) =
      ∑ k ∈ S, coeff k * fourier ((v : ℤ) * k) t := by
  simp only [circleFourierPoly, circleFourier_nsmul]

/-- 论文 `lem:triple`：整数倍代入后的有限 Fourier 多项式仍可积。 -/
theorem circleFourierPoly_nsmul_integrable (S : Finset ℤ) (coeff : ℤ → ℂ)
    (v : ℕ) :
    Integrable (fun t : UnitAddCircle => circleFourierPoly S coeff (v • t)) circleHaar := by
  simp_rw [circleFourierPoly_nsmul]
  exact integrable_finsetSum S (fun k hk =>
    (circleFourier_integrable _).const_mul (coeff k))

/-- 论文 `lem:triple`：两个有限 Fourier 多项式的积分只保留总频率为零的项。 -/
theorem circleFourierPoly_integral_mul (S T : Finset ℤ) (u v : ℤ → ℂ)
    (a b : ℕ) :
    (∫ t : UnitAddCircle,
      circleFourierPoly S u (a • t) * circleFourierPoly T v (b • t) ∂circleHaar) =
      ∑ k ∈ S, ∑ l ∈ T,
        if (a : ℤ) * k + (b : ℤ) * l = 0 then u k * v l else 0 := by
  have hexp (t : UnitAddCircle) :
      circleFourierPoly S u (a • t) * circleFourierPoly T v (b • t) =
        ∑ k ∈ S, ∑ l ∈ T,
          (u k * v l) * fourier ((a : ℤ) * k + (b : ℤ) * l) t := by
    simp only [circleFourierPoly_nsmul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro l hl
    rw [fourier_add]
    ring
  calc
    _ = ∫ t : UnitAddCircle, ∑ k ∈ S, ∑ l ∈ T,
          (u k * v l) * fourier ((a : ℤ) * k + (b : ℤ) * l) t ∂circleHaar := by
        congr 1
        funext t
        exact hexp t
    _ = ∑ k ∈ S, ∑ l ∈ T,
          (u k * v l) *
            (if (a : ℤ) * k + (b : ℤ) * l = 0 then 1 else 0) := by
        rw [integral_finsetSum S (fun k hk =>
          integrable_finsetSum T (fun l hl =>
            (circleFourier_integrable _).const_mul (u k * v l)))]
        simp_rw [integral_finsetSum T (fun l hl =>
          (circleFourier_integrable _).const_mul (u _ * v l))]
        simp_rw [integral_const_mul, integral_circleFourier]
    _ = _ := by simp only [mul_ite, mul_one, mul_zero]

/-- 论文 `lem:triple`：三个有限 Fourier 多项式的积分只保留总频率为零的项。 -/
theorem circleFourierPoly_integral_mul_three (S T U : Finset ℤ)
    (u v w : ℤ → ℂ) (a b c : ℕ) :
    (∫ t : UnitAddCircle,
      circleFourierPoly S u (a • t) * circleFourierPoly T v (b • t) *
        circleFourierPoly U w (c • t) ∂circleHaar) =
      ∑ k ∈ S, ∑ l ∈ T, ∑ r ∈ U,
        if (a : ℤ) * k + (b : ℤ) * l + (c : ℤ) * r = 0
        then u k * v l * w r else 0 := by
  have hexp (t : UnitAddCircle) :
      circleFourierPoly S u (a • t) * circleFourierPoly T v (b • t) *
          circleFourierPoly U w (c • t) =
        ∑ k ∈ S, ∑ l ∈ T, ∑ r ∈ U,
          (u k * v l * w r) *
            fourier ((a : ℤ) * k + (b : ℤ) * l + (c : ℤ) * r) t := by
    simp only [circleFourierPoly_nsmul]
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_comm (s := U) (t := S)]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro l hl
    apply Finset.sum_congr rfl
    intro r hr
    rw [fourier_add, fourier_add]
    ring
  calc
    _ = ∫ t : UnitAddCircle, ∑ k ∈ S, ∑ l ∈ T, ∑ r ∈ U,
          (u k * v l * w r) *
            fourier ((a : ℤ) * k + (b : ℤ) * l + (c : ℤ) * r) t ∂circleHaar := by
        congr 1
        funext t
        exact hexp t
    _ = ∑ k ∈ S, ∑ l ∈ T, ∑ r ∈ U,
          (u k * v l * w r) *
            (if (a : ℤ) * k + (b : ℤ) * l + (c : ℤ) * r = 0 then 1 else 0) := by
        rw [integral_finsetSum S (fun k hk =>
          integrable_finsetSum T (fun l hl =>
            integrable_finsetSum U (fun r hr =>
              (circleFourier_integrable _).const_mul (u k * v l * w r))))]
        simp_rw [integral_finsetSum T (fun l hl =>
          integrable_finsetSum U (fun r hr =>
            (circleFourier_integrable _).const_mul (u _ * v l * w r)))]
        simp_rw [integral_finsetSum U (fun r hr =>
          (circleFourier_integrable _).const_mul (u _ * v _ * w r))]
        simp_rw [integral_const_mul, integral_circleFourier]
    _ = _ := by simp only [mul_ite, mul_one, mul_zero]

/-- 论文 `lem:separation` 证明中的整数论步骤：既约比值及短频率只允许零关系。 -/
theorem reduced_ratio_short_relation_zero
    (R g h a b : ℕ) (hg : 0 < g) (ha : 0 < a) (hb : 0 < b)
    (hratio : h * b = g * a) (hcop : Nat.Coprime a b)
    (hlarge : R ≤ max a b) (k l : ℤ)
    (hk : k.natAbs < R) (hl : l.natAbs < R)
    (hrel : (g : ℤ) * k + (h : ℤ) * l = 0) :
    k = 0 ∧ l = 0 := by
  have hgZ : (g : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hg)
  have haZ : (a : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ha)
  have hbZ : (b : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  have hratioZ : (h : ℤ) * (b : ℤ) = (g : ℤ) * (a : ℤ) := by
    exact_mod_cast hratio
  have hscaled : (g : ℤ) * ((b : ℤ) * k + (a : ℤ) * l) = 0 := by
    calc
      _ = (b : ℤ) * (g : ℤ) * k + ((g : ℤ) * (a : ℤ)) * l := by ring
      _ = (b : ℤ) * ((g : ℤ) * k + (h : ℤ) * l) := by
        rw [← hratioZ]
        ring
      _ = 0 := by rw [hrel]; ring
  have hshort : (b : ℤ) * k + (a : ℤ) * l = 0 :=
    (mul_eq_zero.mp hscaled).resolve_left hgZ
  have hak : (a : ℤ) ∣ k := by
    apply (hcop.isCoprime : IsCoprime (a : ℤ) (b : ℤ)).dvd_of_dvd_mul_left
    refine ⟨-l, ?_⟩
    nlinarith [hshort]
  have hbl : (b : ℤ) ∣ l := by
    apply (hcop.symm.isCoprime : IsCoprime (b : ℤ) (a : ℤ)).dvd_of_dvd_mul_left
    refine ⟨-k, ?_⟩
    nlinarith [hshort]
  have hka : k ≠ 0 → a < R := by
    intro hk0
    have hka0 : 0 < k.natAbs := Int.natAbs_pos.mpr hk0
    have hle : a ≤ k.natAbs := by
      apply Nat.le_of_dvd hka0
      simpa using Int.natAbs_dvd_natAbs.mpr hak
    omega
  have hlb : l ≠ 0 → b < R := by
    intro hl0
    have hlb0 : 0 < l.natAbs := Int.natAbs_pos.mpr hl0
    have hle : b ≤ l.natAbs := by
      apply Nat.le_of_dvd hlb0
      simpa using Int.natAbs_dvd_natAbs.mpr hbl
    omega
  by_cases hk0 : k = 0
  · constructor
    · exact hk0
    · rw [hk0, mul_zero, zero_add] at hshort
      exact (mul_eq_zero.mp hshort).resolve_left haZ
  · have haR := hka hk0
    have hbR : R ≤ b := by omega
    have hl0 : l = 0 := by
      by_contra hne
      have := hlb hne
      omega
    constructor
    · rw [hl0, mul_zero, add_zero] at hshort
      exact (mul_eq_zero.mp hshort).resolve_left hbZ
    · exact hl0

/-- 论文 `lem:separation`：有限频率分离，乘积积分仅为两个零频率系数之积。
若零频率未列入频率集，相应常数项按零计算。 -/
theorem circleFourierPoly_integral_separated (S T : Finset ℤ) (u v : ℤ → ℂ)
    (R g h a b : ℕ) (hg : 0 < g) (ha : 0 < a) (hb : 0 < b)
    (hratio : h * b = g * a) (hcop : Nat.Coprime a b)
    (hlarge : R ≤ max a b)
    (hS : ∀ k ∈ S, k.natAbs < R) (hT : ∀ l ∈ T, l.natAbs < R) :
    (∫ t : UnitAddCircle,
      circleFourierPoly S u (g • t) * circleFourierPoly T v (h • t) ∂circleHaar) =
      (if (0 : ℤ) ∈ S then u 0 else 0) *
        (if (0 : ℤ) ∈ T then v 0 else 0) := by
  rw [circleFourierPoly_integral_mul]
  have hrel (k : ℤ) (hk : k ∈ S) (l : ℤ) (hl : l ∈ T) :
      ((g : ℤ) * k + (h : ℤ) * l = 0) ↔ k = 0 ∧ l = 0 := by
    constructor
    · exact reduced_ratio_short_relation_zero R g h a b hg ha hb hratio hcop
        hlarge k l (hS k hk) (hT l hl)
    · rintro ⟨rfl, rfl⟩
      ring
  calc
    (∑ k ∈ S, ∑ l ∈ T,
      if (g : ℤ) * k + (h : ℤ) * l = 0 then u k * v l else 0) =
        ∑ k ∈ S, ∑ l ∈ T,
          if k = 0 ∧ l = 0 then u k * v l else 0 := by
            apply Finset.sum_congr rfl
            intro k hk
            apply Finset.sum_congr rfl
            intro l hl
            simp only [hrel k hk l hl]
    _ = _ := by
      simp [ite_and, Finset.sum_ite_eq']
      by_cases hs : (0 : ℤ) ∈ S <;> by_cases ht : (0 : ℤ) ∈ T <;>
        simp [hs, ht]

#print axioms LonelyRunner.circleFourierPoly_integrable
#print axioms LonelyRunner.circleFourierPoly_integral
#print axioms LonelyRunner.circleFourierPoly_nsmul
#print axioms LonelyRunner.circleFourierPoly_nsmul_integrable
#print axioms LonelyRunner.circleFourierPoly_integral_mul
#print axioms LonelyRunner.circleFourierPoly_integral_mul_three
#print axioms LonelyRunner.reduced_ratio_short_relation_zero
#print axioms LonelyRunner.circleFourierPoly_integral_separated

end LonelyRunner
