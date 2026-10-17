import LonelyRunner.WeightedST
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# 本原方向的有理截距直线

论文短关系计数中的几何编码：整数法向量 `(p,q)`、有理截距 `r`
确定实平面直线 `p*x+q*y=r`，并将速度对嵌入实欧氏平面。
-/

namespace LonelyRunner

/-- 坐标 `(x,y)` 在实欧氏平面中的点。 -/
def directionPoint (x y : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![x, y]

@[simp] theorem directionPoint_zero (x y : ℝ) : directionPoint x y 0 = x := by
  simp [directionPoint]

@[simp] theorem directionPoint_one (x y : ℝ) : directionPoint x y 1 = y := by
  simp [directionPoint]

/-- 法向量 `(p,q)` 对应的实线性泛函。 -/
def directionNormal (p q : ℤ) : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℝ where
  toFun z := (p : ℝ) * z 0 + (q : ℝ) * z 1
  map_add' x y := by
    simp [mul_add]
    ring
  map_smul' t z := by
    simp [smul_eq_mul]
    ring

@[simp] theorem directionNormal_apply (p q : ℤ)
    (z : EuclideanSpace ℝ (Fin 2)) :
    directionNormal p q z = (p : ℝ) * z 0 + (q : ℝ) * z 1 := rfl

/-- `p≠0` 时的一个显式基点 `(r/p,0)`。 -/
noncomputable def directionBase (p : ℤ) (r : ℚ) : EuclideanSpace ℝ (Fin 2) :=
  directionPoint ((r : ℝ) / (p : ℝ)) 0

/-- 截距方程构成的实仿射子空间。 -/
noncomputable def primitiveDirectionAffine (p q : ℤ) (r : ℚ) :
    AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) :=
  AffineSubspace.mk' (directionBase p r) (directionNormal p q).ker

/-- 显式基点满足直线方程。 -/
theorem directionNormal_base (p q : ℤ) (r : ℚ) (hp : p ≠ 0) :
    directionNormal p q (directionBase p r) = (r : ℝ) := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp
  simp only [directionNormal_apply, directionBase, directionPoint_zero,
    directionPoint_one, mul_zero, add_zero]
  exact mul_div_cancel₀ (r : ℝ) hpR

/-- 几何成员条件准确等价于 `p*x+q*y=r`。 -/
theorem mem_primitiveDirectionAffine_iff (p q : ℤ) (r : ℚ)
    (hp : p ≠ 0) (z : EuclideanSpace ℝ (Fin 2)) :
    z ∈ primitiveDirectionAffine p q r ↔
      (p : ℝ) * z 0 + (q : ℝ) * z 1 = (r : ℝ) := by
  rw [primitiveDirectionAffine, AffineSubspace.mem_mk', LinearMap.mem_ker]
  change directionNormal p q (z - directionBase p r) = 0 ↔ _
  rw [map_sub, directionNormal_base p q r hp]
  simp only [directionNormal_apply]
  exact sub_eq_zero

/-- 直线的载集精确是方程 `p*x+q*y=r` 的解集。 -/
theorem primitiveDirectionAffine_carrier (p q : ℤ) (r : ℚ) (hp : p ≠ 0) :
    (primitiveDirectionAffine p q r : Set (EuclideanSpace ℝ (Fin 2))) =
      {z | (p : ℝ) * z 0 + (q : ℝ) * z 1 = (r : ℝ)} := by
  ext z
  exact mem_primitiveDirectionAffine_iff p q r hp z

/-- 当 `p>0` 时，该仿射子空间非空。 -/
theorem primitiveDirectionAffine_nonempty (p q : ℤ) (r : ℚ) :
    (primitiveDirectionAffine p q r : Set (EuclideanSpace ℝ (Fin 2))).Nonempty := by
  exact AffineSubspace.mk'_nonempty (directionBase p r) (directionNormal p q).ker

/-- 当 `p>0` 时，其方向空间的实维数为一。 -/
theorem primitiveDirectionAffine_finrank (p q : ℤ) (r : ℚ) (hp : 0 < p) :
    Module.finrank ℝ (primitiveDirectionAffine p q r).direction = 1 := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hp)
  have hsurj : Function.Surjective (directionNormal p q) := by
    intro t
    refine ⟨directionPoint (t / (p : ℝ)) 0, ?_⟩
    simp only [directionNormal_apply, directionPoint_zero, directionPoint_one,
      mul_zero, add_zero]
    exact mul_div_cancel₀ t hpR
  have hrange : (directionNormal p q).range = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  have hdim := (directionNormal p q).finrank_range_add_finrank_ker
  rw [hrange] at hdim
  change Module.finrank ℝ
    (AffineSubspace.mk' (directionBase p r) (directionNormal p q).ker).direction = 1
  rw [AffineSubspace.direction_mk']
  simp at hdim
  omega

/-- `WeightedST` 所用的一维实仿射直线。 -/
noncomputable def primitiveDirectionLine (p q : ℤ) (r : ℚ) (hp : 0 < p) :
    WeightedLine :=
  ⟨primitiveDirectionAffine p q r,
    ⟨primitiveDirectionAffine_nonempty p q r,
      primitiveDirectionAffine_finrank p q r hp⟩⟩

/-- 两个本原法向量给出同一几何直线时，归一化整数系数及有理截距相同。 -/
theorem primitiveDirectionAffine_parameters_unique
    (p q p' q' : ℤ) (r r' : ℚ)
    (hp : 0 < p) (hp' : 0 < p')
    (_hq : q ≠ 0) (_hq' : q' ≠ 0)
    (hprimitive : Nat.gcd p.natAbs q.natAbs = 1)
    (hprimitive' : Nat.gcd p'.natAbs q'.natAbs = 1)
    (hline : primitiveDirectionAffine p q r = primitiveDirectionAffine p' q' r') :
    p = p' ∧ q = q' ∧ r = r' := by
  have hker : (directionNormal p q).ker = (directionNormal p' q').ker := by
    have hdir := congrArg AffineSubspace.direction hline
    simpa [primitiveDirectionAffine] using hdir
  let v := directionPoint (-(q : ℝ)) (p : ℝ)
  have hv : v ∈ (directionNormal p q).ker := by
    rw [LinearMap.mem_ker]
    simp only [directionNormal_apply, v, directionPoint_zero, directionPoint_one]
    ring
  have hv' : v ∈ (directionNormal p' q').ker := hker ▸ hv
  have hcrossR : (p : ℝ) * (q' : ℝ) = (p' : ℝ) * (q : ℝ) := by
    rw [LinearMap.mem_ker] at hv'
    simp only [directionNormal_apply, v, directionPoint_zero, directionPoint_one] at hv'
    nlinarith
  have hcross : p * q' = p' * q := by exact_mod_cast hcrossR
  have hcop : IsCoprime p q :=
    Int.isCoprime_iff_gcd_eq_one.mpr (by simpa [Int.gcd] using hprimitive)
  have hcop' : IsCoprime p' q' :=
    Int.isCoprime_iff_gcd_eq_one.mpr (by simpa [Int.gcd] using hprimitive')
  have hpdvd : p ∣ p' := hcop.dvd_of_dvd_mul_right (by
    rw [← hcross]
    exact ⟨q', rfl⟩)
  have hp'dvd : p' ∣ p := hcop'.dvd_of_dvd_mul_right (by
    rw [hcross]
    exact ⟨q, rfl⟩)
  have hpeq : p = p' :=
    le_antisymm (Int.le_of_dvd hp' hpdvd) (Int.le_of_dvd hp hp'dvd)
  have hqeq : q = q' := by
    rw [hpeq] at hcross
    exact (mul_left_cancel₀ (ne_of_gt hp') hcross).symm
  have hrEq : r = r' := by
    subst p'
    subst q'
    have hb : directionBase p r ∈ primitiveDirectionAffine p q r := by
      exact AffineSubspace.self_mem_mk' (directionBase p r) (directionNormal p q).ker
    have hb' : directionBase p r ∈ primitiveDirectionAffine p q r' := by
      rw [← hline]
      exact hb
    have hnormal := directionNormal_base p q r (ne_of_gt hp)
    have hmem := (mem_primitiveDirectionAffine_iff p q r' (ne_of_gt hp)
      (directionBase p r)).mp hb'
    have hrealeq : (r : ℝ) = (r' : ℝ) := by
      rw [← hnormal]
      exact hmem
    exact_mod_cast hrealeq
  exact ⟨hpeq, hqeq, hrEq⟩

/-- 与 `WeightedST` 的直线子类型对接后的参数唯一性。 -/
theorem primitiveDirectionLine_parameters_unique
    (p q p' q' : ℤ) (r r' : ℚ)
    (hp : 0 < p) (hp' : 0 < p')
    (hq : q ≠ 0) (hq' : q' ≠ 0)
    (hprimitive : Nat.gcd p.natAbs q.natAbs = 1)
    (hprimitive' : Nat.gcd p'.natAbs q'.natAbs = 1)
    (hline : primitiveDirectionLine p q r hp =
      primitiveDirectionLine p' q' r' hp') :
    p = p' ∧ q = q' ∧ r = r' := by
  exact primitiveDirectionAffine_parameters_unique p q p' q' r r' hp hp' hq hq'
    hprimitive hprimitive' (congrArg Subtype.val hline)

/-- 自然数速度对 `(a,b)` 的实欧氏平面嵌入。 -/
def velocityPairPoint (a b : ℕ) : EuclideanSpace ℝ (Fin 2) :=
  directionPoint (a : ℝ) (b : ℝ)

/-- 速度对嵌入是单射，两个实坐标各自恢复一个自然数。 -/
theorem velocityPairPoint_injective :
    Function.Injective (fun ab : ℕ × ℕ => velocityPairPoint ab.1 ab.2) := by
  intro ab cd heq
  have h0 := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) heq
  have h1 := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 1) heq
  simp only [velocityPairPoint, directionPoint_zero] at h0
  simp only [velocityPairPoint, directionPoint_one] at h1
  exact Prod.ext (by exact_mod_cast h0) (by exact_mod_cast h1)

/-- 速度集的笛卡尔平方在平面中的点集 `P_V`。 -/
noncomputable def velocityPairPoints (V : Finset ℕ) :
    Finset (EuclideanSpace ℝ (Fin 2)) :=
  (V.product V).image (fun ab => velocityPairPoint ab.1 ab.2)

theorem mem_velocityPairPoints_iff (V : Finset ℕ)
    (z : EuclideanSpace ℝ (Fin 2)) :
    z ∈ velocityPairPoints V ↔
      ∃ a ∈ V, ∃ b ∈ V, z = velocityPairPoint a b := by
  constructor
  · intro hz
    obtain ⟨⟨a, b⟩, hab, heq⟩ := Finset.mem_image.mp hz
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    exact ⟨a, ha, b, hb, heq.symm⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩

/-- 论文短关系计数：平面速度对点集恰有 `|V|²` 个点。 -/
theorem velocityPairPoints_card (V : Finset ℕ) :
    (velocityPairPoints V).card = V.card ^ 2 := by
  classical
  calc
    (velocityPairPoints V).card = (V.product V).card := by
      exact Finset.card_image_of_injective (V.product V) velocityPairPoint_injective
    _ = V.card ^ 2 := by simp [Finset.card_product, pow_two]

/-- 平面点在线上的条件与自然数速度对满足的有理方程完全等价。 -/
theorem velocityPairPoint_mem_primitiveDirectionLine_iff
    (p q : ℤ) (r : ℚ) (hp : 0 < p) (a b : ℕ) :
    velocityPairPoint a b ∈
        (primitiveDirectionLine p q r hp : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) ↔
      (p : ℚ) * (a : ℚ) + (q : ℚ) * (b : ℚ) = r := by
  change velocityPairPoint a b ∈ primitiveDirectionAffine p q r ↔ _
  rw [mem_primitiveDirectionAffine_iff p q r (ne_of_gt hp)]
  simp only [velocityPairPoint, directionPoint_zero, directionPoint_one]
  exact ⟨fun h => by exact_mod_cast h, fun h => by exact_mod_cast h⟩

end LonelyRunner
