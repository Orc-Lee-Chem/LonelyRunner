import LonelyRunner.RelationLatticeShortest
import Mathlib.Geometry.Euclidean.Angle.Unoriented.CrossProduct

namespace LonelyRunner

open EuclideanSpace
open scoped RealInnerProductSpace

/-- 论文 `lem:latticecount` 证明开头：实数总能取到距离至多半单位的整数。 -/
theorem relation_exists_nearest_integer (x : ℝ) :
    ∃ q : ℤ, |x - (q : ℝ)| ≤ 1 / 2 := by
  refine ⟨⌊x + 1 / 2⌋, ?_⟩
  have h₁ := Int.floor_le (x + 1 / 2)
  have h₂ := Int.lt_floor_add_one (x + 1 / 2)
  rw [abs_le]
  constructor <;> linarith

/-- 论文 `lem:latticecount`：将第二基向量减去第一基向量的整数倍。 -/
def relationReducedSecond (u v : Fin 3 → ℤ) (q : ℤ) : Fin 3 → ℤ :=
  fun i => v i - q * u i

private theorem relationReducedSecond_mem (a b c : ℕ) (u v : Fin 3 → ℤ)
    (hu : u ∈ relationLattice a b c) (hv : v ∈ relationLattice a b c) (q : ℤ) :
    relationReducedSecond u v q ∈ relationLattice a b c := by
  change (a : ℤ) * u 0 + (b : ℤ) * u 1 + (c : ℤ) * u 2 = 0 at hu
  change (a : ℤ) * v 0 + (b : ℤ) * v 1 + (c : ℤ) * v 2 = 0 at hv
  change (a : ℤ) * (v 0 - q * u 0) + (b : ℤ) * (v 1 - q * u 1) +
    (c : ℤ) * (v 2 - q * u 2) = 0
  linear_combination hv - q * hu

private theorem relationReducedSecond_combo (u v : Fin 3 → ℤ) (q j t : ℤ) :
    relationCombo u (relationReducedSecond u v q) j t =
      relationCombo u v (j - t * q) t := by
  funext i
  simp only [relationCombo, relationReducedSecond]
  ring

private theorem relationReducedSecond_cross (u v : Fin 3 → ℤ) (q : ℤ) :
    relationCross u (relationReducedSecond u v q) = relationCross u v := by
  funext i
  fin_cases i <;> simp [relationCross, relationReducedSecond] <;> ring

/-- 论文 `lem:latticecount`：整数化约保持关系格的唯一整数表示与叉积。 -/
theorem relation_reduced_basis (a b c : ℕ) (u v : Fin 3 → ℤ)
    (hu : u ∈ relationLattice a b c) (hv : v ∈ relationLattice a b c)
    (hbase : ∀ z : Fin 3 → ℤ, z ∈ relationLattice a b c →
      ∃! pq : ℤ × ℤ, z = relationCombo u v pq.1 pq.2)
    (q : ℤ) :
    relationReducedSecond u v q ∈ relationLattice a b c ∧
    relationReducedSecond u v q ≠ 0 ∧
    (∀ z : Fin 3 → ℤ, z ∈ relationLattice a b c →
      ∃! pq : ℤ × ℤ, z = relationCombo u (relationReducedSecond u v q) pq.1 pq.2) ∧
    relationCross u (relationReducedSecond u v q) = relationCross u v := by
  have hw := relationReducedSecond_mem a b c u v hu hv q
  have hzero : (0 : Fin 3 → ℤ) ∈ relationLattice a b c := by
    change (a : ℤ) * 0 + (b : ℤ) * 0 + (c : ℤ) * 0 = 0
    ring
  refine ⟨hw, ?_, ?_, relationReducedSecond_cross u v q⟩
  · intro hw0
    obtain ⟨p, _, hp⟩ := hbase 0 hzero
    have h₀ : (0 : Fin 3 → ℤ) = relationCombo u v 0 0 := by
      funext i; simp [relationCombo]
    have h₁ : (0 : Fin 3 → ℤ) = relationCombo u v (-q) 1 := by
      rw [← hw0]
      funext i; simp [relationCombo, relationReducedSecond]; ring
    have heq := (hp (0, 0) h₀).trans (hp (-q, 1) h₁).symm
    have := congrArg Prod.snd heq
    norm_num at this
  · intro z hz
    obtain ⟨p, hp, hunique⟩ := hbase z hz
    refine ⟨(p.1 + p.2 * q, p.2), ?_, ?_⟩
    · change z = relationCombo u (relationReducedSecond u v q)
        (p.1 + p.2 * q) p.2
      rw [relationReducedSecond_combo]
      simpa only [add_sub_cancel_right] using hp
    · intro r hr
      have hr' : z = relationCombo u v (r.1 - r.2 * q) r.2 := by
        simpa only [relationReducedSecond_combo] using hr
      have heq := hunique (r.1 - r.2 * q, r.2) hr'
      have hfirst := congrArg Prod.fst heq
      have hsecond := congrArg Prod.snd heq
      dsimp at hfirst hsecond
      apply Prod.ext
      · dsimp
        rw [hsecond] at hfirst
        nlinarith
      · exact hsecond

private theorem relationToEuclidean_ne_zero (u : Fin 3 → ℤ) (hu : u ≠ 0) :
    relationToEuclidean u ≠ 0 := by
  intro h
  apply hu
  funext i
  have hi : (u i : ℝ) = 0 := by
    have := congrArg (fun x : EuclideanSpace ℝ (Fin 3) => x i) h
    simpa [relationToEuclidean] using this
  exact_mod_cast hi

/-- 论文 `lem:latticecount`：整数向量的欧氏嵌入保持化约运算。 -/
theorem relationToEuclidean_reduced (u v : Fin 3 → ℤ) (q : ℤ) :
    relationToEuclidean (relationReducedSecond u v q) =
      relationToEuclidean v - (q : ℝ) • relationToEuclidean u := by
  apply PiLp.ext
  intro i
  simp [relationToEuclidean, relationReducedSecond]

/-- 论文 `lem:latticecount`：化约基的平行方向坐标。 -/
noncomputable def relationProjectionAlpha (U W : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  inner ℝ W U / ‖U‖

/-- 论文 `lem:latticecount`：从第二基向量去掉沿第一基向量的正交投影。 -/
noncomputable def relationOrthogonalPart (U W : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) :=
  W - (inner ℝ W U / ‖U‖ ^ 2) • U

/-- 论文 `lem:latticecount`：正交方向的长度 `β`。 -/
noncomputable def relationProjectionBeta (U W : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ‖relationOrthogonalPart U W‖

/-- 论文 `lem:latticecount`：正交分解、平行坐标半宽界及勾股恒等式。 -/
theorem relation_projection_geometry (U W : EuclideanSpace ℝ (Fin 3))
    (hU : U ≠ 0)
    (hq : |inner ℝ W U / ‖U‖ ^ 2| ≤ 1 / 2) :
    inner ℝ (relationOrthogonalPart U W) U = 0 ∧
    |relationProjectionAlpha U W| ≤ ‖U‖ / 2 ∧
    ‖W‖ ^ 2 = relationProjectionAlpha U W ^ 2 +
      relationProjectionBeta U W ^ 2 := by
  have hn : ‖U‖ ≠ 0 := norm_ne_zero_iff.mpr hU
  have hn2 : ‖U‖ ^ 2 ≠ 0 := pow_ne_zero 2 hn
  let s : ℝ := inner ℝ W U / ‖U‖ ^ 2
  let Z : EuclideanSpace ℝ (Fin 3) := W - s • U
  have horth : inner ℝ Z U = 0 := by
    dsimp [Z, s]
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
    ring
  have halpha : relationProjectionAlpha U W = s * ‖U‖ := by
    dsimp [relationProjectionAlpha, s]
    field_simp
  have hW : W = Z + s • U := by
    dsimp [Z]
    abel
  have horth' : inner ℝ Z (s • U) = 0 := by
    rw [real_inner_smul_right, horth]
    ring
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_real horth'
  have hsquare : ‖s • U‖ ^ 2 = (s * ‖U‖) ^ 2 := by
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hpyth' : ‖W‖ ^ 2 = ‖Z‖ ^ 2 + ‖s • U‖ ^ 2 := by
    rw [hW]
    nlinarith [hpyth]
  refine ⟨horth, ?_, ?_⟩
  · rw [halpha, abs_mul, abs_norm]
    have hnorm : 0 ≤ ‖U‖ := norm_nonneg _
    exact (mul_le_mul_of_nonneg_right hq hnorm).trans_eq (by ring)
  · change ‖W‖ ^ 2 = relationProjectionAlpha U W ^ 2 + ‖Z‖ ^ 2
    rw [halpha]
    linarith [hpyth', hsquare]

private theorem relation_inner_coordinates (u w : Fin 3 → ℤ) :
    inner ℝ (relationToEuclidean w) (relationToEuclidean u) =
      (w 0 : ℝ) * (u 0 : ℝ) + (w 1 : ℝ) * (u 1 : ℝ) +
        (w 2 : ℝ) * (u 2 : ℝ) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, Fin.sum_univ_three, relationToEuclidean, mul_comm]

/-- 论文 `lem:latticecount`：三维整数叉积满足欧氏拉格朗日恒等式。 -/
theorem relation_cross_lagrange (u w : Fin 3 → ℤ) :
    ‖relationToEuclidean (relationCross u w)‖ ^ 2 =
      ‖relationToEuclidean u‖ ^ 2 * ‖relationToEuclidean w‖ ^ 2 -
        (inner ℝ (relationToEuclidean w) (relationToEuclidean u)) ^ 2 := by
  rw [relationToEuclidean_norm_sq, relationToEuclidean_norm_sq,
    relationToEuclidean_norm_sq, relation_inner_coordinates]
  simp [relationCross]
  ring

/-- 论文 `lem:latticecount`：最近整数取整后，化约向量的投影系数至多 `1/2`。 -/
theorem relation_reduced_projection_bound (u v : Fin 3 → ℤ) (hu : u ≠ 0) :
    ∃ q : ℤ,
      |inner ℝ (relationToEuclidean v) (relationToEuclidean u) /
          ‖relationToEuclidean u‖ ^ 2 - (q : ℝ)| ≤ 1 / 2 ∧
      |inner ℝ (relationToEuclidean (relationReducedSecond u v q))
          (relationToEuclidean u) / ‖relationToEuclidean u‖ ^ 2| ≤ 1 / 2 := by
  let U := relationToEuclidean u
  let V := relationToEuclidean v
  have hU : U ≠ 0 := relationToEuclidean_ne_zero u hu
  have hn : ‖U‖ ≠ 0 := norm_ne_zero_iff.mpr hU
  obtain ⟨q, hq⟩ := relation_exists_nearest_integer (inner ℝ V U / ‖U‖ ^ 2)
  refine ⟨q, hq, ?_⟩
  have heq : inner ℝ (relationToEuclidean (relationReducedSecond u v q)) U /
      ‖U‖ ^ 2 = inner ℝ V U / ‖U‖ ^ 2 - (q : ℝ) := by
    rw [relationToEuclidean_reduced, inner_sub_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
    field_simp
    ring
  rw [heq]
  exact hq

/-- 论文 `lem:latticecount`：最短向量与半宽界给出正交高度的 `√3/2` 下界。 -/
theorem relation_reduced_height (U W : EuclideanSpace ℝ (Fin 3))
    (hU : U ≠ 0) (hshort : ‖U‖ ≤ ‖W‖)
    (hq : |inner ℝ W U / ‖U‖ ^ 2| ≤ 1 / 2) :
    0 < relationProjectionBeta U W ∧
      3 * ‖U‖ ^ 2 / 4 ≤ relationProjectionBeta U W ^ 2 ∧
      Real.sqrt 3 * ‖U‖ / 2 ≤ relationProjectionBeta U W := by
  obtain ⟨_, hα, hpyth⟩ := relation_projection_geometry U W hU hq
  have hUn : 0 ≤ ‖U‖ := norm_nonneg _
  have hUp : 0 < ‖U‖ := norm_pos_iff.mpr hU
  have hWn : 0 ≤ ‖W‖ := norm_nonneg _
  have hβn : 0 ≤ relationProjectionBeta U W := norm_nonneg _
  have hαabs := (abs_le.mp hα)
  have hαsq : relationProjectionAlpha U W ^ 2 ≤ ‖U‖ ^ 2 / 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hαabs.2)
      (by linarith [hαabs.1] : 0 ≤ ‖U‖ / 2 + relationProjectionAlpha U W)]
  have hβsq : 3 * ‖U‖ ^ 2 / 4 ≤ relationProjectionBeta U W ^ 2 := by
    nlinarith [sq_nonneg (‖W‖ - ‖U‖)]
  have hsqrt : 0 ≤ Real.sqrt (3 : ℝ) := Real.sqrt_nonneg _
  have hsqrt2 : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := by norm_num
  have htarget : 0 ≤ Real.sqrt 3 * ‖U‖ / 2 := by positivity
  have hbetabound : Real.sqrt 3 * ‖U‖ / 2 ≤ relationProjectionBeta U W := by
    nlinarith [sq_nonneg (relationProjectionBeta U W + Real.sqrt 3 * ‖U‖ / 2)]
  refine ⟨?_, hβsq, hbetabound⟩
  nlinarith [sq_pos_of_pos hUp]

/-- 论文 `lem:latticecount`：平面关系格基本平行四边形面积等于 `β‖U‖`。 -/
theorem relation_reduced_area (u w : Fin 3 → ℤ) (hu : u ≠ 0) :
    relationProjectionBeta (relationToEuclidean u) (relationToEuclidean w) *
      ‖relationToEuclidean u‖ = ‖relationToEuclidean (relationCross u w)‖ := by
  let U := relationToEuclidean u
  let W := relationToEuclidean w
  have hU : U ≠ 0 := relationToEuclidean_ne_zero u hu
  have hn : ‖U‖ ≠ 0 := norm_ne_zero_iff.mpr hU
  have hn2 : ‖U‖ ^ 2 ≠ 0 := pow_ne_zero 2 hn
  let s : ℝ := inner ℝ W U / ‖U‖ ^ 2
  have hproj : s * ‖U‖ ^ 2 = inner ℝ W U := by
    dsimp [s]
    field_simp
  have hsinner : inner ℝ W (s • U) = s * inner ℝ W U := by
    rw [real_inner_smul_right]
  have hsnorm : ‖s • U‖ ^ 2 = s ^ 2 * ‖U‖ ^ 2 := by
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hZsq : relationProjectionBeta U W ^ 2 =
      ‖W‖ ^ 2 - 2 * s * inner ℝ W U + s ^ 2 * ‖U‖ ^ 2 := by
    change ‖W - s • U‖ ^ 2 = _
    rw [norm_sub_sq_real, hsinner, hsnorm]
    ring
  have harea_sq : relationProjectionBeta U W ^ 2 * ‖U‖ ^ 2 =
      ‖U‖ ^ 2 * ‖W‖ ^ 2 - (inner ℝ W U) ^ 2 := by
    calc
      _ = (‖W‖ ^ 2 - 2 * s * inner ℝ W U + s ^ 2 * ‖U‖ ^ 2) * ‖U‖ ^ 2 := by
        rw [hZsq]
      _ = _ := by rw [← hproj]; ring
  have hcross := relation_cross_lagrange u w
  have hβn : 0 ≤ relationProjectionBeta U W := norm_nonneg _
  have hUn : 0 ≤ ‖U‖ := norm_nonneg _
  have hcrossn : 0 ≤ ‖relationToEuclidean (relationCross u w)‖ := norm_nonneg _
  dsimp [U, W] at harea_sq
  apply (sq_eq_sq₀ (mul_nonneg hβn hUn) hcrossn).mp
  calc
    (relationProjectionBeta (relationToEuclidean u) (relationToEuclidean w) *
      ‖relationToEuclidean u‖) ^ 2 =
        relationProjectionBeta (relationToEuclidean u) (relationToEuclidean w) ^ 2 *
          ‖relationToEuclidean u‖ ^ 2 := by ring
    _ = ‖relationToEuclidean (relationCross u w)‖ ^ 2 := harea_sq.trans hcross.symm

/-- 论文 `lem:latticebasis` 与 `lem:latticecount`：本原法向量 `(a/g,b/g,c/g)`。 -/
def relationPrimitiveNormal (a b c : ℕ) : Fin 3 → ℤ :=
  ![(relationA a b c : ℤ), (relationB a b c : ℤ), (relationC a b c : ℤ)]

/-- 论文 `lem:latticecount`：显式格基叉积的欧氏长度是本原法向量长度。 -/
theorem relation_basis_cross_norm (a b c : ℕ) (ha : 0 < a) (hc : 0 < c) :
    ‖relationToEuclidean
      (relationCross (relationBasisFirst a b c) (relationBasisSecond a b c))‖ =
      ‖relationToEuclidean (relationPrimitiveNormal a b c)‖ := by
  rw [show relationCross (relationBasisFirst a b c) (relationBasisSecond a b c) =
    ![-(relationA a b c : ℤ), -(relationB a b c : ℤ), -(relationC a b c : ℤ)] from
      relationLattice_basis_cross a b c ha hc]
  have hsq : ‖relationToEuclidean
      ![-(relationA a b c : ℤ), -(relationB a b c : ℤ), -(relationC a b c : ℤ)]‖ ^ 2 =
      ‖relationToEuclidean (relationPrimitiveNormal a b c)‖ ^ 2 := by
    rw [relationToEuclidean_norm_sq, relationToEuclidean_norm_sq]
    simp [relationPrimitiveNormal]
  nlinarith [norm_nonneg (relationToEuclidean
      ![-(relationA a b c : ℤ), -(relationB a b c : ℤ), -(relationC a b c : ℤ)]),
    norm_nonneg (relationToEuclidean (relationPrimitiveNormal a b c))]

/-- 论文 `lem:latticecount` 证明的化约步骤：从最短整数格基取得所需整数 `q`、
化约整数基、正交分解、高度下界和以本原法向量表示的面积公式。 -/
theorem relationLattice_reduce_shortest_basis (a b c : ℕ)
    (ha : 0 < a) (_hb : 0 < b) (hc : 0 < c)
    (u v : Fin 3 → ℤ)
    (hu : u ∈ relationLattice a b c) (hune : u ≠ 0)
    (hshort : ∀ z : Fin 3 → ℤ, z ∈ relationLattice a b c → z ≠ 0 →
      ‖relationToEuclidean u‖ ≤ ‖relationToEuclidean z‖)
    (hv : v ∈ relationLattice a b c)
    (hbase : ∀ z : Fin 3 → ℤ, z ∈ relationLattice a b c →
      ∃! pq : ℤ × ℤ, z = relationCombo u v pq.1 pq.2)
    (hcross : relationCross u v =
      relationCross (relationBasisFirst a b c) (relationBasisSecond a b c)) :
    ∃ q : ℤ, ∃ w : Fin 3 → ℤ,
      w = relationReducedSecond u v q ∧
      |inner ℝ (relationToEuclidean v) (relationToEuclidean u) /
          ‖relationToEuclidean u‖ ^ 2 - (q : ℝ)| ≤ 1 / 2 ∧
      w ∈ relationLattice a b c ∧ w ≠ 0 ∧
      (∀ z : Fin 3 → ℤ, z ∈ relationLattice a b c →
        ∃! pq : ℤ × ℤ, z = relationCombo u w pq.1 pq.2) ∧
      relationCross u w = relationCross u v ∧
      inner ℝ (relationOrthogonalPart (relationToEuclidean u)
        (relationToEuclidean w)) (relationToEuclidean u) = 0 ∧
      |relationProjectionAlpha (relationToEuclidean u) (relationToEuclidean w)| ≤
        ‖relationToEuclidean u‖ / 2 ∧
      ‖relationToEuclidean w‖ ^ 2 =
        relationProjectionAlpha (relationToEuclidean u) (relationToEuclidean w) ^ 2 +
        relationProjectionBeta (relationToEuclidean u) (relationToEuclidean w) ^ 2 ∧
      0 < relationProjectionBeta (relationToEuclidean u) (relationToEuclidean w) ∧
      3 * ‖relationToEuclidean u‖ ^ 2 / 4 ≤
        relationProjectionBeta (relationToEuclidean u) (relationToEuclidean w) ^ 2 ∧
      Real.sqrt 3 * ‖relationToEuclidean u‖ / 2 ≤
        relationProjectionBeta (relationToEuclidean u) (relationToEuclidean w) ∧
      relationProjectionBeta (relationToEuclidean u) (relationToEuclidean w) *
        ‖relationToEuclidean u‖ =
        ‖relationToEuclidean (relationPrimitiveNormal a b c)‖ := by
  obtain ⟨q, hnearest, hq⟩ := relation_reduced_projection_bound u v hune
  let w := relationReducedSecond u v q
  obtain ⟨hw, hwne, hbase', hcross'⟩ := relation_reduced_basis a b c u v hu hv hbase q
  have hU := relationToEuclidean_ne_zero u hune
  obtain ⟨horth, halpha, hpyth⟩ :=
    relation_projection_geometry (relationToEuclidean u) (relationToEuclidean w) hU hq
  obtain ⟨hbeta, hbetasq, hbetalower⟩ :=
    relation_reduced_height (relationToEuclidean u) (relationToEuclidean w)
      hU (hshort w hw hwne) hq
  refine ⟨q, w, rfl, hnearest, hw, hwne, hbase', hcross', horth, halpha, hpyth,
    hbeta, hbetasq, hbetalower, ?_⟩
  rw [relation_reduced_area u w hune, hcross', hcross]
  exact relation_basis_cross_norm a b c ha hc

/-- 论文 `lem:latticebasis` 至 `lem:latticecount`：正整数三元组确实存在满足上述全部
化约结论的最短关系格基。 -/
theorem relationLattice_exists_reduced_shortest_basis (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ∃ u v : Fin 3 → ℤ,
      u ∈ relationLattice a b c ∧ u ≠ 0 ∧
      (∀ z : Fin 3 → ℤ, z ∈ relationLattice a b c → z ≠ 0 →
        ‖relationToEuclidean u‖ ≤ ‖relationToEuclidean z‖) ∧
      v ∈ relationLattice a b c ∧
      (∀ z : Fin 3 → ℤ, z ∈ relationLattice a b c →
        ∃! pq : ℤ × ℤ, z = relationCombo u v pq.1 pq.2) ∧
      relationCross u v =
        relationCross (relationBasisFirst a b c) (relationBasisSecond a b c) ∧
      0 < relationProjectionBeta (relationToEuclidean u) (relationToEuclidean v) ∧
      Real.sqrt 3 * ‖relationToEuclidean u‖ / 2 ≤
        relationProjectionBeta (relationToEuclidean u) (relationToEuclidean v) ∧
      relationProjectionBeta (relationToEuclidean u) (relationToEuclidean v) *
        ‖relationToEuclidean u‖ =
        ‖relationToEuclidean (relationPrimitiveNormal a b c)‖ := by
  obtain ⟨u, v, hu, hune, hshort, hv, hbase, hcross⟩ :=
    relationLattice_exists_shortest_basis a b c ha hb hc
  obtain ⟨q, w, _, _, hw, hwne, hbase', hcross', _, _, _, hbeta, _, hbetalower,
    harea⟩ := relationLattice_reduce_shortest_basis a b c ha hb hc u v
      hu hune hshort hv hbase hcross
  refine ⟨u, w, hu, hune, hshort, hw, hbase', ?_, hbeta, hbetalower, harea⟩
  exact hcross'.trans hcross

#print axioms LonelyRunner.relation_reduced_basis
#print axioms LonelyRunner.relation_projection_geometry
#print axioms LonelyRunner.relation_cross_lagrange
#print axioms LonelyRunner.relation_reduced_projection_bound
#print axioms LonelyRunner.relation_reduced_height
#print axioms LonelyRunner.relation_reduced_area
#print axioms LonelyRunner.relation_basis_cross_norm
#print axioms LonelyRunner.relationLattice_reduce_shortest_basis
#print axioms LonelyRunner.relationLattice_exists_reduced_shortest_basis

end LonelyRunner
