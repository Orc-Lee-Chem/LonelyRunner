import LonelyRunner.RelationLatticeReduction
import Mathlib.Data.Int.Interval

namespace LonelyRunner

/-- 论文 `lem:latticecount` 第 255 行：非零整数关系向量的最大坐标绝对值。 -/
def relationMaxAbs (w : Fin 3 → ℤ) : ℕ :=
  max (w 0).natAbs (max (w 1).natAbs (w 2).natAbs)

/-- 论文 `lem:latticecount` 第 255 行：最小最大范数的候选集合。 -/
def relationLambdaCandidates (a b c : ℕ) : Set ℕ :=
  {n | ∃ w : Fin 3 → ℤ, w ∈ relationLattice a b c ∧ w ≠ 0 ∧
    relationMaxAbs w = n}

/-- 论文 `lem:latticecount` 第 255 行：`λ` 是非零整数关系的最小最大范数。 -/
noncomputable def relationLambda (a b c : ℕ) : ℕ :=
  sInf (relationLambdaCandidates a b c)

private theorem relationMaxAbs_pos (w : Fin 3 → ℤ) (hw : w ≠ 0) :
    0 < relationMaxAbs w := by
  by_contra hn
  have hm : relationMaxAbs w = 0 := by omega
  have h0 : w 0 = 0 := by
    have : (w 0).natAbs = 0 := by unfold relationMaxAbs at hm; omega
    simpa using this
  have h1 : w 1 = 0 := by
    have : (w 1).natAbs = 0 := by unfold relationMaxAbs at hm; omega
    simpa using this
  have h2 : w 2 = 0 := by
    have : (w 2).natAbs = 0 := by unfold relationMaxAbs at hm; omega
    simpa using this
  apply hw
  funext i
  fin_cases i <;> simp [h0, h1, h2]

/-- 论文 `lem:latticecount`：最小最大范数候选非空。 -/
theorem relationLambdaCandidates_nonempty (a b c : ℕ) (hb : 0 < b) :
    (relationLambdaCandidates a b c).Nonempty := by
  obtain ⟨w, hw, hwne⟩ := relationLattice_exists_nonzero a b c hb
  exact ⟨relationMaxAbs w, w, hw, hwne, rfl⟩

/-- 论文 `lem:latticecount`：`λ` 为正，且其最小值由实际非零格点取到。 -/
theorem relationLambda_pos_and_attained (a b c : ℕ) (hb : 0 < b) :
    0 < relationLambda a b c ∧
      ∃ w : Fin 3 → ℤ, w ∈ relationLattice a b c ∧ w ≠ 0 ∧
        relationMaxAbs w = relationLambda a b c := by
  have hne := relationLambdaCandidates_nonempty a b c hb
  obtain ⟨w, hw, hwne, hmax⟩ := Nat.sInf_mem hne
  refine ⟨?_, w, hw, hwne, hmax⟩
  change 0 < sInf (relationLambdaCandidates a b c)
  rw [← hmax]
  exact relationMaxAbs_pos w hwne

/-- 论文 `lem:latticecount`：任何非零关系的最大范数至少为 `λ`。 -/
theorem relationLambda_le_maxAbs (a b c : ℕ) (w : Fin 3 → ℤ)
    (hw : w ∈ relationLattice a b c) (hwne : w ≠ 0) :
    relationLambda a b c ≤ relationMaxAbs w := by
  exact Nat.sInf_le ⟨w, hw, hwne, rfl⟩

/-- 论文 `lem:latticecount` 第 255–257 行：有限的关系格立方体点集。 -/
noncomputable def relationCube (a b c : ℕ) (R : ℝ) : Finset (Fin 3 → ℤ) :=
  by
    classical
    exact (Fintype.piFinset fun _ : Fin 3 => Finset.Icc (-⌈R⌉ : ℤ) ⌈R⌉).filter
      (fun w => w ∈ relationLattice a b c ∧ ∀ i : Fin 3, |(w i : ℝ)| ≤ R)

/-- 论文 `lem:latticecount`：有限集逐点等于 `Λ∩[-R,R]^3`。 -/
theorem mem_relationCube_iff (a b c : ℕ) (R : ℝ) (w : Fin 3 → ℤ) :
    w ∈ relationCube a b c R ↔
      w ∈ relationLattice a b c ∧ ∀ i : Fin 3, |(w i : ℝ)| ≤ R := by
  classical
  constructor
  · intro hw
    exact (Finset.mem_filter.mp (show w ∈
      (Fintype.piFinset fun _ : Fin 3 => Finset.Icc (-⌈R⌉ : ℤ) ⌈R⌉).filter
        (fun w => w ∈ relationLattice a b c ∧ ∀ i : Fin 3, |(w i : ℝ)| ≤ R) from hw)).2
  · intro hw
    change w ∈ (Fintype.piFinset fun _ : Fin 3 =>
      Finset.Icc (-⌈R⌉ : ℤ) ⌈R⌉).filter _
    apply Finset.mem_filter.mpr
    constructor
    · apply Fintype.mem_piFinset.mpr
      intro i
      have habs := (abs_le.mp (hw.2 i))
      have hceil : R ≤ (⌈R⌉ : ℝ) := Int.le_ceil R
      apply Finset.mem_Icc.mpr
      constructor
      · exact_mod_cast (by linarith [habs.1] : (-(⌈R⌉ : ℤ) : ℝ) ≤ (w i : ℝ))
      · exact_mod_cast (habs.2.trans hceil)
    · exact hw

/-- 论文 `lem:latticecount`：有限集的强制类型转换精确等于原关系格与闭立方体的交。 -/
theorem relationCube_eq_lattice_inter_box (a b c : ℕ) (R : ℝ) :
    ((relationCube a b c R : Finset (Fin 3 → ℤ)) : Set (Fin 3 → ℤ)) =
      relationLattice a b c ∩ {w | ∀ i : Fin 3, |(w i : ℝ)| ≤ R} := by
  ext w
  simpa [Set.mem_inter_iff] using mem_relationCube_iff a b c R w

/-- 论文 `lem:latticecount` 第 267 行：间距为 `d>0` 的一维整数仿射点在闭区间
`[A,B]` 内至多有 `1+(B-A)/d` 个；两个端点均计入。 -/
theorem relation_affine_integer_card (s : Finset ℤ) (d A B offset : ℝ)
    (hd : 0 < d) (hAB : A ≤ B)
    (hs : ∀ n ∈ s, A ≤ (n : ℝ) * d + offset ∧
      (n : ℝ) * d + offset ≤ B) :
    (s.card : ℝ) ≤ 1 + (B - A) / d := by
  classical
  by_cases hne : s.Nonempty
  · let lo := s.min' hne
    let hi := s.max' hne
    have hlo : lo ∈ s := s.min'_mem hne
    have hhi : hi ∈ s := s.max'_mem hne
    have hlohi : lo ≤ hi := s.min'_le _ hhi
    have hsub : s ⊆ Finset.Icc lo hi := by
      intro n hn
      exact Finset.mem_Icc.mpr ⟨s.min'_le _ hn, Finset.le_max' _ _ hn⟩
    have hcardZ : (s.card : ℤ) ≤ hi + 1 - lo := by
      rw [← Int.card_Icc_of_le lo hi (by omega)]
      exact_mod_cast Finset.card_le_card hsub
    have hcardR : (s.card : ℝ) ≤ (hi : ℝ) + 1 - (lo : ℝ) := by
      exact_mod_cast hcardZ
    have hleft := (hs lo hlo).1
    have hright := (hs hi hhi).2
    have hspan : ((hi : ℝ) - (lo : ℝ)) * d ≤ B - A := by
      nlinarith
    have hcardD : ((s.card : ℝ) - 1) * d ≤ B - A := by
      nlinarith [mul_le_mul_of_nonneg_right hcardR hd.le]
    have := (le_div_iff₀ hd).mpr hcardD
    linarith
  · have hzero : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [hzero]
    positivity

private theorem relation_coord_abs_le_norm (w : Fin 3 → ℤ) (i : Fin 3) :
    |(w i : ℝ)| ≤ ‖relationToEuclidean w‖ := by
  have hsq := relationToEuclidean_norm_sq w
  have hn := norm_nonneg (relationToEuclidean w)
  fin_cases i
  · change |(w 0 : ℝ)| ≤ ‖relationToEuclidean w‖
    apply (sq_le_sq₀ (abs_nonneg _) hn).mp
    rw [sq_abs]
    nlinarith [sq_nonneg (w 1 : ℝ), sq_nonneg (w 2 : ℝ)]
  · change |(w 1 : ℝ)| ≤ ‖relationToEuclidean w‖
    apply (sq_le_sq₀ (abs_nonneg _) hn).mp
    rw [sq_abs]
    nlinarith [sq_nonneg (w 0 : ℝ), sq_nonneg (w 2 : ℝ)]
  · change |(w 2 : ℝ)| ≤ ‖relationToEuclidean w‖
    apply (sq_le_sq₀ (abs_nonneg _) hn).mp
    rw [sq_abs]
    nlinarith [sq_nonneg (w 0 : ℝ), sq_nonneg (w 1 : ℝ)]

/-- 论文 `lem:latticecount` 第 272 行：真正的最大范数 `λ` 不超过任意非零
格点的欧氏长度。 -/
theorem relationLambda_le_euclidean (a b c : ℕ) (w : Fin 3 → ℤ)
    (hw : w ∈ relationLattice a b c) (hwne : w ≠ 0) :
    (relationLambda a b c : ℝ) ≤ ‖relationToEuclidean w‖ := by
  have hlam : relationLambda a b c ≤ relationMaxAbs w :=
    relationLambda_le_maxAbs a b c w hw hwne
  have hmax : (relationMaxAbs w : ℝ) ≤ ‖relationToEuclidean w‖ := by
    simp only [relationMaxAbs, Nat.cast_max, Nat.cast_natAbs, Int.cast_abs]
    exact max_le (relation_coord_abs_le_norm w 0)
      (max_le (relation_coord_abs_le_norm w 1) (relation_coord_abs_le_norm w 2))
  have hcast : (relationLambda a b c : ℝ) ≤ (relationMaxAbs w : ℝ) := by
    exact_mod_cast hlam
  exact hcast.trans hmax

/-- 论文 `lem:latticecount` 第 267 行：闭立方体内格点的欧氏长度至多为
`√3·R`，此处使用的确是 `EuclideanSpace ℝ (Fin 3)` 范数。 -/
theorem relationCube_norm_le (a b c : ℕ) (R : ℝ) (hR : 0 ≤ R)
    (w : Fin 3 → ℤ) (hw : w ∈ relationCube a b c R) :
    ‖relationToEuclidean w‖ ≤ Real.sqrt 3 * R := by
  have hcoord := (mem_relationCube_iff a b c R w).mp hw |>.2
  have hsqi (i : Fin 3) : (w i : ℝ) ^ 2 ≤ R ^ 2 := by
    have habs := hcoord i
    have hprod := mul_nonneg (sub_nonneg.mpr habs)
      (add_nonneg hR (abs_nonneg (w i : ℝ)))
    nlinarith [sq_abs (w i : ℝ)]
  have hsq := relationToEuclidean_norm_sq w
  have hsqrt : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := by norm_num
  have hn := norm_nonneg (relationToEuclidean w)
  have hrhs : 0 ≤ Real.sqrt 3 * R := by positivity
  nlinarith [hsqi 0, hsqi 1, hsqi 2]

/-- 论文 `lem:latticecount`：整数线性组合进入欧氏空间后仍是同一线性组合。 -/
theorem relationToEuclidean_combo (u v : Fin 3 → ℤ) (j k : ℤ) :
    relationToEuclidean (relationCombo u v j k) =
      (j : ℝ) • relationToEuclidean u + (k : ℝ) • relationToEuclidean v := by
  apply PiLp.ext
  intro i
  simp [relationToEuclidean, relationCombo]

/-- 论文 `lem:latticecount` 第 267 行：格点 `ju+kv` 的正交投影与平行投影
分别控制第二、第一整数基坐标。 -/
theorem relation_combo_projection_bounds (u v : Fin 3 → ℤ) (hu : u ≠ 0)
    (hbeta : 0 < relationProjectionBeta (relationToEuclidean u)
      (relationToEuclidean v))
    (horth : inner ℝ (relationOrthogonalPart (relationToEuclidean u)
      (relationToEuclidean v)) (relationToEuclidean u) = 0)
    (j k : ℤ) :
    |(k : ℝ) * relationProjectionBeta (relationToEuclidean u)
      (relationToEuclidean v)| ≤
        ‖relationToEuclidean (relationCombo u v j k)‖ ∧
    |(j : ℝ) * ‖relationToEuclidean u‖ +
        (k : ℝ) * relationProjectionAlpha (relationToEuclidean u)
          (relationToEuclidean v)| ≤
        ‖relationToEuclidean (relationCombo u v j k)‖ := by
  let U := relationToEuclidean u
  let V := relationToEuclidean v
  let Z := relationOrthogonalPart U V
  let β := relationProjectionBeta U V
  have hU : U ≠ 0 := by
    intro h
    apply hu
    funext i
    have hi : (u i : ℝ) = 0 := by
      have := congrArg (fun x : EuclideanSpace ℝ (Fin 3) => x i) h
      simpa [U, relationToEuclidean] using this
    exact_mod_cast hi
  have hn : 0 < ‖U‖ := norm_pos_iff.mpr hU
  have hUZ : inner ℝ U Z = 0 := by
    rw [real_inner_comm]
    exact horth
  let s : ℝ := inner ℝ V U / ‖U‖ ^ 2
  have hV : V = Z + s • U := by
    dsimp [Z, relationOrthogonalPart, s]
    abel
  have hVZ : inner ℝ V Z = β ^ 2 := by
    rw [hV, inner_add_left, real_inner_smul_left, hUZ,
      real_inner_self_eq_norm_sq]
    change ‖Z‖ ^ 2 + s * 0 = ‖Z‖ ^ 2
    ring
  have hcomb := relationToEuclidean_combo u v j k
  have hk : inner ℝ (relationToEuclidean (relationCombo u v j k)) Z =
      (k : ℝ) * β ^ 2 := by
    rw [hcomb, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      hUZ, hVZ]
    ring
  have hc := abs_real_inner_le_norm
    (relationToEuclidean (relationCombo u v j k)) Z
  have hβ : 0 < β := hbeta
  have hkbound : |(k : ℝ) * β| ≤
      ‖relationToEuclidean (relationCombo u v j k)‖ := by
    apply le_of_mul_le_mul_right ?_ hβ
    calc
      |(k : ℝ) * β| * β = |(k : ℝ) * β ^ 2| := by
        rw [abs_mul, abs_mul, abs_of_pos hβ, abs_of_nonneg (sq_nonneg β)]
        ring
      _ = |inner ℝ (relationToEuclidean (relationCombo u v j k)) Z| := by rw [hk]
      _ ≤ ‖relationToEuclidean (relationCombo u v j k)‖ * β := hc
  have hj : inner ℝ (relationToEuclidean (relationCombo u v j k)) U / ‖U‖ =
      (j : ℝ) * ‖U‖ + (k : ℝ) * relationProjectionAlpha U V := by
    rw [hcomb, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
    dsimp [relationProjectionAlpha]
    field_simp
    ring
  have hc' := abs_real_inner_le_norm
    (relationToEuclidean (relationCombo u v j k)) U
  have hjbound : |(j : ℝ) * ‖U‖ +
      (k : ℝ) * relationProjectionAlpha U V| ≤
      ‖relationToEuclidean (relationCombo u v j k)‖ := by
    rw [← hj, abs_div, abs_of_pos hn]
    exact (div_le_iff₀ hn).mpr (by nlinarith [hc'])
  exact ⟨hkbound, hjbound⟩

/-- 论文 `lem:latticecount` 第 267 行：先数第二坐标的行，再对每行数第一坐标。
每一层都调用已证的闭区间整数计数，未假设逐行计数结论。 -/
theorem relation_pair_row_count (T : Finset (ℤ × ℤ))
    (d₁ d₂ M alpha : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hM : 0 ≤ M)
    (hpoint : ∀ p ∈ T, |(p.2 : ℝ) * d₂| ≤ M ∧
      |(p.1 : ℝ) * d₁ + (p.2 : ℝ) * alpha| ≤ M) :
    (T.card : ℝ) ≤ (1 + 2 * M / d₂) * (1 + 2 * M / d₁) := by
  classical
  let K : Finset ℤ := T.image Prod.snd
  let F : ℤ → Finset (ℤ × ℤ) := fun k => T.filter (fun p => p.2 = k)
  let J : ℤ → Finset ℤ := fun k => (F k).image Prod.fst
  have hK : (K.card : ℝ) ≤ 1 + 2 * M / d₂ := by
    have h := relation_affine_integer_card K d₂ (-M) M 0 hd₂ (by linarith)
      (by
        intro k hk
        obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp hk
        have hkp := (abs_le.mp (hpoint p hp).1)
        simpa [heq, sub_eq_add_neg] using hkp)
    convert h using 1
    ring
  have hJ (k : ℤ) : ((J k).card : ℝ) ≤ 1 + 2 * M / d₁ := by
    have h := relation_affine_integer_card (J k) d₁ (-M) M
      ((k : ℝ) * alpha) hd₁ (by linarith) (by
        intro j hj
        obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp hj
        have hpT := (Finset.mem_filter.mp hp).1
        have hpk := (Finset.mem_filter.mp hp).2
        have hjp := (abs_le.mp (hpoint p hpT).2)
        simpa [heq, hpk] using hjp)
    convert h using 1
    ring
  have hF (k : ℤ) : (F k).card = (J k).card := by
    symm
    apply Finset.card_image_of_injOn
    intro p hp q hq hfst
    have hp2 := (Finset.mem_filter.mp hp).2
    have hq2 := (Finset.mem_filter.mp hq).2
    apply Prod.ext hfst
    exact hp2.trans hq2.symm
  have hsum : (T.card : ℝ) = ∑ k ∈ K, ((F k).card : ℝ) := by
    have h := Finset.card_eq_sum_card_image Prod.snd T
    exact_mod_cast h
  have hsumle : (T.card : ℝ) ≤
      ∑ _k ∈ K, (1 + 2 * M / d₁) := by
    rw [hsum]
    apply Finset.sum_le_sum
    intro k hk
    rw [hF]
    exact hJ k
  rw [Finset.sum_const] at hsumle
  simp only [nsmul_eq_mul] at hsumle
  have hfac : 0 ≤ 1 + 2 * M / d₁ := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hK hfac]

/-- 论文 `lem:latticecount` 第 267 行：关系格有限点集通过唯一整数坐标映射
注入 `ℤ²`，再按行求和，得到精确的两个一维选择数之积。 -/
theorem relationCube_card_le_reduced (a b c : ℕ) (R : ℝ) (hR : 0 ≤ R)
    (u v : Fin 3 → ℤ) (hu : u ≠ 0)
    (hbase : ∀ z : Fin 3 → ℤ, z ∈ relationLattice a b c →
      ∃! pq : ℤ × ℤ, z = relationCombo u v pq.1 pq.2)
    (hbeta : 0 < relationProjectionBeta (relationToEuclidean u)
      (relationToEuclidean v))
    (horth : inner ℝ (relationOrthogonalPart (relationToEuclidean u)
      (relationToEuclidean v)) (relationToEuclidean u) = 0) :
    ((relationCube a b c R).card : ℝ) ≤
      (1 + 2 * (Real.sqrt 3 * R) /
        relationProjectionBeta (relationToEuclidean u) (relationToEuclidean v)) *
      (1 + 2 * (Real.sqrt 3 * R) / ‖relationToEuclidean u‖) := by
  classical
  let coord : (Fin 3 → ℤ) → ℤ × ℤ := fun z =>
    if hz : z ∈ relationLattice a b c then Classical.choose (hbase z hz) else (0, 0)
  have hcoord (z : Fin 3 → ℤ) (hz : z ∈ relationLattice a b c) :
      z = relationCombo u v (coord z).1 (coord z).2 := by
    simpa [coord, hz] using (Classical.choose_spec (hbase z hz)).1
  have hcoordCube (z : Fin 3 → ℤ) (hz : z ∈ relationCube a b c R) :
      z = relationCombo u v (coord z).1 (coord z).2 :=
    hcoord z ((mem_relationCube_iff a b c R z).mp hz).1
  let T : Finset (ℤ × ℤ) := (relationCube a b c R).image coord
  have hinj : Set.InjOn coord (relationCube a b c R : Set (Fin 3 → ℤ)) := by
    intro z hz z' hz' heq
    calc
      z = relationCombo u v (coord z).1 (coord z).2 := hcoordCube z hz
      _ = relationCombo u v (coord z').1 (coord z').2 := by rw [heq]
      _ = z' := (hcoordCube z' hz').symm
  have hcard : T.card = (relationCube a b c R).card :=
    Finset.card_image_of_injOn hinj
  have hn : 0 < ‖relationToEuclidean u‖ := by
    apply norm_pos_iff.mpr
    intro h
    apply hu
    funext i
    have hi : (u i : ℝ) = 0 := by
      have := congrArg (fun x : EuclideanSpace ℝ (Fin 3) => x i) h
      simpa [relationToEuclidean] using this
    exact_mod_cast hi
  have hM : 0 ≤ Real.sqrt 3 * R := by positivity
  have hpoint (p : ℤ × ℤ) (hp : p ∈ T) :
      |(p.2 : ℝ) * relationProjectionBeta (relationToEuclidean u)
        (relationToEuclidean v)| ≤ Real.sqrt 3 * R ∧
      |(p.1 : ℝ) * ‖relationToEuclidean u‖ +
        (p.2 : ℝ) * relationProjectionAlpha (relationToEuclidean u)
          (relationToEuclidean v)| ≤ Real.sqrt 3 * R := by
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hp
    have hrep := hcoordCube z hz
    have hnorm := relationCube_norm_le a b c R hR z hz
    rw [hrep] at hnorm
    obtain ⟨hk, hj⟩ := relation_combo_projection_bounds u v hu hbeta horth
      (coord z).1 (coord z).2
    exact ⟨hk.trans hnorm, hj.trans hnorm⟩
  have h := relation_pair_row_count T ‖relationToEuclidean u‖
    (relationProjectionBeta (relationToEuclidean u) (relationToEuclidean v))
    (Real.sqrt 3 * R)
    (relationProjectionAlpha (relationToEuclidean u) (relationToEuclidean v))
    hn hbeta hM hpoint
  simpa only [hcard] using h

/-- 论文 `lem:latticecount` 第 273 行：本原法向量的欧氏长度至少为
第三坐标 `h=c/gcd(a,b,c)`。 -/
theorem relationPrimitiveNormal_norm_ge_height (a b c : ℕ) :
    (relationC a b c : ℝ) ≤
      ‖relationToEuclidean (relationPrimitiveNormal a b c)‖ := by
  have h := relation_coord_abs_le_norm (relationPrimitiveNormal a b c) 2
  simpa [relationPrimitiveNormal] using h

/-- 论文 `lem:latticecount` 第 273 行：当 `c>0` 时，分母高度
`h=c/gcd(a,b,c)` 严格为正。 -/
theorem relationHeight_pos (a b c : ℕ) (hc : 0 < c) :
    0 < relationC a b c := by
  have hg : 0 < relationGcd a b c := by
    exact Nat.gcd_pos_of_pos_right (a.gcd b) hc
  have hd : relationGcd a b c ∣ c := Nat.gcd_dvd_right _ _
  exact Nat.div_pos (Nat.le_of_dvd hc hd) hg

/-- 论文 `lem:latticecount` 第 269–273 行：将逐行乘积界化为含 `λ` 和
`h` 的表达式。常数 `12` 与所有格参数及 `R` 无关。 -/
theorem relation_row_product_le_final (R L U beta H : ℝ)
    (hR : 0 ≤ R) (hL : 0 < L) (hU : L ≤ U) (hbeta : 0 < beta)
    (hheight : Real.sqrt 3 * U / 2 ≤ beta)
    (hH : 0 < H) (harea : H ≤ beta * U) :
    (1 + 2 * (Real.sqrt 3 * R) / beta) *
      (1 + 2 * (Real.sqrt 3 * R) / U) ≤
        12 * (1 + R / L + R ^ 2 / H) := by
  have hUpos : 0 < U := lt_of_lt_of_le hL hU
  have hsqrt : 0 ≤ Real.sqrt (3 : ℝ) := Real.sqrt_nonneg _
  have hsqrt2 : Real.sqrt (3 : ℝ) ^ 2 = 3 := by norm_num
  have hsqrtle : Real.sqrt (3 : ℝ) ≤ 2 := by nlinarith
  have htermB : 2 * (Real.sqrt 3 * R) / beta ≤ 4 * R / U := by
    apply (div_le_div_iff₀ hbeta hUpos).mpr
    have hmul := mul_le_mul_of_nonneg_left hheight (by positivity : 0 ≤ 4 * R)
    nlinarith
  have htermU : 2 * (Real.sqrt 3 * R) / U ≤ 4 * R / L := by
    apply (div_le_div_iff₀ hUpos hL).mpr
    have hmul := mul_le_mul_of_nonneg_right hsqrtle
      (by positivity : 0 ≤ 2 * R * L)
    have hmul' := mul_le_mul_of_nonneg_left hU (by positivity : 0 ≤ 4 * R)
    nlinarith
  have hcross :
      (2 * (Real.sqrt 3 * R) / beta) *
        (2 * (Real.sqrt 3 * R) / U) ≤ 12 * R ^ 2 / H := by
    have heq : (2 * (Real.sqrt 3 * R) / beta) *
        (2 * (Real.sqrt 3 * R) / U) = 12 * R ^ 2 / (beta * U) := by
      field_simp
      nlinarith [hsqrt2]
    rw [heq]
    apply (div_le_div_iff₀ (mul_pos hbeta hUpos) hH).mpr
    exact mul_le_mul_of_nonneg_left harea (by positivity)
  have htermB' : 2 * (Real.sqrt 3 * R) / beta ≤ 4 * R / L :=
    htermB.trans (by
      apply (div_le_div_iff₀ hUpos hL).mpr
      nlinarith [mul_le_mul_of_nonneg_left hU (by positivity : 0 ≤ 4 * R)])
  have hRL : 0 ≤ R / L := div_nonneg hR hL.le
  have hRH : 0 ≤ R ^ 2 / H := div_nonneg (sq_nonneg R) hH.le
  calc
    _ = 1 + 2 * (Real.sqrt 3 * R) / beta +
        2 * (Real.sqrt 3 * R) / U +
        (2 * (Real.sqrt 3 * R) / beta) *
          (2 * (Real.sqrt 3 * R) / U) := by ring
    _ ≤ 1 + 8 * R / L + 12 * R ^ 2 / H := by
      have hsum := add_le_add (add_le_add htermB' htermU) hcross
      have hsum' := add_le_add_left hsum (1 : ℝ)
      convert hsum' using 1 <;> ring
    _ ≤ 12 * (1 + R / L + R ^ 2 / H) := by
      have hcompare : 1 + 8 * (R / L) + 12 * (R ^ 2 / H) ≤
          12 * (1 + R / L + R ^ 2 / H) := by nlinarith [hRL, hRH]
      convert hcompare using 1
      ring

/-- 论文 `lem:latticecount`，式 `(eq:lattice)`：对 `0<a<b<c`、`R≥1`，
立方体内满足原整数关系的格点数至多
`12·(1+R/λ+R²/h)`，其中 `λ` 是最小最大范数，`h=c/gcd(a,b,c)`。
常数 `12` 独立于 `a,b,c,R`。 -/
theorem relationLattice_count (a b c : ℕ)
    (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (R : ℝ) (hR : 1 ≤ R) :
    ((relationCube a b c R).card : ℝ) ≤
      12 * (1 + R / (relationLambda a b c : ℝ) +
        R ^ 2 / (relationC a b c : ℝ)) := by
  have hb : 0 < b := lt_trans ha hab
  have hc : 0 < c := lt_trans hb hbc
  obtain ⟨u, v₀, hu, hune, hshort, hv₀, hbase₀, hcross₀⟩ :=
    relationLattice_exists_shortest_basis a b c ha hb hc
  obtain ⟨q, v, _, _, hv, hvne, hbase, hcross, horth, _, _, hbeta,
    _, hheight, harea⟩ :=
      relationLattice_reduce_shortest_basis a b c ha hb hc u v₀
        hu hune hshort hv₀ hbase₀ hcross₀
  have hrow := relationCube_card_le_reduced a b c R (by linarith) u v
    hune hbase hbeta horth
  have hlamNat := (relationLambda_pos_and_attained a b c hb).1
  have hlam : (0 : ℝ) < relationLambda a b c := by exact_mod_cast hlamNat
  have hheightNat := relationHeight_pos a b c hc
  have hH : (0 : ℝ) < relationC a b c := by exact_mod_cast hheightNat
  have hU := relationLambda_le_euclidean a b c u hu hune
  have hHle : (relationC a b c : ℝ) ≤
      relationProjectionBeta (relationToEuclidean u) (relationToEuclidean v) *
        ‖relationToEuclidean u‖ := by
    rw [harea]
    exact relationPrimitiveNormal_norm_ge_height a b c
  have hfinal := relation_row_product_le_final R
    (relationLambda a b c : ℝ) ‖relationToEuclidean u‖
    (relationProjectionBeta (relationToEuclidean u) (relationToEuclidean v))
    (relationC a b c : ℝ) (by linarith) hlam hU hbeta hheight hH hHle
  exact hrow.trans hfinal

/-- 论文 `lem:latticecount` 的集合表述：通过已经证明的有限集精确对应，
上式直接计数 `Λ∩[-R,R]^3`，没有更改关系方程或闭区间端点。 -/
theorem relationLattice_count_set (a b c : ℕ)
    (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (R : ℝ) (hR : 1 ≤ R) :
    (((relationLattice a b c ∩
      {w : Fin 3 → ℤ | ∀ i : Fin 3, |(w i : ℝ)| ≤ R}).ncard : ℝ)) ≤
      12 * (1 + R / (relationLambda a b c : ℝ) +
        R ^ 2 / (relationC a b c : ℝ)) := by
  rw [← relationCube_eq_lattice_inter_box a b c R]
  simpa using relationLattice_count a b c ha hab hbc R hR

#print axioms LonelyRunner.relationLambda_pos_and_attained
#print axioms LonelyRunner.relationCube_eq_lattice_inter_box
#print axioms LonelyRunner.relation_affine_integer_card
#print axioms LonelyRunner.relationCube_norm_le
#print axioms LonelyRunner.relation_pair_row_count
#print axioms LonelyRunner.relationCube_card_le_reduced
#print axioms LonelyRunner.relation_row_product_le_final
#print axioms LonelyRunner.relationLattice_count
#print axioms LonelyRunner.relationLattice_count_set

end LonelyRunner
