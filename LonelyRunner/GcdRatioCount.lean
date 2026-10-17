import LonelyRunner.GcdTripleInverse

/-!
# 公共因子比值的精确计数

论文 `paper/lonely_runner_zh.tex` 第 200 行 `eq:energy` 后的计数恒等式。
-/

namespace LonelyRunner

/-- 论文 `eq:energy`：满足 `1 ≤ u,v ≤ U` 与 `u*c=v*c'` 的有序正整数对。 -/
noncomputable def gcdRatioSolutions (U c c' : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 U).product (Finset.Icc 1 U)).filter
    (fun uv => uv.1 * c = uv.2 * c')

@[simp] theorem gcdRatioSolutions_zero (c c' : ℕ) :
    gcdRatioSolutions 0 c c' = ∅ := by
  simp [gcdRatioSolutions]

private lemma gcdRatio_factors (c c' : ℕ) (hc : 0 < c) (hc' : 0 < c') :
    let g := Nat.gcd c c'
    let a := c / g
    let b := c' / g
    0 < g ∧ 0 < a ∧ 0 < b ∧ c = g * a ∧ c' = g * b ∧ Nat.Coprime a b := by
  dsimp
  have hg : 0 < Nat.gcd c c' := Nat.gcd_pos_of_pos_left c' hc
  have hca : Nat.gcd c c' * (c / Nat.gcd c c') = c :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left c c')
  have hcb : Nat.gcd c c' * (c' / Nat.gcd c c') = c' :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_right c c')
  have ha : 0 < c / Nat.gcd c c' := by
    by_contra h
    have hz : c / Nat.gcd c c' = 0 := Nat.eq_zero_of_not_pos h
    simp [hz] at hca
    omega
  have hb : 0 < c' / Nat.gcd c c' := by
    by_contra h
    have hz : c' / Nat.gcd c c' = 0 := Nat.eq_zero_of_not_pos h
    simp [hz] at hcb
    omega
  exact ⟨hg, ha, hb, hca.symm, hcb.symm,
    Nat.coprime_div_gcd_div_gcd hg⟩

/-- 论文 `eq:energy` 后的参数化：在 `u,v>0` 下，关系 `uc=vc'` 的全部解恰为
`u=(c'/g)j, v=(c/g)j`，其中 `j≥1`。 -/
theorem gcdRatio_parameterization (c c' u v : ℕ)
    (hc : 0 < c) (hc' : 0 < c') (hu : 0 < u) (hv : 0 < v) :
    u * c = v * c' ↔
      ∃ j : ℕ, 1 ≤ j ∧
        u = (c' / Nat.gcd c c') * j ∧
        v = (c / Nat.gcd c c') * j := by
  let g := Nat.gcd c c'
  let a := c / g
  let b := c' / g
  obtain ⟨hg, ha, hb, hca, hcb, hab⟩ := gcdRatio_factors c c' hc hc'
  change u * c = v * c' ↔ ∃ j, 1 ≤ j ∧ u = b * j ∧ v = a * j
  constructor
  · intro h
    have hred : u * a = v * b := by
      apply Nat.eq_of_mul_eq_mul_left hg
      calc
        g * (u * a) = u * c := by rw [hca]; ring
        _ = v * c' := h
        _ = g * (v * b) := by rw [hcb]; ring
    have hbdvd : b ∣ u := hab.symm.dvd_of_dvd_mul_right (by
      rw [hred]
      exact dvd_mul_left b v)
    obtain ⟨j, hj⟩ := hbdvd
    have hjpos : 1 ≤ j := by
      by_contra hzero
      have : j = 0 := by omega
      subst j
      simp at hj
      omega
    have hvj : v = a * j := by
      have hcancel : b * (j * a) = b * v := by
        calc
          b * (j * a) = (b * j) * a := by ring
          _ = u * a := by rw [hj]
          _ = v * b := hred
          _ = b * v := by ring
      have := Nat.eq_of_mul_eq_mul_left hb hcancel
      simpa [mul_comm] using this.symm
    exact ⟨j, hjpos, hj, hvj⟩
  · rintro ⟨j, _, rfl, rfl⟩
    calc
      (b * j) * c = (b * j) * (g * a) := congrArg _ hca
      _ = (a * j) * (g * b) := by ring
      _ = (a * j) * c' := (congrArg _ hcb).symm

/-- 上述参数 `j` 唯一；因此它可用于有限集合的单射计数。 -/
theorem gcdRatio_parameter_unique (c c' u j k : ℕ)
    (hc : 0 < c) (hc' : 0 < c')
    (hj : u = (c' / Nat.gcd c c') * j)
    (hk : u = (c' / Nat.gcd c c') * k) : j = k := by
  have hb := (gcdRatio_factors c c' hc hc').2.2.1
  exact Nat.eq_of_mul_eq_mul_left hb (hj.symm.trans hk)

/-- 参数的精确范围：`1≤j` 时，两个坐标都不超过 `U` 等价于
`j≤U/max(a,b)`。 -/
theorem gcdRatio_parameter_range (U a b j : ℕ) (ha : 0 < a) :
    (b * j ≤ U ∧ a * j ≤ U) ↔ j ≤ U / max a b := by
  have hmax : 0 < max a b := lt_of_lt_of_le ha (le_max_left a b)
  rw [Nat.le_div_iff_mul_le hmax]
  constructor
  · rintro ⟨hbU, haU⟩
    have h := max_le haU hbU
    simpa [max_mul, mul_comm] using h
  · intro h
    have hmaxU : max (a * j) (b * j) ≤ U := by
      simpa [max_mul, mul_comm] using h
    exact ⟨(le_max_right _ _).trans hmaxU, (le_max_left _ _).trans hmaxU⟩

/-- `E_U(c,c')` 与正整数参数区间的双射所对应的集合等式。 -/
theorem gcdRatioSolutions_eq_image (U c c' : ℕ) (hc : 0 < c) (hc' : 0 < c') :
    let g := Nat.gcd c c'
    let a := c / g
    let b := c' / g
    gcdRatioSolutions U c c' =
      (Finset.Icc 1 (U / max a b)).image (fun j => (b * j, a * j)) := by
  dsimp
  let g := Nat.gcd c c'
  let a := c / g
  let b := c' / g
  obtain ⟨_, ha, hb, _, _, _⟩ := gcdRatio_factors c c' hc hc'
  ext ⟨u, v⟩
  constructor
  · intro hmem
    obtain ⟨hprod, hrel⟩ := Finset.mem_filter.mp hmem
    obtain ⟨huI, hvI⟩ := Finset.mem_product.mp hprod
    obtain ⟨hu0, huU⟩ := Finset.mem_Icc.mp huI
    obtain ⟨hv0, hvU⟩ := Finset.mem_Icc.mp hvI
    obtain ⟨j, hj, huj, hvj⟩ :=
      (gcdRatio_parameterization c c' u v hc hc' hu0 hv0).mp hrel
    have hjU : j ≤ U / max a b :=
      (gcdRatio_parameter_range U a b j ha).mp (by simpa [huj, hvj] using And.intro huU hvU)
    exact Finset.mem_image.mpr ⟨j, Finset.mem_Icc.mpr ⟨hj, hjU⟩,
      Prod.ext huj.symm hvj.symm⟩
  · intro hmem
    obtain ⟨j, hjI, heq⟩ := Finset.mem_image.mp hmem
    obtain ⟨hj0, hjU⟩ := Finset.mem_Icc.mp hjI
    have hjbounds := (gcdRatio_parameter_range U a b j ha).mpr hjU
    have hu0 : 1 ≤ b * j := Nat.mul_pos hb hj0
    have hv0 : 1 ≤ a * j := Nat.mul_pos ha hj0
    have hrel : (b * j) * c = (a * j) * c' :=
      (gcdRatio_parameterization c c' (b * j) (a * j) hc hc' hu0 hv0).mpr
        ⟨j, hj0, rfl, rfl⟩
    have hpair : (b * j, a * j) ∈ gcdRatioSolutions U c c' := by
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_product.mpr
          ⟨Finset.mem_Icc.mpr ⟨hu0, hjbounds.1⟩,
            Finset.mem_Icc.mpr ⟨hv0, hjbounds.2⟩⟩
      · exact hrel
    exact heq ▸ hpair

/-- 论文 `eq:energy` 第 200 行：有序解对的精确计数，自然数除法即向下取整。 -/
theorem gcdRatioSolutions_card (U c c' : ℕ) (hc : 0 < c) (hc' : 0 < c') :
    (gcdRatioSolutions U c c').card =
      U * Nat.gcd c c' / max c c' := by
  let g := Nat.gcd c c'
  let a := c / g
  let b := c' / g
  obtain ⟨hg, _, hb, hca, hcb, _⟩ := gcdRatio_factors c c' hc hc'
  have hmax : max c c' = g * max a b := by
    calc
      max c c' = max (g * a) (g * b) := congrArg₂ max hca hcb
      _ = g * max a b := max_mul_mul_left g a b
  have hdiv : U * g / max c c' = U / max a b := by
    calc
      U * g / max c c' = U * g / (max a b * g) := by rw [hmax, mul_comm g]
      _ = U / max a b := Nat.mul_div_mul_right U (max a b) hg
  rw [gcdRatioSolutions_eq_image U c c' hc hc']
  have hinj : Set.InjOn (fun j : ℕ => (b * j, a * j))
      (Finset.Icc 1 (U / max a b)) := by
    intro j _ k _ h
    exact Nat.eq_of_mul_eq_mul_left hb (congrArg Prod.fst h)
  rw [(Finset.card_image_iff.mpr hinj), Nat.card_Icc]
  simp [g, a, b, hdiv]

/-- 相同速度时，精确地有 `U` 个解 `(j,j)`；也涵盖 `U=0`。 -/
theorem gcdRatioSolutions_same_card (U c : ℕ) (hc : 0 < c) :
    (gcdRatioSolutions U c c).card = U := by
  rw [gcdRatioSolutions_card U c c hc hc]
  simp [Nat.gcd_self, hc.ne']

/-- 精确自然数商公式给出的实数上界，所有分母因 `c,c'>0` 而非零。 -/
theorem gcdRatioSolutions_card_real_le (U c c' : ℕ)
    (hc : 0 < c) (hc' : 0 < c') :
    ((gcdRatioSolutions U c c').card : ℝ) ≤
      (U : ℝ) * (Nat.gcd c c' : ℝ) / (max c c' : ℝ) := by
  rw [gcdRatioSolutions_card U c c' hc hc']
  simpa only [Nat.cast_mul, Nat.cast_max] using
    (Nat.cast_div_le (α := ℝ) (m := U * Nat.gcd c c') (n := max c c'))

/-- 论文 `eq:energy` 第 200 行：对有限正整数速度集求和，右侧正是项目中
`inversePairGcdSum W = S₂(W)`。不使用任何 Bondarenko–Seip 输入。 -/
theorem gcdRatioSolutions_sum_le_inversePairGcdSum
    (W : Finset ℕ) (hWpos : ∀ c ∈ W, 0 < c) (U : ℕ) :
    (∑ c ∈ W, ∑ c' ∈ W, ((gcdRatioSolutions U c c').card : ℝ)) ≤
      (U : ℝ) * inversePairGcdSum W := by
  unfold inversePairGcdSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c hc
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c' hc'
  convert gcdRatioSolutions_card_real_le U c c' (hWpos c hc) (hWpos c' hc') using 1
  ring

end LonelyRunner
