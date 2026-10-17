import LonelyRunner.RelationLatticeBasis
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace LonelyRunner

open EuclideanSpace



/-- 论文 `lem:latticebasis` 最短向量段：整数三元向量嵌入真正的三维欧氏空间。 -/
def relationToEuclidean (w : Fin 3 → ℤ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (fun i => (w i : ℝ))

/-- 论文 `lem:latticebasis`：此范数是欧氏范数，平方等于三个坐标的平方和。 -/
theorem relationToEuclidean_norm_sq (w : Fin 3 → ℤ) :
    ‖relationToEuclidean w‖ ^ 2 =
      (w 0 : ℝ) ^ 2 + (w 1 : ℝ) ^ 2 + (w 2 : ℝ) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  simp [relationToEuclidean]

/-- 论文 `lem:latticebasis`：整数坐标平方和，用于自然数良序取最小值。 -/
def relationSqLen (w : Fin 3 → ℤ) : ℕ :=
  (w 0).natAbs ^ 2 + (w 1).natAbs ^ 2 + (w 2).natAbs ^ 2

/-- 论文 `lem:latticebasis`：平方欧氏长度精确等于整数平方和的实数嵌入。 -/
theorem relationToEuclidean_norm_sq_nat (w : Fin 3 → ℤ) :
    ‖relationToEuclidean w‖ ^ 2 = (relationSqLen w : ℝ) := by
  rw [relationToEuclidean_norm_sq]
  simp only [relationSqLen, Nat.cast_add, Nat.cast_pow, Nat.cast_natAbs, Int.cast_abs]
  simp only [sq_abs]

/-- 论文 `lem:latticebasis`：正整数速度给出的关系格中至少有一个非零向量。 -/
theorem relationLattice_exists_nonzero (a b c : ℕ) (hb : 0 < b) :
    ∃ w : Fin 3 → ℤ, w ∈ relationLattice a b c ∧ w ≠ 0 := by
  refine ⟨![(b : ℤ), -(a : ℤ), 0], ?_, ?_⟩
  · show (a : ℤ) * (b : ℤ) + (b : ℤ) * (-(a : ℤ)) + (c : ℤ) * 0 = 0
    ring
  · intro hw
    have h0 := congrArg (fun w : Fin 3 → ℤ => w 0) hw
    simp at h0
    omega

private theorem relationSqLen_eq_zero_iff (w : Fin 3 → ℤ) :
    relationSqLen w = 0 ↔ w = 0 := by
  constructor
  · intro h
    have h0 : (w 0).natAbs ^ 2 = 0 := by
      unfold relationSqLen at h
      omega
    have h1 : (w 1).natAbs ^ 2 = 0 := by
      unfold relationSqLen at h
      omega
    have h2 : (w 2).natAbs ^ 2 = 0 := by
      unfold relationSqLen at h
      omega
    have hw0 : w 0 = 0 := by simpa using h0
    have hw1 : w 1 = 0 := by simpa using h1
    have hw2 : w 2 = 0 := by simpa using h2
    funext i
    fin_cases i <;> simp [hw0, hw1, hw2]
  · rintro rfl
    simp [relationSqLen]

private theorem relationSqLen_pos (w : Fin 3 → ℤ) (hw : w ≠ 0) :
    0 < relationSqLen w := by
  exact Nat.pos_of_ne_zero (fun h => hw ((relationSqLen_eq_zero_iff w).mp h))

/-- 论文 `lem:latticebasis`：用正整数平方长度的良序性取得非零关系格的欧氏最短向量。 -/
theorem relationLattice_exists_shortest (a b c : ℕ) (hb : 0 < b) :
    ∃ u : Fin 3 → ℤ, u ∈ relationLattice a b c ∧ u ≠ 0 ∧
      ∀ w : Fin 3 → ℤ, w ∈ relationLattice a b c → w ≠ 0 →
        ‖relationToEuclidean u‖ ≤ ‖relationToEuclidean w‖ := by
  classical
  obtain ⟨w₀, hw₀, hw₀ne⟩ := relationLattice_exists_nonzero a b c hb
  let p : ℕ → Prop := fun n =>
    ∃ w : Fin 3 → ℤ, w ∈ relationLattice a b c ∧ w ≠ 0 ∧ relationSqLen w = n
  have hex : ∃ n, p n := ⟨relationSqLen w₀, w₀, hw₀, hw₀ne, rfl⟩
  obtain ⟨u, hu, hune, hlen⟩ := Nat.find_spec hex
  refine ⟨u, hu, hune, ?_⟩
  intro w hw hwne
  have hmin : relationSqLen u ≤ relationSqLen w := by
    rw [hlen]
    exact Nat.find_min' hex ⟨w, hw, hwne, rfl⟩
  have hsq : ‖relationToEuclidean u‖ ^ 2 ≤ ‖relationToEuclidean w‖ ^ 2 := by
    rw [relationToEuclidean_norm_sq_nat, relationToEuclidean_norm_sq_nat]
    exact_mod_cast hmin
  nlinarith [norm_nonneg (relationToEuclidean u), norm_nonneg (relationToEuclidean w)]

/-- 论文 `lem:latticebasis`：整数向量的线性组合，坐标仍在 `ℤ³` 中。 -/
def relationCombo (u v : Fin 3 → ℤ) (j t : ℤ) : Fin 3 → ℤ :=
  fun i => j * u i + t * v i

private theorem relationCombo_mem (a b c : ℕ) (u v : Fin 3 → ℤ)
    (hu : u ∈ relationLattice a b c) (hv : v ∈ relationLattice a b c)
    (j t : ℤ) : relationCombo u v j t ∈ relationLattice a b c := by
  change (a : ℤ) * u 0 + (b : ℤ) * u 1 + (c : ℤ) * u 2 = 0 at hu
  change (a : ℤ) * v 0 + (b : ℤ) * v 1 + (c : ℤ) * v 2 = 0 at hv
  change (a : ℤ) * (j * u 0 + t * v 0) +
    (b : ℤ) * (j * u 1 + t * v 1) +
    (c : ℤ) * (j * u 2 + t * v 2) = 0
  linear_combination j * hu + t * hv

private theorem relationSqLen_scale (d : ℕ) (w : Fin 3 → ℤ) :
    relationSqLen (fun i => (d : ℤ) * w i) = d ^ 2 * relationSqLen w := by
  unfold relationSqLen
  simp only [Int.natAbs_mul, Int.natAbs_natCast]
  ring

/-- 论文 `lem:latticebasis`：对原始速度三元组指定第一个显式格基向量。 -/
def relationBasisFirst (a b c : ℕ) : Fin 3 → ℤ :=
  relationU0 (relationA a b c) (relationB a b c)

/-- 论文 `lem:latticebasis`：对原始速度三元组指定第二个显式格基向量。 -/
def relationBasisSecond (a b c : ℕ) : Fin 3 → ℤ :=
  relationV0 (relationA a b c) (relationB a b c) (relationC a b c)

/-- 论文 `lem:latticebasis`：任意最短非零格点的旧基坐标 `j,t` 互素。
公因子大于一时，除去公因子得到严格更短的非零格点。 -/
theorem relationLattice_shortest_coords_coprime (a b c : ℕ)
    (hc : 0 < c) (u : Fin 3 → ℤ)
    (_hu : u ∈ relationLattice a b c) (hune : u ≠ 0)
    (hshort : ∀ w : Fin 3 → ℤ, w ∈ relationLattice a b c → w ≠ 0 →
      ‖relationToEuclidean u‖ ≤ ‖relationToEuclidean w‖)
    (j t : ℤ) (hrep : u = relationCombo (relationBasisFirst a b c)
      (relationBasisSecond a b c) j t) :
    Nat.Coprime j.natAbs t.natAbs := by
  let d := Nat.gcd j.natAbs t.natAbs
  change d = 1
  by_contra hdone
  by_cases hd0 : d = 0
  · have hz := Nat.gcd_eq_zero_iff.mp hd0
    have hj0 : j = 0 := by simpa using hz.1
    have ht0 : t = 0 := by simpa using hz.2
    have hu0 : u = 0 := by
      rw [hrep]
      funext i
      simp [relationCombo, hj0, ht0]
    exact hune hu0
  · have hdgt : 1 < d := by omega
    have hdj : (d : ℤ) ∣ j :=
      Int.natCast_dvd.mpr (Nat.gcd_dvd_left j.natAbs t.natAbs)
    have hdt : (d : ℤ) ∣ t :=
      Int.natCast_dvd.mpr (Nat.gcd_dvd_right j.natAbs t.natAbs)
    obtain ⟨j', hj'⟩ := hdj
    obtain ⟨t', ht'⟩ := hdt
    let w' := relationCombo (relationBasisFirst a b c)
      (relationBasisSecond a b c) j' t'
    have hw' : w' ∈ relationLattice a b c :=
      relationCombo_mem a b c _ _
        (relationU0_mem_lattice a b c hc)
        (relationV0_mem_lattice a b c hc) j' t'
    have hscale : u = fun i => (d : ℤ) * w' i := by
      rw [hrep]
      funext i
      dsimp [relationCombo, w']
      rw [hj', ht']
      ring
    have hlen : relationSqLen u = d ^ 2 * relationSqLen w' := by
      rw [hscale]
      exact relationSqLen_scale d w'
    have hw'ne : w' ≠ 0 := by
      intro hw0
      have hu0 : relationSqLen u = 0 := by
        rw [hlen, hw0]
        simp [relationSqLen]
      exact hune ((relationSqLen_eq_zero_iff u).mp hu0)
    have hnorm := hshort w' hw' hw'ne
    have hle : relationSqLen u ≤ relationSqLen w' := by
      have hsq : ‖relationToEuclidean u‖ ^ 2 ≤
          ‖relationToEuclidean w'‖ ^ 2 := by
        nlinarith [norm_nonneg (relationToEuclidean u),
          norm_nonneg (relationToEuclidean w')]
      rw [relationToEuclidean_norm_sq_nat,
        relationToEuclidean_norm_sq_nat] at hsq
      exact_mod_cast hsq
    have hlt : relationSqLen w' < relationSqLen u := by
      rw [hlen]
      have hd2 : 1 < d ^ 2 := by nlinarith
      have h := Nat.mul_lt_mul_of_pos_right hd2 (relationSqLen_pos w' hw'ne)
      simpa using h
    omega

/-- 论文 `lem:latticebasis`：任意最短非零格点有唯一旧基坐标，且坐标互素。 -/
theorem relationLattice_shortest_repr (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (u : Fin 3 → ℤ) (hu : u ∈ relationLattice a b c) (hune : u ≠ 0)
    (hshort : ∀ w : Fin 3 → ℤ, w ∈ relationLattice a b c → w ≠ 0 →
      ‖relationToEuclidean u‖ ≤ ‖relationToEuclidean w‖) :
    ∃! jt : ℤ × ℤ,
      u = relationCombo (relationBasisFirst a b c) (relationBasisSecond a b c)
        jt.1 jt.2 ∧ Nat.Coprime jt.1.natAbs jt.2.natAbs := by
  obtain ⟨jt, hrepr, huniq⟩ :=
    relationLattice_basis_existsUnique a b c ha hb hc u hu
  have hcop := relationLattice_shortest_coords_coprime a b c hc u hu hune hshort
    jt.1 jt.2 hrepr
  refine ⟨jt, ⟨hrepr, hcop⟩, ?_⟩
  intro jt' h
  exact huniq jt' h.1

/-- 论文 `lem:latticebasis`：互素整数坐标的 Bézout 系数给出行列式一。 -/
theorem relationCoords_bezout (j t : ℤ)
    (hcop : Nat.Coprime j.natAbs t.natAbs) :
    ∃ α β : ℤ, j * β - t * α = 1 := by
  refine ⟨-Int.gcdB j t, Int.gcdA j t, ?_⟩
  have hg : Int.gcd j t = 1 := hcop
  have hbez := Int.gcd_eq_gcd_ab j t
  rw [hg] at hbez
  calc
    j * j.gcdA t - t * -j.gcdB t = j * j.gcdA t + t * j.gcdB t := by ring
    _ = 1 := hbez.symm

private theorem relationCombo_comp (U V : Fin 3 → ℤ) (j t α β p q : ℤ) :
    relationCombo (relationCombo U V j t) (relationCombo U V α β) p q =
      relationCombo U V (p * j + q * α) (p * t + q * β) := by
  funext i
  simp only [relationCombo]
  ring

private theorem relationCombo_inverse (U V : Fin 3 → ℤ) (j t α β : ℤ)
    (hdet : j * β - t * α = 1) (k l : ℤ) :
    relationCombo U V k l =
      relationCombo (relationCombo U V j t) (relationCombo U V α β)
        (β * k - α * l) (-t * k + j * l) := by
  rw [relationCombo_comp]
  have hfirst : (β * k - α * l) * j + (-t * k + j * l) * α = k := by
    calc
      _ = (j * β - t * α) * k := by ring
      _ = k := by rw [hdet]; ring
  have hsecond : (β * k - α * l) * t + (-t * k + j * l) * β = l := by
    calc
      _ = (j * β - t * α) * l := by ring
      _ = l := by rw [hdet]; ring
  rw [hfirst, hsecond]

/-- 论文 `lem:latticebasis`：行列式一的整数换基保持线性组合映射的单射性。 -/
theorem relationCombo_change_injective (U V : Fin 3 → ℤ)
    (hinj : Function.Injective (fun jt : ℤ × ℤ => relationCombo U V jt.1 jt.2))
    (j t α β : ℤ) (hdet : j * β - t * α = 1) :
    Function.Injective (fun pq : ℤ × ℤ =>
      relationCombo (relationCombo U V j t) (relationCombo U V α β) pq.1 pq.2) := by
  intro p q hpq
  have hpq' : (p.1 * j + p.2 * α, p.1 * t + p.2 * β) =
      (q.1 * j + q.2 * α, q.1 * t + q.2 * β) := by
    apply hinj
    simpa only [relationCombo_comp] using hpq
  have hfirst := congrArg Prod.fst hpq'
  have hsecond := congrArg Prod.snd hpq'
  dsimp at hfirst hsecond
  have hpeq : p.1 = q.1 := by
    calc
      p.1 = (j * β - t * α) * p.1 := by rw [hdet]; ring
      _ = β * (p.1 * j + p.2 * α) - α * (p.1 * t + p.2 * β) := by ring
      _ = β * (q.1 * j + q.2 * α) - α * (q.1 * t + q.2 * β) := by
        rw [hfirst, hsecond]
      _ = (j * β - t * α) * q.1 := by ring
      _ = q.1 := by rw [hdet]; ring
  have hqeq : p.2 = q.2 := by
    calc
      p.2 = (j * β - t * α) * p.2 := by rw [hdet]; ring
      _ = -t * (p.1 * j + p.2 * α) + j * (p.1 * t + p.2 * β) := by ring
      _ = -t * (q.1 * j + q.2 * α) + j * (q.1 * t + q.2 * β) := by
        rw [hfirst, hsecond]
      _ = (j * β - t * α) * q.2 := by ring
      _ = q.2 := by rw [hdet]; ring
  exact Prod.ext hpeq hqeq

/-- 论文 `lem:latticebasis`：行列式一的换基把旧基的每个整数点唯一表示为新基坐标。 -/
theorem relationCombo_change_existsUnique (U V : Fin 3 → ℤ)
    (hinj : Function.Injective (fun jt : ℤ × ℤ => relationCombo U V jt.1 jt.2))
    (j t α β : ℤ) (hdet : j * β - t * α = 1)
    (w : Fin 3 → ℤ) (k l : ℤ) (hw : w = relationCombo U V k l) :
    ∃! pq : ℤ × ℤ,
      w = relationCombo (relationCombo U V j t) (relationCombo U V α β)
        pq.1 pq.2 := by
  let p := β * k - α * l
  let q := -t * k + j * l
  have hrepr : w = relationCombo (relationCombo U V j t)
      (relationCombo U V α β) p q := by
    rw [hw]
    exact relationCombo_inverse U V j t α β hdet k l
  refine ⟨(p, q), hrepr, ?_⟩
  intro pq hpq
  exact relationCombo_change_injective U V hinj j t α β hdet
    (hpq.symm.trans hrepr)

private theorem relationDet2_change (x₁ x₂ y₁ y₂ j t α β : ℤ) :
    (j * x₁ + t * y₁) * (α * x₂ + β * y₂) -
      (j * x₂ + t * y₂) * (α * x₁ + β * y₁) =
        (j * β - t * α) * (x₁ * y₂ - x₂ * y₁) := by
  ring

/-- 论文 `lem:latticebasis`：行列式一的整数换基保持三维整数叉积。 -/
theorem relationCross_change_basis (U V : Fin 3 → ℤ) (j t α β : ℤ)
    (hdet : j * β - t * α = 1) :
    relationCross (relationCombo U V j t) (relationCombo U V α β) =
      relationCross U V := by
  funext i
  fin_cases i
  · simpa [relationCross, relationCombo, hdet] using
      (relationDet2_change (U 1) (U 2) (V 1) (V 2) j t α β)
  · simpa [relationCross, relationCombo, hdet] using
      (relationDet2_change (U 2) (U 0) (V 2) (V 0) j t α β)
  · simpa [relationCross, relationCombo, hdet] using
      (relationDet2_change (U 0) (U 1) (V 0) (V 1) j t α β)

private theorem relationBasis_map_injective (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Function.Injective (fun jt : ℤ × ℤ =>
      relationCombo (relationBasisFirst a b c) (relationBasisSecond a b c)
        jt.1 jt.2) := by
  intro p q hpq
  let w := relationCombo (relationBasisFirst a b c)
    (relationBasisSecond a b c) p.1 p.2
  have hw : w ∈ relationLattice a b c :=
    relationCombo_mem a b c _ _
      (relationU0_mem_lattice a b c hc)
      (relationV0_mem_lattice a b c hc) p.1 p.2
  obtain ⟨jt, hrepr, huniq⟩ :=
    relationLattice_basis_existsUnique a b c ha hb hc w hw
  have hq : w = relationCombo (relationBasisFirst a b c)
      (relationBasisSecond a b c) q.1 q.2 := hpq
  exact (huniq p rfl).trans (huniq q hq).symm

/-- 论文 `lem:latticebasis` 最短向量扩基段：任意最短非零格点 `u` 可与某个
`v=αu₀+βv₀` 组成整数基；新基叉积等于旧基叉积。 -/
theorem relationLattice_shortest_extends_basis (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (u : Fin 3 → ℤ) (hu : u ∈ relationLattice a b c) (hune : u ≠ 0)
    (hshort : ∀ w : Fin 3 → ℤ, w ∈ relationLattice a b c → w ≠ 0 →
      ‖relationToEuclidean u‖ ≤ ‖relationToEuclidean w‖) :
    ∃ j t α β : ℤ, ∃ v : Fin 3 → ℤ,
      u = relationCombo (relationBasisFirst a b c) (relationBasisSecond a b c) j t ∧
      Nat.Coprime j.natAbs t.natAbs ∧
      j * β - t * α = 1 ∧
      v = relationCombo (relationBasisFirst a b c) (relationBasisSecond a b c) α β ∧
      v ∈ relationLattice a b c ∧
      (∀ w : Fin 3 → ℤ, w ∈ relationLattice a b c →
        ∃! pq : ℤ × ℤ, w = relationCombo u v pq.1 pq.2) ∧
      relationCross u v =
        relationCross (relationBasisFirst a b c) (relationBasisSecond a b c) := by
  obtain ⟨jt, ⟨hrep, hcop⟩, _⟩ :=
    relationLattice_shortest_repr a b c ha hb hc u hu hune hshort
  obtain ⟨α, β, hdet⟩ := relationCoords_bezout jt.1 jt.2 hcop
  let U := relationBasisFirst a b c
  let V := relationBasisSecond a b c
  let v := relationCombo U V α β
  have hinj := relationBasis_map_injective a b c ha hb hc
  refine ⟨jt.1, jt.2, α, β, v, hrep, hcop, hdet, rfl, ?_, ?_, ?_⟩
  · exact relationCombo_mem a b c U V
      (relationU0_mem_lattice a b c hc)
      (relationV0_mem_lattice a b c hc) α β
  · intro w hw
    obtain ⟨kl, hkl, _⟩ := relationLattice_basis_existsUnique a b c ha hb hc w hw
    rw [hrep]
    exact relationCombo_change_existsUnique U V hinj jt.1 jt.2 α β hdet
      w kl.1 kl.2 hkl
  · rw [hrep]
    exact relationCross_change_basis U V jt.1 jt.2 α β hdet

/-- 论文 `lem:latticebasis`：正整数速度三元组的关系格存在最短整数基，
新基的叉积保持为原显式基的叉积。 -/
theorem relationLattice_exists_shortest_basis (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ∃ u v : Fin 3 → ℤ,
      u ∈ relationLattice a b c ∧ u ≠ 0 ∧
      (∀ w : Fin 3 → ℤ, w ∈ relationLattice a b c → w ≠ 0 →
        ‖relationToEuclidean u‖ ≤ ‖relationToEuclidean w‖) ∧
      v ∈ relationLattice a b c ∧
      (∀ w : Fin 3 → ℤ, w ∈ relationLattice a b c →
        ∃! pq : ℤ × ℤ, w = relationCombo u v pq.1 pq.2) ∧
      relationCross u v =
        relationCross (relationBasisFirst a b c) (relationBasisSecond a b c) := by
  obtain ⟨u, hu, hune, hshort⟩ := relationLattice_exists_shortest a b c hb
  obtain ⟨j, t, α, β, v, _, _, _, _, hv, hrepr, hcross⟩ :=
    relationLattice_shortest_extends_basis a b c ha hb hc u hu hune hshort
  exact ⟨u, v, hu, hune, hshort, hv, hrepr, hcross⟩

#print axioms LonelyRunner.relationToEuclidean_norm_sq
#print axioms LonelyRunner.relationToEuclidean_norm_sq_nat
#print axioms LonelyRunner.relationLattice_exists_nonzero
#print axioms LonelyRunner.relationLattice_exists_shortest
#print axioms LonelyRunner.relationLattice_shortest_coords_coprime
#print axioms LonelyRunner.relationLattice_shortest_repr
#print axioms LonelyRunner.relationCoords_bezout
#print axioms LonelyRunner.relationCombo_change_existsUnique
#print axioms LonelyRunner.relationCross_change_basis
#print axioms LonelyRunner.relationLattice_shortest_extends_basis
#print axioms LonelyRunner.relationLattice_exists_shortest_basis

end LonelyRunner
