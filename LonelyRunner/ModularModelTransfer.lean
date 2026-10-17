import LonelyRunner.TwoDissociatedDimension
import LonelyRunner.CircleMeasure
import Mathlib.Analysis.Normed.Group.Int

/-!
# 模群代表的模型转移

对应论文 `prop:bedert` 建模输入的转移步骤。素数、缩放、代表及数值界
均为明确参数；这里不承担这些参数的构造。
-/

namespace LonelyRunner
open Finset

/-- 实际自然数模型速度集，使用整数代表的自然数绝对值。 -/
def modularModelSpeeds (V : Finset ℕ) (z : ℕ → ℤ) : Finset ℕ := V.image (fun v => (z v).natAbs)

/-- 正速度的非零模像不能有零整数代表。 -/
theorem modularModel_representative_ne_zero (V : Finset ℕ) (M p : ℕ)
    (hp : p.Prime) (hlarge : 2 * M < p) (lam : ZMod p) (hlam : lam ≠ 0)
    (z : ℕ → ℤ) (hV : ∀ v ∈ V, 0 < v ∧ v ≤ M)
    (hz : ∀ v ∈ V, (z v : ZMod p) = lam * (v : ZMod p)) :
    ∀ v ∈ V, z v ≠ 0 := by
  have : Fact p.Prime := ⟨hp⟩
  intro v hv hzero
  have hvlt : v < p := by have := (hV v hv).2; omega
  have hmod : (v : ZMod p) = 0 := by
    have h := hz v hv
    rw [hzero, Int.cast_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hlam
  have hval := congrArg ZMod.val hmod
  have hvzero : v = 0 := by simpa [ZMod.val_natCast_of_lt hvlt] using hval
  have := (hV v hv).1
  omega

/-- 绝对值单射：同号时取消非零缩放；异号时 `a+b<p` 排除模相反。
没有把绝对值映射单射作为额外假设。 -/
theorem modularModel_natAbs_injOn (V : Finset ℕ) (M p : ℕ)
    (hp : p.Prime) (hlarge : 2 * M < p) (lam : ZMod p) (hlam : lam ≠ 0)
    (z : ℕ → ℤ) (hV : ∀ v ∈ V, 0 < v ∧ v ≤ M)
    (hz : ∀ v ∈ V, (z v : ZMod p) = lam * (v : ZMod p)) :
    Set.InjOn (fun v => (z v).natAbs) V := by
  have : Fact p.Prime := ⟨hp⟩
  intro a ha b hb hab
  rcases Int.natAbs_eq_natAbs_iff.mp hab with heq | heq
  · have hmod : (a : ZMod p) = (b : ZMod p) := by
      apply mul_left_cancel₀ hlam
      rw [← hz a ha, ← hz b hb, heq]
    have halt : a < p := by have := (hV a ha).2; omega
    have hblt : b < p := by have := (hV b hb).2; omega
    simpa [ZMod.val_natCast_of_lt halt, ZMod.val_natCast_of_lt hblt] using
      congrArg ZMod.val hmod
  · have hablt : a + b < p := by
      have := (hV a ha).2
      have := (hV b hb).2
      omega
    have hmul : lam * ((a + b : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_add, mul_add, ← hz a ha, ← hz b hb, heq, Int.cast_neg]
      simp
    have hmod := (mul_eq_zero.mp hmul).resolve_left hlam
    have habzero : a + b = 0 := by
      simpa only [ZMod.val_natCast_of_lt hablt, ZMod.val_zero] using congrArg ZMod.val hmod
    have := (hV a ha).1
    omega

/-- 模型保留速度数，且每个速度实际属于自然数区间 `[1,Q]`。 -/
theorem modularModel_card_bounds (V : Finset ℕ) (M p Q : ℕ)
    (hp : p.Prime) (hlarge : 2 * M < p) (lam : ZMod p) (hlam : lam ≠ 0)
    (z : ℕ → ℤ) (hV : ∀ v ∈ V, 0 < v ∧ v ≤ M)
    (hz : ∀ v ∈ V, (z v : ZMod p) = lam * (v : ZMod p))
    (hQ : ∀ v ∈ V, |z v| ≤ (Q : ℤ)) :
    (modularModelSpeeds V z).card = V.card ∧
      ∀ w ∈ modularModelSpeeds V z, 1 ≤ w ∧ w ≤ Q := by
  classical
  refine ⟨card_image_iff.mpr (modularModel_natAbs_injOn V M p hp hlarge lam hlam z hV hz), ?_⟩
  intro w hw
  obtain ⟨v, hv, rfl⟩ := mem_image.mp hw
  have hn := modularModel_representative_ne_zero V M p hp hlarge lam hlam z hV hz v hv
  constructor
  · have hpos : 0 < (z v).natAbs := Int.natAbs_pos.mpr hn
    omega
  · have hh : ((z v).natAbs : ℤ) ≤ (Q : ℤ) := by
      simpa only [Int.natCast_natAbs] using hQ v hv
    exact_mod_cast hh

/-- 模 `p` 为零的有界整数关系，在严格绝对值界小于 `p` 时确实为零。 -/
theorem modularModel_relation_lift (V : Finset ℕ) (p Q : ℕ)
    (z : ℕ → ℤ) (lam : ZMod p)
    (hz : ∀ v ∈ V, (z v : ZMod p) = lam * (v : ZMod p))
    (hQ : ∀ v ∈ V, |z v| ≤ (Q : ℤ)) (hsmall : 2 * V.card * Q < p)
    (c : ℕ → ℤ) (hc : ∀ v ∈ V, c v ∈ Set.Icc (-2 : ℤ) 2)
    (hs : ∑ v ∈ V, c v * (v : ℤ) = 0) : ∑ v ∈ V, c v * z v = 0 := by
  let s : ℤ := ∑ v ∈ V, c v * z v
  have hmod : (s : ZMod p) = 0 := by
    have hsz : (∑ v ∈ V, (c v : ZMod p) * (v : ZMod p)) = 0 := by
      have h := congrArg (fun t : ℤ => (t : ZMod p)) hs
      simpa only [Int.cast_sum, Int.cast_mul, Int.cast_natCast, Int.cast_zero] using h
    calc
      _ = ∑ v ∈ V, (c v : ZMod p) * (lam * (v : ZMod p)) := by
        simp only [s, Int.cast_sum, Int.cast_mul]
        apply sum_congr rfl
        intro v hv
        rw [hz v hv]
      _ = lam * (∑ v ∈ V, (c v : ZMod p) * (v : ZMod p)) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro v hv
        ring
      _ = 0 := by rw [hsz, mul_zero]
  have habs : |s| ≤ (2 * V.card * Q : ℕ) := by
    calc
      _ ≤ ∑ v ∈ V, |c v * z v| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _v ∈ V, (2 : ℤ) * Q := by
        apply sum_le_sum
        intro v hv
        rw [abs_mul]
        exact mul_le_mul (abs_le.mpr (hc v hv)) (hQ v hv) (abs_nonneg _) (by norm_num)
      _ = _ := by simp; ring
  have hd : (p : ℤ) ∣ s := (ZMod.intCast_zmod_eq_zero_iff_dvd s p).mp hmod
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd
  have hnat : s.natAbs ≤ 2 * V.card * Q := by
    have hh : (s.natAbs : ℤ) ≤ ((2 * V.card * Q : ℕ) : ℤ) := by
      simpa only [Int.natCast_natAbs] using habs
    exact_mod_cast hh
  simpa using hnat.trans_lt hsmall

/-- 对单射像上的二解离性，可直接输入原指标上的系数关系。
像上的系数由有限单点求和实际构造，不假设系数可传递。 -/
theorem TwoDissociated.image_relation {A I : Type*} [AddCommGroup A] [DecidableEq A]
    (S : Finset I) (f : I → A) (hinj : Set.InjOn f S)
    (hD : TwoDissociated (S.image f)) (c : I → ℤ)
    (hc : ∀ i ∈ S, c i ∈ Set.Icc (-2 : ℤ) 2)
    (hs : ∑ i ∈ S, c i • f i = 0) : ∀ i ∈ S, c i = 0 := by
  classical
  let d : A → ℤ := fun x => ∑ i ∈ S, if f i = x then c i else 0
  have hd (i : I) (hi : i ∈ S) : d (f i) = c i := by
    dsimp [d]
    rw [sum_eq_single i]
    · simp
    · intro j hj hji
      have hne : f j ≠ f i := fun h => hji (hinj hj hi h)
      simp [hne]
    · exact fun hn => (hn hi).elim
  have hdb : ∀ x ∈ S.image f, d x ∈ Set.Icc (-2 : ℤ) 2 := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    rw [hd i hi]
    exact hc i hi
  have hds : ∑ x ∈ S.image f, d x • x = 0 := by
    rw [sum_image (fun i hi j hj he => hinj hi hj he)]
    calc
      _ = ∑ i ∈ S, c i • f i := sum_congr rfl (fun i hi => by rw [hd i hi])
      _ = 0 := hs
  intro i hi
  rw [← hd i hi]
  exact hD d hdb hds (f i) (mem_image.mpr ⟨i, hi, rfl⟩)

/-- 符号变换及短关系提升使模型的二解离子集拉回为原速度的二解离子集。 -/
theorem modularModel_pullback_dissociated (V S : Finset ℕ) (p Q : ℕ)
    (lam : ZMod p) (z : ℕ → ℤ) (hSV : S ⊆ V)
    (hz : ∀ v ∈ V, (z v : ZMod p) = lam * (v : ZMod p))
    (hQ : ∀ v ∈ V, |z v| ≤ (Q : ℤ)) (hsmall : 2 * V.card * Q < p)
    (hinj : Set.InjOn (fun v => (z v).natAbs) V)
    (hD : TwoDissociated (S.image (fun v => ((z v).natAbs : ℤ)))) :
    TwoDissociated (S.image (fun v : ℕ => (v : ℤ))) := by
  classical
  intro c hc hs x hx
  obtain ⟨v, hv, rfl⟩ := mem_image.mp hx
  let e : ℕ → ℤ := fun u => if 0 ≤ z u then 1 else -1
  have he (u : ℕ) : e u * ((z u).natAbs : ℤ) = z u := by
    dsimp [e]
    by_cases h : 0 ≤ z u
    · simp [h, abs_of_nonneg h]
    · simp [h, abs_of_neg (lt_of_not_ge h)]
  have hsN : ∑ u ∈ S, c (u : ℤ) * (u : ℤ) = 0 := by
    rw [sum_image] at hs
    · simpa [zsmul_eq_mul] using hs
    · intro a ha b hb heq
      exact Nat.cast_injective heq
  have hcN : ∀ u ∈ S, c (u : ℤ) ∈ Set.Icc (-2 : ℤ) 2 :=
    fun u hu => hc (u : ℤ) (mem_image.mpr ⟨u, hu, rfl⟩)
  have hsmallS : 2 * S.card * Q < p := by
    calc
      _ ≤ 2 * V.card * Q := by gcongr
      _ < p := hsmall
  have hlift := modularModel_relation_lift S p Q z lam
    (fun u hu => hz u (hSV hu)) (fun u hu => hQ u (hSV hu)) hsmallS
    (fun u => c (u : ℤ)) hcN hsN
  have hcE : ∀ u ∈ S, c (u : ℤ) * e u ∈ Set.Icc (-2 : ℤ) 2 := by
    intro u hu
    obtain ⟨hlo, hhi⟩ := hcN u hu
    dsimp [e]
    split_ifs <;> simp only [mul_one, mul_neg_one, Set.mem_Icc] <;> constructor <;> omega
  have hrel : ∑ u ∈ S, (c (u : ℤ) * e u) • ((z u).natAbs : ℤ) = 0 := by
    calc
      _ = ∑ u ∈ S, c (u : ℤ) * z u := by
        apply sum_congr rfl
        intro u hu
        simp only [zsmul_eq_mul, Int.cast_id, mul_assoc, he]
      _ = 0 := hlift
  have hf : Set.InjOn (fun u => ((z u).natAbs : ℤ)) S := by
    intro a ha b hb heq
    exact hinj (hSV ha) (hSV hb) (Nat.cast_injective heq)
  have hzero := hD.image_relation S (fun u => ((z u).natAbs : ℤ)) hf
    (fun u => c (u : ℤ) * e u) hcE hrel v hv
  by_cases h : 0 ≤ z v <;> simpa [e, h] using hzero

/-- 整数嵌入后的最大二解离维数不增。最大模型子集实际拉回到原速度集。 -/
theorem modularModel_dimension_le (V : Finset ℕ) (M p Q : ℕ)
    (hp : p.Prime) (hlarge : 2 * M < p) (lam : ZMod p) (hlam : lam ≠ 0)
    (z : ℕ → ℤ) (hV : ∀ v ∈ V, 0 < v ∧ v ≤ M)
    (hz : ∀ v ∈ V, (z v : ZMod p) = lam * (v : ZMod p))
    (hQ : ∀ v ∈ V, |z v| ≤ (Q : ℤ)) (hsmall : 2 * V.card * Q < p) :
    twoDissociatedDimension ((modularModelSpeeds V z).image (fun w : ℕ => (w : ℤ))) ≤
      twoDissociatedDimension (V.image (fun v : ℕ => (v : ℤ))) := by
  classical
  obtain ⟨D, hDW, hD, hcard⟩ := twoDissociatedDimension_attained
    ((modularModelSpeeds V z).image (fun w : ℕ => (w : ℤ)))
  let S := V.filter (fun v => ((z v).natAbs : ℤ) ∈ D)
  have hSV : S ⊆ V := filter_subset _ _
  have himage : S.image (fun v => ((z v).natAbs : ℤ)) = D := by
    apply subset_antisymm
    · intro x hx
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hx
      exact (mem_filter.mp hv).2
    · intro x hx
      obtain ⟨w, hw, rfl⟩ := mem_image.mp (hDW hx)
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hw
      exact mem_image.mpr ⟨v, mem_filter.mpr ⟨hv, hx⟩, rfl⟩
  have hinj := modularModel_natAbs_injOn V M p hp hlarge lam hlam z hV hz
  have hf : Set.InjOn (fun v => ((z v).natAbs : ℤ)) S := by
    intro a ha b hb heq
    exact hinj (hSV ha) (hSV hb) (Nat.cast_injective heq)
  have hsource : TwoDissociated (S.image (fun v : ℕ => (v : ℤ))) :=
    modularModel_pullback_dissociated V S p Q lam z hSV hz hQ hsmall hinj
      (by rw [himage]; exact hD)
  rw [← hcard]
  calc
    D.card = (S.image (fun v => ((z v).natAbs : ℤ))).card := by rw [himage]
    _ = S.card := card_image_iff.mpr hf
    _ = (S.image (fun v : ℕ => (v : ℤ))).card :=
      (card_image_iff.mpr (fun a ha b hb heq => Nat.cast_injective heq)).symm
    _ ≤ twoDissociatedDimension (V.image (fun v : ℕ => (v : ℤ))) :=
      card_le_twoDissociatedDimension (image_subset_image hSV) hsource

/-- 模同余在实际 `j/p` 网格上给出距离恒等式，包括代表的负号。
原速度在 `lam*j/p` 处的距离等于模型速度在 `j/p` 处的距离。 -/
theorem modularModel_grid_distance (p : ℕ) [NeZero p] (hp : 0 < p) (lam : ZMod p)
    (v : ℕ) (z : ℤ) (hz : (z : ZMod p) = lam * (v : ZMod p)) (j : ZMod p) :
    dist (z.natAbs • ZMod.toAddCircle j) 0 =
      dist (v • ZMod.toAddCircle (lam * j)) 0 := by
  have : NeZero p := ⟨hp.ne'⟩
  have hleft : z • ZMod.toAddCircle j = ZMod.toAddCircle ((z : ZMod p) * j) := by
    rw [← map_zsmul, zsmul_eq_mul]
  have hright : v • ZMod.toAddCircle (lam * j) =
      ZMod.toAddCircle ((v : ZMod p) * (lam * j)) := by
    rw [← map_nsmul, nsmul_eq_mul]
  rw [dist_zero_right, norm_natAbs_smul, hleft, hz, hright, dist_zero_right]
  congr 2
  ring

/-- 任意圆周点距某个 `j/p` 网格点至多 `1/p`。
实际提升到实轴并取 `floor(p*s)`，再用商群投影不增范数。 -/
theorem modularModel_grid_approx (p : ℕ) [NeZero p] (hp : 0 < p) (t : UnitAddCircle) :
    ∃ j : ZMod p, dist t (ZMod.toAddCircle j) ≤ 1 / (p : ℝ) := by
  have : NeZero p := ⟨hp.ne'⟩
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  induction t using Quotient.inductionOn with
  | _ s =>
    let j : ℤ := ⌊(p : ℝ) * s⌋
    have hjlo : (j : ℝ) ≤ (p : ℝ) * s := Int.floor_le _
    have hjhi : (p : ℝ) * s < (j : ℝ) + 1 := Int.lt_floor_add_one _
    have hdiff0 : 0 ≤ s - (j : ℝ) / (p : ℝ) := by
      have hle : (j : ℝ) / (p : ℝ) ≤ s :=
        (div_le_iff₀ hpR).mpr (by nlinarith)
      linarith
    have hdiff1 : s - (j : ℝ) / (p : ℝ) ≤ 1 / (p : ℝ) := by
      apply (le_div_iff₀ hpR).mpr
      have hjcancel := div_mul_cancel₀ (j : ℝ) hpR.ne'
      nlinarith
    refine ⟨(j : ZMod p), ?_⟩
    rw [ZMod.toAddCircle_intCast, dist_eq_norm, ← AddCircle.coe_sub]
    calc
      _ ≤ |s - (j : ℝ) / (p : ℝ)| :=
        (show ‖((s - (j : ℝ) / (p : ℝ) : ℝ) : UnitAddCircle)‖ ≤
          ‖s - (j : ℝ) / (p : ℝ)‖ from QuotientAddGroup.norm_mk_le_norm)
      _ ≤ 1 / (p : ℝ) := by rw [abs_of_nonneg hdiff0]; exact hdiff1

/-- 逐点距离覆盖的转移：先在网格上由模同余转移，再逼近任意圆周点。
此距离形式无需对 `δ` 增加范围条件。 -/
theorem modularModel_distance_cover (V : Finset ℕ) (p Q : ℕ) (hp : 0 < p)
    (lam : ZMod p) (z : ℕ → ℤ)
    (hz : ∀ v ∈ V, (z v : ZMod p) = lam * (v : ZMod p))
    (hQ : ∀ v ∈ V, |z v| ≤ (Q : ℤ)) (δ : ℝ)
    (hcover : ∀ t : UnitAddCircle, ∃ v ∈ V, dist (v • t) 0 ≤ δ) :
    ∀ t : UnitAddCircle, ∃ w ∈ modularModelSpeeds V z,
      dist (w • t) 0 ≤ δ + (Q : ℝ) / (p : ℝ) := by
  have : NeZero p := ⟨hp.ne'⟩
  intro t
  obtain ⟨j, hj⟩ := modularModel_grid_approx p hp t
  obtain ⟨v, hv, hdist⟩ := hcover (ZMod.toAddCircle (lam * j))
  have hgrid : dist ((z v).natAbs • ZMod.toAddCircle j) 0 ≤ δ := by
    rw [modularModel_grid_distance p hp lam v (z v) (hz v hv) j]
    exact hdist
  have hwQ : ((z v).natAbs : ℝ) ≤ (Q : ℝ) := by
    have hi : ((z v).natAbs : ℤ) ≤ (Q : ℤ) := by
      simpa only [Int.natCast_natAbs] using hQ v hv
    exact_mod_cast hi
  have hmove : dist ((z v).natAbs • t)
      ((z v).natAbs • ZMod.toAddCircle j) ≤ (Q : ℝ) / (p : ℝ) := by
    calc
      _ = ‖(z v).natAbs • (t - ZMod.toAddCircle j)‖ := by
        rw [dist_eq_norm, smul_sub]
      _ ≤ ((z v).natAbs : ℝ) * ‖t - ZMod.toAddCircle j‖ := norm_nsmul_le
      _ ≤ (Q : ℝ) * (1 / (p : ℝ)) := by
        apply mul_le_mul hwQ
        · simpa only [dist_eq_norm] using hj
        · exact norm_nonneg _
        · positivity
      _ = _ := by ring
  refine ⟨(z v).natAbs, mem_image.mpr ⟨v, hv, rfl⟩, ?_⟩
  have htriangle := dist_triangle ((z v).natAbs • t)
    ((z v).natAbs • ZMod.toAddCircle j) 0
  linarith

/-- 在闭弧与闭球等价的范围内接入项目原有 `Covers`，不改动 Bohr 集定义。 -/
theorem modularModel_covers (V : Finset ℕ) (p Q : ℕ) (hp : 0 < p)
    (lam : ZMod p) (z : ℕ → ℤ)
    (hz : ∀ v ∈ V, (z v : ZMod p) = lam * (v : ZMod p))
    (hQ : ∀ v ∈ V, |z v| ≤ (Q : ℤ)) (δ : ℝ)
    (hδ : 0 ≤ δ) (hδhalf : δ < 1 / 2)
    (hnewhalf : δ + (Q : ℝ) / (p : ℝ) < 1 / 2) (hcover : Covers V δ) :
    Covers (modularModelSpeeds V z) (δ + (Q : ℝ) / (p : ℝ)) := by
  have hdist : ∀ t : UnitAddCircle, ∃ v ∈ V, dist (v • t) 0 ≤ δ := by
    intro t
    obtain ⟨v, hv, hvt⟩ := hcover t
    exact ⟨v, hv, (mem_bohrSet_iff_dist v δ hδ hδhalf t).mp hvt⟩
  intro t
  obtain ⟨w, hw, hwt⟩ := modularModel_distance_cover V p Q hp lam z hz hQ δ hdist t
  refine ⟨w, hw, (mem_bohrSet_iff_dist w _ (by positivity) hnewhalf t).mpr hwt⟩

/-- 完整转移接口：保留素数、代表及数值条件为明确参数，同时给出速度数、
正性、高度、二解离维数及逐点距离覆盖的全部结论。 -/
theorem modularModel_transfer (V : Finset ℕ) (M p Q : ℕ)
    (hp : p.Prime) (hlarge : 2 * M < p) (lam : ZMod p) (hlam : lam ≠ 0)
    (z : ℕ → ℤ) (hV : ∀ v ∈ V, 0 < v ∧ v ≤ M)
    (hz : ∀ v ∈ V, (z v : ZMod p) = lam * (v : ZMod p))
    (hQ : ∀ v ∈ V, |z v| ≤ (Q : ℤ)) (hsmall : 2 * V.card * Q < p)
    (δ : ℝ) (hcover : ∀ t : UnitAddCircle, ∃ v ∈ V, dist (v • t) 0 ≤ δ) :
    let W := modularModelSpeeds V z
    W.card = V.card ∧ (∀ w ∈ W, 1 ≤ w ∧ w ≤ Q) ∧
      twoDissociatedDimension (W.image (fun w : ℕ => (w : ℤ))) ≤
        twoDissociatedDimension (V.image (fun v : ℕ => (v : ℤ))) ∧
      ∀ t : UnitAddCircle, ∃ w ∈ W,
        dist (w • t) 0 ≤ δ + (Q : ℝ) / (p : ℝ) := by
  obtain ⟨hcard, hbounds⟩ := modularModel_card_bounds V M p Q hp hlarge lam hlam z hV hz hQ
  exact ⟨hcard, hbounds, modularModel_dimension_le V M p Q hp hlarge lam hlam z hV hz hQ hsmall,
    modularModel_distance_cover V p Q hp.pos lam z hz hQ δ hcover⟩

#print axioms modularModel_card_bounds
#print axioms modularModel_relation_lift
#print axioms modularModel_dimension_le
#print axioms modularModel_grid_distance
#print axioms modularModel_grid_approx
#print axioms modularModel_distance_cover
#print axioms modularModel_covers
#print axioms modularModel_transfer

end LonelyRunner
