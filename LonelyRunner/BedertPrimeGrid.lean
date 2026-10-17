import LonelyRunner.PrimeGridCover
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Order.Interval.Finset.Nat

/-!
# Bedert 第 5 节的素数网格

引理 5.3 的严格坏点计数与推论 5.4 的好余数衔接。
只使用有限余类计数，不使用素数分布或小高度定理。
-/

namespace LonelyRunner

/-- Bedert 引理 5.3 的整数网格阈值；除法在实数中进行，再取自然数 ceiling。 -/
noncomputable def bedertGridOrder (p m : ℕ) : ℕ :=
  ⌈((p : ℝ) - 1) / (2 * (m : ℝ))⌉₊

/-- 正速度数及 `p≥2` 时 ceiling 为正，且总坏点预算严格小于非零网格的大小。 -/
theorem bedertGridOrder_budget (p m : ℕ) (hp : 2 ≤ p) (hm : 0 < m) :
    0 < bedertGridOrder p m ∧ 2 * m * (bedertGridOrder p m - 1) < p - 1 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hk : 0 < bedertGridOrder p m := Nat.ceil_pos.mpr (by
    apply div_pos <;> linarith)
  have h := (Nat.ceil_eq_iff hk.ne').mp (show
    ⌈((p : ℝ) - 1) / (2 * (m : ℝ))⌉₊ = bedertGridOrder p m from rfl)
  have hmul := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * (m : ℝ))).mp h.1
  have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ p)]; norm_num
  have hreal : ((2 * m * (bedertGridOrder p m - 1) : ℕ) : ℝ) < ((p - 1 : ℕ) : ℝ) := by
    rw [hcast]
    push_cast
    nlinarith [hmul]
  exact ⟨hk, by exact_mod_cast hreal⟩

/-- Bedert 引理 5.3：规范余类的圆周距离是两个端点距离的最小值除以 `p`。 -/
theorem bedertGrid_distance (p : ℕ) [NeZero p] (a : ZMod p) :
    dist (ZMod.toAddCircle a) (0 : UnitAddCircle) =
      ((min a.val (p - a.val) : ℕ) : ℝ) / (p : ℝ) := by
  rw [dist_zero_right, ZMod.toAddCircle_apply]
  haveI : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  simpa [Nat.mod_eq_of_lt (ZMod.val_lt a)] using
    (AddCircle.norm_div_natCast (p := (1 : ℝ)) (m := a.val) (n := p))

/-- 非零余类的严格坏集合；阈值端点不计入坏点。 -/
noncomputable def bedertBadResidues (p v k : ℕ) [NeZero p] : Finset (ZMod p) := by
  classical
  exact (Finset.univ.erase 0).filter (fun a =>
    dist (v • ZMod.toAddCircle a) (0 : UnitAddCircle) < (k : ℝ) / (p : ℝ))

/-- 速度一的坏余类实际包含于 `1,…,k−1` 及其负数的并。 -/
theorem bedertBadResidues_one_subset (p k : ℕ) [NeZero p] :
    bedertBadResidues p 1 k ⊆
      ((Finset.Ico 1 k).image (fun j : ℕ => (j : ZMod p))) ∪
        ((Finset.Ico 1 k).image (fun j : ℕ => -(j : ZMod p))) := by
  classical
  intro a ha
  obtain ⟨haNonzero, hdist⟩ := Finset.mem_filter.mp ha
  have ha0 : a ≠ 0 := (Finset.mem_erase.mp haNonzero).1
  have haval : 0 < a.val := Nat.pos_of_ne_zero (fun h => ha0 ((ZMod.val_eq_zero a).mp h))
  have hpR : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  simp only [one_smul] at hdist
  rw [bedertGrid_distance] at hdist
  have hmin : min a.val (p - a.val) < k := by
    exact_mod_cast (div_lt_div_iff_of_pos_right hpR).mp hdist
  rcases (min_lt_iff.mp hmin) with hleft | hright
  · exact Finset.mem_union_left _ (Finset.mem_image.mpr
      ⟨a.val, Finset.mem_Ico.mpr ⟨haval, hleft⟩, ZMod.natCast_zmod_val a⟩)
  · have hjpos : 1 ≤ p - a.val := by have := ZMod.val_lt a; omega
    have heq : -((p - a.val : ℕ) : ZMod p) = a := by
      rw [Nat.cast_sub (Nat.le_of_lt (ZMod.val_lt a)), ZMod.natCast_zmod_val]
      simp
    exact Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨p - a.val, Finset.mem_Ico.mpr ⟨hjpos, hright⟩, heq⟩)

/-- Bedert 引理 5.3 的精确严格计数：非零坏余类至多 `2(k−1)` 个。 -/
theorem bedertBadResidues_one_card (p k : ℕ) [NeZero p] :
    (bedertBadResidues p 1 k).card ≤ 2 * (k - 1) := by
  classical
  calc
    _ ≤ (((Finset.Ico 1 k).image (fun j : ℕ => (j : ZMod p))) ∪
        ((Finset.Ico 1 k).image (fun j : ℕ => -(j : ZMod p)))).card :=
      Finset.card_le_card (bedertBadResidues_one_subset p k)
    _ ≤ ((Finset.Ico 1 k).image (fun j : ℕ => (j : ZMod p))).card +
        ((Finset.Ico 1 k).image (fun j : ℕ => -(j : ZMod p))).card := Finset.card_union_le _ _
    _ ≤ (Finset.Ico 1 k).card + (Finset.Ico 1 k).card :=
      Nat.add_le_add Finset.card_image_le Finset.card_image_le
    _ = 2 * (k - 1) := by simp; omega

/-- Bedert 引理 5.3：模乘置换非零余类，并把速度 `v` 的严格坏集合
双射到速度一的严格坏集合。 -/
theorem bedertBadResidues_card_eq (p v k : ℕ) [NeZero p]
    (hp : p.Prime) (hnp : ¬ p ∣ v) :
    (bedertBadResidues p v k).card = (bedertBadResidues p 1 k).card := by
  classical
  obtain ⟨hinj, hsurj⟩ := nondivisible_grid_permutation p v hp hnp
  have hzero : ∀ a : ZMod p, (v : ZMod p) * a = 0 ↔ a = 0 := by
    intro a
    constructor
    · intro h
      exact hinj (by simpa using h)
    · rintro rfl
      simp
  have hpoint (a : ZMod p) :
      v • ZMod.toAddCircle a = ZMod.toAddCircle ((v : ZMod p) * a) := by
    rw [← map_nsmul, nsmul_eq_mul]
  refine Finset.card_bij (fun a _ => (v : ZMod p) * a) ?_ ?_ ?_
  · intro a ha
    obtain ⟨hane, hadist⟩ := Finset.mem_filter.mp ha
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩, ?_⟩
    · exact fun h => (Finset.mem_erase.mp hane).1 ((hzero a).mp h)
    · simpa only [one_smul, hpoint] using hadist
  · intro a ha b hb hab
    exact hinj hab
  · intro b hb
    obtain ⟨a, rfl⟩ := hsurj b
    obtain ⟨hbne, hbdist⟩ := Finset.mem_filter.mp hb
    refine ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩, ?_⟩, rfl⟩
    · intro ha0
      apply (Finset.mem_erase.mp hbne).1
      simp [ha0]
    · simpa only [one_smul, hpoint] using hbdist

/-- 对实际坏集合取有限并，由严格预算得到非零好余类。没有使用粗网格误差界。 -/
theorem bedert_prime_grid_of_budget (V : Finset ℕ) (p k : ℕ)
    (hp : p.Prime) (hnp : ∀ v ∈ V, ¬ p ∣ v)
    (hbudget : 2 * V.card * (k - 1) < p - 1) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    ∃ a : ZMod p, a ≠ 0 ∧ ∀ v ∈ V,
      (k : ℝ) / (p : ℝ) ≤ dist (v • ZMod.toAddCircle a) (0 : UnitAddCircle) := by
  classical
  letI : NeZero p := ⟨hp.ne_zero⟩
  let S : Finset (ZMod p) := Finset.univ.erase 0
  let B := V.biUnion (fun v => bedertBadResidues p v k)
  have hS : S.card = p - 1 := by simp [S, ZMod.card]
  have hB : B.card ≤ 2 * V.card * (k - 1) := by
    calc
      B.card ≤ ∑ v ∈ V, (bedertBadResidues p v k).card := Finset.card_biUnion_le
      _ ≤ ∑ _v ∈ V, 2 * (k - 1) := by
        apply Finset.sum_le_sum
        intro v hv
        rw [bedertBadResidues_card_eq p v k hp (hnp v hv)]
        exact bedertBadResidues_one_card p k
      _ = 2 * V.card * (k - 1) := by simp; ring
  have hnot : ¬ S ⊆ B := by
    intro hsub
    have hle := Finset.card_le_card hsub
    rw [hS] at hle
    omega
  obtain ⟨a, haS, haB⟩ := Finset.not_subset.mp hnot
  refine ⟨a, (Finset.mem_erase.mp haS).1, ?_⟩
  intro v hv
  by_contra hbad
  apply haB
  exact Finset.mem_biUnion.mpr ⟨v, hv,
    Finset.mem_filter.mpr ⟨haS, lt_of_not_ge hbad⟩⟩

/-- Bedert 第 5 节引理 5.3：非零素数网格上实际取得同时远离零的时刻。
自然数 `a` 满足 `1≤a<p`，时刻就是圆周中的实数代表 `a/p`。 -/
theorem bedert_prime_grid_lower (V : Finset ℕ) (p : ℕ)
    (hV : V.Nonempty) (_hVpos : ∀ v ∈ V, 0 < v)
    (hp : p.Prime) (hnp : ∀ v ∈ V, ¬ p ∣ v) :
    ∃ a : ℕ, 1 ≤ a ∧ a < p ∧ ∀ v ∈ V,
      (bedertGridOrder p V.card : ℝ) / (p : ℝ) ≤
        dist (v • ((((a : ℝ) / (p : ℝ)) : ℝ) : UnitAddCircle)) 0 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hm : 0 < V.card := Finset.card_pos.mpr hV
  obtain ⟨hk, hbudget⟩ := bedertGridOrder_budget p V.card hp.two_le hm
  obtain ⟨a, ha0, hgood⟩ := bedert_prime_grid_of_budget V p
    (bedertGridOrder p V.card) hp hnp hbudget
  have haval : 1 ≤ a.val := by
    have hval : a.val ≠ 0 := fun h => ha0 ((ZMod.val_eq_zero a).mp h)
    omega
  refine ⟨a.val, haval, ZMod.val_lt a, ?_⟩
  intro v hv
  simpa only [ZMod.toAddCircle_apply] using hgood v hv

/-- 边界 `p=2`：对任意非空速度数，ceiling 阈值恰为一。 -/
theorem bedertGridOrder_two (m : ℕ) (hm : 0 < m) : bedertGridOrder 2 m = 1 := by
  apply (Nat.ceil_eq_iff (by decide : (1 : ℕ) ≠ 0)).2
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hpos : (0 : ℝ) < ((2 : ℝ) - 1) / (2 * (m : ℝ)) := by positivity
  have hle : ((2 : ℝ) - 1) / (2 * (m : ℝ)) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (m : ℝ))).2
    linarith
  simpa only [Nat.sub_self, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using And.intro hpos hle

/-- 边界 `p=2` 的时刻可直接取 `1/2`；严格坏集合在阈值端点为空。 -/
theorem bedert_prime_grid_two (V : Finset ℕ) (hV : V.Nonempty)
    (hVpos : ∀ v ∈ V, 0 < v) (hnp : ∀ v ∈ V, ¬ 2 ∣ v) :
    ∀ v ∈ V, (1 / 2 : ℝ) ≤
      dist (v • (((1 / 2 : ℝ)) : UnitAddCircle)) 0 := by
  obtain ⟨a, ha1, ha2, hgood⟩ := bedert_prime_grid_lower V 2 hV hVpos Nat.prime_two hnp
  have ha : a = 1 := by omega
  simpa [ha, bedertGridOrder_two V.card (Finset.card_pos.mpr hV)] using hgood

/-- 边界 `m=1`：单速度族不需要额外的速度高度或互素假设。 -/
theorem bedert_prime_grid_singleton (v p : ℕ) (hv : 0 < v)
    (hp : p.Prime) (hnp : ¬ p ∣ v) :
    ∃ a : ℕ, 1 ≤ a ∧ a < p ∧
      (bedertGridOrder p 1 : ℝ) / (p : ℝ) ≤
        dist (v • ((((a : ℝ) / (p : ℝ)) : ℝ) : UnitAddCircle)) 0 := by
  obtain ⟨a, ha1, hap, hgood⟩ := bedert_prime_grid_lower {v} p
    (by simp) (by simpa using hv) hp (by simpa using hnp)
  exact ⟨a, ha1, hap, by simpa using hgood v (by simp)⟩

/-- Bedert 推论 5.4 的 ceiling–余数恒等式：若 `r=p mod 2m≥2`，
则 `ceil((p−1)/(2m))=floor(p/(2m))+1`。 -/
theorem bedertGridOrder_of_good_remainder (p m : ℕ) (hm : 0 < m)
    (hr : 2 ≤ p % (2 * m)) : bedertGridOrder p m = p / (2 * m) + 1 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hden : 0 < 2 * m := by omega
  have hrlt : p % (2 * m) < 2 * m := Nat.mod_lt _ hden
  have heq : p = (2 * m) * (p / (2 * m)) + p % (2 * m) :=
    (Nat.div_add_mod p (2 * m)).symm
  have heqR : (p : ℝ) = 2 * (m : ℝ) * (p / (2 * m) : ℕ) + (p % (2 * m) : ℕ) := by
    exact_mod_cast heq
  have hrR : (2 : ℝ) ≤ (p % (2 * m) : ℕ) := by exact_mod_cast hr
  have hrltR : ((p % (2 * m) : ℕ) : ℝ) < 2 * (m : ℝ) := by exact_mod_cast hrlt
  have hqne : p / (2 * m) + 1 ≠ 0 := Nat.succ_ne_zero _
  apply (Nat.ceil_eq_iff (n := p / (2 * m) + 1) hqne).2
  constructor
  · simp only [Nat.add_sub_cancel]
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * (m : ℝ))).2
    nlinarith [heqR]
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (m : ℝ))).2
    push_cast
    nlinarith [heqR]

/-- Bedert 推论 5.4 的数值衔接：好余数把网格阈值提高到 `1/(2m)+c/p`。 -/
theorem bedertGridOrder_good_remainder_bound (p m : ℕ) (c : ℝ)
    (hp : 0 < p) (hm : 0 < m) (_hc : 0 < c) (_hc1 : c < 1)
    (hr2 : 2 ≤ p % (2 * m))
    (hrc : ((p % (2 * m) : ℕ) : ℝ) ≤ (1 - c) * (2 * (m : ℝ))) :
    1 / (2 * (m : ℝ)) + c / (p : ℝ) ≤ (bedertGridOrder p m : ℝ) / (p : ℝ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hk := bedertGridOrder_of_good_remainder p m hm hr2
  have heq : p = (2 * m) * (p / (2 * m)) + p % (2 * m) :=
    (Nat.div_add_mod p (2 * m)).symm
  have heqR : (p : ℝ) = 2 * (m : ℝ) * (p / (2 * m) : ℕ) + (p % (2 * m) : ℕ) := by
    exact_mod_cast heq
  have hmain : (p : ℝ) + c * (2 * (m : ℝ)) ≤
      2 * (m : ℝ) * (bedertGridOrder p m : ℝ) := by
    rw [hk]
    push_cast
    nlinarith [hrc, heqR]
  apply (le_div_iff₀ hpR).2
  apply (mul_le_mul_iff_of_pos_right (by positivity : (0 : ℝ) < 2 * (m : ℝ))).mp
  have hid : (1 / (2 * (m : ℝ)) + c / (p : ℝ)) * (p : ℝ) * (2 * (m : ℝ)) =
      (p : ℝ) + c * (2 * (m : ℝ)) := by field_simp
  rw [hid]
  nlinarith [hmain]

/-- Bedert 第 5 节推论 5.4：好余数条件给出同时的 `1/(2m)+c/p` 下界。
时刻仍由非零素数网格实际构造，不引入素数分布假设。 -/
theorem bedert_prime_grid_good_remainder (V : Finset ℕ) (p : ℕ) (c : ℝ)
    (hV : V.Nonempty) (hVpos : ∀ v ∈ V, 0 < v)
    (hp : p.Prime) (hnp : ∀ v ∈ V, ¬ p ∣ v) (hc : 0 < c) (hc1 : c < 1)
    (hr2 : 2 ≤ p % (2 * V.card))
    (hrc : ((p % (2 * V.card) : ℕ) : ℝ) ≤ (1 - c) * (2 * (V.card : ℝ))) :
    ∃ t : UnitAddCircle, ∀ v ∈ V,
      1 / (2 * (V.card : ℝ)) + c / (p : ℝ) ≤ dist (v • t) 0 := by
  obtain ⟨a, ha1, hap, hgood⟩ := bedert_prime_grid_lower V p hV hVpos hp hnp
  have hbound := bedertGridOrder_good_remainder_bound p V.card c hp.pos
    (Finset.card_pos.mpr hV) hc hc1 hr2 hrc
  exact ⟨(((a : ℝ) / (p : ℝ)) : UnitAddCircle),
    fun v hv => hbound.trans (hgood v hv)⟩

#print axioms bedertBadResidues_one_card
#print axioms bedertBadResidues_card_eq
#print axioms bedert_prime_grid_lower
#print axioms bedert_prime_grid_two
#print axioms bedert_prime_grid_singleton
#print axioms bedert_prime_grid_good_remainder

end LonelyRunner
