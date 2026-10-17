import LonelyRunner.DivisorPowerBound
import LonelyRunner.GcdRatioCount
import Mathlib.Data.Int.Lemmas

/-!
# 有理截距的平方权重能量

对应论文 `paper/lonely_runner_zh.tex` 第 189–202 行 `eq:energy` 的前两步。
-/

namespace LonelyRunner

/-- 非零整数分子，严格满足 `0<|γ|≤H`。 -/
def interceptNumerators (H : ℕ) : Finset ℤ :=
  (Finset.Icc (-(H : ℤ)) (H : ℤ)).filter (fun γ => 0 < γ.natAbs)

/-- 正整数分母，满足 `1≤d≤D`。 -/
def interceptDenominators (D : ℕ) : Finset ℕ := Finset.Icc 1 D

theorem mem_interceptNumerators_iff (H : ℕ) (γ : ℤ) :
    γ ∈ interceptNumerators H ↔ 0 < γ.natAbs ∧ γ.natAbs ≤ H := by
  simp only [interceptNumerators, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, hpos⟩
    constructor
    · exact hpos
    · have habs : |γ| ≤ (H : ℤ) := (abs_le.mpr ⟨hlo, hhi⟩)
      have hcast : (γ.natAbs : ℤ) ≤ (H : ℤ) := by
        simpa only [Int.natCast_natAbs] using habs
      exact_mod_cast hcast
  · rintro ⟨hpos, hle⟩
    have habs : |γ| ≤ (H : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hle
    exact ⟨(abs_le.mp habs), hpos⟩

/-- 截距 `γ c / d`，其中整数先嵌入 `ℚ`，分母为自然数的有理数像。 -/
def rationalIntercept (γ : ℤ) (c d : ℕ) : ℚ :=
  (γ : ℚ) * (c : ℚ) / (d : ℚ)

/-- `(r,c)` 的合法表示集合。 -/
def interceptRepresentations (H D : ℕ) (r : ℚ) (c : ℕ) : Finset (ℤ × ℕ) :=
  ((interceptNumerators H).product (interceptDenominators D)).filter
    (fun gd => r = rationalIntercept gd.1 c gd.2)

/-- 有限有理截距集 `ℛ`。 -/
def rationalIntercepts (V : Finset ℕ) (H D : ℕ) : Finset ℚ :=
  ((V.product (interceptNumerators H)).product (interceptDenominators D)).image
    (fun x => rationalIntercept x.1.2 x.1.1 x.2)

/-- 论文的 `C_r`：能以合法分子与分母表示截距 `r` 的速度。 -/
def interceptCore (V : Finset ℕ) (H D : ℕ) (r : ℚ) : Finset ℕ :=
  V.filter (fun c => (interceptRepresentations H D r c).Nonempty)

/-- 论文的 `w(r)=|C_r|`。 -/
def interceptWeight (V : Finset ℕ) (H D : ℕ) (r : ℚ) : ℕ :=
  (interceptCore V H D r).card

theorem interceptCore_subset (V : Finset ℕ) (H D : ℕ) (r : ℚ) :
    interceptCore V H D r ⊆ V := Finset.filter_subset _ _

theorem interceptCore_mem_iff (V : Finset ℕ) (H D : ℕ) (r : ℚ) (c : ℕ) :
    c ∈ interceptCore V H D r ↔
      c ∈ V ∧ ∃ γ ∈ interceptNumerators H, ∃ d ∈ interceptDenominators D,
        r = rationalIntercept γ c d := by
  simp only [interceptCore, Finset.mem_filter]
  constructor
  · rintro ⟨hcV, ⟨⟨γ, d⟩, hrep⟩⟩
    obtain ⟨hgd, hr⟩ := Finset.mem_filter.mp hrep
    obtain ⟨hγ, hd⟩ := Finset.mem_product.mp hgd
    exact ⟨hcV, γ, hγ, d, hd, hr⟩
  · rintro ⟨hcV, γ, hγ, d, hd, hr⟩
    refine ⟨hcV, ⟨(γ, d), ?_⟩⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hγ, hd⟩, hr⟩

theorem interceptCore_mem_rationalIntercepts (V : Finset ℕ) (H D : ℕ)
    (r : ℚ) (c : ℕ) (hc : c ∈ interceptCore V H D r) :
    r ∈ rationalIntercepts V H D := by
  obtain ⟨hcV, γ, hγ, d, hd, hr⟩ :=
    (interceptCore_mem_iff V H D r c).mp hc
  apply Finset.mem_image.mpr
  refine ⟨((c, γ), d), ?_, ?_⟩
  · exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hcV, hγ⟩, hd⟩
  · exact hr.symm

/-- 对每个合法的 `(r,c)` 确定地选取一个分子、分母表示。 -/
noncomputable def selectedInterceptRep (H D : ℕ) (r : ℚ) (c : ℕ) : ℤ × ℕ :=
  if h : (interceptRepresentations H D r c).Nonempty then Classical.choose h else (0, 0)

theorem selectedInterceptRep_mem (V : Finset ℕ) (H D : ℕ) (r : ℚ) (c : ℕ)
    (hc : c ∈ interceptCore V H D r) :
    selectedInterceptRep H D r c ∈ interceptRepresentations H D r c := by
  have h : (interceptRepresentations H D r c).Nonempty :=
    (Finset.mem_filter.mp hc).2
  unfold selectedInterceptRep
  simpa [h] using Classical.choose_spec h

theorem selectedInterceptRep_ratio (V : Finset ℕ) (H D : ℕ) (r : ℚ) (c : ℕ)
    (hc : c ∈ interceptCore V H D r) :
    r = rationalIntercept (selectedInterceptRep H D r c).1 c
      (selectedInterceptRep H D r c).2 := by
  exact (Finset.mem_filter.mp (selectedInterceptRep_mem V H D r c hc)).2

/-- 固定两速度时，共同出现的截距。 -/
def commonIntercepts (V : Finset ℕ) (H D c c' : ℕ) : Finset ℚ :=
  (rationalIntercepts V H D).filter
    (fun r => c ∈ interceptCore V H D r ∧ c' ∈ interceptCore V H D r)

/-- 两个被选表示可以恢复原截距，因此共同截距到表示对的编码为单射。 -/
theorem selectedPair_injective (V : Finset ℕ) (H D c c' : ℕ) :
    Set.InjOn (fun r : ℚ =>
      (selectedInterceptRep H D r c, selectedInterceptRep H D r c'))
      (commonIntercepts V H D c c') := by
  intro r hr s hs heq
  have hrc := (Finset.mem_filter.mp hr).2.1
  have hsc := (Finset.mem_filter.mp hs).2.1
  have hr' := selectedInterceptRep_ratio V H D r c hrc
  have hs' := selectedInterceptRep_ratio V H D s c hsc
  have hfirst : selectedInterceptRep H D r c = selectedInterceptRep H D s c :=
    congrArg Prod.fst heq
  calc
    r = rationalIntercept (selectedInterceptRep H D r c).1 c
          (selectedInterceptRep H D r c).2 := hr'
    _ = rationalIntercept (selectedInterceptRep H D s c).1 c
          (selectedInterceptRep H D s c).2 := by rw [hfirst]
    _ = s := hs'.symm

/-- 两个有理表示相等时，交叉相乘得到整数等式。 -/
private lemma rationalIntercept_eq_cross (γ γ' : ℤ) (c c' d d' : ℕ)
    (hd : 0 < d) (hd' : 0 < d') :
    rationalIntercept γ c d = rationalIntercept γ' c' d' ↔
      γ * (c : ℤ) * (d' : ℤ) = γ' * (c' : ℤ) * (d : ℤ) := by
  unfold rationalIntercept
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hd'q : (d' : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd')
  rw [div_eq_div_iff hdq hd'q]
  exact ⟨fun h => by exact_mod_cast h, fun h => by exact_mod_cast h⟩

/-- 论文第 193 行：截距相同时非零整数分子的符号相同。 -/
theorem rationalIntercept_equal_sign (γ γ' : ℤ) (c c' d d' : ℕ)
    (hc : 0 < c) (hc' : 0 < c') (hd : 0 < d) (hd' : 0 < d')
    (hγ : γ ≠ 0) (hγ' : γ' ≠ 0)
    (heq : rationalIntercept γ c d = rationalIntercept γ' c' d') :
    (γ < 0) ↔ (γ' < 0) := by
  have hcross := (rationalIntercept_eq_cross γ γ' c c' d d' hd hd').mp heq
  have hpos : (0 < γ) ↔ (0 < γ') := by
    have hcZ : (0 : ℤ) < c := by exact_mod_cast hc
    have hc'Z : (0 : ℤ) < c' := by exact_mod_cast hc'
    have hdZ : (0 : ℤ) < d := by exact_mod_cast hd
    have hd'Z : (0 : ℤ) < d' := by exact_mod_cast hd'
    constructor
    · intro hγpos
      have hprod : 0 < γ * (c : ℤ) * (d' : ℤ) := by positivity
      rw [hcross] at hprod
      exact (mul_pos_iff_of_pos_right hc'Z).mp
        ((mul_pos_iff_of_pos_right hdZ).mp hprod)
    · intro hγ'pos
      have hprod : 0 < γ' * (c' : ℤ) * (d : ℤ) := by positivity
      rw [← hcross] at hprod
      exact (mul_pos_iff_of_pos_right hcZ).mp
        ((mul_pos_iff_of_pos_right hd'Z).mp hprod)
  constructor
  · intro hneg
    by_contra hnot
    have hpos' : 0 < γ' := by omega
    have hposγ := hpos.mpr hpos'
    omega
  · intro hneg
    by_contra hnot
    have hposγ : 0 < γ := by omega
    have hpos' := hpos.mp hposγ
    omega

/-- 论文第 193–195 行：`u=|γ|d'`, `v=|γ'|d` 满足 `uc=vc'`。 -/
theorem rationalIntercept_equal_natAbs_relation (γ γ' : ℤ) (c c' d d' : ℕ)
    (hd : 0 < d) (hd' : 0 < d')
    (heq : rationalIntercept γ c d = rationalIntercept γ' c' d') :
    (γ.natAbs * d') * c = (γ'.natAbs * d) * c' := by
  have hcross := (rationalIntercept_eq_cross γ γ' c c' d d' hd hd').mp heq
  have habs := congrArg Int.natAbs hcross
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at habs
  nlinarith [habs]

private lemma int_eq_of_natAbs_eq_sign (γ γ' : ℤ)
    (habs : γ.natAbs = γ'.natAbs) (hsign : (γ < 0) ↔ (γ' < 0)) : γ = γ' := by
  by_cases hneg : γ < 0
  · exact (Int.natAbs_inj_of_nonpos_of_nonpos hneg.le (hsign.mp hneg).le).mp habs
  · exact (Int.natAbs_inj_of_nonneg_of_nonneg (le_of_not_gt hneg)
      (le_of_not_gt (mt hsign.mpr hneg))).mp habs

private lemma selectedInterceptRep_data (V : Finset ℕ) (H D : ℕ)
    (r : ℚ) (c : ℕ) (hc : c ∈ interceptCore V H D r) :
    let ρ := selectedInterceptRep H D r c
    0 < ρ.1.natAbs ∧ ρ.1.natAbs ≤ H ∧ 1 ≤ ρ.2 ∧ ρ.2 ≤ D ∧
      r = rationalIntercept ρ.1 c ρ.2 := by
  dsimp
  have hmem := selectedInterceptRep_mem V H D r c hc
  obtain ⟨hprod, hr⟩ := Finset.mem_filter.mp hmem
  obtain ⟨hγ, hd⟩ := Finset.mem_product.mp hprod
  obtain ⟨hγpos, hγle⟩ := (mem_interceptNumerators_iff H _).mp hγ
  obtain ⟨hdpos, hdle⟩ := Finset.mem_Icc.mp hd
  exact ⟨hγpos, hγle, hdpos, hdle, hr⟩

/-- 从一个共同截距选定的两个表示形成纤维编码。 -/
noncomputable def interceptFiberCode (H D c c' : ℕ) (r : ℚ) :
    (ℕ × ℕ) × (Bool × (ℕ × ℕ)) :=
  let ρ := selectedInterceptRep H D r c
  let ρ' := selectedInterceptRep H D r c'
  ((ρ.1.natAbs * ρ'.2, ρ'.1.natAbs * ρ.2),
    (decide (ρ.1 < 0), (ρ.1.natAbs, ρ'.1.natAbs)))

/-- 编码的键属于 `E_{HD}(c,c')`，其余坐标属于符号与约数的有限乘积。 -/
theorem interceptFiberCode_valid (V : Finset ℕ) (H D c c' : ℕ)
    (hV : ∀ x ∈ V, 0 < x) (r : ℚ)
    (hr : r ∈ commonIntercepts V H D c c') :
    (interceptFiberCode H D c c' r).1 ∈ gcdRatioSolutions (H * D) c c' ∧
    (interceptFiberCode H D c c' r).2.2.1 ∈
      ((interceptFiberCode H D c c' r).1.1).divisors ∧
    (interceptFiberCode H D c c' r).2.2.2 ∈
      ((interceptFiberCode H D c c' r).1.2).divisors := by
  set ρ := selectedInterceptRep H D r c with hρ
  set ρ' := selectedInterceptRep H D r c' with hρ'
  obtain ⟨hrc, hrc'⟩ := (Finset.mem_filter.mp hr).2
  obtain ⟨hcV, _⟩ := Finset.mem_filter.mp hrc
  obtain ⟨hc'V, _⟩ := Finset.mem_filter.mp hrc'
  have hc := hV c hcV
  have hc' := hV c' hc'V
  obtain ⟨hγpos, hγle, hdpos, hdle, hratio⟩ :=
    selectedInterceptRep_data V H D r c hrc
  obtain ⟨hγ'pos, hγ'le, hd'pos, hd'le, hratio'⟩ :=
    selectedInterceptRep_data V H D r c' hrc'
  have heq : rationalIntercept ρ.1 c ρ.2 = rationalIntercept ρ'.1 c' ρ'.2 :=
    hratio.symm.trans hratio'
  have hrel : (ρ.1.natAbs * ρ'.2) * c = (ρ'.1.natAbs * ρ.2) * c' :=
    rationalIntercept_equal_natAbs_relation ρ.1 ρ'.1 c c' ρ.2 ρ'.2 hdpos hd'pos heq
  have hu0 : 1 ≤ ρ.1.natAbs * ρ'.2 := Nat.mul_pos hγpos hd'pos
  have hv0 : 1 ≤ ρ'.1.natAbs * ρ.2 := Nat.mul_pos hγ'pos hdpos
  have huU : ρ.1.natAbs * ρ'.2 ≤ H * D := Nat.mul_le_mul hγle hd'le
  have hvU : ρ'.1.natAbs * ρ.2 ≤ H * D := Nat.mul_le_mul hγ'le hdle
  have huDiv : ρ.1.natAbs ∈ (ρ.1.natAbs * ρ'.2).divisors :=
    Nat.mem_divisors.mpr ⟨dvd_mul_right _ _, Nat.ne_of_gt hu0⟩
  have hvDiv : ρ'.1.natAbs ∈ (ρ'.1.natAbs * ρ.2).divisors :=
    Nat.mem_divisors.mpr ⟨dvd_mul_right _ _, Nat.ne_of_gt hv0⟩
  refine ⟨?_, ?_, ?_⟩
  · change (ρ.1.natAbs * ρ'.2, ρ'.1.natAbs * ρ.2) ∈
      gcdRatioSolutions (H * D) c c'
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hu0, huU⟩,
       Finset.mem_Icc.mpr ⟨hv0, hvU⟩⟩, hrel⟩
  · exact huDiv
  · exact hvDiv

/-- 纤维编码单射：固定两个速度，符号、两个分子绝对值和交叉乘积能恢复截距。 -/
theorem interceptFiberCode_injOn (V : Finset ℕ) (H D c c' : ℕ) :
    Set.InjOn (interceptFiberCode H D c c')
      (commonIntercepts V H D c c') := by
  intro r hr s hs hcode
  let ρr := selectedInterceptRep H D r c
  let ρr' := selectedInterceptRep H D r c'
  let ρs := selectedInterceptRep H D s c
  let ρs' := selectedInterceptRep H D s c'
  have hγabs : ρr.1.natAbs = ρs.1.natAbs := by
    exact congrArg (fun z : (ℕ × ℕ) × (Bool × (ℕ × ℕ)) => z.2.2.1) hcode
  have hγ'abs : ρr'.1.natAbs = ρs'.1.natAbs := by
    exact congrArg (fun z : (ℕ × ℕ) × (Bool × (ℕ × ℕ)) => z.2.2.2) hcode
  have hsign : (ρr.1 < 0) ↔ (ρs.1 < 0) := by
    exact decide_eq_decide.mp
      (congrArg (fun z : (ℕ × ℕ) × (Bool × (ℕ × ℕ)) => z.2.1) hcode)
  have hγeq : ρr.1 = ρs.1 := int_eq_of_natAbs_eq_sign _ _ hγabs hsign
  have hvEq : ρr'.1.natAbs * ρr.2 = ρs'.1.natAbs * ρs.2 := by
    exact congrArg (fun z : (ℕ × ℕ) × (Bool × (ℕ × ℕ)) => z.1.2) hcode
  have hspos : 0 < ρs'.1.natAbs :=
    (selectedInterceptRep_data V H D s c' (Finset.mem_filter.mp hs |>.2.2)).1
  have hdEq : ρr.2 = ρs.2 := by
    rw [hγ'abs] at hvEq
    exact Nat.eq_of_mul_eq_mul_left hspos hvEq
  have hr' := selectedInterceptRep_ratio V H D r c (Finset.mem_filter.mp hr).2.1
  have hs' := selectedInterceptRep_ratio V H D s c (Finset.mem_filter.mp hs).2.1
  calc
    r = rationalIntercept ρr.1 c ρr.2 := hr'
    _ = rationalIntercept ρs.1 c ρs.2 := by rw [hγeq, hdEq]
    _ = s := hs'.symm

/-- 固定交叉乘积 `u,v` 的共同截距纤维。 -/
noncomputable def interceptCodeFiber (V : Finset ℕ) (H D c c' : ℕ)
    (uv : ℕ × ℕ) : Finset ℚ :=
  (commonIntercepts V H D c c').filter
    (fun r => (interceptFiberCode H D c c' r).1 = uv)

/-- 论文 `eq:energy` 前的关键计数：固定 `c,c',u,v` 至多有
`2 τ(u) τ(v)` 个截距。 -/
theorem interceptCodeFiber_card_le (V : Finset ℕ) (H D c c' : ℕ)
    (hV : ∀ x ∈ V, 0 < x) (uv : ℕ × ℕ) :
    (interceptCodeFiber V H D c c' uv).card ≤
      2 * uv.1.divisors.card * uv.2.divisors.card := by
  classical
  let target : Finset (Bool × (ℕ × ℕ)) :=
    (Finset.univ : Finset Bool).product
      (uv.1.divisors.product uv.2.divisors)
  have hmap : Set.MapsTo (fun r => (interceptFiberCode H D c c' r).2)
      (interceptCodeFiber V H D c c' uv) target := by
    intro r hr
    have hrc : r ∈ commonIntercepts V H D c c' :=
      (Finset.mem_filter.mp hr).1
    have hkey : (interceptFiberCode H D c c' r).1 = uv :=
      (Finset.mem_filter.mp hr).2
    obtain ⟨_, hdiv, hdiv'⟩ := interceptFiberCode_valid V H D c c' hV r hrc
    change (interceptFiberCode H D c c' r).2 ∈
      (Finset.univ : Finset Bool).product
        (uv.1.divisors.product uv.2.divisors)
    have hfirst : (interceptFiberCode H D c c' r).2.2.1 ∈ uv.1.divisors := by
      simpa only [hkey] using hdiv
    have hsecond : (interceptFiberCode H D c c' r).2.2.2 ∈ uv.2.divisors := by
      simpa only [hkey] using hdiv'
    exact Finset.mk_mem_product (Finset.mem_univ _)
      (Finset.mk_mem_product hfirst hsecond)
  have hinj : Set.InjOn (fun r => (interceptFiberCode H D c c' r).2)
      (interceptCodeFiber V H D c c' uv) := by
    intro r hr s hs hdec
    have hrc : r ∈ commonIntercepts V H D c c' := (Finset.mem_filter.mp hr).1
    have hsc : s ∈ commonIntercepts V H D c c' := (Finset.mem_filter.mp hs).1
    have hkeyr := (Finset.mem_filter.mp hr).2
    have hkeys := (Finset.mem_filter.mp hs).2
    apply interceptFiberCode_injOn V H D c c' hrc hsc
    exact Prod.ext (hkeyr.trans hkeys.symm) hdec
  have hcard := Finset.card_le_card_of_injOn
    (fun r => (interceptFiberCode H D c c' r).2) hmap hinj
  dsimp only [target] at hcard
  simpa [Finset.card_product, mul_assoc] using hcard

/-- 共同截距的基数由 `E_{HD}(c,c')` 上的纤维分解并估计。 -/
theorem commonIntercepts_card_le (V : Finset ℕ) (H D c c' : ℕ)
    (hV : ∀ x ∈ V, 0 < x) :
    (commonIntercepts V H D c c').card ≤
      ∑ uv ∈ gcdRatioSolutions (H * D) c c',
        2 * uv.1.divisors.card * uv.2.divisors.card := by
  classical
  have hmap : ∀ r ∈ commonIntercepts V H D c c',
      (interceptFiberCode H D c c' r).1 ∈ gcdRatioSolutions (H * D) c c' := by
    intro r hr
    exact (interceptFiberCode_valid V H D c c' hV r hr).1
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  apply Finset.sum_le_sum
  intro uv huv
  exact interceptCodeFiber_card_le V H D c c' hV uv

/-- 任意有限二部关联的平方权重可按两个标签的有序对计数。 -/
private theorem finiteSquareCount {α β : Type} [DecidableEq β]
    (R : Finset α) (V : Finset β) (C : α → Finset β) (hC : ∀ r, C r ⊆ V) :
    (∑ r ∈ R, (C r).card ^ 2) =
      ∑ c ∈ V, ∑ c' ∈ V, (R.filter (fun r => c ∈ C r ∧ c' ∈ C r)).card := by
  classical
  have hper (r : α) :
      (∑ c ∈ V, ∑ c' ∈ V, if c ∈ C r ∧ c' ∈ C r then (1:ℕ) else 0) =
        (C r).card ^ 2 := by
    have hsingle : (∑ c ∈ V, if c ∈ C r then (1:ℕ) else 0) = (C r).card := by
      rw [Finset.sum_ite]
      simp only [Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one]
      congr 1
      ext c
      simp [hC r]
    have hinner (c : β) :
        (∑ c' ∈ V, if c ∈ C r ∧ c' ∈ C r then (1:ℕ) else 0) =
        if c ∈ C r then (C r).card else 0 := by
      by_cases hc : c ∈ C r
      · simp only [hc, true_and, ite_true, hsingle]
      · simp only [hc, false_and, ite_false, Finset.sum_const_zero]
    simp_rw [hinner]
    rw [Finset.sum_ite]
    simp only [Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
    have hfilter : V.filter (· ∈ C r) = C r := by
      ext c
      simp [hC r]
    rw [hfilter]
    simp [pow_two]
  calc
    (∑ r ∈ R, (C r).card ^ 2) =
        ∑ r ∈ R, ∑ c ∈ V, ∑ c' ∈ V,
          if c ∈ C r ∧ c' ∈ C r then (1:ℕ) else 0 := by
            apply Finset.sum_congr rfl
            intro r hr
            exact (hper r).symm
    _ = ∑ c ∈ V, ∑ c' ∈ V, ∑ r ∈ R,
          if c ∈ C r ∧ c' ∈ C r then (1:ℕ) else 0 := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro c hc
            rw [Finset.sum_comm]
    _ = ∑ c ∈ V, ∑ c' ∈ V,
          (R.filter (fun r => c ∈ C r ∧ c' ∈ C r)).card := by
            apply Finset.sum_congr rfl
            intro c hc
            apply Finset.sum_congr rfl
            intro c' hc'
            rw [Finset.sum_ite]
            simp only [Finset.sum_const_zero, add_zero, Finset.sum_const,
              smul_eq_mul, mul_one]

/-- 论文 `eq:energy` 第一步：截距权重的平方和恰为按有序速度对求和的共同截距数。 -/
theorem rationalInterceptEnergy_eq_common (V : Finset ℕ) (H D : ℕ) :
    (∑ r ∈ rationalIntercepts V H D, (interceptWeight V H D r) ^ 2) =
      ∑ c ∈ V, ∑ c' ∈ V, (commonIntercepts V H D c c').card := by
  simpa only [interceptWeight, commonIntercepts] using
    finiteSquareCount (rationalIntercepts V H D) V (interceptCore V H D)
      (fun r => interceptCore_subset V H D r)

/-- 论文 `eq:energy` 前两步：有理截距的平方权重能量受两个分子的约数数控制。 -/
theorem rationalInterceptEnergy_le_divisors (V : Finset ℕ) (H D : ℕ)
    (hV : ∀ c ∈ V, 0 < c) :
    (∑ r ∈ rationalIntercepts V H D, ((interceptWeight V H D r : ℝ) ^ 2)) ≤
      2 * ∑ c ∈ V, ∑ c' ∈ V, ∑ uv ∈ gcdRatioSolutions (H * D) c c',
        (uv.1.divisors.card : ℝ) * (uv.2.divisors.card : ℝ) := by
  have hNat :
      (∑ r ∈ rationalIntercepts V H D, (interceptWeight V H D r) ^ 2) ≤
        ∑ c ∈ V, ∑ c' ∈ V, ∑ uv ∈ gcdRatioSolutions (H * D) c c',
          2 * uv.1.divisors.card * uv.2.divisors.card := by
    rw [rationalInterceptEnergy_eq_common]
    apply Finset.sum_le_sum
    intro c hc
    apply Finset.sum_le_sum
    intro c' hc'
    exact commonIntercepts_card_le V H D c c' hV
  calc
    (∑ r ∈ rationalIntercepts V H D, ((interceptWeight V H D r : ℝ) ^ 2)) =
        ((∑ r ∈ rationalIntercepts V H D, (interceptWeight V H D r) ^ 2 : ℕ) : ℝ) := by
          simp
    _ ≤ ((∑ c ∈ V, ∑ c' ∈ V,
        ∑ uv ∈ gcdRatioSolutions (H * D) c c',
          2 * uv.1.divisors.card * uv.2.divisors.card : ℕ) : ℝ) := by
          exact_mod_cast hNat
    _ = 2 * ∑ c ∈ V, ∑ c' ∈ V, ∑ uv ∈ gcdRatioSolutions (H * D) c c',
        (uv.1.divisors.card : ℝ) * (uv.2.divisors.card : ℝ) := by
          simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat]
          simp only [Finset.mul_sum, mul_assoc]

/-- 论文 `eq:energy` 第二步：结合统一的约数幂界和 `E_{HD}` 的 GCD 比值计数。
常数仅依赖 `θ`；此处仍保留 `S₂(V)`。 -/
theorem rationalInterceptEnergy_power_bound (θ : ℝ) (hθ : 0 < θ) :
    ∃ Cθ : ℝ, 0 < Cθ ∧
      ∀ (V : Finset ℕ) (H D m : ℕ),
        (∀ c ∈ V, 0 < c) → 0 < H → 0 < D → 1 ≤ m → H * D ≤ m ^ 2 →
        (∑ r ∈ rationalIntercepts V H D,
          ((interceptWeight V H D r : ℝ) ^ 2)) ≤
          Cθ * (m : ℝ) ^ (4 * θ) * ((H * D : ℕ) : ℝ) * inversePairGcdSum V := by
  obtain ⟨K, hKpos, _, hdiv⟩ := divisorPowerBound_energy θ hθ
  refine ⟨2 * K ^ 2, by positivity, ?_⟩
  intro V H D m hV hH hD hm hHD
  let F : ℝ := K ^ 2 * (m : ℝ) ^ (4 * θ)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hterm (c c' : ℕ) (uv : ℕ × ℕ)
      (huv : uv ∈ gcdRatioSolutions (H * D) c c') :
      (uv.1.divisors.card : ℝ) * (uv.2.divisors.card : ℝ) ≤ F := by
    obtain ⟨hprod, _⟩ := Finset.mem_filter.mp huv
    obtain ⟨hu, hv⟩ := Finset.mem_product.mp hprod
    obtain ⟨hu0, huHD⟩ := Finset.mem_Icc.mp hu
    obtain ⟨hv0, hvHD⟩ := Finset.mem_Icc.mp hv
    exact hdiv m uv.1 uv.2 hm hu0 hv0 (huHD.trans hHD) (hvHD.trans hHD)
  have hweighted :
      (∑ c ∈ V, ∑ c' ∈ V, ∑ uv ∈ gcdRatioSolutions (H * D) c c',
          (uv.1.divisors.card : ℝ) * (uv.2.divisors.card : ℝ)) ≤
        F * (∑ c ∈ V, ∑ c' ∈ V,
          ((gcdRatioSolutions (H * D) c c').card : ℝ)) := by
    calc
      (∑ c ∈ V, ∑ c' ∈ V, ∑ uv ∈ gcdRatioSolutions (H * D) c c',
          (uv.1.divisors.card : ℝ) * (uv.2.divisors.card : ℝ)) ≤
          ∑ c ∈ V, ∑ c' ∈ V, ∑ uv ∈ gcdRatioSolutions (H * D) c c', F := by
            apply Finset.sum_le_sum
            intro c hc
            apply Finset.sum_le_sum
            intro c' hc'
            apply Finset.sum_le_sum
            intro uv huv
            exact hterm c c' uv huv
      _ = F * (∑ c ∈ V, ∑ c' ∈ V,
          ((gcdRatioSolutions (H * D) c c').card : ℝ)) := by
            simp [Finset.mul_sum, mul_comm]
  have hS2 := gcdRatioSolutions_sum_le_inversePairGcdSum V hV (H * D)
  calc
    (∑ r ∈ rationalIntercepts V H D,
        ((interceptWeight V H D r : ℝ) ^ 2)) ≤
        2 * (∑ c ∈ V, ∑ c' ∈ V,
          ∑ uv ∈ gcdRatioSolutions (H * D) c c',
            (uv.1.divisors.card : ℝ) * (uv.2.divisors.card : ℝ)) :=
              rationalInterceptEnergy_le_divisors V H D hV
    _ ≤ 2 * (F * ∑ c ∈ V, ∑ c' ∈ V,
          ((gcdRatioSolutions (H * D) c c').card : ℝ)) := by
            gcongr
    _ ≤ 2 * (F * (((H * D : ℕ) : ℝ) * inversePairGcdSum V)) := by
            gcongr
    _ = (2 * K ^ 2) * (m : ℝ) ^ (4 * θ) * ((H * D : ℕ) : ℝ) *
          inversePairGcdSum V := by
            dsimp [F]
            ring

end LonelyRunner
