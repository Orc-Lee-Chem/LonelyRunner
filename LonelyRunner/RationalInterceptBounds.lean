import LonelyRunner.RationalInterceptEnergy
import Mathlib.Data.Int.Interval

/-!
# 有理截距的权重与总关联数

对应论文 `paper/lonely_runner_zh.tex` 的 `eq:energy` 前的基本计数：
合法分子、分母的数量以及截距权重的上界。
-/

namespace LonelyRunner

/-- 非零整数分子恰有 `2H` 个；`H=0` 时同样成立。 -/
theorem interceptNumerators_card (H : ℕ) :
    (interceptNumerators H).card = 2 * H := by
  have hset : interceptNumerators H =
      (Finset.Icc (-(H : ℤ)) (H : ℤ)).erase 0 := by
    ext γ
    simp [interceptNumerators, and_comm, and_assoc]
  have hzero : (0 : ℤ) ∈ Finset.Icc (-(H : ℤ)) (H : ℤ) := by
    simp
  have hinterval : (Finset.Icc (-(H : ℤ)) (H : ℤ)).card = 2 * H + 1 := by
    rw [Int.card_Icc]
    omega
  rw [hset, Finset.card_erase_of_mem hzero, hinterval]
  omega

/-- 正整数分母 `1≤d≤D` 恰有 `D` 个；`D=0` 时为空。 -/
theorem interceptDenominators_card (D : ℕ) :
    (interceptDenominators D).card = D := by
  simp [interceptDenominators]

/-- `ℛ` 的逐项描述：截距由一个速度、非零整数分子与正整数分母产生。 -/
theorem mem_rationalIntercepts_iff (V : Finset ℕ) (H D : ℕ) (r : ℚ) :
    r ∈ rationalIntercepts V H D ↔
      ∃ c ∈ V, ∃ γ ∈ interceptNumerators H,
        ∃ d ∈ interceptDenominators D, r = rationalIntercept γ c d := by
  constructor
  · intro hr
    obtain ⟨⟨⟨c, γ⟩, d⟩, hmem, heq⟩ := Finset.mem_image.mp hr
    obtain ⟨hcg, hd⟩ := Finset.mem_product.mp hmem
    obtain ⟨hc, hγ⟩ := Finset.mem_product.mp hcg
    exact ⟨c, hc, γ, hγ, d, hd, heq.symm⟩
  · rintro ⟨c, hc, γ, hγ, d, hd, hr⟩
    apply Finset.mem_image.mpr
    exact ⟨((c, γ), d),
      Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hc, hγ⟩, hd⟩, hr.symm⟩

/-- 正速度生成的每个合法截距均非零。 -/
theorem rationalIntercepts_ne_zero (V : Finset ℕ) (H D : ℕ)
    (hV : ∀ c ∈ V, 0 < c) (r : ℚ) (hr : r ∈ rationalIntercepts V H D) :
    r ≠ 0 := by
  obtain ⟨c, hc, γ, hγ, d, hd, heq⟩ :=
    (mem_rationalIntercepts_iff V H D r).mp hr
  have hγpos := ((mem_interceptNumerators_iff H γ).mp hγ).1
  have hdpos := (Finset.mem_Icc.mp hd).1
  have hγq : (γ : ℚ) ≠ 0 := by
    exact_mod_cast (show γ ≠ 0 by omega)
  have hcq : (c : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (hV c hc))
  have hdq : (d : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hdpos)
  rw [heq]
  exact div_ne_zero (mul_ne_zero hγq hcq) hdq

/-- 合法截距至少有一个速度表示，所以 `w(r)>0`。 -/
theorem interceptWeight_pos (V : Finset ℕ) (H D : ℕ) (r : ℚ)
    (hr : r ∈ rationalIntercepts V H D) :
    0 < interceptWeight V H D r := by
  obtain ⟨c, hc, γ, hγ, d, hd, heq⟩ :=
    (mem_rationalIntercepts_iff V H D r).mp hr
  apply Finset.card_pos.mpr
  refine ⟨c, (interceptCore_mem_iff V H D r c).mpr ?_⟩
  exact ⟨hc, γ, hγ, d, hd, heq⟩

/-- 固定合法非零分子、正分母和截距时，速度唯一。 -/
theorem rationalIntercept_speed_unique (H D : ℕ) (γ : ℤ) (d c c' : ℕ)
    (hγ : γ ∈ interceptNumerators H) (hd : d ∈ interceptDenominators D)
    (heq : rationalIntercept γ c d = rationalIntercept γ c' d) :
    c = c' := by
  have hγpos := ((mem_interceptNumerators_iff H γ).mp hγ).1
  have hdpos := (Finset.mem_Icc.mp hd).1
  have hrel := rationalIntercept_equal_natAbs_relation γ γ c c' d d hdpos hdpos heq
  exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hγpos hdpos) hrel

/-- 论文 `eq:energy` 前的单点计数：固定 `r`，所选表示将 `C_r`
单射编码为合法的 `(γ,d)` 对。 -/
theorem selectedInterceptRep_injOn (V : Finset ℕ) (H D : ℕ) (r : ℚ) :
    Set.InjOn (selectedInterceptRep H D r) (interceptCore V H D r) := by
  intro c hc c' hc' hrepEq
  let ρ := selectedInterceptRep H D r c
  have hselected := selectedInterceptRep_mem V H D r c hc
  obtain ⟨hproduct, _⟩ := Finset.mem_filter.mp hselected
  obtain ⟨hγ, hd⟩ := Finset.mem_product.mp hproduct
  have hr_c := selectedInterceptRep_ratio V H D r c hc
  have hr_c' : r = rationalIntercept ρ.1 c' ρ.2 := by
    simpa only [ρ, hrepEq] using selectedInterceptRep_ratio V H D r c' hc'
  exact rationalIntercept_speed_unique H D ρ.1 ρ.2 c c' hγ hd
    (hr_c.symm.trans hr_c')

/-- 单个截距的速度权重不超过合法分子、分母对的数量 `2HD`。 -/
theorem interceptWeight_le (V : Finset ℕ) (H D : ℕ) (r : ℚ) :
    interceptWeight V H D r ≤ 2 * H * D := by
  classical
  have hmap : Set.MapsTo (selectedInterceptRep H D r)
      (interceptCore V H D r)
      ((interceptNumerators H).product (interceptDenominators D)) := by
    intro c hc
    exact (Finset.mem_filter.mp (selectedInterceptRep_mem V H D r c hc)).1
  have hcard := Finset.card_le_card_of_injOn
    (selectedInterceptRep H D r) hmap (selectedInterceptRep_injOn V H D r)
  simpa [interceptWeight, Finset.card_product, interceptNumerators_card,
    interceptDenominators_card, mul_assoc] using hcard

/-- 论文 `eq:energy` 前的逐项结论：正速度产生非零截距，
且 `0<w(r)≤2HD`。 -/
theorem rationalIntercept_pointwise_bounds (V : Finset ℕ) (H D : ℕ)
    (hV : ∀ c ∈ V, 0 < c) (_hH : 0 < H) (_hD : 0 < D)
    (r : ℚ) (hr : r ∈ rationalIntercepts V H D) :
    r ≠ 0 ∧ 0 < interceptWeight V H D r ∧
      interceptWeight V H D r ≤ 2 * H * D := by
  exact ⟨rationalIntercepts_ne_zero V H D hV r hr,
    interceptWeight_pos V H D r hr, interceptWeight_le V H D r⟩

/-- 截距集上的最大权重；空截距集取 `0`。 -/
noncomputable def interceptMaxWeight (V : Finset ℕ) (H D : ℕ) : ℕ :=
  (rationalIntercepts V H D).sup (interceptWeight V H D)

theorem interceptMaxWeight_le (V : Finset ℕ) (H D : ℕ) :
    interceptMaxWeight V H D ≤ 2 * H * D := by
  exact Finset.sup_le fun r hr => interceptWeight_le V H D r

theorem interceptMaxWeight_eq_zero_of_empty (V : Finset ℕ) (H D : ℕ)
    (hEmpty : rationalIntercepts V H D = ∅) :
    interceptMaxWeight V H D = 0 := by
  simp [interceptMaxWeight, hEmpty]

@[simp] theorem interceptMaxWeight_empty (H D : ℕ) :
    interceptMaxWeight ∅ H D = 0 := by
  exact interceptMaxWeight_eq_zero_of_empty ∅ H D (by simp [rationalIntercepts])

/-- 合法关联对 `(r,c)`：截距属于 `ℛ`，速度属于 `C_r`。 -/
def interceptIncidences (V : Finset ℕ) (H D : ℕ) : Finset (Σ _ : ℚ, ℕ) :=
  (rationalIntercepts V H D).sigma (interceptCore V H D)

/-- 总权重恰好是合法关联对的数量。 -/
theorem interceptIncidences_card (V : Finset ℕ) (H D : ℕ) :
    (interceptIncidences V H D).card =
      ∑ r ∈ rationalIntercepts V H D, interceptWeight V H D r := by
  classical
  simp [interceptIncidences, interceptWeight, Finset.card_sigma]

/-- 每个关联对编码为 `(c,γ,d)`，其中 `(γ,d)` 取已选的合法表示。 -/
noncomputable def interceptIncidenceCode (H D : ℕ) (p : Σ _ : ℚ, ℕ) :
    (ℕ × ℤ) × ℕ :=
  let ρ := selectedInterceptRep H D p.1 p.2
  ((p.2, ρ.1), ρ.2)

set_option maxHeartbeats 800000 in
-- The chosen rational representations create a large reducible equality during Sigma injectivity.
/-- `eq:energy` 前的总权重编码单射：速度和已选表示可以恢复截距。 -/
theorem interceptIncidenceCode_injOn (V : Finset ℕ) (H D : ℕ) :
    Set.InjOn (interceptIncidenceCode H D) (interceptIncidences V H D) := by
  intro p hp q hq hcode
  obtain ⟨hpr, hpc⟩ := Finset.mem_sigma.mp hp
  obtain ⟨hqr, hqc⟩ := Finset.mem_sigma.mp hq
  have hcEq : p.2 = q.2 :=
    congrArg (fun x : (ℕ × ℤ) × ℕ => x.1.1) hcode
  have hγEq : (selectedInterceptRep H D p.1 p.2).1 =
      (selectedInterceptRep H D q.1 q.2).1 :=
    congrArg (fun x : (ℕ × ℤ) × ℕ => x.1.2) hcode
  have hdEq : (selectedInterceptRep H D p.1 p.2).2 =
      (selectedInterceptRep H D q.1 q.2).2 :=
    congrArg (fun x : (ℕ × ℤ) × ℕ => x.2) hcode
  have hrepEq : selectedInterceptRep H D p.1 p.2 =
      selectedInterceptRep H D q.1 q.2 := Prod.ext hγEq hdEq
  have hratio_p := selectedInterceptRep_ratio V H D p.1 p.2 hpc
  have hratio_q := selectedInterceptRep_ratio V H D q.1 q.2 hqc
  have hrEq : p.1 = q.1 := by
    calc
      p.1 = rationalIntercept (selectedInterceptRep H D p.1 p.2).1 p.2
          (selectedInterceptRep H D p.1 p.2).2 := hratio_p
      _ = rationalIntercept (selectedInterceptRep H D q.1 q.2).1 q.2
          (selectedInterceptRep H D q.1 q.2).2 := by rw [hrepEq, hcEq]
      _ = q.1 := hratio_q.symm
  cases p with
  | mk rp cp =>
    cases q with
    | mk rq cq =>
      change rp = rq at hrEq
      change cp = cq at hcEq
      subst rq
      subst cq
      rfl

/-- 论文 `eq:energy` 前的总权重界：合法关联对数不超过
`|V|·(2H)·D`，即 `2|V|HD`。 -/
theorem interceptWeight_sum_le (V : Finset ℕ) (H D : ℕ) :
    (∑ r ∈ rationalIntercepts V H D, interceptWeight V H D r) ≤
      2 * V.card * H * D := by
  classical
  let target := (V.product (interceptNumerators H)).product
    (interceptDenominators D)
  have hmap : Set.MapsTo (interceptIncidenceCode H D)
      (interceptIncidences V H D) target := by
    intro p hp
    obtain ⟨_, hc⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hcV, _⟩ := Finset.mem_filter.mp hc
    have hrep := selectedInterceptRep_mem V H D p.1 p.2 hc
    obtain ⟨hproduct, _⟩ := Finset.mem_filter.mp hrep
    obtain ⟨hγ, hd⟩ := Finset.mem_product.mp hproduct
    exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hcV, hγ⟩, hd⟩
  have hcard := Finset.card_le_card_of_injOn
    (interceptIncidenceCode H D) hmap (interceptIncidenceCode_injOn V H D)
  calc
    (∑ r ∈ rationalIntercepts V H D, interceptWeight V H D r) =
        (interceptIncidences V H D).card := (interceptIncidences_card V H D).symm
    _ ≤ target.card := hcard
    _ = 2 * V.card * H * D := by
      dsimp only [target]
      simp [Finset.card_product, interceptNumerators_card,
        interceptDenominators_card, mul_comm, mul_left_comm]

@[simp] theorem interceptWeight_sum_empty (H D : ℕ) :
    (∑ r ∈ rationalIntercepts ∅ H D, interceptWeight ∅ H D r) = 0 := by
  simp [rationalIntercepts]

end LonelyRunner
