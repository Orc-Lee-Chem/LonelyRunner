import LonelyRunner.MainTheorem

/-!
# 主定理的普通实数语义检查

直接调用 `LonelyRunner.mainTheorem`。选取真实圆周代表并用小数部分
归一化到 `[0,1)`；商群投影不增范数给出对每个整数的距离下界。
不引入新的数学假设，不修改已有主定理证明。
-/

namespace LonelyRunner

/-- 每个单位圆周点有一个实际处于 `[0,1)` 的实数代表。 -/
theorem semantic_circle_representative (s : UnitAddCircle) :
    ∃ t : ℝ, t ∈ Set.Ico (0 : ℝ) 1 ∧ (t : UnitAddCircle) = s := by
  induction s using Quotient.inductionOn with
  | _ x =>
    exact ⟨Int.fract x, ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩, AddCircle.coe_fract x⟩

/-- 圆周距离不超过任一整数代表差的实绝对值；整数在单位圆周投影为零。 -/
theorem semantic_circle_dist_le_integer (v : ℕ) (t : ℝ) (k : ℤ) :
    dist (v • (t : UnitAddCircle)) 0 ≤ |(v : ℝ) * t - (k : ℝ)| := by
  have hk : (((k : ℝ) : UnitAddCircle)) = 0 := by
    apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
    exact ⟨k, by simp [zsmul_eq_mul]⟩
  have hco : (((v : ℝ) * t - (k : ℝ) : ℝ) : UnitAddCircle) =
      v • (t : UnitAddCircle) := by
    rw [AddCircle.coe_sub, hk, sub_zero, ← nsmul_eq_mul, AddCircle.coe_nsmul]
  calc
    _ = ‖(((v : ℝ) * t - (k : ℝ) : ℝ) : UnitAddCircle)‖ := by
      rw [hco, dist_zero_right]
    _ ≤ ‖(v : ℝ) * t - (k : ℝ)‖ := QuotientAddGroup.norm_mk_le_norm
    _ = _ := Real.norm_eq_abs _

/-- 主定理的普通实数表述：同一个 `t∈[0,1)` 对所有速度及所有整数同时成立。
只有正参数、正速度及足够大基数三个条件。 -/
theorem mainTheorem_real :
    ∀ κ : ℝ, 0 < κ → ∃ N : ℕ, 2 ≤ N ∧
      ∀ V : Finset ℕ, (∀ v ∈ V, 0 < v) → N ≤ V.card →
        ∃ t : ℝ, t ∈ Set.Ico (0 : ℝ) 1 ∧ ∀ v ∈ V, ∀ k : ℤ,
          1 / (2 * (V.card : ℝ)) + 1 / (2 * (V.card : ℝ)^(3/2+κ)) ≤
            |(v : ℝ) * t - (k : ℝ)| := by
  intro κ hκ
  obtain ⟨N, hN, hmain⟩ := mainTheorem κ hκ
  refine ⟨N, hN, ?_⟩
  intro V hV hsize
  obtain ⟨s, hs⟩ := hmain V hV hsize
  obtain ⟨t, ht, hts⟩ := semantic_circle_representative s
  refine ⟨t, ht, ?_⟩
  intro v hv k
  have hvbound := hs v hv
  rw [← hts] at hvbound
  exact hvbound.trans (semantic_circle_dist_le_integer v t k)

set_option pp.proofs false in
#print mainTheorem
set_option pp.proofs false in
#print mainTheorem_real
#print axioms mainTheorem
#print axioms semantic_circle_representative
#print axioms semantic_circle_dist_le_integer
#print axioms mainTheorem_real

end LonelyRunner
