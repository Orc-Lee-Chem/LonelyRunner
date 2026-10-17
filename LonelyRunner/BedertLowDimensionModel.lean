import LonelyRunner.BedertModelNumerics

/-!
# 低二解离维数的低高度模型

论文 `prop:bedert` 的建模输入：复用单步压缩，以自然数高度强归纳，
由显式势函数支付并望远镜消去所有误差。最终接口不保留压缩次数、
素数、代表函数、累计误差假设或辅助数值条件。
-/

namespace LonelyRunner
open Finset

/-- 高度强归纳的精确不变量：误差为 `F(H)-F(max M H)`。
基例直接保留速度，归纳步取下一高度 `max Q H`，不要求它本身是速度。 -/
theorem bedertLowDimensionModel_iterate (m d : ℕ) (hm : 2 ≤ m) (hd : 1 ≤ d) :
    ∀ M : ℕ, ∀ (V : Finset ℕ) (δ : ℝ), V.card = m →
      (∀ v ∈ V, 0 < v ∧ v ≤ M) →
      twoDissociatedDimension (V.image (fun v : ℕ => (v : ℤ))) ≤ d →
      (∀ t : UnitAddCircle, ∃ v ∈ V, dist (v • t) 0 ≤ δ) →
      ∃ W : Finset ℕ, W.card = m ∧
        (∀ w ∈ W, 0 < w ∧ w ≤ 2 * bedertModelThreshold m d) ∧
        twoDissociatedDimension (W.image (fun w : ℕ => (w : ℤ))) ≤ d ∧
        ∀ t : UnitAddCircle, ∃ w ∈ W,
          dist (w • t) 0 ≤ δ + bedertModelPotential d (bedertModelThreshold m d : ℝ) -
            bedertModelPotential d ((max M (bedertModelThreshold m d) : ℕ) : ℝ) := by
  intro M
  induction M using Nat.strong_induction_on with
  | h M ih =>
    intro V δ hcard hV hdim hcover
    let H := bedertModelThreshold m d
    have hmpos : 0 < m := by omega
    have hdpos : 0 < d := by omega
    have hHpos : 0 < H := by dsimp [H, bedertModelThreshold]; positivity
    have hHR : (0 : ℝ) < H := by exact_mod_cast hHpos
    by_cases hbase : M ≤ 2 * H
    · refine ⟨V, hcard, (fun v hv => ⟨(hV v hv).1, (hV v hv).2.trans hbase⟩), hdim, ?_⟩
      have hanti := bedertModelPotential_antitone d hHR
        (by exact_mod_cast (le_max_right M H) : (H : ℝ) ≤ ((max M H : ℕ) : ℝ))
      intro t
      obtain ⟨v, hv, hvt⟩ := hcover t
      have hδ : δ ≤ δ + bedertModelPotential d (H : ℝ) -
          bedertModelPotential d ((max M H : ℕ) : ℝ) := by linarith
      exact ⟨v, hv, hvt.trans hδ⟩
    · have hMlarge : 2 * H < M := by omega
      let L := ⌊(M : ℝ) ^ ((2 * (d : ℝ))⁻¹)⌋₊
      obtain ⟨hL, hpow, herr⟩ := bedertModel_floor_root m d M hm hd hMlarge
      have hmV : 2 ≤ V.card := by omega
      obtain ⟨U, Q, hQpos, hUcard, hUbounds, hUdim, hQheight, hhalf, hstep⟩ :=
        bedertCompressionStep V M d L hV hmV hd hdim (by simpa only [hcard] using hL) hpow
      let N := max Q H
      have hMR : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
      have hHhalf : (H : ℝ) ≤ (M : ℝ) / 2 := by
        have hh : (2 : ℝ) * (H : ℝ) < M := by exact_mod_cast hMlarge
        linarith
      have hNhalf : (N : ℝ) ≤ (M : ℝ) / 2 := by
        dsimp [N]
        rw [Nat.cast_max]
        exact max_le (hQheight.trans hhalf) hHhalf
      have hNlt : N < M := by
        have hh : (N : ℝ) < M := by linarith
        exact_mod_cast hh
      have hNpos : 0 < N := lt_of_lt_of_le hHpos (le_max_right Q H)
      have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
      have hUN : ∀ u ∈ U, 0 < u ∧ u ≤ N := by
        intro u hu
        exact ⟨(hUbounds u hu).1, (hUbounds u hu).2.trans (le_max_left Q H)⟩
      obtain ⟨W, hWcard, hWbounds, hWdim, hWcover⟩ :=
        ih N hNlt U (δ + 4 * (d : ℝ) / (L : ℝ)) (hUcard.trans hcard) hUN hUdim
          (hstep δ hcover)
      have hgap := bedertModel_potential_gap d hd hNR hNhalf
      have hpay : 4 * (d : ℝ) / (L : ℝ) ≤
          bedertModelPotential d (N : ℝ) - bedertModelPotential d (M : ℝ) :=
        herr.trans hgap
      have hmaxN : max N H = N := max_eq_left (le_max_right Q H)
      have hmaxM : max M H = M := max_eq_left (by omega)
      refine ⟨W, hWcard, hWbounds, hWdim, ?_⟩
      intro t
      obtain ⟨w, hw, hwt⟩ := hWcover t
      change dist (w • t) 0 ≤ (δ + 4 * (d : ℝ) / (L : ℝ)) +
        bedertModelPotential d (H : ℝ) - bedertModelPotential d ((max N H : ℕ) : ℝ) at hwt
      rw [hmaxN] at hwt
      refine ⟨w, hw, ?_⟩
      change dist (w • t) 0 ≤ δ + bedertModelPotential d (H : ℝ) -
        bedertModelPotential d ((max M H : ℕ) : ℝ)
      rw [hmaxM]
      linarith

/-- 最终低高度模型。常数 `2048`、误差 `m^(-100)` 均实际证明；
不以待证明模型界或累计误差作为参数。只要求原族具有逐点距离覆盖界。 -/
theorem bedertLowDimensionModel (V : Finset ℕ) (d : ℕ)
    (hV : ∀ v ∈ V, 0 < v) (hm : 2 ≤ V.card) (hd : 1 ≤ d) (hdm : d ≤ V.card)
    (hdim : twoDissociatedDimension (V.image (fun v : ℕ => (v : ℤ))) ≤ d)
    (δ : ℝ) (hcover : ∀ t : UnitAddCircle, ∃ v ∈ V, dist (v • t) 0 ≤ δ) :
    ∃ (W : Finset ℕ) (T : ℕ), 0 < T ∧ W.card = V.card ∧
      (∀ w ∈ W, 1 ≤ w ∧ w ≤ T) ∧
      twoDissociatedDimension (W.image (fun w : ℕ => (w : ℤ))) ≤ d ∧
      Real.log (T : ℝ) ≤ 2048 * (d : ℝ) * Real.log (2 * (V.card : ℝ)) ∧
      ∀ t : UnitAddCircle, ∃ w ∈ W,
        dist (w • t) 0 ≤ δ + (V.card : ℝ)^(-100 : ℝ) := by
  classical
  let M := V.sup id
  let H := bedertModelThreshold V.card d
  have hmpos : 0 < V.card := by omega
  have hdpos : 0 < d := by omega
  have hbound : ∀ v ∈ V, 0 < v ∧ v ≤ M :=
    fun v hv => ⟨hV v hv, Finset.le_sup (f := id) hv⟩
  obtain ⟨W, hWcard, hWbounds, hWdim, hWcover⟩ :=
    bedertLowDimensionModel_iterate V.card d hm hd M V δ rfl hbound hdim hcover
  have hHpos : 0 < H := by dsimp [H, bedertModelThreshold]; positivity
  refine ⟨W, 2 * H, by positivity, hWcard, hWbounds, hWdim,
    bedertModel_threshold_log V.card d hm hd hdm, ?_⟩
  have herr := bedertModel_threshold_error V.card d hm hd
  have hnonneg : 0 ≤ bedertModelPotential d ((max M H : ℕ) : ℝ) := by
    unfold bedertModelPotential
    positivity
  intro t
  obtain ⟨w, hw, hwt⟩ := hWcover t
  exact ⟨w, hw, hwt.trans (by linarith)⟩

#print axioms bedertLowDimensionModel_iterate
#print axioms bedertLowDimensionModel

end LonelyRunner
