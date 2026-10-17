import LonelyRunner.CircleFejerMoment

/-! # 圆周闭弧的平移误差 -/
namespace LonelyRunner
open MeasureTheory Metric

private theorem closedArc_eq_closedBall (s ℓ : ℝ) (hℓ0 : 0 ≤ ℓ) (hℓ1 : ℓ < 1) :
    closedArc s ℓ = closedBall ((s + ℓ / 2 : ℝ) : UnitAddCircle) (ℓ / 2) := by
  let c : ℝ := s + ℓ / 2
  let δ : ℝ := ℓ / 2
  have hδ0 : 0 ≤ δ := by dsimp [δ]; linarith
  have hδhalf : δ < 1 / 2 := by dsimp [δ]; linarith
  have hsym := closedArc_symm_eq_closedBall δ hδ0 hδhalf
  ext t
  change (∃ x : ℝ, x ∈ Set.Icc s (s+ℓ) ∧ (x : UnitAddCircle) = t) ↔
    t ∈ closedBall (c : UnitAddCircle) δ
  have hcenter : (t ∈ closedBall (c : UnitAddCircle) δ) ↔
      t - (c : UnitAddCircle) ∈ closedBall 0 δ := by
    simp only [mem_closedBall, dist_eq_norm, sub_zero]
  rw [hcenter]
  rw [← hsym]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x-c, ?_, ?_⟩
    · change -δ ≤ x-c ∧ x-c ≤ -δ + 2*δ
      constructor <;> dsimp [c,δ] <;> linarith [hx.1,hx.2]
    · change ((x-c : ℝ) : UnitAddCircle) = (x : UnitAddCircle) - (c : UnitAddCircle)
      push_cast
      rfl
  · rintro ⟨y, hy, hyt⟩
    refine ⟨c+y, ?_, ?_⟩
    · change s ≤ c+y ∧ c+y ≤ s+ℓ
      have hy' : -δ ≤ y ∧ y ≤ -δ + 2*δ := hy
      constructor <;> dsimp [c,δ] at * <;> linarith [hy'.1,hy'.2]
    · calc
        ((c+y : ℝ) : UnitAddCircle) = (c : UnitAddCircle) + (y : UnitAddCircle) := by push_cast; rfl
        _ = t := by
          change (y : UnitAddCircle) = t - (c : UnitAddCircle) at hyt
          rw [hyt]
          abel

/-- 论文 `lem:smoothing` 区间误差步骤：长度小于一的闭圆周弧可测。 -/
theorem closedArc_measurable (s ℓ : ℝ) (hℓ0 : 0 ≤ ℓ) (hℓ1 : ℓ < 1) :
    MeasurableSet (closedArc s ℓ) := by
  rw [closedArc_eq_closedBall s ℓ hℓ0 hℓ1]
  exact measurableSet_closedBall

theorem closedArc_measure_real (s ℓ : ℝ) (hℓ0 : 0 ≤ ℓ) (hℓ1 : ℓ < 1) :
    circleHaar.real (closedArc s ℓ) = ℓ := by
  rw [closedArc_eq_closedBall s ℓ hℓ0 hℓ1, circleHaar_eq_volume]
  rw [measureReal_def, AddCircle.volume_closedBall]
  have hmin : min (1 : ℝ) (2 * (ℓ / 2)) = ℓ := by
    rw [min_eq_right (by linarith)]
    ring
  rw [hmin]
  exact ENNReal.toReal_ofReal hℓ0

private theorem closedArc_shift_membership (s ℓ y : ℝ) (t : UnitAddCircle) :
    t - (y : UnitAddCircle) ∈ closedArc s ℓ ↔
      t ∈ closedArc (s+y) ℓ := by
  constructor
  · rintro ⟨x, hx, hxt⟩
    refine ⟨x+y, ?_, ?_⟩
    · change s+y ≤ x+y ∧ x+y ≤ s+y+ℓ
      constructor <;> linarith [hx.1,hx.2]
    · change ((x+y : ℝ) : UnitAddCircle) = t
      rw [show ((x+y : ℝ) : UnitAddCircle) = (x : UnitAddCircle) + (y : UnitAddCircle) by push_cast; rfl]
      change (x : UnitAddCircle) = t - (y : UnitAddCircle) at hxt
      rw [hxt]
      abel
  · rintro ⟨x, hx, hxt⟩
    refine ⟨x-y, ?_, ?_⟩
    · change s ≤ x-y ∧ x-y ≤ s+ℓ
      constructor <;> linarith [hx.1,hx.2]
    · change ((x-y : ℝ) : UnitAddCircle) = t - (y : UnitAddCircle)
      rw [show ((x-y : ℝ) : UnitAddCircle) = (x : UnitAddCircle) - (y : UnitAddCircle) by push_cast; rfl]
      change (x : UnitAddCircle) = t at hxt
      rw [hxt]

private theorem closedArc_left_sweep (s ℓ y : ℝ) (hy : 0 ≤ y) :
    closedArc s ℓ \ closedArc (s+y) ℓ ⊆ closedArc s y := by
  rintro t ⟨ht, hnot⟩
  obtain ⟨x, hx, rfl⟩ := ht
  by_contra hnotSweep
  have hxy : s+y ≤ x := by
    by_contra h
    have hlt : x < s+y := lt_of_not_ge h
    apply hnotSweep
    exact ⟨x, ⟨hx.1, hlt.le⟩, rfl⟩
  apply hnot
  exact ⟨x, ⟨hxy, by linarith [hx.2]⟩, rfl⟩

private theorem closedArc_right_sweep (s ℓ y : ℝ) (hy : 0 ≤ y) :
    closedArc (s+y) ℓ \ closedArc s ℓ ⊆ closedArc (s+ℓ) y := by
  rintro t ⟨ht, hnot⟩
  obtain ⟨x, hx, rfl⟩ := ht
  by_contra hnotSweep
  have hxy : s+ℓ ≤ x := by
    by_contra h
    have hlt : x < s+ℓ := lt_of_not_ge h
    apply hnot
    exact ⟨x, ⟨by linarith [hx.1, hy], hlt.le⟩, rfl⟩
  apply hnotSweep
  exact ⟨x, ⟨hxy, by linarith [hx.2]⟩, rfl⟩

private theorem circleIndicator_abs_diff (A B : Set UnitAddCircle) (t : UnitAddCircle) :
    |circleSetIndicator A t - circleSetIndicator B t| =
      circleSetIndicator ((A \ B) ∪ (B \ A)) t := by
  by_cases ha : t ∈ A <;> by_cases hb : t ∈ B <;>
    simp [circleSetIndicator, ha, hb]

theorem circleIndicator_abs_diff_integral (A B : Set UnitAddCircle)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (∫ t : UnitAddCircle,
      |circleSetIndicator A t - circleSetIndicator B t| ∂circleHaar) =
      circleHaar.real ((A \ B) ∪ (B \ A)) := by
  simp_rw [circleIndicator_abs_diff]
  exact integral_indicator_one ((hA.diff hB).union (hB.diff hA))

private theorem closedArc_shift_symmDiff_pos (s ℓ y : ℝ)
    (hℓ0 : 0 ≤ ℓ) (hℓ1 : ℓ < 1) (hy0 : 0 ≤ y) (hyhalf : y ≤ 1 / 2) :
    circleHaar.real ((closedArc s ℓ \ closedArc (s+y) ℓ) ∪
      (closedArc (s+y) ℓ \ closedArc s ℓ)) ≤ 2*y := by
  have hy1 : y < 1 := by linarith
  have hsubset : ((closedArc s ℓ \ closedArc (s+y) ℓ) ∪
      (closedArc (s+y) ℓ \ closedArc s ℓ)) ⊆
      closedArc s y ∪ closedArc (s+ℓ) y := by
    exact Set.union_subset_union (closedArc_left_sweep s ℓ y hy0)
      (closedArc_right_sweep s ℓ y hy0)
  calc
    circleHaar.real ((closedArc s ℓ \ closedArc (s+y) ℓ) ∪
      (closedArc (s+y) ℓ \ closedArc s ℓ)) ≤
        circleHaar.real (closedArc s y ∪ closedArc (s+ℓ) y) :=
          measureReal_mono hsubset (measure_ne_top circleHaar _)
    _ ≤ circleHaar.real (closedArc s y) + circleHaar.real (closedArc (s+ℓ) y) :=
      measureReal_union_le _ _
    _ = 2*y := by rw [closedArc_measure_real s y hy0 hy1,
      closedArc_measure_real (s+ℓ) y hy0 hy1]; ring

private theorem closedArc_shift_symmDiff_real (s ℓ y : ℝ)
    (hℓ0 : 0 ≤ ℓ) (hℓ1 : ℓ < 1) (hyhalf : |y| ≤ 1 / 2) :
    circleHaar.real ((closedArc s ℓ \ closedArc (s+y) ℓ) ∪
      (closedArc (s+y) ℓ \ closedArc s ℓ)) ≤ 2 * |y| := by
  rcases le_total 0 y with hy | hy
  · rw [abs_of_nonneg hy]
    exact closedArc_shift_symmDiff_pos s ℓ y hℓ0 hℓ1 hy (by simpa [abs_of_nonneg hy] using hyhalf)
  · have hy0 : 0 ≤ -y := by linarith
    have hyh : -y ≤ 1 / 2 := by simpa [abs_of_nonpos hy] using hyhalf
    have hs : s + y + -y = s := by ring
    simpa [abs_of_nonpos hy, hs, Set.union_comm] using
      (closedArc_shift_symmDiff_pos (s+y) ℓ (-y) hℓ0 hℓ1 hy0 hyh)

/-- 论文 `lem:smoothing` 区间误差步骤：单个闭弧的平移指标函数误差至多两倍平移距离。 -/
theorem closedArc_translation_L1 (s ℓ : ℝ) (u : UnitAddCircle)
    (hℓ0 : 0 ≤ ℓ) (hℓ1 : ℓ < 1) :
    (∫ t : UnitAddCircle,
      |circleSetIndicator (closedArc s ℓ) (t-u) -
       circleSetIndicator (closedArc s ℓ) t| ∂circleHaar) ≤
      2 * dist u 0 := by
  induction u using Quotient.inductionOn with
  | _ z =>
    let y : ℝ := z - (round z : ℝ)
    have hyhalf : |y| ≤ 1 / 2 := by
      simpa [y] using (abs_sub_round z)
    have hcast : (y : UnitAddCircle) = (z : UnitAddCircle) := by
      have hint : (((round z : ℤ) : ℝ) : UnitAddCircle) = 0 := by
        apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).2
        refine ⟨round z, ?_⟩
        simp [zsmul_eq_mul]
      simp [y, hint]
    have hdist : dist (z : UnitAddCircle) 0 = |y| := by
      simpa [dist_zero_right, y] using (AddCircle.norm_eq (1 : ℝ) (x := z))
    have hind : ∀ t : UnitAddCircle,
        circleSetIndicator (closedArc s ℓ) (t-(z:UnitAddCircle)) =
        circleSetIndicator (closedArc (s+y) ℓ) t := by
      intro t
      rw [← hcast]
      by_cases ht : t - (y : UnitAddCircle) ∈ closedArc s ℓ
      · have ht' := (closedArc_shift_membership s ℓ y t).1 ht
        simp [circleSetIndicator, ht, ht']
      · have ht' : t ∉ closedArc (s+y) ℓ := by
          exact fun h => ht ((closedArc_shift_membership s ℓ y t).2 h)
        simp [circleSetIndicator, ht, ht']
    simp_rw [hind]
    rw [circleIndicator_abs_diff_integral _ _
      (closedArc_measurable (s+y) ℓ hℓ0 hℓ1)
      (closedArc_measurable s ℓ hℓ0 hℓ1)]
    rw [hdist]
    simpa [Set.union_comm] using
      closedArc_shift_symmDiff_real s ℓ y hℓ0 hℓ1 hyhalf

/-- 有限族闭圆周弧的并；允许重叠与零长度。 -/
def circleArcUnion {ι : Type*} (J : Finset ι) (s ℓ : ι → ℝ) : Set UnitAddCircle :=
  ⋃ j ∈ J, closedArc (s j) (ℓ j)

/-- 论文 `lem:smoothing`：有限闭弧并可测。 -/
theorem circleArcUnion_measurable {ι : Type*} (J : Finset ι) (s ℓ : ι → ℝ)
    (hℓ : ∀ j ∈ J, 0 ≤ ℓ j ∧ ℓ j < 1) :
    MeasurableSet (circleArcUnion J s ℓ) := by
  exact J.measurableSet_biUnion (fun j hj =>
    closedArc_measurable (s j) (ℓ j) (hℓ j hj).1 (hℓ j hj).2)

private theorem circleArcUnion_shift_membership {ι : Type*} (J : Finset ι)
    (s ℓ : ι → ℝ) (y : ℝ) (t : UnitAddCircle) :
    t - (y : UnitAddCircle) ∈ circleArcUnion J s ℓ ↔
      t ∈ circleArcUnion J (fun j => s j+y) ℓ := by
  simp only [circleArcUnion, Set.mem_iUnion]
  constructor
  · rintro ⟨j, hj, ht⟩
    exact ⟨j, hj, (closedArc_shift_membership (s j) (ℓ j) y t).1 ht⟩
  · rintro ⟨j, hj, ht⟩
    exact ⟨j, hj, (closedArc_shift_membership (s j) (ℓ j) y t).2 ht⟩

private theorem symmDiff_union_subset {ι : Type*} (J : Finset ι)
    (A B : ι → Set UnitAddCircle) :
    (((⋃ j ∈ J, A j) \ (⋃ j ∈ J, B j)) ∪
     ((⋃ j ∈ J, B j) \ (⋃ j ∈ J, A j))) ⊆
      ⋃ j ∈ J, ((A j \ B j) ∪ (B j \ A j)) := by
  intro t ht
  rcases ht with ht | ht
  · obtain ⟨j, htA⟩ := Set.mem_iUnion.mp ht.1
    obtain ⟨hj, htA⟩ := Set.mem_iUnion.mp htA
    exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hj,
      Or.inl ⟨htA, fun hb => ht.2 (Set.mem_iUnion.mpr
        ⟨j, Set.mem_iUnion.mpr ⟨hj, hb⟩⟩)⟩⟩⟩
  · obtain ⟨j, htB⟩ := Set.mem_iUnion.mp ht.1
    obtain ⟨hj, htB⟩ := Set.mem_iUnion.mp htB
    exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hj,
      Or.inr ⟨htB, fun ha => ht.2 (Set.mem_iUnion.mpr
        ⟨j, Set.mem_iUnion.mpr ⟨hj, ha⟩⟩)⟩⟩⟩

/-- 有限并的指标函数差逐点不超过各个指标函数差之和；区间可以重叠。 -/
theorem circleIndicator_union_diff_le_sum {ι : Type*} (J : Finset ι)
    (A B : ι → Set UnitAddCircle) (t : UnitAddCircle) :
    |circleSetIndicator (⋃ j ∈ J, A j) t -
      circleSetIndicator (⋃ j ∈ J, B j) t| ≤
      ∑ j ∈ J, |circleSetIndicator (A j) t - circleSetIndicator (B j) t| := by
  rw [circleIndicator_abs_diff]
  let S : Set UnitAddCircle :=
    (((⋃ j ∈ J, A j) \ (⋃ j ∈ J, B j)) ∪
      ((⋃ j ∈ J, B j) \ (⋃ j ∈ J, A j)))
  by_cases ht : t ∈ S
  · have hmem : t ∈ ⋃ j ∈ J, ((A j \ B j) ∪ (B j \ A j)) :=
      symmDiff_union_subset J A B ht
    obtain ⟨j, hrest⟩ := Set.mem_iUnion.mp hmem
    obtain ⟨hj, hsingle⟩ := Set.mem_iUnion.mp hrest
    have hsum : (∀ j ∈ J,
        0 ≤ |circleSetIndicator (A j) t - circleSetIndicator (B j) t|) := by
      intro j hj
      positivity
    have hterm : |circleSetIndicator (A j) t - circleSetIndicator (B j) t| = 1 := by
      rw [circleIndicator_abs_diff]
      simp [circleSetIndicator, hsingle]
    calc
      circleSetIndicator S t = 1 := by simp [circleSetIndicator, ht]
      _ = |circleSetIndicator (A j) t - circleSetIndicator (B j) t| := hterm.symm
      _ ≤ ∑ j ∈ J,
        |circleSetIndicator (A j) t - circleSetIndicator (B j) t| :=
          Finset.single_le_sum hsum hj
  · have hzero : circleSetIndicator S t = 0 := by simp [circleSetIndicator, ht]
    simpa only [S, hzero] using
      (Finset.sum_nonneg (fun j hj => abs_nonneg
        (circleSetIndicator (A j) t - circleSetIndicator (B j) t)) :
        0 ≤ ∑ j ∈ J, |circleSetIndicator (A j) t - circleSetIndicator (B j) t|)

private theorem measureReal_biUnion_le_sum {ι : Type*} (J : Finset ι)
    (A : ι → Set UnitAddCircle) :
    circleHaar.real (⋃ j ∈ J, A j) ≤ ∑ j ∈ J, circleHaar.real (A j) := by
  classical
  induction J using Finset.induction_on with
  | empty => simp
  | @insert j J hj ih =>
    simp only [Finset.sum_insert hj]
    have heq : (⋃ k ∈ insert j J, A k) = A j ∪ (⋃ k ∈ J, A k) := by
      simp [Set.biUnion_insert]
    rw [heq]
    exact (measureReal_union_le _ _).trans (add_le_add_right ih _)

/-- 论文 `lem:smoothing`：有限闭弧并的平移 L¹ 误差，含空族及重叠。 -/
theorem circleArcUnion_translation_L1 {ι : Type*} (J : Finset ι)
    (s ℓ : ι → ℝ) (u : UnitAddCircle)
    (hℓ : ∀ j ∈ J, 0 ≤ ℓ j ∧ ℓ j < 1) :
    (∫ t : UnitAddCircle,
      |circleSetIndicator (circleArcUnion J s ℓ) (t-u) -
       circleSetIndicator (circleArcUnion J s ℓ) t| ∂circleHaar) ≤
      2 * (J.card : ℝ) * dist u 0 := by
  induction u using Quotient.inductionOn with
  | _ z =>
    let y : ℝ := z - (round z : ℝ)
    have hyhalf : |y| ≤ 1 / 2 := by simpa [y] using (abs_sub_round z)
    have hcast : (y : UnitAddCircle) = (z : UnitAddCircle) := by
      have hint : (((round z : ℤ) : ℝ) : UnitAddCircle) = 0 := by
        apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).2
        refine ⟨round z, ?_⟩
        simp [zsmul_eq_mul]
      simp [y, hint]
    have hdist : dist (z : UnitAddCircle) 0 = |y| := by
      simpa [dist_zero_right, y] using (AddCircle.norm_eq (1 : ℝ) (x := z))
    have hind : ∀ t : UnitAddCircle,
        circleSetIndicator (circleArcUnion J s ℓ) (t-(z:UnitAddCircle)) =
        circleSetIndicator (circleArcUnion J (fun j => s j+y) ℓ) t := by
      intro t
      rw [← hcast]
      by_cases ht : t - (y : UnitAddCircle) ∈ circleArcUnion J s ℓ
      · have ht' := (circleArcUnion_shift_membership J s ℓ y t).1 ht
        simp [circleSetIndicator, ht, ht']
      · have ht' : t ∉ circleArcUnion J (fun j => s j+y) ℓ := by
          exact fun h => ht ((circleArcUnion_shift_membership J s ℓ y t).2 h)
        simp [circleSetIndicator, ht, ht']
    simp_rw [hind]
    rw [circleIndicator_abs_diff_integral _ _
      (circleArcUnion_measurable J (fun j => s j+y) ℓ hℓ)
      (circleArcUnion_measurable J s ℓ hℓ), hdist]
    let A : ι → Set UnitAddCircle := fun j => closedArc (s j) (ℓ j)
    let B : ι → Set UnitAddCircle := fun j => closedArc (s j+y) (ℓ j)
    have hsubset := symmDiff_union_subset J B A
    have hmono : circleHaar.real (((⋃ j ∈ J, B j) \ (⋃ j ∈ J, A j)) ∪
      ((⋃ j ∈ J, A j) \ (⋃ j ∈ J, B j))) ≤
        circleHaar.real (⋃ j ∈ J, ((B j \ A j) ∪ (A j \ B j))) :=
      measureReal_mono hsubset (measure_ne_top circleHaar _)
    have hsum := measureReal_biUnion_le_sum J (fun j => (B j \ A j) ∪ (A j \ B j))
    have hterm : ∀ j ∈ J,
        circleHaar.real ((B j \ A j) ∪ (A j \ B j)) ≤ 2 * |y| := by
      intro j hj
      simpa [A, B, Set.union_comm] using
        closedArc_shift_symmDiff_real (s j) (ℓ j) y (hℓ j hj).1 (hℓ j hj).2 hyhalf
    have htotal : (∑ j ∈ J, circleHaar.real ((B j \ A j) ∪ (A j \ B j))) ≤
      ∑ j ∈ J, 2 * |y| := Finset.sum_le_sum hterm
    calc
      circleHaar.real ((circleArcUnion J (fun j => s j+y) ℓ \
        circleArcUnion J s ℓ) ∪
        (circleArcUnion J s ℓ \ circleArcUnion J (fun j => s j+y) ℓ)) ≤
          circleHaar.real (⋃ j ∈ J, ((B j \ A j) ∪ (A j \ B j))) := by
            simpa only [A, B, circleArcUnion] using hmono
      _ ≤ ∑ j ∈ J, circleHaar.real ((B j \ A j) ∪ (A j \ B j)) := hsum
      _ ≤ ∑ j ∈ J, 2 * |y| := htotal
      _ = 2 * (J.card : ℝ) * |y| := by simp; ring

#print axioms circleArcUnion_translation_L1

end LonelyRunner

