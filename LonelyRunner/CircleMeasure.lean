import LonelyRunner.PrimeGridCover
import Mathlib.Dynamics.Ergodic.AddCircle
import Mathlib.Analysis.Fourier.AddCircle

/-! 论文 `paper/lonely_runner_zh.tex` 第 74–83、94、97–100 行：
现有闭 Bohr 集与圆周距离的等价，以及归一化 Haar 测度。 -/

namespace LonelyRunner

open Metric MeasureTheory

/-- 论文第 74–83 行：项目原有闭弧 `[-δ,δ]` 与圆周闭球一致。
端点包含在两边，允许 `δ=0`。 -/
theorem closedArc_symm_eq_closedBall (δ : ℝ) (_hδ0 : 0 ≤ δ)
    (hδhalf : δ < 1 / 2) :
    closedArc (-δ) (2 * δ) = closedBall (0 : UnitAddCircle) δ := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, ⟨hylo, hyhi⟩, rfl⟩ := hx
    have hyhi' : y ≤ δ := by linarith
    have habs : |y| ≤ δ := abs_le.mpr ⟨hylo, hyhi'⟩
    have hhalf : |y| ≤ |(1 : ℝ)| / 2 := by
      rw [abs_one]
      linarith
    have hnorm : ‖(y : UnitAddCircle)‖ = |y| :=
      (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).2 hhalf
    simpa only [mem_closedBall, dist_zero_right, hnorm] using habs
  · intro hx
    induction x using Quotient.inductionOn with
    | _ z =>
      let y : ℝ := z - (round z : ℝ)
      have hnorm : ‖(z : UnitAddCircle)‖ = |y| := by
        simpa [y] using (AddCircle.norm_eq (1 : ℝ) (x := z))
      have habs : |y| ≤ δ := by
        simpa only [mem_closedBall, dist_zero_right, hnorm] using hx
      have hcast : (y : UnitAddCircle) = (z : UnitAddCircle) := by
        have hint : (((round z : ℤ) : ℝ) : UnitAddCircle) = 0 := by
          apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).2
          refine ⟨round z, ?_⟩
          simp [zsmul_eq_mul]
        simp [y, hint]
      change (z : UnitAddCircle) ∈ closedArc (-δ) (2 * δ)
      refine ⟨y, ?_, hcast⟩
      change -δ ≤ y ∧ y ≤ -δ + 2 * δ
      rcases abs_le.mp habs with ⟨hlo, hhi⟩
      constructor <;> linarith

/-- 论文第 74–83 行：现有 `bohrSet` 的成员条件等价于圆周距离条件。
此处直接连接原有闭弧定义，没有重定义 Bohr 集。 -/
theorem mem_bohrSet_iff_dist (v : ℕ) (δ : ℝ)
    (hδ0 : 0 ≤ δ) (hδhalf : δ < 1 / 2) (t : UnitAddCircle) :
    t ∈ bohrSet v δ ↔ dist (v • t) 0 ≤ δ := by
  rw [bohrSet, closedArc_symm_eq_closedBall δ hδ0 hδhalf]
  simp only [Set.mem_ofPred_eq, mem_closedBall]

/-- 论文第 94、97–100 行：单位圆周上的归一化 Haar 概率测度。 -/
noncomputable def circleHaar : Measure UnitAddCircle := AddCircle.haarAddCircle

/-- 论文第 94 行：选定的 Haar 测度总质量为 1。 -/
instance : IsProbabilityMeasure circleHaar := by
  unfold circleHaar
  infer_instance

instance : circleHaar.IsAddHaarMeasure := by
  unfold circleHaar
  infer_instance

/-- 论文第 97–100 行：正整数倍映射保持归一化 Haar 概率测度。 -/
theorem circleHaar_measurePreserving_nsmul (v : ℕ) (hv : 0 < v) :
    MeasurePreserving (fun t : UnitAddCircle => v • t) circleHaar circleHaar := by
  have hh : MeasurePreserving (fun t : UnitAddCircle => (v : ℤ) • t)
      circleHaar circleHaar :=
    Measure.measurePreserving_zsmul circleHaar (by exact_mod_cast hv.ne')
  simpa using hh

/-- 论文第 94 行：单位周期为 1，所以标准圆周体积恰是归一化 Haar 测度。 -/
theorem circleHaar_eq_volume : circleHaar = (volume : Measure UnitAddCircle) := by
  unfold circleHaar
  have h := AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ))
  simpa using h.symm

/-- 论文第 74–83 行：正速度的原有闭 Bohr 集可测，测度为 `2δ`。
证明使用上面的闭弧等价及整数倍映射的保测性。 -/
theorem bohrSet_measurable_measure (v : ℕ) (δ : ℝ)
    (hv : 0 < v) (hδ0 : 0 < δ) (hδhalf : δ < 1 / 2) :
    MeasurableSet (bohrSet v δ) ∧
      circleHaar (bohrSet v δ) = ENNReal.ofReal (2 * δ) := by
  have hset : bohrSet v δ =
      (fun t : UnitAddCircle => v • t) ⁻¹' closedBall (0 : UnitAddCircle) δ := by
    ext t
    exact mem_bohrSet_iff_dist v δ hδ0.le hδhalf t
  have hmeas : MeasurableSet (bohrSet v δ) := by
    rw [hset]
    exact (isClosed_closedBall.preimage (continuous_nsmul v)).measurableSet
  refine ⟨hmeas, ?_⟩
  rw [hset, (circleHaar_measurePreserving_nsmul v hv).measure_preimage
    measurableSet_closedBall.nullMeasurableSet, circleHaar_eq_volume,
    AddCircle.volume_closedBall]
  rw [min_eq_right (by linarith : 2 * δ ≤ (1 : ℝ))]

#print axioms LonelyRunner.bohrSet_measurable_measure

end LonelyRunner
