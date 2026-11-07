import LonelyRunnerNew.Definitions
import Mathlib.Dynamics.Ergodic.AddCircle
import Mathlib.Tactic.Linarith

noncomputable section
open MeasureTheory Set Metric

namespace LonelyRunnerNew

def forbidden (v : ℕ) (r : ℝ) : Set ℝ :=
  {t | ∃ k : ℤ, |(v : ℝ) * t - (k : ℝ)| ≤ r}

def forbiddenInUnit (v : ℕ) (r : ℝ) : Set ℝ := Ico 0 1 ∩ forbidden v r

theorem forbidden_eq_circle_preimage (v : ℕ) (r : ℝ) :
    forbidden v r = (fun t : ℝ => v • (t : UnitAddCircle)) ⁻¹'
      closedBall (0 : UnitAddCircle) r := by
  ext t
  have h := Set.ext_iff.mp
    (AddCircle.coe_real_preimage_closedBall_eq_iUnion (p := (1 : ℝ)) 0 r)
    ((v : ℝ) * t)
  have heq : (((v : ℝ) * t : ℝ) : UnitAddCircle) = v • (t : UnitAddCircle) := by
    simpa only [nsmul_eq_mul] using (AddCircle.coe_nsmul (1 : ℝ) (n := v) (x := t))
  simpa only [forbidden, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_iUnion,
    mem_closedBall, Real.dist_eq, zero_add, zsmul_eq_mul, mul_one,
    AddCircle.coe_zero, heq] using h.symm

theorem measurePreserving_speed (v : ℕ) (hv : 0 < v) :
    MeasurePreserving (fun t : ℝ => v • (t : UnitAddCircle))
      (volume.restrict (Ico 0 1)) volume := by
  have hq : MeasurePreserving ((↑) : ℝ → UnitAddCircle)
      (volume.restrict (Ico 0 1)) volume := by
    rw [restrict_Ico_eq_restrict_Ioc]
    simpa using AddCircle.measurePreserving_mk (T := (1 : ℝ)) 0
  have hm : MeasurePreserving (fun t : UnitAddCircle => v • t) volume volume := by
    have h := Measure.measurePreserving_zsmul (volume : Measure UnitAddCircle)
      (by exact_mod_cast hv.ne' : (v : ℤ) ≠ 0)
    simpa using h
  exact hm.comp hq

theorem forbidden_measurable (v : ℕ) (hv : 0 < v) (r : ℝ) :
    MeasurableSet (forbidden v r) := by
  rw [forbidden_eq_circle_preimage]
  exact (measurePreserving_speed v hv).measurable measurableSet_closedBall

theorem forbiddenInUnit_measurable (v : ℕ) (hv : 0 < v) (r : ℝ) :
    MeasurableSet (forbiddenInUnit v r) :=
  measurableSet_Ico.inter (forbidden_measurable v hv r)

/-- The exact single-speed closed forbidden measure, including both endpoint radii. -/
theorem forbiddenInUnit_measure (v : ℕ) (hv : 0 < v) (r : ℝ)
    (_hr0 : 0 ≤ r) (hrhalf : r ≤ 1 / 2) :
    volume (forbiddenInUnit v r) = ENNReal.ofReal (2 * r) := by
  have hp := (measurePreserving_speed v hv).measure_preimage
    (s := closedBall (0 : UnitAddCircle) r) measurableSet_closedBall.nullMeasurableSet
  rw [Measure.restrict_apply ((measurePreserving_speed v hv).measurable
    measurableSet_closedBall), AddCircle.volume_closedBall,
    min_eq_right (by linarith : 2 * r ≤ (1 : ℝ))] at hp
  simpa only [forbiddenInUnit, forbidden_eq_circle_preimage, Set.inter_comm] using hp

end LonelyRunnerNew
