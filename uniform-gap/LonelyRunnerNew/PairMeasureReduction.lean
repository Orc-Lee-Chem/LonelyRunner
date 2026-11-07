import LonelyRunnerNew.SingleSpeedMeasure
import LonelyRunnerNew.ForbiddenCommonCenter

noncomputable section
set_option autoImplicit false
open MeasureTheory Set Metric
namespace LonelyRunnerNew

def circlePairSet (a b : ℕ) (r : ℝ) : Set UnitAddCircle :=
  {z | a • z∈closedBall 0 r ∧ b • z∈closedBall 0 r}

theorem circlePairSet_measurable (a b : ℕ) (r : ℝ) :
    MeasurableSet (circlePairSet a b r) := by
  have ha : Continuous (fun z : UnitAddCircle => a • z) := continuous_id.nsmul a
  have hb : Continuous (fun z : UnitAddCircle => b • z) := continuous_id.nsmul b
  have hA : IsClosed ((fun z : UnitAddCircle => a • z) ⁻¹' closedBall (0:UnitAddCircle) r) :=
    isClosed_closedBall.preimage ha
  have hB : IsClosed ((fun z : UnitAddCircle => b • z) ⁻¹' closedBall (0:UnitAddCircle) r) :=
    isClosed_closedBall.preimage hb
  exact (hA.inter hB).measurableSet

theorem pair_measure_mul (d a b : ℕ) (hd : 0<d) (r : ℝ) :
    volume (forbiddenInUnit (d*a) r∩forbiddenInUnit (d*b) r)=
      volume (forbiddenInUnit a r∩forbiddenInUnit b r) := by
  have main (e : ℕ) (he : 0<e) :
      volume (forbiddenInUnit (e*a) r∩forbiddenInUnit (e*b) r)=
        volume (circlePairSet a b r) := by
    have hm := measurePreserving_speed e he
    have hme := hm.measurable (circlePairSet_measurable a b r)
    have hh := hm.measure_preimage (circlePairSet_measurable a b r).nullMeasurableSet
    rw [Measure.restrict_apply hme] at hh
    have hset : (fun t : ℝ => e • (t:UnitAddCircle)) ⁻¹' circlePairSet a b r∩Ico 0 1=
        forbiddenInUnit (e*a) r∩forbiddenInUnit (e*b) r := by
      simp only [forbiddenInUnit,forbidden_eq_circle_preimage]
      ext t
      simp only [Set.mem_inter_iff,Set.mem_preimage,circlePairSet,Set.mem_setOf_eq]
      simp only [smul_smul,Nat.mul_comm a e,Nat.mul_comm b e]
      tauto
    rwa [hset] at hh
  rw [main d hd]
  simpa using (main 1 (by norm_num)).symm

theorem pair_measure_gcd (u v : ℕ) (hu : 0<u) (r : ℝ) :
    volume (forbiddenInUnit u r∩forbiddenInUnit v r)=
      volume (forbiddenInUnit (u/Nat.gcd u v) r∩forbiddenInUnit (v/Nat.gcd u v) r) := by
  have hd : 0<Nat.gcd u v := Nat.gcd_pos_of_pos_left v hu
  have hU : Nat.gcd u v*(u/Nat.gcd u v)=u := Nat.mul_div_cancel' (Nat.gcd_dvd_left u v)
  have hV : Nat.gcd u v*(v/Nat.gcd u v)=v := Nat.mul_div_cancel' (Nat.gcd_dvd_right u v)
  simpa only [hU,hV] using pair_measure_mul (Nat.gcd u v) (u/Nat.gcd u v) (v/Nat.gcd u v) hd r

end LonelyRunnerNew
