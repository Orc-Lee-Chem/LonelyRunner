import LonelyRunner.PrimePowerAllocation
import LonelyRunner.CoverMultiplicity

/-! # 论文 `lem:exceptions`：核心 Bohr 并集的网格平均 -/
namespace LonelyRunner
open MeasureTheory

private noncomputable def coreShift (G a : ℕ) : UnitAddCircle :=
  (((a : ℝ) / (G : ℝ)) : UnitAddCircle)

private theorem coreShift_nsmul_zero (G a : ℕ) (hG : 0 < G) :
    G • coreShift G a = 0 := by
  have hGR : (G : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hG)
  change G • (((a : ℝ) / (G : ℝ)) : UnitAddCircle) = 0
  rw [← AddCircle.coe_nsmul]
  rw [nsmul_eq_mul]
  change ((((G : ℝ) * ((a : ℝ) / (G : ℝ))) : ℝ) : UnitAddCircle) = 0
  have hreal : (G : ℝ) * ((a : ℝ) / (G : ℝ)) = (a : ℝ) := by
    field_simp
  rw [hreal]
  apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).2
  refine ⟨(a : ℤ), ?_⟩
  simp [zsmul_eq_mul]

/-- 论文 `lem:exceptions` 第 596 行：核心并集在 `a/G` 的平移下逐点不变。 -/
theorem bohrUnion_coreShift (C : Finset ℕ) (G a : ℕ) (δ : ℝ)
    (hG : 0 < G) (hC : ∀ c ∈ C, G ∣ c) (t : UnitAddCircle) :
    t + coreShift G a ∈ bohrUnion C δ ↔ t ∈ bohrUnion C δ := by
  have hzero (c : ℕ) (hc : c ∈ C) : c • coreShift G a = 0 := by
    obtain ⟨k, rfl⟩ := hC c hc
    rw [mul_nsmul, coreShift_nsmul_zero G a hG]
    simp
  simp only [bohrUnion, Set.mem_iUnion]
  constructor
  · rintro ⟨c, hc, ht⟩
    refine ⟨c, hc, ?_⟩
    simpa only [bohrSet, Set.mem_setOf_eq, nsmul_add, hzero c hc, add_zero] using ht
  · rintro ⟨c, hc, ht⟩
    refine ⟨c, hc, ?_⟩
    simpa only [bohrSet, Set.mem_setOf_eq, nsmul_add, hzero c hc, add_zero] using ht

private theorem coreShift_velocity_grid (G v a : ℕ) (hG : 0 < G) :
    let q := reducedDenominator G v
    let u := v / Nat.gcd G v
    haveI : NeZero q := ⟨Nat.ne_of_gt (reducedDenominator_pos_dvd G v hG).1⟩
    v • coreShift G a = ZMod.toAddCircle ((u * a : ℕ) : ZMod q) := by
  let q := reducedDenominator G v
  let u := v / Nat.gcd G v
  letI : NeZero q := ⟨Nat.ne_of_gt (reducedDenominator_pos_dvd G v hG).1⟩
  let d := Nat.gcd G v
  have hd : 0 < d := Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left G v) hG
  have hdG : d ∣ G := Nat.gcd_dvd_left G v
  have hdv : d ∣ v := Nat.gcd_dvd_right G v
  have hGmul : q * d = G := Nat.div_mul_cancel hdG
  have hvmul : u * d = v := Nat.div_mul_cancel hdv
  have hqreal : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt
    (reducedDenominator_pos_dvd G v hG).1)
  have hdreal : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
  have hreal : (v : ℝ) * ((a : ℝ) / (G : ℝ)) =
      ((u * a : ℕ) : ℝ) / (q : ℝ) := by
    have hGr : (G : ℝ) = (q : ℝ) * (d : ℝ) := by exact_mod_cast hGmul.symm
    have hvr : (v : ℝ) = (u : ℝ) * (d : ℝ) := by exact_mod_cast hvmul.symm
    rw [hGr, hvr]
    push_cast
    field_simp
  change v • coreShift G a = ZMod.toAddCircle ((u * a : ℕ) : ZMod q)
  rw [ZMod.toAddCircle_natCast]
  change v • (((a : ℝ) / (G : ℝ)) : UnitAddCircle) = _
  rw [← AddCircle.coe_nsmul, nsmul_eq_mul]
  change (((v : ℝ) * ((a : ℝ) / (G : ℝ)) : ℝ) : UnitAddCircle) =
    ((((u * a : ℕ) : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle)
  exact congrArg (fun x : ℝ => (x : UnitAddCircle)) hreal

private theorem reducedDenominator_coprime (G v : ℕ) (hG : 0 < G) :
    Nat.Coprime (v / Nat.gcd G v) (reducedDenominator G v) := by
  have hd : 0 < Nat.gcd v G :=
    Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_right v G) hG
  simpa [reducedDenominator, Nat.gcd_comm] using
    (Nat.coprime_div_gcd_div_gcd (m := v) (n := G) hd)

private noncomputable def coreShiftHits (G v : ℕ) (δ : ℝ)
    (t : UnitAddCircle) : Finset ℕ := by
  classical
  exact (Finset.range (reducedDenominator G v)).filter
    (fun a => t + coreShift G a ∈ bohrSet v δ)

/-- 论文 `lem:exceptions` 第 599 行：`q` 个平移经既约分子作用后恰好置换全部余类。 -/
theorem coreShift_grid_count (G v : ℕ) (hG : 0 < G) (δ : ℝ)
    (t : UnitAddCircle) :
    let q := reducedDenominator G v
    haveI : NeZero q := ⟨Nat.ne_of_gt (reducedDenominator_pos_dvd G v hG).1⟩
    (coreShiftHits G v δ t).card =
      (circleGridResidues q (v • t) (-δ) (2 * δ)).card := by
  classical
  let q := reducedDenominator G v
  let u := v / Nat.gcd G v
  letI : NeZero q := ⟨Nat.ne_of_gt (reducedDenominator_pos_dvd G v hG).1⟩
  let e : ZMod q ≃ ZMod q :=
    (ZMod.unitOfCoprime u (reducedDenominator_coprime G v hG)).mulLeft
  have he (a : ℕ) : e (a : ZMod q) = ((u * a : ℕ) : ZMod q) := by
    simp [e, Nat.cast_mul]
  have hpoint (a : ℕ) :
      (t + coreShift G a ∈ bohrSet v δ) ↔
        (v • t + ZMod.toAddCircle ((u * a : ℕ) : ZMod q) ∈
          closedArc (-δ) (2 * δ)) := by
    change v • (t + coreShift G a) ∈ closedArc (-δ) (2 * δ) ↔ _
    rw [nsmul_add, coreShift_velocity_grid G v a hG]
  change ((Finset.range q).filter (fun a => t + coreShift G a ∈ bohrSet v δ)).card =
    (circleGridResidues q (v • t) (-δ) (2 * δ)).card
  apply Finset.card_bij (fun (a : ℕ) _ => e (a : ZMod q))
  · intro a ha
    change e (a : ZMod q) ∈ Finset.univ.filter
      (fun b => v • t + ZMod.toAddCircle b ∈ closedArc (-δ) (2 * δ))
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [he]
    exact (hpoint a).1 (Finset.mem_filter.mp ha).2
  · intro a ha b hb heq
    have hab : (a : ZMod q) = (b : ZMod q) := e.injective heq
    have ha' : a < q := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
    have hb' : b < q := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
    calc
      a = (a : ZMod q).val := (ZMod.val_natCast_of_lt ha').symm
      _ = (b : ZMod q).val := congrArg ZMod.val hab
      _ = b := ZMod.val_natCast_of_lt hb'
  · intro b hb
    let a : ℕ := (e.symm b).val
    have ha : a < q := ZMod.val_lt _
    have heq : e (a : ZMod q) = b := by
      simpa [a, ZMod.natCast_zmod_val] using e.apply_symm_apply b
    refine ⟨a, ?_, heq⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ha, ?_⟩
    apply (hpoint a).2
    rw [← he]
    rw [heq]
    exact (Finset.mem_filter.mp hb).2

/-- 论文 `lem:exceptions` 式 `(grid)` 的逐点网格下界，闭端点计入。 -/
theorem coreShift_grid_lower (G v : ℕ) (hG : 0 < G) (δ : ℝ)
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2) (t : UnitAddCircle) :
    let q := reducedDenominator G v
    (q : ℝ) * (2 * δ) - 1 ≤ (coreShiftHits G v δ t).card := by
  let q := reducedDenominator G v
  have hq : 0 < q := (reducedDenominator_pos_dvd G v hG).1
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  have hgrid := (circleGridIndices_count q hq (v • t) (-δ) (2 * δ)
    (by linarith) (by linarith)).1
  rw [circleGridIndices_card_eq_residues q] at hgrid
  have hEq := coreShift_grid_count G v hG δ t
  change (coreShiftHits G v δ t).card =
    (circleGridResidues q (v • t) (-δ) (2 * δ)).card at hEq
  simpa [q, hEq] using hgrid

private theorem coreShiftHits_sum (G v : ℕ) (δ : ℝ) (t : UnitAddCircle) :
    (∑ a ∈ Finset.range (reducedDenominator G v),
      bohrIndicator v δ (t + coreShift G a)) =
      ((coreShiftHits G v δ t).card : ℝ) := by
  classical
  simp only [coreShiftHits, bohrIndicator]
  rw [Finset.card_filter]
  simp only [Finset.sum_ite]
  simp [Set.indicator]

private theorem coreShift_overlap_integral (C : Finset ℕ) (G v a : ℕ)
    (δ : ℝ) (hG : 0 < G) (hv : 0 < v)
    (hCpos : ∀ c ∈ C, 0 < c) (hCdvd : ∀ c ∈ C, G ∣ c)
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    (∫ t : UnitAddCircle,
      (bohrUnion C δ).indicator (1 : UnitAddCircle → ℝ) t *
        bohrIndicator v δ (t + coreShift G a) ∂circleHaar) =
      circleHaar.real (bohrUnion C δ ∩ bohrSet v δ) := by
  let U := bohrUnion C δ
  let B := bohrSet v δ
  let f : UnitAddCircle → ℝ := fun t =>
    U.indicator (1 : UnitAddCircle → ℝ) t * B.indicator 1 t
  have hpoint (t : UnitAddCircle) :
      U.indicator (1 : UnitAddCircle → ℝ) t *
        bohrIndicator v δ (t + coreShift G a) = f (t + coreShift G a) := by
    have hshift : t + coreShift G a ∈ U ↔ t ∈ U :=
      bohrUnion_coreShift C G a δ hG hCdvd t
    by_cases ht : t ∈ U
    · have ht' : t + coreShift G a ∈ U := hshift.mpr ht
      simp [f, bohrIndicator, B, ht, ht']
    · have ht' : t + coreShift G a ∉ U := fun h => ht (hshift.mp h)
      simp [f, bohrIndicator, B, ht, ht']
  have hmeas : MeasurableSet (U ∩ B) :=
    (bohrUnion_measurable C δ hCpos hδ hδhalf).inter
      (bohrSet_measurable_measure v δ hv hδ hδhalf).1
  have hf (t : UnitAddCircle) :
      f t = (U ∩ B).indicator (1 : UnitAddCircle → ℝ) t := by
    by_cases hU : t ∈ U <;> by_cases hB : t ∈ B <;>
      simp [f, hU, hB]
  calc
    _ = ∫ t : UnitAddCircle, f (t + coreShift G a) ∂circleHaar := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun t => hpoint t)
    _ = ∫ t : UnitAddCircle, f t ∂circleHaar :=
      integral_add_right_eq_self f (coreShift G a)
    _ = circleHaar.real (U ∩ B) := by
      simp_rw [hf]
      exact integral_indicator_one hmeas

private theorem coreShift_product_integrable (C : Finset ℕ) (G v a : ℕ)
    (δ : ℝ) (hv : 0 < v) (hCpos : ∀ c ∈ C, 0 < c)
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    Integrable (fun t : UnitAddCircle =>
      (bohrUnion C δ).indicator (1 : UnitAddCircle → ℝ) t *
        bohrIndicator v δ (t + coreShift G a)) circleHaar := by
  let U := bohrUnion C δ
  let B := bohrSet v δ
  let Bshift := (fun t : UnitAddCircle => t + coreShift G a) ⁻¹' B
  have hmeas : MeasurableSet (U ∩ Bshift) :=
    (bohrUnion_measurable C δ hCpos hδ hδhalf).inter
      ((bohrSet_measurable_measure v δ hv hδ hδhalf).1.preimage
        (measurable_id.add measurable_const))
  have hpoint (t : UnitAddCircle) :
      U.indicator (1 : UnitAddCircle → ℝ) t *
        bohrIndicator v δ (t + coreShift G a) =
        (U ∩ Bshift).indicator (1 : UnitAddCircle → ℝ) t := by
    by_cases hU : t ∈ U <;> by_cases hB : t + coreShift G a ∈ B <;>
      simp [bohrIndicator, U, B, Bshift, hU, hB]
  convert ((integrable_const (μ := circleHaar) (1 : ℝ)).indicator hmeas) using 1
  funext t
  exact hpoint t

/-- 论文 `lem:exceptions` 式 `(grid)`：核心并集与任一正速度的 Bohr 集交集有网格平均下界。 -/
theorem coreGridOverlap_lower (C : Finset ℕ) (G v : ℕ) (δ : ℝ)
    (hG : 0 < G) (hv : 0 < v)
    (hCpos : ∀ c ∈ C, 0 < c) (hCdvd : ∀ c ∈ C, G ∣ c)
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    let q := reducedDenominator G v
    circleHaar.real (bohrUnion C δ ∩ bohrSet v δ) ≥
      circleHaar.real (bohrUnion C δ) * (2 * δ - 1 / (q : ℝ)) := by
  let q := reducedDenominator G v
  let U := bohrUnion C δ
  let B := bohrSet v δ
  let ψ : UnitAddCircle → ℝ := U.indicator 1
  let φ (a : ℕ) (t : UnitAddCircle) : ℝ :=
    bohrIndicator v δ (t + coreShift G a)
  have hq : 0 < q := (reducedDenominator_pos_dvd G v hG).1
  have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
  have hψint : Integrable ψ circleHaar :=
    (integrable_const (1 : ℝ)).indicator
      (bohrUnion_measurable C δ hCpos hδ hδhalf)
  have hφint (a : ℕ) : Integrable (fun t => ψ t * φ a t) circleHaar :=
    coreShift_product_integrable C G v a δ hv hCpos hδ hδhalf
  have hsumInt : Integrable
      (fun t => ψ t * (∑ a ∈ Finset.range q, φ a t)) circleHaar := by
    have h := integrable_finsetSum (Finset.range q)
      (fun a ha => hφint a)
    convert h using 1
    funext t
    rw [Finset.mul_sum]
  have hψnonneg (t : UnitAddCircle) : 0 ≤ ψ t := by
    by_cases ht : t ∈ U <;> simp [ψ, ht]
  have hpoint (t : UnitAddCircle) :
      ψ t * ((q : ℝ) * (2 * δ) - 1) ≤
        ψ t * (∑ a ∈ Finset.range q, φ a t) := by
    have hgrid := coreShift_grid_lower G v hG δ hδ hδhalf t
    have hsum := coreShiftHits_sum G v δ t
    change (q : ℝ) * (2 * δ) - 1 ≤ (coreShiftHits G v δ t).card at hgrid
    change (∑ a ∈ Finset.range q, φ a t) =
      ((coreShiftHits G v δ t).card : ℝ) at hsum
    rw [hsum]
    exact mul_le_mul_of_nonneg_left hgrid (hψnonneg t)
  have hle := integral_mono (hψint.mul_const _) hsumInt hpoint
  have hleft : (∫ t : UnitAddCircle,
      ψ t * ((q : ℝ) * (2 * δ) - 1) ∂circleHaar) =
      circleHaar.real U * ((q : ℝ) * (2 * δ) - 1) := by
    rw [integral_mul_const, integral_indicator_one
      (bohrUnion_measurable C δ hCpos hδ hδhalf)]
  have hright : (∫ t : UnitAddCircle,
      ψ t * (∑ a ∈ Finset.range q, φ a t) ∂circleHaar) =
      (q : ℝ) * circleHaar.real (U ∩ B) := by
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum (Finset.range q)
      (fun a ha => hφint a)]
    rw [Finset.sum_congr rfl (fun a ha =>
      coreShift_overlap_integral C G v a δ hG hv hCpos hCdvd hδ hδhalf)]
    simp [hq.ne']
    rfl
  rw [hright, hleft] at hle
  have hfinal : circleHaar.real U * (2 * δ - 1 / (q : ℝ)) ≤
      circleHaar.real (U ∩ B) := by
    have hEq : circleHaar.real U * (2 * δ - 1 / (q : ℝ)) =
        (circleHaar.real U * ((q : ℝ) * (2 * δ) - 1)) / (q : ℝ) := by
      field_simp
    rw [hEq]
    exact (div_le_iff₀ hqreal).2 (by nlinarith [hle])
  exact hfinal

#print axioms coreGridOverlap_lower
end LonelyRunner
