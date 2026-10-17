import LonelyRunner.BohrUnionSmoothing

/-! # 块并集交叉测度与有限频率分离 -/
namespace LonelyRunner
open MeasureTheory

private theorem circleSetIndicator_bohrUnion_le (W : Finset ℕ) (δ : ℝ)
    (t : UnitAddCircle) :
    circleSetIndicator (bohrUnion W δ) t ≤ coverMultiplicity W δ t := by
  have h := coverMultiplicity_eq_excess_add_unionIndicator W δ t
  unfold circleSetIndicator
  rw [h]
  exact le_add_of_nonneg_left (le_max_right _ _)

private theorem coverMultiplicity_union (A B : Finset ℕ) (δ : ℝ)
    (hAB : Disjoint A B) (t : UnitAddCircle) :
    coverMultiplicity (A ∪ B) δ t =
      coverMultiplicity A δ t + coverMultiplicity B δ t := by
  simp [coverMultiplicity, Finset.sum_union hAB]

private theorem coverMultiplicity_biUnion {ι : Type*} (F : Finset ι)
    (I : ι → Finset ℕ) (δ : ℝ) (t : UnitAddCircle)
    (hdisj : (F : Set ι).PairwiseDisjoint I) :
    coverMultiplicity (F.biUnion I) δ t =
      ∑ j ∈ F, coverMultiplicity (I j) δ t := by
  unfold coverMultiplicity
  exact Finset.sum_biUnion hdisj

private theorem circleSetIndicator_intersection (A B : Set UnitAddCircle)
    (t : UnitAddCircle) :
    circleSetIndicator (A ∩ B) t =
      circleSetIndicator A t * circleSetIndicator B t := by
  by_cases ha : t ∈ A <;> by_cases hb : t ∈ B <;>
    simp [circleSetIndicator, ha, hb]

private theorem blockCross_pointwise (V : Finset ℕ) (δ : ℝ)
    (F : Finset (Finset ℕ)) (P : Finset ℕ) (hP : P ∈ F)
    (hsub : ∀ I ∈ F, I ⊆ V)
    (hdisj : ∀ I ∈ F, ∀ J ∈ F, I ≠ J → Disjoint I J)
    (t : UnitAddCircle) :
    circleSetIndicator (bohrUnion P δ) t *
      (∑ I ∈ F.erase P, circleSetIndicator (bohrUnion I δ) t) ≤
        max (coverMultiplicity V δ t - 1) 0 := by
  classical
  let E := F.erase P
  let U := E.biUnion id
  have hdisjE : (E : Set (Finset ℕ)).PairwiseDisjoint id := by
    intro I hI J hJ hIJ
    exact hdisj I (Finset.mem_of_mem_erase hI) J
      (Finset.mem_of_mem_erase hJ) hIJ
  have hPU : Disjoint P U := by
    apply Finset.disjoint_left.mpr
    intro v hvP hvU
    obtain ⟨I, hI, hvI⟩ := Finset.mem_biUnion.mp hvU
    have hIF : I ∈ F := Finset.mem_of_mem_erase hI
    have hIP : I ≠ P := (Finset.ne_of_mem_erase hI)
    exact (Finset.disjoint_left.mp (hdisj P hP I hIF hIP.symm)) hvP hvI
  have hUsub : U ⊆ V := by
    intro v hv
    obtain ⟨I, hI, hvI⟩ := Finset.mem_biUnion.mp hv
    exact hsub I (Finset.mem_of_mem_erase hI) hvI
  have hAllSub : P ∪ U ⊆ V := Finset.union_subset (hsub P hP) hUsub
  have hY : coverMultiplicity P δ t +
      (∑ I ∈ E, coverMultiplicity I δ t) ≤ coverMultiplicity V δ t := by
    calc
      coverMultiplicity P δ t + (∑ I ∈ E, coverMultiplicity I δ t) =
          coverMultiplicity (P ∪ U) δ t := by
            rw [coverMultiplicity_union P U δ hPU t]
            congr 1
            exact (coverMultiplicity_biUnion E id δ t hdisjE).symm
      _ ≤ coverMultiplicity V δ t := coverMultiplicity_mono hAllSub δ t
  have hJ : (∑ I ∈ E, circleSetIndicator (bohrUnion I δ) t) ≤
      ∑ I ∈ E, coverMultiplicity I δ t := by
    exact Finset.sum_le_sum (fun I hI => circleSetIndicator_bohrUnion_le I δ t)
  by_cases ht : t ∈ bohrUnion P δ
  · have hIP : circleSetIndicator (bohrUnion P δ) t = 1 := by
      simp [circleSetIndicator, ht]
    have hPge : 1 ≤ coverMultiplicity P δ t := by
      simpa [hIP] using circleSetIndicator_bohrUnion_le P δ t
    have hVge : 1 ≤ coverMultiplicity V δ t := by
      have hsumpos : 0 ≤ ∑ I ∈ E, coverMultiplicity I δ t :=
        Finset.sum_nonneg (fun I hI => coverMultiplicity_nonneg I δ t)
      linarith
    rw [hIP, one_mul, max_eq_left (by linarith)]
    linarith
  · have hIP : circleSetIndicator (bohrUnion P δ) t = 0 := by
      simp [circleSetIndicator, ht]
    rw [hIP, zero_mul]
    exact le_max_right _ _

/-- 论文 `lem:merge` 式 (cross)：固定主块后，与其余互不相交块的交集测度总和不超过 ε。 -/
theorem blockCross_measure_bound (V : Finset ℕ) (δ : ℝ)
    (F : Finset (Finset ℕ)) (P : Finset ℕ)
    (hP : P ∈ F) (hsub : ∀ I ∈ F, I ⊆ V)
    (hdisj : ∀ I ∈ F, ∀ J ∈ F, I ≠ J → Disjoint I J)
    (hVpos : ∀ v ∈ V, 0 < v) (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hcover : Covers V δ) :
    (∑ I ∈ F.erase P,
      circleHaar.real (bohrUnion P δ ∩ bohrUnion I δ)) ≤
        2 * δ * (V.card : ℝ) - 1 := by
  have hIP : MeasurableSet (bohrUnion P δ) :=
    bohrUnion_measurable_arcs P δ
      (fun v hv => hVpos v (hsub P hP hv)) hδ.le hδhalf
  have hI (I : Finset ℕ) (hIF : I ∈ F) :
      MeasurableSet (bohrUnion I δ) :=
    bohrUnion_measurable_arcs I δ
      (fun v hv => hVpos v (hsub I hIF hv)) hδ.le hδhalf
  have hterm (I : Finset ℕ) (hIE : I ∈ F.erase P) :
      Integrable (circleSetIndicator (bohrUnion P δ ∩ bohrUnion I δ)) circleHaar :=
    (integrable_const (1 : ℝ)).indicator
      (hIP.inter (hI I (Finset.mem_of_mem_erase hIE)))
  have hsum : Integrable (fun t : UnitAddCircle =>
      ∑ I ∈ F.erase P, circleSetIndicator (bohrUnion P δ ∩ bohrUnion I δ) t)
      circleHaar := by
    exact integrable_finset_sum _ (fun I hIE => hterm I hIE)
  have hVint := coverExcess_integrable V δ hVpos hδ hδhalf
  have hpoint (t : UnitAddCircle) :
      (∑ I ∈ F.erase P, circleSetIndicator (bohrUnion P δ ∩ bohrUnion I δ) t) ≤
      max (coverMultiplicity V δ t - 1) 0 := by
    simp_rw [circleSetIndicator_intersection]
    rw [← Finset.mul_sum]
    exact blockCross_pointwise V δ F P hP hsub hdisj t
  have hmain := integral_mono hsum hVint hpoint
  rw [integral_finset_sum _ (fun I hIE => hterm I hIE)] at hmain
  have heq : (∑ I ∈ F.erase P,
      ∫ t : UnitAddCircle,
        circleSetIndicator (bohrUnion P δ ∩ bohrUnion I δ) t ∂circleHaar) =
      ∑ I ∈ F.erase P,
        circleHaar.real (bohrUnion P δ ∩ bohrUnion I δ) := by
    apply Finset.sum_congr rfl
    intro I hIE
    exact integral_indicator_one (hIP.inter (hI I (Finset.mem_of_mem_erase hIE)))
  rw [heq] at hmain
  change (∑ I ∈ F.erase P,
    circleHaar.real (bohrUnion P δ ∩ bohrUnion I δ)) ≤ coverExcess V δ at hmain
  rwa [coverExcess_eq_epsilon V δ hVpos hδ hδhalf hcover] at hmain

/-- 平滑函数实际使用的整数频率集，包含零频率及全部正负短频率。 -/
def smoothingFrequencySet (R : ℕ) : Finset ℤ :=
  insert 0
    (((Finset.range (R-1)).image (fun j => ((j+1 : ℕ) : ℤ))) ∪
     ((Finset.range (R-1)).image (fun j => -((j+1 : ℕ) : ℤ))))

noncomputable def smoothingFourierCoeff (A : Set UnitAddCircle) (R : ℕ)
    (k : ℤ) : ℂ :=
  if k = 0 then (circleHaar.real A : ℂ) else
    (circleFejerCoefficient R k : ℂ) * circleSetFourierCoeff A k

theorem smoothingFrequencySet_short (R : ℕ) (hR : 1 ≤ R) :
    ∀ k ∈ smoothingFrequencySet R, k.natAbs < R := by
  intro k hk
  simp only [smoothingFrequencySet, Finset.mem_insert, Finset.mem_union,
    Finset.mem_image] at hk
  rcases hk with rfl | hk | hk
  · omega
  · obtain ⟨j, hj, rfl⟩ := hk
    exact (circleFejerSmoothing_frequency_range R j hj).1
  · obtain ⟨j, hj, rfl⟩ := hk
    exact (circleFejerSmoothing_frequency_range R j hj).2

theorem smoothingFrequencySet_zero (R : ℕ) : (0 : ℤ) ∈ smoothingFrequencySet R := by
  simp [smoothingFrequencySet]

/-- 论文 `lem:merge`：已证明的卷积有限展开等于真正的 `circleFourierPoly`。 -/
theorem circleFejerSmoothing_eq_poly {A : Set UnitAddCircle}
    (hA : MeasurableSet A) (R : ℕ) (hR : 1 ≤ R) (t : UnitAddCircle) :
    (circleFejerSmoothing A R t : ℂ) =
      circleFourierPoly (smoothingFrequencySet R) (smoothingFourierCoeff A R) t := by
  classical
  let pos : Finset ℤ := (Finset.range (R-1)).image (fun j => ((j+1 : ℕ) : ℤ))
  let neg : Finset ℤ := (Finset.range (R-1)).image (fun j => -((j+1 : ℕ) : ℤ))
  have hpos0 : (0 : ℤ) ∉ pos := by
    intro h
    obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp h
    omega
  have hneg0 : (0 : ℤ) ∉ neg := by
    intro h
    obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp h
    omega
  have hpn : Disjoint pos neg := by
    apply Finset.disjoint_left.mpr
    intro k hk hkn
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨l, hl, heq⟩ := Finset.mem_image.mp hkn
    omega
  have hinjpos : Set.InjOn (fun j : ℕ => ((j+1 : ℕ) : ℤ))
      (Finset.range (R-1) : Set ℕ) := by
    intro j hj l hl heq
    change ((j+1 : ℕ) : ℤ) = ((l+1 : ℕ) : ℤ) at heq
    omega
  have hinjneg : Set.InjOn (fun j : ℕ => -((j+1 : ℕ) : ℤ))
      (Finset.range (R-1) : Set ℕ) := by
    intro j hj l hl heq
    change -((j+1 : ℕ) : ℤ) = -((l+1 : ℕ) : ℤ) at heq
    omega
  have hunion0 : (0 : ℤ) ∉ pos ∪ neg := by simpa [hpos0,hneg0]
  rw [circleFejerSmoothing_finiteExpansion hA R hR t]
  unfold circleFourierPoly smoothingFrequencySet
  change (circleHaar.real A : ℂ) + _ + _ =
    ∑ k ∈ insert 0 (pos ∪ neg), smoothingFourierCoeff A R k * fourier k t
  rw [Finset.sum_insert hunion0, Finset.sum_union hpn]
  rw [Finset.sum_image hinjpos, Finset.sum_image hinjneg]
  simp only [smoothingFourierCoeff, fourier_zero, mul_one,
    if_pos rfl]
  have hpos (j : ℕ) : (((j+1 : ℕ) : ℤ) ≠ 0) := by omega
  have hneg (j : ℕ) : (-((j+1 : ℕ) : ℤ) ≠ 0) := by omega
  simp only [if_neg (hpos _), if_neg (hneg _)]
  simp only [ite_true]
  ring

/-- 论文 `lem:merge`：两个已证明的平滑多项式在分离尺度下的积分恰为均值之积。 -/
theorem circleFejerSmoothing_integral_separated
    {A B : Set UnitAddCircle} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (R g h a b : ℕ) (hR : 1 ≤ R) (hg : 0 < g)
    (ha : 0 < a) (hb : 0 < b)
    (hratio : h*b = g*a) (hcop : Nat.Coprime a b)
    (hlarge : R ≤ max a b) :
    (∫ t : UnitAddCircle,
      circleFejerSmoothing A R (g • t) * circleFejerSmoothing B R (h • t)
        ∂circleHaar) = circleHaar.real A * circleHaar.real B := by
  let S := smoothingFrequencySet R
  let cA := smoothingFourierCoeff A R
  let cB := smoothingFourierCoeff B R
  have hspec := circleFourierPoly_integral_separated S S cA cB R g h a b
    hg ha hb hratio hcop hlarge
    (smoothingFrequencySet_short R hR) (smoothingFrequencySet_short R hR)
  have hz : (0 : ℤ) ∈ S := smoothingFrequencySet_zero R
  have hcA : cA 0 = (circleHaar.real A : ℂ) := by simp [cA, smoothingFourierCoeff]
  have hcB : cB 0 = (circleHaar.real B : ℂ) := by simp [cB, smoothingFourierCoeff]
  have hcomplex :
      (∫ t : UnitAddCircle,
        ((circleFejerSmoothing A R (g • t) *
          circleFejerSmoothing B R (h • t) : ℝ) : ℂ) ∂circleHaar) =
        ((circleHaar.real A * circleHaar.real B : ℝ) : ℂ) := by
    convert hspec using 1
    · congr 1
      funext t
      push_cast
      rw [circleFejerSmoothing_eq_poly hA R hR,
        circleFejerSmoothing_eq_poly hB R hR]
    · simp [hz, hcA, hcB]
  rw [integral_complex_ofReal] at hcomplex
  exact_mod_cast hcomplex

private theorem unit_mul_difference_bound (a b x y : ℝ)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |a*b-x*y| ≤ |a-x| + |b-y| := by
  calc
    |a*b-x*y| = |(a-x)*b + x*(b-y)| := by congr 1; ring
    _ ≤ |(a-x)*b| + |x*(b-y)| := abs_add_le _ _
    _ = |a-x| * b + x * |b-y| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hb0, abs_of_nonneg hx0]
    _ ≤ |a-x| + |b-y| := by
      nlinarith [mul_nonneg (abs_nonneg (a-x)) (sub_nonneg.mpr hb1),
        mul_nonneg (abs_nonneg (b-y)) (sub_nonneg.mpr hx1)]

private theorem circleSetIndicator_bounds_new (A : Set UnitAddCircle)
    (t : UnitAddCircle) :
    0 ≤ circleSetIndicator A t ∧ circleSetIndicator A t ≤ 1 := by
  by_cases ht : t ∈ A <;> simp [circleSetIndicator, ht]

/-- 论文 `lem:merge`：由有限频率分离和实际卷积误差得到交集的实测度比较。 -/
theorem circleSmoothing_intersection_separated
    {A B : Set UnitAddCircle} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (R g h a b : ℕ) (hR : 1 ≤ R) (hg : 0 < g) (hh : 0 < h)
    (ha : 0 < a) (hb : 0 < b)
    (hratio : h*b = g*a) (hcop : Nat.Coprime a b)
    (hlarge : R ≤ max a b) :
    |circleHaar.real (((fun t : UnitAddCircle => g • t) ⁻¹' A) ∩
        ((fun t : UnitAddCircle => h • t) ⁻¹' B)) -
      circleHaar.real A * circleHaar.real B| ≤
      (∫ t : UnitAddCircle,
        |circleFejerSmoothing A R (g • t) - circleSetIndicator A (g • t)| ∂circleHaar) +
      (∫ t : UnitAddCircle,
        |circleFejerSmoothing B R (h • t) - circleSetIndicator B (h • t)| ∂circleHaar) := by
  let Ug : Set UnitAddCircle := (fun t => g • t) ⁻¹' A
  let Uh : Set UnitAddCircle := (fun t => h • t) ⁻¹' B
  let fa : UnitAddCircle → ℝ := fun t => circleFejerSmoothing A R (g • t)
  let fb : UnitAddCircle → ℝ := fun t => circleFejerSmoothing B R (h • t)
  let ia : UnitAddCircle → ℝ := circleSetIndicator Ug
  let ib : UnitAddCircle → ℝ := circleSetIndicator Uh
  have hUg : MeasurableSet Ug := hA.preimage (continuous_nsmul g).measurable
  have hUh : MeasurableSet Uh := hB.preimage (continuous_nsmul h).measurable
  have hfa : Continuous fa := (circleFejerSmoothing_continuous hA R).comp (continuous_nsmul g)
  have hfb : Continuous fb := (circleFejerSmoothing_continuous hB R).comp (continuous_nsmul h)
  have hfaInt : Integrable fa circleHaar :=
    hfa.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hfbInt : Integrable fb circleHaar :=
    hfb.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiaInt : Integrable ia circleHaar := (integrable_const (1 : ℝ)).indicator hUg
  have hibInt : Integrable ib circleHaar := (integrable_const (1 : ℝ)).indicator hUh
  have hsInt : Integrable (fun t => fa t * fb t) circleHaar :=
    (hfa.mul hfb).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiInt : Integrable (fun t => ia t * ib t) circleHaar := by
    have h : Integrable (circleSetIndicator (Ug ∩ Uh)) circleHaar :=
      (integrable_const (1 : ℝ)).indicator (hUg.inter hUh)
    convert h using 1
    funext t
    exact (circleSetIndicator_intersection Ug Uh t).symm
  have hpoint (t : UnitAddCircle) :
      |ia t * ib t - fa t * fb t| ≤ |ia t - fa t| + |ib t - fb t| := by
    have hiB := circleSetIndicator_bounds_new Uh t
    have hfA := circleFejerSmoothing_bounds hA R hR (g • t)
    exact unit_mul_difference_bound (ia t) (ib t) (fa t) (fb t)
      hiB.1 hiB.2 hfA.1 hfA.2
  have hEq : circleHaar.real (Ug ∩ Uh) - circleHaar.real A * circleHaar.real B =
      ∫ t : UnitAddCircle, ia t * ib t - fa t * fb t ∂circleHaar := by
    rw [integral_sub hiInt hsInt]
    have hInter : (∫ t : UnitAddCircle, ia t * ib t ∂circleHaar) =
        circleHaar.real (Ug ∩ Uh) := by
      have ht : ∀ t, ia t * ib t = circleSetIndicator (Ug ∩ Uh) t := by
        intro t
        exact (circleSetIndicator_intersection Ug Uh t).symm
      simp_rw [ht]
      exact integral_indicator_one (hUg.inter hUh)
    rw [hInter]
    rw [circleFejerSmoothing_integral_separated hA hB R g h a b
      hR hg ha hb hratio hcop hlarge]
  change |circleHaar.real (Ug ∩ Uh) - circleHaar.real A * circleHaar.real B| ≤ _
  rw [hEq]
  have hAerr : Integrable (fun t => |ia t-fa t|) circleHaar := (hiaInt.sub hfaInt).abs
  have hBerr : Integrable (fun t => |ib t-fb t|) circleHaar := (hibInt.sub hfbInt).abs
  calc
    |∫ t : UnitAddCircle, ia t * ib t - fa t * fb t ∂circleHaar| ≤
      ∫ t : UnitAddCircle, |ia t * ib t - fa t * fb t| ∂circleHaar :=
        abs_integral_le_integral_abs
    _ ≤ ∫ t : UnitAddCircle, (|ia t-fa t| + |ib t-fb t|) ∂circleHaar := by
      exact integral_mono (hiInt.sub hsInt).abs (hAerr.add hBerr) hpoint
    _ = (∫ t : UnitAddCircle, |fa t-ia t| ∂circleHaar) +
        (∫ t : UnitAddCircle, |fb t-ib t| ∂circleHaar) := by
      rw [integral_add hAerr hBerr]
      simp only [abs_sub_comm]
    _ = _ := by
      congr 1 <;> congr 1 <;> funext t <;> rfl

/-- 论文 `lem:merge`：实际归一化 Bohr 并集的远尺度交集比较。 -/
theorem bohrUnion_intersection_separated
    (W Z : Finset ℕ) (δ : ℝ) (R g h a b : ℕ)
    (hW : ∀ w ∈ W, 0 < w) (hZ : ∀ z ∈ Z, 0 < z)
    (hδ0 : 0 ≤ δ) (hδhalf : δ < 1 / 2)
    (hR : 2 ≤ R) (hg : 0 < g) (hh : 0 < h)
    (ha : 0 < a) (hb : 0 < b)
    (hratio : h*b = g*a) (hcop : Nat.Coprime a b)
    (hlarge : R ≤ max a b) :
    |circleHaar.real (bohrUnion (W.image (fun w => g*w)) δ ∩
      bohrUnion (Z.image (fun z => h*z)) δ) -
      circleHaar.real (bohrUnion W δ) * circleHaar.real (bohrUnion Z δ)| ≤
      (∫ t : UnitAddCircle,
        |circleFejerSmoothing (bohrUnion W δ) R t -
          circleSetIndicator (bohrUnion W δ) t| ∂circleHaar) +
      (∫ t : UnitAddCircle,
        |circleFejerSmoothing (bohrUnion Z δ) R t -
          circleSetIndicator (bohrUnion Z δ) t| ∂circleHaar) := by
  have hA := bohrUnion_measurable_arcs W δ hW hδ0 hδhalf
  have hB := bohrUnion_measurable_arcs Z δ hZ hδ0 hδhalf
  have hsep := circleSmoothing_intersection_separated hA hB R g h a b
    (by omega) hg hh ha hb hratio hcop hlarge
  rw [← bohrUnion_scale W g δ, ← bohrUnion_scale Z h δ] at hsep
  have hApoint (t : UnitAddCircle) :
      circleSetIndicator (bohrUnion W δ) (g • t) =
        circleSetIndicator (bohrUnion (W.image (fun w => g*w)) δ) t := by
    rw [bohrUnion_scale W g δ]
    rfl
  have hBpoint (t : UnitAddCircle) :
      circleSetIndicator (bohrUnion Z δ) (h • t) =
        circleSetIndicator (bohrUnion (Z.image (fun z => h*z)) δ) t := by
    rw [bohrUnion_scale Z h δ]
    rfl
  simp_rw [hApoint, hBpoint] at hsep
  rw [bohrUnion_smoothing_pullback_error W g δ R hg hW hδ0 hδhalf,
    bohrUnion_smoothing_pullback_error Z h δ R hh hZ hδ0 hδhalf] at hsep
  exact hsep

#print axioms blockCross_measure_bound
#print axioms bohrUnion_intersection_separated

end LonelyRunner
