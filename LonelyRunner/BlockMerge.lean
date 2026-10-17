import LonelyRunner.BlockSeparation

/-! # 论文 `lem:merge` 的尺度合并整数代数 -/
namespace LonelyRunner
open MeasureTheory
open Filter
set_option maxHeartbeats 1000000

/-- 以 `g` 为主尺度时，`h/g` 的既约分子。 -/
def blockScaleNumer (g h : ℕ) : ℕ := h / Nat.gcd h g

/-- 以 `g` 为主尺度时，`h/g` 的既约分母。 -/
def blockScaleDenom (g h : ℕ) : ℕ := g / Nat.gcd h g

/-- 论文 `lem:merge`：实际构造尺度比的既约分子与分母。 -/
theorem blockScale_reduced (g h : ℕ) (hg : 0 < g) (hh : 0 < h) :
    0 < blockScaleNumer g h ∧ 0 < blockScaleDenom g h ∧
      Nat.Coprime (blockScaleNumer g h) (blockScaleDenom g h) ∧
      h * blockScaleDenom g h = g * blockScaleNumer g h ∧
      blockScaleDenom g h ∣ g := by
  let d := Nat.gcd h g
  have hd : 0 < d := Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left h g) hh
  have hdh : d ∣ h := Nat.gcd_dvd_left h g
  have hdg : d ∣ g := Nat.gcd_dvd_right h g
  have hnum : 0 < h / d := Nat.div_pos (Nat.le_of_dvd hh hdh) hd
  have hden : 0 < g / d := Nat.div_pos (Nat.le_of_dvd hg hdg) hd
  have hhd : h / d * d = h := Nat.div_mul_cancel hdh
  have hgd : g / d * d = g := Nat.div_mul_cancel hdg
  refine ⟨hnum, hden, Nat.coprime_div_gcd_div_gcd hd, ?_, ?_⟩
  · change h * (g / d) = g * (h / d)
    calc
      h * (g / d) = (h / d * d) * (g / d) := by rw [hhd]
      _ = (g / d * d) * (h / d) := by ring
      _ = g * (h / d) := by rw [hgd]
  · change g / d ∣ g
    exact ⟨d, hgd.symm⟩

/-- 论文 `lem:merge`：保留的尺度比的分母的最小公倍数整除主尺度，且至多为 `R^s`。 -/
theorem blockScale_lcm_bound (F : Finset (Finset ℕ)) (g : Finset ℕ → ℕ)
    (P : Finset ℕ) (R : ℕ)
    (hgP : 0 < g P)
    (hg : ∀ I ∈ F, 0 < g I)
    (hnear : ∀ I ∈ F,
      max (blockScaleNumer (g P) (g I)) (blockScaleDenom (g P) (g I)) ≤ R) :
    let Q₀ := F.lcm (fun I => blockScaleDenom (g P) (g I))
    0 < Q₀ ∧ Q₀ ∣ g P ∧ Q₀ ≤ R ^ F.card := by
  classical
  intro Q₀
  have hbpos (I : Finset ℕ) (hI : I ∈ F) :
      0 < blockScaleDenom (g P) (g I) :=
    (blockScale_reduced (g P) (g I) hgP (hg I hI)).2.1
  have hQpos : 0 < Q₀ := by
    apply Nat.pos_of_ne_zero
    exact Finset.lcm_ne_zero_iff.mpr (fun I hI => Nat.ne_of_gt (hbpos I hI))
  have hQdvd : Q₀ ∣ g P := by
    exact Finset.lcm_dvd (fun I hI =>
      (blockScale_reduced (g P) (g I) hgP (hg I hI)).2.2.2.2)
  have hQprod : Q₀ ∣ ∏ I ∈ F, blockScaleDenom (g P) (g I) := by
    exact Finset.lcm_dvd (fun I hI =>
      Finset.dvd_prod_of_mem (fun I => blockScaleDenom (g P) (g I)) hI)
  have hprodpos : 0 < ∏ I ∈ F, blockScaleDenom (g P) (g I) :=
    Finset.prod_pos hbpos
  have hprodle : (∏ I ∈ F, blockScaleDenom (g P) (g I)) ≤ R ^ F.card := by
    calc
      (∏ I ∈ F, blockScaleDenom (g P) (g I)) ≤ ∏ _I ∈ F, R := by
        apply Finset.prod_le_prod
        intro I hI
        exact le_trans (le_max_right _ _) (hnear I hI)
      _ = R ^ F.card := by simp
  exact ⟨hQpos, hQdvd, (Nat.le_of_dvd hprodpos hQprod).trans hprodle⟩

private theorem blockScale_factor (g h Q₀ : ℕ)
    (hg : 0 < g) (hh : 0 < h) (hQ : 0 < Q₀)
    (hQdvd : Q₀ ∣ g) (hbQ : blockScaleDenom g h ∣ Q₀) :
    h = (g / Q₀) * (blockScaleNumer g h * (Q₀ / blockScaleDenom g h)) := by
  let a := blockScaleNumer g h
  let b := blockScaleDenom g h
  let q := Q₀ / b
  let G := g / Q₀
  have hbpos : 0 < b := (blockScale_reduced g h hg hh).2.1
  have hrel : h*b = g*a := (blockScale_reduced g h hg hh).2.2.2.1
  have hQeq : q*b = Q₀ := Nat.div_mul_cancel hbQ
  have hGeq : G*Q₀ = g := Nat.div_mul_cancel hQdvd
  apply Nat.eq_of_mul_eq_mul_right hbpos
  calc
    h*b = g*a := hrel
    _ = (G*Q₀)*a := by rw [hGeq]
    _ = (G*(a*q))*b := by rw [← hQeq]; ring

/-- 论文 `lem:merge`：由全部保留块的既约分母构造公共因子和显式高度。 -/
theorem blockScale_common_factor
    (F : Finset (Finset ℕ)) (g : Finset ℕ → ℕ)
    (P : Finset ℕ) (R M : ℕ)
    (hgP : 0 < g P) (hR : 0 < R) (hM : 0 < M)
    (hg : ∀ I ∈ F, 0 < g I)
    (hnear : ∀ I ∈ F,
      max (blockScaleNumer (g P) (g I)) (blockScaleDenom (g P) (g I)) ≤ R)
    (hblock : ∀ I ∈ F, ∀ v ∈ I, ∃ k : ℕ, 1 ≤ k ∧ k ≤ M ∧ v = g I * k) :
    let Q₀ := F.lcm (fun I => blockScaleDenom (g P) (g I))
    let G₀ := g P / Q₀
    0 < G₀ ∧ Q₀ ∣ g P ∧ Q₀ ≤ R ^ F.card ∧
      ∀ v ∈ extractionUnion F,
        ∃ k : ℕ, 1 ≤ k ∧ k ≤ M * R * Q₀ ∧ v = G₀ * k := by
  classical
  intro Q₀ G₀
  obtain ⟨hQpos, hQdvd, hQle⟩ := blockScale_lcm_bound F g P R hgP hg hnear
  have hGpos : 0 < G₀ := Nat.div_pos (Nat.le_of_dvd hgP hQdvd) hQpos
  refine ⟨hGpos, hQdvd, hQle, ?_⟩
  intro v hv
  obtain ⟨I, hI, hvI⟩ := Finset.mem_biUnion.mp hv
  obtain ⟨k, hk1, hkM, hvEq⟩ := hblock I hI v hvI
  let a := blockScaleNumer (g P) (g I)
  let b := blockScaleDenom (g P) (g I)
  let q := Q₀ / b
  have hbQ : b ∣ Q₀ := Finset.dvd_lcm hI
  have hfactor : g I = G₀ * (a*q) :=
    blockScale_factor (g P) (g I) Q₀ hgP (hg I hI) hQpos hQdvd hbQ
  have ha1 : 1 ≤ a := (blockScale_reduced (g P) (g I) hgP (hg I hI)).1
  have hb1 : 1 ≤ b := (blockScale_reduced (g P) (g I) hgP (hg I hI)).2.1
  have hq1 : 1 ≤ q := Nat.div_pos (Nat.le_of_dvd hQpos hbQ) hb1
  have haR : a ≤ R := le_trans (le_max_left _ _) (hnear I hI)
  have hqQ : q ≤ Q₀ := Nat.div_le_self Q₀ b
  have hakpos : 0 < a*q*k :=
    Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  refine ⟨a*q*k, hakpos, ?_, ?_⟩
  · calc
      a*q*k ≤ R*q*k := by gcongr
      _ ≤ R*Q₀*k := by gcongr
      _ ≤ R*Q₀*M := by gcongr
      _ = M*R*Q₀ := by ring
  · rw [hvEq, hfactor]
    ring

/-- 论文 `lem:merge`：把公共因子替换为保留速度集的 gcd，归一化高度不增。 -/
theorem blockScale_replace_by_gcd (C : Finset ℕ) (G₀ T : ℕ)
    (hC : C.Nonempty) (hCpos : ∀ v ∈ C, 0 < v)
    (hG : 0 < G₀)
    (hrep : ∀ v ∈ C, ∃ k : ℕ, 1 ≤ k ∧ k ≤ T ∧ v = G₀ * k) :
    let G := C.gcd id
    0 < G ∧ ∀ v ∈ C, v ∈ inverseBoundedMultiples G (T : ℝ) := by
  classical
  intro G
  obtain ⟨v₀, hv₀⟩ := hC
  have hGdvdv : G ∣ v₀ := Finset.gcd_dvd hv₀
  have hGpos : 0 < G := Nat.pos_of_dvd_of_pos hGdvdv (hCpos v₀ hv₀)
  have hG0dvd : G₀ ∣ G := Finset.dvd_gcd (fun v hv => by
    obtain ⟨k, hk1, hkT, hEq⟩ := hrep v hv
    exact ⟨k, hEq⟩)
  have hG0le : G₀ ≤ G := Nat.le_of_dvd hGpos hG0dvd
  refine ⟨hGpos, ?_⟩
  intro v hv
  obtain ⟨k, hk1, hkT, hEq⟩ := hrep v hv
  have hGdvd : G ∣ v := Finset.gcd_dvd hv
  have hdivpos : 1 ≤ v / G :=
    Nat.div_pos (Nat.le_of_dvd (hCpos v hv) hGdvd) hGpos
  have hquot : v / G ≤ k := by
    calc
      v / G ≤ v / G₀ := Nat.div_le_div_left hG0le hG
      _ = k := by rw [hEq]; exact Nat.mul_div_cancel_left k hG
  refine ⟨v/G, hdivpos, ?_, ?_⟩
  · exact_mod_cast hquot.trans hkT
  · simpa [mul_comm] using (Nat.div_mul_cancel hGdvd).symm

/-- 论文 `lem:merge` 的算术结论：在已筛出的近尺度块上，
最终公共因子可直接取保留速度集的 gcd。此处不包含筛块的测度论论证。 -/
theorem blockScale_common_gcd
    (F : Finset (Finset ℕ)) (g : Finset ℕ → ℕ)
    (P : Finset ℕ) (R M : ℕ)
    (hC : (extractionUnion F).Nonempty)
    (hCpos : ∀ v ∈ extractionUnion F, 0 < v)
    (hgP : 0 < g P) (hR : 0 < R) (hM : 0 < M)
    (hg : ∀ I ∈ F, 0 < g I)
    (hnear : ∀ I ∈ F,
      max (blockScaleNumer (g P) (g I)) (blockScaleDenom (g P) (g I)) ≤ R)
    (hblock : ∀ I ∈ F, ∀ v ∈ I, ∃ k : ℕ, 1 ≤ k ∧ k ≤ M ∧ v = g I * k) :
    let C := extractionUnion F
    let Q₀ := F.lcm (fun I => blockScaleDenom (g P) (g I))
    0 < C.gcd id ∧
      (∀ v ∈ C, v ∈ inverseBoundedMultiples (C.gcd id) ((M * R * Q₀ : ℕ) : ℝ)) ∧
      Q₀ ∣ g P ∧ Q₀ ≤ R ^ F.card := by
  classical
  intro C Q₀
  obtain ⟨hGpos, hQdvd, hQle, hrep⟩ :=
    blockScale_common_factor F g P R M hgP hR hM hg hnear hblock
  have hmain := blockScale_replace_by_gcd C (g P / Q₀) (M * R * Q₀)
    hC hCpos hGpos hrep
  exact ⟨hmain.1, hmain.2, hQdvd, hQle⟩

/-- 把块抽取接口中的实数高度 `m³` 明确转为自然数高度 `m³`。 -/
theorem extractedBlock_nat_height (F : Finset (Finset ℕ))
    (g : Finset ℕ → ℕ) (m : ℕ)
    (hblock : ∀ I ∈ F, ∀ v ∈ I,
      v ∈ inverseBoundedMultiples (g I) ((m : ℝ) ^ 3)) :
    ∀ I ∈ F, ∀ v ∈ I,
      ∃ k : ℕ, 1 ≤ k ∧ k ≤ m ^ 3 ∧ v = g I * k := by
  intro I hI v hv
  obtain ⟨k, hk1, hkReal, hEq⟩ := hblock I hI v hv
  refine ⟨k, hk1, ?_, hEq⟩
  exact_mod_cast hkReal

/-- 论文 `lem:merge`：交集上界和逐块平滑比较给出远块总质量界的有限求和步骤。 -/
theorem farBlock_mass_sum {ι : Type*} (F : Finset ι)
    (α₁ ε ρ₁ : ℝ) (α ρ β : ι → ℝ)
    (hcross : (∑ j ∈ F, β j) ≤ ε)
    (hsep : ∀ j ∈ F, |β j - α₁ * α j| ≤ ρ₁ + ρ j) :
    α₁ * (∑ j ∈ F, α j) ≤
      ε + (F.card : ℝ) * ρ₁ + ∑ j ∈ F, ρ j := by
  have hpoint (j : ι) (hj : j ∈ F) :
      α₁ * α j ≤ β j + ρ₁ + ρ j := by
    have h := (abs_le.mp (hsep j hj)).1
    linarith
  have hsum := Finset.sum_le_sum hpoint
  calc
    α₁ * (∑ j ∈ F, α j) = ∑ j ∈ F, α₁ * α j := by rw [Finset.mul_sum]
    _ ≤ ∑ j ∈ F, (β j + ρ₁ + ρ j) := hsum
    _ = (∑ j ∈ F, β j) + (F.card : ℝ) * ρ₁ + ∑ j ∈ F, ρ j := by
      simp [Finset.sum_add_distrib, mul_comm]
    _ ≤ ε + (F.card : ℝ) * ρ₁ + ∑ j ∈ F, ρ j := by linarith

/-- 抽取块 `I⊆g[m³]` 的归一化速度集合。 -/
def normalizedBlock (I : Finset ℕ) (g : ℕ) : Finset ℕ :=
  I.image (fun v => v / g)

theorem normalizedBlock_image_eq (I : Finset ℕ) (g : ℕ) (m : ℕ)
    (hg : 0 < g)
    (hI : ∀ v ∈ I, v ∈ inverseBoundedMultiples g ((m : ℝ) ^ 3)) :
    (normalizedBlock I g).image (fun w => g * w) = I := by
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨k, hk1, hkM, hkEq⟩ := hI z hz
    simpa [hkEq, Nat.mul_div_cancel_left k hg] using hz
  · intro hv
    refine Finset.mem_image.mpr ⟨v/g, Finset.mem_image.mpr ⟨v, hv, rfl⟩, ?_⟩
    obtain ⟨k, hk1, hkM, hkEq⟩ := hI v hv
    simp [hkEq, Nat.mul_div_cancel_left k hg]

theorem normalizedBlock_positive_height (I : Finset ℕ) (g : ℕ) (m : ℕ)
    (hg : 0 < g)
    (hI : ∀ v ∈ I, v ∈ inverseBoundedMultiples g ((m : ℝ) ^ 3)) :
    ∀ w ∈ normalizedBlock I g, 0 < w ∧ w ≤ m ^ 3 := by
  intro w hw
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
  obtain ⟨k, hk1, hkReal, hEq⟩ := hI v hv
  have hkNat : k ≤ m ^ 3 := by exact_mod_cast hkReal
  simpa [hEq, Nat.mul_div_cancel_left k hg] using
    (And.intro (show 0 < k by omega) hkNat)

theorem normalizedBlock_arcCount_bound (I : Finset ℕ) (g : ℕ) (m : ℕ)
    (hg : 0 < g)
    (hI : ∀ v ∈ I, v ∈ inverseBoundedMultiples g ((m : ℝ) ^ 3)) :
    (∑ w ∈ normalizedBlock I g, (w : ℝ)) ≤
      (I.card : ℝ) * (m : ℝ) ^ 3 := by
  have hsum : (∑ w ∈ normalizedBlock I g, (w : ℝ)) ≤
      ∑ _w ∈ normalizedBlock I g, ((m : ℝ) ^ 3) := by
    apply Finset.sum_le_sum
    intro w hw
    exact_mod_cast (normalizedBlock_positive_height I g m hg hI w hw).2
  have hcard : (normalizedBlock I g).card ≤ I.card := by
    exact Finset.card_image_le
  calc
    (∑ w ∈ normalizedBlock I g, (w : ℝ)) ≤
      ∑ _w ∈ normalizedBlock I g, ((m : ℝ) ^ 3) := hsum
    _ = ((normalizedBlock I g).card : ℝ) * (m : ℝ) ^ 3 := by simp
    _ ≤ (I.card : ℝ) * (m : ℝ) ^ 3 := by
      gcongr

/-- 论文 `lem:merge`：抽取块归一化后拉回的 Fejér 误差，由块基数和 `m³` 控制。 -/
theorem normalizedBlock_smoothing_error :
    ∃ C : ℝ, 0 < C ∧
      ∀ (I : Finset ℕ) (g m R : ℕ) (δ : ℝ),
        0 < g → (∀ v ∈ I, v ∈ inverseBoundedMultiples g ((m : ℝ) ^ 3)) →
        0 ≤ δ → δ < 1 / 2 → 2 ≤ R →
        (∫ t : UnitAddCircle,
          |circleFejerSmoothing (bohrUnion (normalizedBlock I g) δ) R (g • t) -
            circleSetIndicator (bohrUnion I δ) t| ∂circleHaar) ≤
          C * (I.card : ℝ) * (m : ℝ) ^ 3 *
            Real.log (2 * (R : ℝ)) / (R : ℝ) := by
  obtain ⟨C, hC, hErr⟩ := bohrUnion_smoothing_error
  refine ⟨C, hC, ?_⟩
  intro I g m R δ hg hI hδ0 hδhalf hR
  let W := normalizedBlock I g
  have hW : ∀ w ∈ W, 0 < w :=
    fun w hw => (normalizedBlock_positive_height I g m hg hI w hw).1
  have hEq := normalizedBlock_image_eq I g m hg hI
  have hPull := bohrUnion_smoothing_pullback_error W g δ R hg hW hδ0 hδhalf
  rw [hEq] at hPull
  rw [hPull]
  have hbound := hErr W δ R hW hδ0 hδhalf hR
  have harcs := normalizedBlock_arcCount_bound I g m hg hI
  have hRreal : (0 : ℝ) < R := by exact_mod_cast (by omega : 0 < R)
  have hLog : 0 ≤ Real.log (2 * (R : ℝ)) := by
    apply Real.log_nonneg
    have hRtwo : (2 : ℝ) ≤ R := by exact_mod_cast hR
    nlinarith
  calc
    (∫ t : UnitAddCircle,
      |circleFejerSmoothing (bohrUnion W δ) R t -
        circleSetIndicator (bohrUnion W δ) t| ∂circleHaar) ≤
      C * (∑ w ∈ W, (w : ℝ)) * Real.log (2 * (R : ℝ)) / (R : ℝ) := hbound
    _ ≤ C * ((I.card : ℝ) * (m : ℝ) ^ 3) *
      Real.log (2 * (R : ℝ)) / (R : ℝ) := by
        gcongr
    _ = _ := by ring

/-- 论文 `lem:merge`：每块按 `m³` 个闭弧估计后的有限误差求和。
此辅助命题的 `F.card≤m` 将由抽取时的 `sK≤m` 和 `K≥1` 推出。 -/
theorem normalizedBlocks_smoothing_error_sum (C : ℝ) (hC : 0 < C)
    (F : Finset (Finset ℕ)) (g : Finset ℕ → ℕ)
    (m R : ℕ) (δ : ℝ)
    (hg : ∀ I ∈ F, 0 < g I)
    (hblock : ∀ I ∈ F, ∀ v ∈ I,
      v ∈ inverseBoundedMultiples (g I) ((m : ℝ) ^ 3))
    (hcard : ∀ I ∈ F, I.card ≤ m) (hFcard : F.card ≤ m)
    (hδ0 : 0 ≤ δ) (hδhalf : δ < 1 / 2) (hR : 2 ≤ R)
    (hErr : ∀ (I : Finset ℕ) (g m R : ℕ) (δ : ℝ),
      0 < g → (∀ v ∈ I, v ∈ inverseBoundedMultiples g ((m : ℝ) ^ 3)) →
      0 ≤ δ → δ < 1 / 2 → 2 ≤ R →
      (∫ t : UnitAddCircle,
        |circleFejerSmoothing (bohrUnion (normalizedBlock I g) δ) R (g • t) -
          circleSetIndicator (bohrUnion I δ) t| ∂circleHaar) ≤
        C * (I.card : ℝ) * (m : ℝ) ^ 3 *
          Real.log (2 * (R : ℝ)) / (R : ℝ)) :
    (∑ I ∈ F,
      ∫ t : UnitAddCircle,
        |circleFejerSmoothing (bohrUnion (normalizedBlock I (g I)) δ) R (g I • t) -
          circleSetIndicator (bohrUnion I δ) t| ∂circleHaar) ≤
      C * (m : ℝ) ^ 5 * Real.log (2 * (R : ℝ)) / (R : ℝ) := by
  have hRpos : (0 : ℝ) < R := by exact_mod_cast (by omega : 0 < R)
  have hlog : 0 ≤ Real.log (2 * (R : ℝ)) := by
    apply Real.log_nonneg
    have hRtwo : (2 : ℝ) ≤ R := by exact_mod_cast hR
    nlinarith
  have hterm (I : Finset ℕ) (hI : I ∈ F) :
      (∫ t : UnitAddCircle,
        |circleFejerSmoothing (bohrUnion (normalizedBlock I (g I)) δ) R (g I • t) -
          circleSetIndicator (bohrUnion I δ) t| ∂circleHaar) ≤
        C * (m : ℝ) ^ 4 * Real.log (2 * (R : ℝ)) / (R : ℝ) := by
    have h := hErr I (g I) m R δ (hg I hI) (hblock I hI) hδ0 hδhalf hR
    have hIc : (I.card : ℝ) ≤ m := by exact_mod_cast hcard I hI
    calc
      _ ≤ C * (I.card : ℝ) * (m : ℝ) ^ 3 *
        Real.log (2 * (R : ℝ)) / (R : ℝ) := h
      _ ≤ C * (m : ℝ) * (m : ℝ) ^ 3 *
        Real.log (2 * (R : ℝ)) / (R : ℝ) := by gcongr
      _ = C * (m : ℝ) ^ 4 * Real.log (2 * (R : ℝ)) / (R : ℝ) := by ring
  have hsum := Finset.sum_le_sum hterm
  have hFc : (F.card : ℝ) ≤ m := by exact_mod_cast hFcard
  calc
    _ ≤ ∑ _I ∈ F,
      C * (m : ℝ) ^ 4 * Real.log (2 * (R : ℝ)) / (R : ℝ) := hsum
    _ = (F.card : ℝ) *
      (C * (m : ℝ) ^ 4 * Real.log (2 * (R : ℝ)) / (R : ℝ)) := by simp
    _ ≤ (m : ℝ) *
      (C * (m : ℝ) ^ 4 * Real.log (2 * (R : ℝ)) / (R : ℝ)) := by gcongr
    _ = C * (m : ℝ) ^ 5 * Real.log (2 * (R : ℝ)) / (R : ℝ) := by ring

/-- 论文 `lem:merge`：真实平滑定理给出的统一累计误差，常数先于块族选取。 -/
theorem normalizedBlocks_smoothing_error_sum_actual :
    ∃ C : ℝ, 0 < C ∧
      ∀ (F : Finset (Finset ℕ)) (g : Finset ℕ → ℕ)
        (m R : ℕ) (δ : ℝ),
        (∀ I ∈ F, 0 < g I) →
        (∀ I ∈ F, ∀ v ∈ I,
          v ∈ inverseBoundedMultiples (g I) ((m : ℝ) ^ 3)) →
        (∀ I ∈ F, I.card ≤ m) → F.card ≤ m →
        0 ≤ δ → δ < 1 / 2 → 2 ≤ R →
        (∑ I ∈ F,
          ∫ t : UnitAddCircle,
            |circleFejerSmoothing (bohrUnion (normalizedBlock I (g I)) δ) R (g I • t) -
              circleSetIndicator (bohrUnion I δ) t| ∂circleHaar) ≤
          C * (m : ℝ) ^ 5 * Real.log (2 * (R : ℝ)) / (R : ℝ) := by
  obtain ⟨C, hC, hErr⟩ := normalizedBlock_smoothing_error
  refine ⟨C, hC, ?_⟩
  intro F g m R δ hg hblock hcard hFcard hδ0 hδhalf hR
  exact normalizedBlocks_smoothing_error_sum C hC F g m R δ
    hg hblock hcard hFcard hδ0 hδhalf hR hErr

private theorem merge_log_order_bound (m : ℕ) (hm : 2 ≤ m) :
    Real.log (2 * (m : ℝ) ^ 12) ≤ 8 * (m : ℝ) ^ 3 := by
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hp0 : 0 ≤ (m : ℝ) ^ 12 := pow_nonneg hm0 _
  have hpow : ((2 : ℝ) * (m : ℝ) ^ 12) ^ ((1 : ℝ) / 4) =
      (2 : ℝ) ^ ((1 : ℝ) / 4) * (m : ℝ) ^ 3 := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hp0]
    rw [← Real.rpow_natCast_mul hm0 12 (1 / 4)]
    norm_num
  have htwo : (2 : ℝ) ^ ((1 : ℝ) / 4) ≤ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (1 : ℝ) / 4 ≤ 1)
    simpa using h
  calc
    Real.log (2 * (m : ℝ) ^ 12) ≤
        (2 * (m : ℝ) ^ 12) ^ ((1 : ℝ) / 4) / ((1 : ℝ) / 4) :=
      Real.log_le_rpow_div (by positivity) (by norm_num)
    _ = 4 * ((2 : ℝ) ^ ((1 : ℝ) / 4) * (m : ℝ) ^ 3) := by rw [hpow]; ring
    _ ≤ 8 * (m : ℝ) ^ 3 := by nlinarith [mul_nonneg (sub_nonneg.mpr htwo) (pow_nonneg hm0 3)]

private theorem merge_smoothing_uniform_threshold (C : ℝ) (hC : 0 < C) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      C * (m : ℝ) ^ 5 * Real.log (2 * (m : ℝ) ^ 12) /
        ((m : ℝ) ^ 12) ≤ 1 / (16 * (m : ℝ) ^ 2) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (128 * C)
  refine ⟨max 2 N, ?_⟩
  intro m hm
  have hm2 : 2 ≤ m := (le_max_left _ _).trans hm
  have hmN : N ≤ m := (le_max_right _ _).trans hm
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hmpos : (0 : ℝ) < m := by linarith
  have hNreal : 128 * C ≤ (m : ℝ) := by
    have hnm : (N : ℝ) ≤ m := by exact_mod_cast hmN
    linarith
  have hm2pow : (m : ℝ) ≤ (m : ℝ) ^ 2 := le_self_pow₀ hmreal (by decide)
  have hCbound : 128 * C ≤ (m : ℝ) ^ 2 := hNreal.trans hm2pow
  have hlog := merge_log_order_bound m hm2
  calc
    C * (m : ℝ) ^ 5 * Real.log (2 * (m : ℝ) ^ 12) /
      ((m : ℝ) ^ 12) ≤
        C * (m : ℝ) ^ 5 * (8 * (m : ℝ) ^ 3) / (m : ℝ) ^ 12 := by
          gcongr
    _ = 8 * C / (m : ℝ) ^ 4 := by field_simp
    _ ≤ 1 / (16 * (m : ℝ) ^ 2) := by
      apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) ^ 4)
        (by positivity : (0 : ℝ) < 16 * (m : ℝ) ^ 2)).2
      nlinarith [mul_nonneg (sub_nonneg.mpr hCbound) (by positivity : (0 : ℝ) ≤ (m : ℝ) ^ 2)]

/-- 论文 `lem:merge`：在 `R=m¹²` 时，所有块的平滑误差之和小于 `ε/(2m)`。
门槛仅来自绝对平滑常数；没有加入速度高度假设。 -/
theorem extractedBlocks_smoothing_error_small :
    ∃ M : ℕ, ∀ (V : Finset ℕ) (m : ℕ) (δ : ℝ)
      (F : Finset (Finset ℕ)) (g : Finset ℕ → ℕ),
      m = V.card → M ≤ m → (∀ v ∈ V, 0 < v) →
      Covers V δ → 0 < δ → δ < 1 / 2 →
      (∀ I ∈ F, 0 < g I) →
      (∀ I ∈ F, ∀ v ∈ I,
        v ∈ inverseBoundedMultiples (g I) ((m : ℝ) ^ 3)) →
      (∀ I ∈ F, I.card ≤ m) → F.card ≤ m →
      (∑ I ∈ F,
        ∫ t : UnitAddCircle,
          |circleFejerSmoothing (bohrUnion (normalizedBlock I (g I)) δ)
              (m ^ 12) (g I • t) -
            circleSetIndicator (bohrUnion I δ) t| ∂circleHaar) ≤
        (2 * δ * (m : ℝ) - 1) / (2 * (m : ℝ)) := by
  obtain ⟨C, hC, hErr⟩ := normalizedBlocks_smoothing_error_sum_actual
  obtain ⟨M₀, hM₀⟩ := merge_smoothing_uniform_threshold C hC
  refine ⟨max 2 M₀, ?_⟩
  intro V m δ F g hmEq hmM hV hcover hδ hδhalf hg hblock hcard hFcard
  have hm2 : 2 ≤ m := (le_max_left _ _).trans hmM
  have hmM₀ : M₀ ≤ m := (le_max_right _ _).trans hmM
  have hmp : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hR : 2 ≤ m ^ 12 := by
    have hmle : m ≤ m ^ 12 := le_self_pow₀ (by omega : 1 ≤ m) (by decide)
    omega
  have hsum := hErr F g m (m ^ 12) δ hg hblock hcard hFcard hδ.le hδhalf hR
  have hRcast : ((m ^ 12 : ℕ) : ℝ) = (m : ℝ) ^ 12 := by norm_cast
  rw [hRcast] at hsum
  have hsmall := hM₀ m hmM₀
  have hε := (coverSecondMoment_and_epsilon_lower_of_covers V δ
    hV hδ hδhalf hcover m hmEq hm2).2
  have hεmul : (1 : ℝ) ≤ 8 * (m : ℝ) * (2 * δ * (m : ℝ) - 1) := by
    have h := (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * (m : ℝ))).1 hε
    nlinarith
  have hcomp : 1 / (16 * (m : ℝ) ^ 2) ≤
      (2 * δ * (m : ℝ) - 1) / (2 * (m : ℝ)) := by
    apply (div_le_div_iff₀
      (by positivity : (0 : ℝ) < 16 * (m : ℝ) ^ 2)
      (by positivity : (0 : ℝ) < 2 * (m : ℝ))).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hεmul) (le_of_lt hmp)]
  exact hsum.trans (hsmall.trans hcomp)

/-- 论文 `lem:merge` 式 (pivotmass) 的有限算术部分。
小量条件将在最终定理中由近覆盖指数界统一推出。 -/
theorem blockPivot_mass_lower (V P : Finset ℕ) (m : ℕ) (δ c η : ℝ)
    (hm : m = V.card) (hmpos : 0 < m)
    (hV : ∀ v ∈ V, 0 < v) (hP : P ⊆ V)
    (hcover : Covers V δ) (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hc : 0 < c) (hη : 0 < η)
    (hε : 0 < 2 * δ * (m : ℝ) - 1)
    (hsize : c / ((2 * δ * (m : ℝ) - 1) * (m : ℝ) ^ η) ≤ (P.card : ℝ))
    (hsmall : 2 * (m : ℝ) * (2 * δ * (m : ℝ) - 1) ^ 2 *
      (m : ℝ) ^ η ≤ c) :
    c / (2 * (m : ℝ) * (2 * δ * (m : ℝ) - 1) * (m : ℝ) ^ η) ≤
      circleHaar.real (bohrUnion P δ) := by
  let ε : ℝ := 2 * δ * (m : ℝ) - 1
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hPpos : ∀ v ∈ P, 0 < v := fun v hv => hV v (hP hv)
  have hδlower := cover_delta_lower_of_covers V δ hV hδ hδhalf
    hcover m hm hmpos
  have hE := coverExcess_le_epsilon V P δ hV hδ hδhalf hP hcover
  rw [← hm] at hE
  have hmass := bohrUnion_measureReal_eq_integral_sub_excess P δ hPpos hδ hδhalf
  have hpow : 0 < (m : ℝ) ^ η := by positivity
  have hden : 0 < ε * (m : ℝ) ^ η := by dsimp [ε]; positivity
  have hK : c / (ε * (m : ℝ) ^ η) ≤ (P.card : ℝ) := hsize
  have hsmall' : ε ≤ c / (2 * (m : ℝ) * ε * (m : ℝ) ^ η) := by
    apply (le_div_iff₀ (by dsimp [ε]; positivity)).2
    dsimp [ε] at *
    nlinarith
  have hδfactor : 1 / (m : ℝ) ≤ 2 * δ := by
    have hmul := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (m : ℝ))).1 hδlower
    apply (div_le_iff₀ hmreal).2
    nlinarith
  calc
    c / (2 * (m : ℝ) * ε * (m : ℝ) ^ η) ≤
      c / ((m : ℝ) * ε * (m : ℝ) ^ η) - ε := by
        have heq : c / ((m : ℝ) * ε * (m : ℝ) ^ η) =
            2 * (c / (2 * (m : ℝ) * ε * (m : ℝ) ^ η)) := by ring
        rw [heq]
        linarith
    _ ≤ (P.card : ℝ) / (m : ℝ) - ε := by
      have hdiv : c / ((m : ℝ) * ε * (m : ℝ) ^ η) =
          (c / (ε * (m : ℝ) ^ η)) / (m : ℝ) := by ring
      rw [hdiv]
      have hKdiv := div_le_div_of_nonneg_right hK hmreal.le
      linarith
    _ ≤ 2 * δ * (P.card : ℝ) - coverExcess P δ := by
      have hcard : (0 : ℝ) ≤ P.card := by positivity
      have hmul := mul_le_mul_of_nonneg_right hδfactor hcard
      change coverExcess P δ ≤ ε at hE
      have hmul' : (P.card : ℝ) / (m : ℝ) ≤ 2 * δ * (P.card : ℝ) := by
        convert hmul using 1 <;> ring
      linarith
    _ = circleHaar.real (bohrUnion P δ) := hmass.symm

/-- 论文 `lem:merge`：非空且互不相交的抽取块数量至多为速度数。 -/
theorem extractedBlocks_card_le (F : Finset (Finset ℕ)) (V : Finset ℕ)
    (hnonempty : ∀ I ∈ F, I.Nonempty)
    (hsub : ∀ I ∈ F, I ⊆ V)
    (hdisj : ∀ I ∈ F, ∀ J ∈ F, I ≠ J → Disjoint I J) :
    F.card ≤ V.card := by
  classical
  have hpair : (F : Set (Finset ℕ)).PairwiseDisjoint id := by
    intro I hI J hJ hne
    exact hdisj I hI J hJ hne
  have hsum : F.card ≤ ∑ I ∈ F, I.card := by
    calc
      F.card = ∑ _I ∈ F, (1 : ℕ) := by simp
      _ ≤ ∑ I ∈ F, I.card := by
        apply Finset.sum_le_sum
        intro I hI
        exact Finset.card_pos.mpr (hnonempty I hI)
  have hUnion : extractionUnion F ⊆ V := by
    intro v hv
    obtain ⟨I, hI, hvI⟩ := Finset.mem_biUnion.mp hv
    exact hsub I hI hvI
  calc
    F.card ≤ ∑ I ∈ F, I.card := hsum
    _ = (extractionUnion F).card := by
      exact (Finset.card_biUnion hpair).symm
    _ ≤ V.card := Finset.card_le_card hUnion

/-- 论文 `lem:merge`：近覆盖指数给出统一的小量条件。 -/
private theorem merge_smallness_threshold (η κ c : ℝ)
    (hη : 0 < η) (hκ : η < κ / 4) (hc : 0 < c) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      ∀ ε : ℝ, 0 < ε → ε ≤ (m : ℝ) ^ (-(1 / 2 + κ)) →
        (m : ℝ) * ε ^ 2 * (m : ℝ) ^ η ≤ c / 32 ∧ ε ≤ 1 / 8 := by
  have hκpos : 0 < κ := by linarith
  have hexp : 0 < 2 * κ - η := by linarith
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(2 * κ - η))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hexp).comp tendsto_natCast_atTop_atTop
  have htε : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / 2 + κ))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by linarith : 0 < (1 : ℝ) / 2 + κ)).comp
      tendsto_natCast_atTop_atTop
  obtain ⟨M₁, hM₁⟩ := eventually_atTop.1
    (ht.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < c / 32)))
  obtain ⟨M₂, hM₂⟩ := eventually_atTop.1
    (htε.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 8)))
  refine ⟨max 1 (max M₁ M₂), ?_⟩
  intro m hm ε hε hεbound
  have hm1 : (1 : ℝ) ≤ m := by
    exact_mod_cast ((le_max_left 1 (max M₁ M₂)).trans hm)
  have hmpos : (0 : ℝ) < m := by linarith
  have hBound₁ : M₁ ≤ m := (le_max_left M₁ M₂).trans
    ((le_max_right 1 (max M₁ M₂)).trans hm)
  have hBound₂ : M₂ ≤ m := (le_max_right M₁ M₂).trans
    ((le_max_right 1 (max M₁ M₂)).trans hm)
  have hpow : (m : ℝ) * ((m : ℝ) ^ (-(1 / 2 + κ))) ^ 2 *
      (m : ℝ) ^ η = (m : ℝ) ^ (-(2 * κ - η)) := by
    nth_rewrite 1 [← Real.rpow_one (m : ℝ)]
    rw [← Real.rpow_mul_natCast hmpos.le, ← Real.rpow_add hmpos,
      ← Real.rpow_add hmpos]
    congr 1
    ring
  have hsmall : (m : ℝ) * ε ^ 2 * (m : ℝ) ^ η ≤
      (m : ℝ) ^ (-(2 * κ - η)) := by
    calc
      _ ≤ (m : ℝ) * ((m : ℝ) ^ (-(1 / 2 + κ))) ^ 2 * (m : ℝ) ^ η := by
        gcongr
      _ = _ := hpow
  exact ⟨hsmall.trans (le_of_lt (hM₁ m hBound₁)),
    hεbound.trans (le_of_lt (hM₂ m hBound₂))⟩

/-- 论文 `lem:merge`：归一化并集和原块并集的 Haar 质量相等。 -/
theorem normalizedBlock_measure_eq (I : Finset ℕ) (g m : ℕ) (δ : ℝ)
    (hg : 0 < g) (hδ : 0 ≤ δ) (hδhalf : δ < 1 / 2)
    (hI : ∀ v ∈ I, v ∈ inverseBoundedMultiples g ((m : ℝ) ^ 3)) :
    circleHaar.real (bohrUnion (normalizedBlock I g) δ) =
      circleHaar.real (bohrUnion I δ) := by
  have hW : ∀ w ∈ normalizedBlock I g, 0 < w :=
    fun w hw => (normalizedBlock_positive_height I g m hg hI w hw).1
  have hMeas : MeasurableSet (bohrUnion (normalizedBlock I g) δ) :=
    bohrUnion_measurable_arcs (normalizedBlock I g) δ hW hδ hδhalf
  have hScale := bohrUnion_scale (normalizedBlock I g) g δ
  rw [normalizedBlock_image_eq I g m hg hI] at hScale
  have hMeasure : circleHaar (bohrUnion I δ) =
      circleHaar (bohrUnion (normalizedBlock I g) δ) := by
    rw [hScale]
    exact (circleHaar_measurePreserving_nsmul g hg).measure_preimage
      hMeas.nullMeasurableSet
  exact congrArg ENNReal.toReal hMeasure.symm

/-- 论文 `lem:merge`：主块质量与远块交集界给出远块速度数至多 `m/4`。 -/
theorem farBlocks_card_quarter (V : Finset ℕ) (m : ℕ) (δ c η : ℝ)
    (E : Finset (Finset ℕ)) (P : Finset ℕ)
    (hm : m = V.card) (hmpos : 0 < m)
    (hV : ∀ v ∈ V, 0 < v) (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hcover : Covers V δ) (hc : 0 < c)
    (hsub : ∀ I ∈ E, I ⊆ V)
    (hdisj : ∀ I ∈ E, ∀ J ∈ E, I ≠ J → Disjoint I J)
    (hε : 0 < 2 * δ * (m : ℝ) - 1)
    (hsmall : (m : ℝ) * (2 * δ * (m : ℝ) - 1) ^ 2 *
      (m : ℝ) ^ η ≤ c / 32)
    (hεsmall : 2 * δ * (m : ℝ) - 1 ≤ 1 / 8)
    (hpivot : c / (2 * (m : ℝ) * (2 * δ * (m : ℝ) - 1) *
      (m : ℝ) ^ η) ≤ circleHaar.real (bohrUnion P δ))
    (hfar : circleHaar.real (bohrUnion P δ) *
      (∑ I ∈ E, circleHaar.real (bohrUnion I δ)) ≤
        2 * (2 * δ * (m : ℝ) - 1)) :
    4 * (extractionUnion E).card ≤ m := by
  let ε : ℝ := 2 * δ * (m : ℝ) - 1
  let A : ℝ := ∑ I ∈ E, circleHaar.real (bohrUnion I δ)
  let N : ℝ := ∑ I ∈ E, (I.card : ℝ)
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hpow : 0 < (m : ℝ) ^ η := Real.rpow_pos_of_pos hmreal _
  have hden : 0 < 2 * (m : ℝ) * ε * (m : ℝ) ^ η := by positivity
  have hApos : 0 ≤ A := by
    dsimp [A]
    exact Finset.sum_nonneg (fun I hI => ENNReal.toReal_nonneg)
  have hAupper : c * A ≤ 4 * (m : ℝ) * ε ^ 2 * (m : ℝ) ^ η := by
    have hmul := mul_le_mul_of_nonneg_right hpivot hApos
    have hchain : (c / (2 * (m : ℝ) * ε * (m : ℝ) ^ η)) * A ≤ 2 * ε :=
      hmul.trans hfar
    have hchain' : c * A / (2 * (m : ℝ) * ε * (m : ℝ) ^ η) ≤ 2 * ε := by
      calc
        _ = (c / (2 * (m : ℝ) * ε * (m : ℝ) ^ η)) * A := by ring
        _ ≤ 2 * ε := hchain
    have hdiv := (div_le_iff₀ hden).1 hchain'
    nlinarith [hdiv]
  have hpair : (E : Set (Finset ℕ)).PairwiseDisjoint id := by
    intro I hI J hJ hne
    exact hdisj I hI J hJ hne
  have hcard : ((extractionUnion E).card : ℝ) = N := by
    dsimp [N]
    exact_mod_cast Finset.card_biUnion hpair
  have hEpos : ∀ I ∈ E, ∀ v ∈ I, 0 < v :=
    fun I hI v hv => hV v (hsub I hI hv)
  have hmass (I : Finset ℕ) (hI : I ∈ E) :
      2 * δ * (I.card : ℝ) =
        circleHaar.real (bohrUnion I δ) + coverExcess I δ := by
    have h := bohrUnion_measureReal_eq_integral_sub_excess I δ
      (hEpos I hI) hδ hδhalf
    linarith
  have hmassSum : 2 * δ * N = A + ∑ I ∈ E, coverExcess I δ := by
    dsimp [N, A]
    calc
      2 * δ * (∑ I ∈ E, (I.card : ℝ)) =
          ∑ I ∈ E, 2 * δ * (I.card : ℝ) := by rw [Finset.mul_sum]
      _ = ∑ I ∈ E,
          (circleHaar.real (bohrUnion I δ) + coverExcess I δ) :=
        Finset.sum_congr rfl hmass
      _ = _ := Finset.sum_add_distrib
  have hEbound : (∑ I ∈ E, coverExcess I δ) ≤ ε := by
    have h := sum_coverExcess_le_epsilon E id V δ hV hδ hδhalf
      hsub hpair hcover
    simpa [ε, hm] using h
  have hδlower := cover_delta_lower_of_covers V δ hV hδ hδhalf
    hcover m hm hmpos
  have hδfactor : 1 ≤ 2 * δ * (m : ℝ) := by
    have h := (div_le_iff₀
      (by positivity : (0 : ℝ) < 2 * (m : ℝ))).1 hδlower
    nlinarith
  have hNpos : 0 ≤ N := by
    dsimp [N]
    exact Finset.sum_nonneg (fun I hI => Nat.cast_nonneg _)
  have hNm : N ≤ (m : ℝ) * (A + ε) := by
    have h := mul_le_mul_of_nonneg_right hδfactor hNpos
    nlinarith [hmassSum]
  have hεterm : (m : ℝ) * ε ≤ (m : ℝ) / 8 := by
    nlinarith [mul_le_mul_of_nonneg_left hεsmall hmreal.le]
  have hbig : (m : ℝ) * A ≤ (m : ℝ) / 8 := by
    have h := mul_le_mul_of_nonneg_left hAupper hmreal.le
    have hsmall' := mul_le_mul_of_nonneg_left hsmall
      (show 0 ≤ 4 * (m : ℝ) / c by positivity)
    have hbound : (m : ℝ) * A ≤
        (4 * (m : ℝ) / c) * ((m : ℝ) * ε ^ 2 * (m : ℝ) ^ η) := by
      calc
        (m : ℝ) * A ≤
            (4 * (m : ℝ) * ((m : ℝ) * ε ^ 2 * (m : ℝ) ^ η)) / c := by
              apply (le_div_iff₀ hc).2
              nlinarith [h]
        _ = _ := by ring
    have hbound' := hbound.trans hsmall'
    have hcalc : (4 * (m : ℝ) / c) * (c / 32) = (m : ℝ) / 8 := by
      field_simp
      ring
    exact hbound'.trans_eq hcalc
  have hNquarter : N ≤ (m : ℝ) / 4 := by
    nlinarith [hNm, hbig, hεterm]
  have hNat : (4 * (extractionUnion E).card : ℝ) ≤ (m : ℝ) := by
    rw [hcard]
    linarith
  exact_mod_cast hNat

/-- 论文 `lem:merge`：有限频率分离与累计误差给出远块质量乘积界。 -/
theorem farBlocks_mass_product_bound (V : Finset ℕ) (m : ℕ) (δ : ℝ)
    (F E : Finset (Finset ℕ)) (P : Finset ℕ)
    (g : Finset ℕ → ℕ) (R : ℕ)
    (hm : m = V.card) (hmpos : 0 < m) (hR : 2 ≤ R)
    (hV : ∀ v ∈ V, 0 < v) (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hcover : Covers V δ)
    (hP : P ∈ F) (hsub : ∀ I ∈ F, I ⊆ V)
    (hdisj : ∀ I ∈ F, ∀ J ∈ F, I ≠ J → Disjoint I J)
    (hg : ∀ I ∈ F, 0 < g I)
    (hblock : ∀ I ∈ F, ∀ v ∈ I,
      v ∈ inverseBoundedMultiples (g I) ((m : ℝ) ^ 3))
    (hE : E ⊆ F.erase P)
    (hfar : ∀ I ∈ E,
      R < max (blockScaleNumer (g P) (g I))
        (blockScaleDenom (g P) (g I)))
    (hFcard : F.card ≤ m)
    (herror : (∑ I ∈ F,
      ∫ t : UnitAddCircle,
        |circleFejerSmoothing (bohrUnion (normalizedBlock I (g I)) δ)
            R (g I • t) - circleSetIndicator (bohrUnion I δ) t| ∂circleHaar) ≤
        (2 * δ * (m : ℝ) - 1) / (2 * (m : ℝ))) :
    circleHaar.real (bohrUnion P δ) *
      (∑ I ∈ E, circleHaar.real (bohrUnion I δ)) ≤
        2 * (2 * δ * (m : ℝ) - 1) := by
  let ε : ℝ := 2 * δ * (m : ℝ) - 1
  let ρ (I : Finset ℕ) : ℝ :=
    ∫ t : UnitAddCircle,
      |circleFejerSmoothing (bohrUnion (normalizedBlock I (g I)) δ)
          R (g I • t) - circleSetIndicator (bohrUnion I δ) t| ∂circleHaar
  let α (I : Finset ℕ) : ℝ := circleHaar.real (bohrUnion I δ)
  let β (I : Finset ℕ) : ℝ := circleHaar.real (bohrUnion P δ ∩ bohrUnion I δ)
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hPpos := hg P hP
  have hCross : (∑ I ∈ E, β I) ≤ ε := by
    have hCrossAll := blockCross_measure_bound V δ F P hP hsub hdisj
      hV hδ hδhalf hcover
    have hterm : ∀ I ∈ F.erase P, 0 ≤ β I := by
      intro I hI
      exact ENNReal.toReal_nonneg
    have hsum : (∑ I ∈ E, β I) ≤ ∑ I ∈ F.erase P, β I :=
      Finset.sum_le_sum_of_subset_of_nonneg hE (fun I hIF hIE => hterm I hIF)
    exact hsum.trans (by simpa [ε, β, hm] using hCrossAll)
  have hρnonneg : ∀ I ∈ F, 0 ≤ ρ I := by
    intro I hI
    dsimp [ρ]
    exact integral_nonneg (fun t => abs_nonneg _)
  have hsep : ∀ I ∈ E, |β I - α P * α I| ≤ ρ P + ρ I := by
    intro I hI
    have hIF : I ∈ F := Finset.mem_of_mem_erase (hE hI)
    obtain ⟨ha, hb, hcop, hrel, _⟩ :=
      blockScale_reduced (g P) (g I) hPpos (hg I hIF)
    have hPblock := hblock P hP
    have hIblock := hblock I hIF
    have hW : ∀ w ∈ normalizedBlock P (g P), 0 < w :=
      fun w hw => (normalizedBlock_positive_height P (g P) m hPpos hPblock w hw).1
    have hZ : ∀ z ∈ normalizedBlock I (g I), 0 < z :=
      fun z hz => (normalizedBlock_positive_height I (g I) m (hg I hIF) hIblock z hz).1
    have hSep := bohrUnion_intersection_separated
      (normalizedBlock P (g P)) (normalizedBlock I (g I)) δ R
      (g P) (g I)
      (blockScaleNumer (g P) (g I)) (blockScaleDenom (g P) (g I))
      hW hZ hδ.le hδhalf hR hPpos (hg I hIF)
      ha hb hrel hcop (Nat.le_of_lt (hfar I hI))
    rw [normalizedBlock_image_eq P (g P) m hPpos hPblock,
      normalizedBlock_image_eq I (g I) m (hg I hIF) hIblock,
      normalizedBlock_measure_eq P (g P) m δ hPpos hδ.le hδhalf hPblock,
      normalizedBlock_measure_eq I (g I) m δ (hg I hIF) hδ.le hδhalf hIblock]
      at hSep
    have hρP := bohrUnion_smoothing_pullback_error
      (normalizedBlock P (g P)) (g P) δ R hPpos hW hδ.le hδhalf
    rw [normalizedBlock_image_eq P (g P) m hPpos hPblock] at hρP
    have hρI := bohrUnion_smoothing_pullback_error
      (normalizedBlock I (g I)) (g I) δ R (hg I hIF) hZ hδ.le hδhalf
    rw [normalizedBlock_image_eq I (g I) m (hg I hIF) hIblock] at hρI
    simpa [ρ, α, β, ← hρP, ← hρI] using hSep
  have hprod := farBlock_mass_sum E (α P) ε (ρ P) α ρ β hCross hsep
  have hρP : ρ P ≤ ∑ I ∈ F, ρ I :=
    Finset.single_le_sum (fun I hI => hρnonneg I hI) hP
  have hρE : (∑ I ∈ E, ρ I) ≤ ∑ I ∈ F, ρ I := by
    have hEF : E ⊆ F := hE.trans (Finset.erase_subset P F)
    exact Finset.sum_le_sum_of_subset_of_nonneg hEF
      (fun I hIF hIE => hρnonneg I hIF)
  have hEcard : E.card ≤ m :=
    (Finset.card_le_card (hE.trans (Finset.erase_subset P F))).trans hFcard
  have hEcardreal : (E.card : ℝ) ≤ m := by exact_mod_cast hEcard
  have hρPpos : 0 ≤ ρ P := hρnonneg P hP
  have hρsum : 0 ≤ ∑ I ∈ F, ρ I := Finset.sum_nonneg hρnonneg
  have herror' : (∑ I ∈ F, ρ I) ≤ ε / (2 * (m : ℝ)) := herror
  have hsmallerror : (E.card : ℝ) * ρ P + ∑ I ∈ E, ρ I ≤ ε := by
    have h1 := mul_le_mul_of_nonneg_left hρP hmreal.le
    have h2 := mul_le_mul_of_nonneg_right hEcardreal hρPpos
    have h3 : (E.card : ℝ) * ρ P ≤ (m : ℝ) * (∑ I ∈ F, ρ I) :=
      h2.trans h1
    have hbound : ((m : ℝ) + 1) * (∑ I ∈ F, ρ I) ≤ ε := by
      have h := mul_le_mul_of_nonneg_left herror' (by linarith : 0 ≤ (m : ℝ) + 1)
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hmpos
      have hεpos : 0 ≤ ε := by
        have hε0 := coverExcess_eq_epsilon V δ hV hδ hδhalf hcover
        rw [← hm] at hε0
        have hnon : 0 ≤ coverExcess V δ :=
          integral_nonneg (fun t => le_max_right _ _)
        rw [hε0] at hnon
        exact hnon
      have hfactor : ((m : ℝ) + 1) / (2 * (m : ℝ)) ≤ 1 := by
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (m : ℝ))).2
        linarith
      calc
        _ ≤ ((m : ℝ) + 1) * (ε / (2 * (m : ℝ))) :=
          mul_le_mul_of_nonneg_left herror' (by linarith)
        _ = (((m : ℝ) + 1) / (2 * (m : ℝ))) * ε := by ring
        _ ≤ 1 * ε := mul_le_mul_of_nonneg_right hfactor hεpos
        _ = ε := one_mul ε
    linarith [h3, hρE]
  dsimp [α] at hprod
  nlinarith [hprod, hsmallerror]

/-- 论文 `lem:merge`：保留块的尺度最小公倍数给出所需高度对数界。 -/
private theorem merge_height_log_bound (m s Q₀ : ℕ) (c ε η : ℝ)
    (hm : 2 ≤ m) (hQpos : 0 < Q₀) (hQle : Q₀ ≤ (m ^ 12) ^ s)
    (hc : 0 < c) (hε : 0 < ε)
    (hsize : (s : ℝ) * (c / (ε * (m : ℝ) ^ η)) ≤ (m : ℝ)) :
    Real.log (((m ^ 3 * m ^ 12 * Q₀ : ℕ) : ℝ)) ≤
      (15 + 12 / c) * ((m : ℝ) * ε * (m : ℝ) ^ η + 1) *
        Real.log (2 * (m : ℝ)) := by
  have hmreal : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hmone : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hlogm : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hmone
  have hlog2m : 0 ≤ Real.log (2 * (m : ℝ)) :=
    Real.log_nonneg (by nlinarith : (1 : ℝ) ≤ 2 * (m : ℝ))
  have hlogcomp : Real.log (m : ℝ) ≤ Real.log (2 * (m : ℝ)) :=
    Real.log_le_log hmreal (by nlinarith)
  have hQcast : (Q₀ : ℝ) ≤ ((m : ℝ) ^ 12) ^ s := by
    exact_mod_cast hQle
  have hQreal : (0 : ℝ) < Q₀ := by exact_mod_cast hQpos
  have hTpos : (0 : ℝ) < ((m ^ 3 * m ^ 12 * Q₀ : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.mul_pos (pow_pos (by omega : 0 < m) 3)
      (pow_pos (by omega : 0 < m) 12)) hQpos
  have hTle : ((m ^ 3 * m ^ 12 * Q₀ : ℕ) : ℝ) ≤
      (m : ℝ) ^ 3 * (m : ℝ) ^ 12 * ((m : ℝ) ^ 12) ^ s := by
    push_cast
    gcongr
  have hTlog : Real.log (((m ^ 3 * m ^ 12 * Q₀ : ℕ) : ℝ)) ≤
      (15 + 12 * (s : ℝ)) * Real.log (m : ℝ) := by
    have h := Real.log_le_log hTpos hTle
    have hpowpos : (0 : ℝ) < (m : ℝ) ^ 3 * (m : ℝ) ^ 12 := by positivity
    rw [Real.log_mul (ne_of_gt hpowpos)
        (ne_of_gt (by positivity : (0 : ℝ) < ((m : ℝ) ^ 12) ^ s)),
      Real.log_mul (ne_of_gt (by positivity : (0 : ℝ) < (m : ℝ) ^ 3))
        (ne_of_gt (by positivity : (0 : ℝ) < (m : ℝ) ^ 12)),
      Real.log_pow, Real.log_pow, Real.log_pow] at h
    simp only [Real.log_pow] at h
    calc
      _ ≤ (3 : ℝ) * Real.log (m : ℝ) + 12 * Real.log (m : ℝ) +
          (s : ℝ) * (12 * Real.log (m : ℝ)) := h
      _ = (15 + 12 * (s : ℝ)) * Real.log (m : ℝ) := by ring
  have hden : 0 < ε * (m : ℝ) ^ η := by positivity
  have hs : (s : ℝ) * c ≤ (m : ℝ) * ε * (m : ℝ) ^ η := by
    have h := (div_le_iff₀ hden).1 (by
      calc
        (s : ℝ) * c / (ε * (m : ℝ) ^ η) =
            (s : ℝ) * (c / (ε * (m : ℝ) ^ η)) := by ring
        _ ≤ (m : ℝ) := hsize)
    nlinarith [h]
  have hX : 0 ≤ (m : ℝ) * ε * (m : ℝ) ^ η := by positivity
  have hcoef : 15 + 12 * (s : ℝ) ≤
      (15 + 12 / c) * ((m : ℝ) * ε * (m : ℝ) ^ η + 1) := by
    have hs' : (s : ℝ) ≤ ((m : ℝ) * ε * (m : ℝ) ^ η) / c :=
      (le_div_iff₀ hc).2 hs
    have hc0 : 0 ≤ 12 / c := by positivity
    calc
      15 + 12 * (s : ℝ) ≤
          15 + 12 * (((m : ℝ) * ε * (m : ℝ) ^ η) / c) := by linarith
      _ = 15 + (12 / c) * ((m : ℝ) * ε * (m : ℝ) ^ η) := by ring
      _ ≤ 15 + (12 / c) * ((m : ℝ) * ε * (m : ℝ) ^ η) +
          15 * ((m : ℝ) * ε * (m : ℝ) ^ η) + 12 / c := by
        nlinarith [hX, hc0]
      _ = _ := by ring
  have hcoefnonneg : 0 ≤ 15 + 12 * (s : ℝ) := by positivity
  calc
    _ ≤ (15 + 12 * (s : ℝ)) * Real.log (m : ℝ) := hTlog
    _ ≤ (15 + 12 * (s : ℝ)) * Real.log (2 * (m : ℝ)) :=
      mul_le_mul_of_nonneg_left hlogcomp hcoefnonneg
    _ ≤ (15 + 12 / c) * ((m : ℝ) * ε * (m : ℝ) ^ η + 1) *
        Real.log (2 * (m : ℝ)) :=
      mul_le_mul_of_nonneg_right hcoef hlog2m

/-- 论文 `lem:merge`：近覆盖下把抽取的完整块合并到同一公因子。
常数仅依赖 `η`，门槛仅依赖 `κ,η`；结论没有平滑或远块辅助假设。 -/
theorem blockMerge :
    ∀ η : ℝ, 0 < η →
      ∃ Cη : ℝ, 0 < Cη ∧
        ∀ κ : ℝ, η < κ / 4 → κ < 1 / 4 →
          ∃ M : ℕ, ∀ (V : Finset ℕ) (m : ℕ) (δ : ℝ),
            (∀ v ∈ V, 0 < v) → m = V.card → M ≤ m →
            Covers V δ → 0 < δ → δ < 1 / 2 →
            let ε := 2 * δ * (m : ℝ) - 1
            0 < ε → ε ≤ (m : ℝ) ^ (-(1 / 2 + κ)) →
            ∃ C : Finset ℕ, ∃ G T : ℕ,
              C ⊆ V ∧ 0 < G ∧ 1 ≤ T ∧ G = C.gcd id ∧
              m ≤ 2 * C.card ∧
              (∀ v ∈ C, v ∈ inverseBoundedMultiples G (T : ℝ)) ∧
              Real.log (T : ℝ) ≤
                Cη * ((m : ℝ) * ε * (m : ℝ) ^ η + 1) *
                  Real.log (2 * (m : ℝ)) := by
  classical
  intro η hη
  obtain ⟨c, hc, hExtract⟩ := blockExtraction η hη
  let Cη : ℝ := 15 + 12 / c
  have hCη : 0 < Cη := by dsimp [Cη]; positivity
  refine ⟨Cη, hCη, ?_⟩
  intro κ hηκ hκ4
  have hηκ' : η < κ := by linarith
  obtain ⟨M₁, hExtractM⟩ := hExtract κ hηκ' hκ4
  obtain ⟨M₂, hSmoothM⟩ := extractedBlocks_smoothing_error_small
  obtain ⟨M₃, hSmallM⟩ := merge_smallness_threshold η κ c hη hηκ hc
  refine ⟨max 2 (max M₁ (max M₂ M₃)), ?_⟩
  intro V m δ hV hm hmM hcover hδ hδhalf ε hε hεbound
  have hm2 : 2 ≤ m := (le_max_left 2 (max M₁ (max M₂ M₃))).trans hmM
  have hmpos : 0 < m := by omega
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hmM₁ : M₁ ≤ m := (le_max_left M₁ (max M₂ M₃)).trans
    ((le_max_right 2 (max M₁ (max M₂ M₃))).trans hmM)
  have hmM₂ : M₂ ≤ m := (le_max_left M₂ M₃).trans
    ((le_max_right M₁ (max M₂ M₃)).trans
      ((le_max_right 2 (max M₁ (max M₂ M₃))).trans hmM))
  have hmM₃ : M₃ ≤ m := (le_max_right M₂ M₃).trans
    ((le_max_right M₁ (max M₂ M₃)).trans
      ((le_max_right 2 (max M₁ (max M₂ M₃))).trans hmM))
  obtain ⟨hsmall, hεsmall⟩ := hSmallM m hmM₃ ε hε hεbound
  obtain ⟨F, g, hF, hdisj, hlarge, hbudget⟩ :=
    hExtractM V m δ hV hm hmM₁ hcover hδ hδhalf hε hεbound
  have hFpos : ∀ I ∈ F, I.Nonempty := fun I hI => (hF I hI).1
  have hFsub : ∀ I ∈ F, I ⊆ V := fun I hI => (hF I hI).2.1
  have hg : ∀ I ∈ F, 0 < g I := fun I hI => (hF I hI).2.2.1
  have hblock : ∀ I ∈ F, ∀ v ∈ I,
      v ∈ inverseBoundedMultiples (g I) ((m : ℝ) ^ 3) :=
    fun I hI => (hF I hI).2.2.2.1
  have hsize : ∀ I ∈ F,
      c / (ε * (m : ℝ) ^ η) ≤ (I.card : ℝ) :=
    fun I hI => (hF I hI).2.2.2.2
  have hFcard : F.card ≤ m :=
    extractedBlocks_card_le F V hFpos hFsub hdisj |>.trans (by rw [← hm])
  obtain ⟨P, hP⟩ : F.Nonempty := by
    by_contra hNone
    have hEmpty : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hNone
    simp [hEmpty, extractionUnion] at hlarge
    linarith
  have hPsub : P ⊆ V := hFsub P hP
  have htwosmall : 2 * (m : ℝ) * ε ^ 2 * (m : ℝ) ^ η ≤ c := by
    nlinarith [hsmall]
  have hpivot := blockPivot_mass_lower V P m δ c η hm hmpos hV hPsub
    hcover hδ hδhalf hc hη hε (hsize P hP) htwosmall
  let R : ℕ := m ^ 12
  have hR : 2 ≤ R := by
    dsimp [R]
    exact le_trans hm2 (le_self_pow₀ (by omega : 1 ≤ m) (by decide))
  have hRpos : 0 < R := by omega
  let far : Finset (Finset ℕ) :=
    (F.erase P).filter (fun I =>
      R < max (blockScaleNumer (g P) (g I))
        (blockScaleDenom (g P) (g I)))
  let near : Finset (Finset ℕ) :=
    F.filter (fun I =>
      max (blockScaleNumer (g P) (g I))
        (blockScaleDenom (g P) (g I)) ≤ R)
  have hfar : far ⊆ F.erase P := Finset.filter_subset _ _
  have hnear : near ⊆ F := Finset.filter_subset _ _
  have hfarcond : ∀ I ∈ far,
      R < max (blockScaleNumer (g P) (g I))
        (blockScaleDenom (g P) (g I)) := by
    intro I hI
    exact (Finset.mem_filter.mp hI).2
  have hnearcond : ∀ I ∈ near,
      max (blockScaleNumer (g P) (g I))
        (blockScaleDenom (g P) (g I)) ≤ R := by
    intro I hI
    exact (Finset.mem_filter.mp hI).2
  have hPnear : P ∈ near := by
    apply Finset.mem_filter.mpr
    constructor
    · exact hP
    · have hgP := hg P hP
      simp [blockScaleNumer, blockScaleDenom, Nat.gcd_self,
        Nat.div_self hgP]
      omega
  have hpartition : near ∪ far = F := by
    ext I
    constructor
    · intro hI
      rcases Finset.mem_union.mp hI with hI | hI
      · exact hnear hI
      · exact Finset.mem_of_mem_erase (hfar hI)
    · intro hI
      rcases le_or_gt (max (blockScaleNumer (g P) (g I))
          (blockScaleDenom (g P) (g I))) R with hle | hgt
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hI, hle⟩))
      · have hIP : I ≠ P := by
          intro hEq
          subst I
          exact (not_lt_of_ge (Finset.mem_filter.mp hPnear).2) hgt
        exact Finset.mem_union.mpr (Or.inr
          (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hIP, hI⟩, hgt⟩))
  have hcardI : ∀ I ∈ F, I.card ≤ m := by
    intro I hI
    rw [hm]
    exact Finset.card_le_card (hFsub I hI)
  have herror := hSmoothM V m δ F g hm hmM₂ hV hcover hδ hδhalf
    hg hblock hcardI hFcard
  have hfarprod := farBlocks_mass_product_bound V m δ F far P g R
    hm hmpos hR hV hδ hδhalf hcover hP hFsub hdisj hg hblock
    hfar hfarcond hFcard herror
  have hfarcard : 4 * (extractionUnion far).card ≤ m :=
    farBlocks_card_quarter V m δ c η far P hm hmpos hV hδ hδhalf
      hcover hc (fun I hI => hFsub I (Finset.mem_of_mem_erase (hfar hI)))
      (fun I hI J hJ hne => hdisj I
        (Finset.mem_of_mem_erase (hfar hI)) J
        (Finset.mem_of_mem_erase (hfar hJ)) hne)
      hε hsmall hεsmall hpivot hfarprod
  let C : Finset ℕ := extractionUnion near
  have hCsub : C ⊆ V := by
    intro v hv
    obtain ⟨I, hI, hvI⟩ := Finset.mem_biUnion.mp hv
    exact hFsub I (hnear hI) hvI
  have hUnionEq : extractionUnion F = C ∪ extractionUnion far := by
    ext v
    constructor
    · intro hv
      obtain ⟨I, hIF, hvI⟩ := Finset.mem_biUnion.mp hv
      rw [← hpartition] at hIF
      rcases Finset.mem_union.mp hIF with hIN | hIE
      · exact Finset.mem_union.mpr (Or.inl
          (Finset.mem_biUnion.mpr ⟨I, hIN, hvI⟩))
      · exact Finset.mem_union.mpr (Or.inr
          (Finset.mem_biUnion.mpr ⟨I, hIE, hvI⟩))
    · intro hv
      rcases Finset.mem_union.mp hv with hv | hv
      · obtain ⟨I, hIN, hvI⟩ := Finset.mem_biUnion.mp hv
        exact Finset.mem_biUnion.mpr ⟨I, hnear hIN, hvI⟩
      · obtain ⟨I, hIE, hvI⟩ := Finset.mem_biUnion.mp hv
        exact Finset.mem_biUnion.mpr
          ⟨I, Finset.mem_of_mem_erase (hfar hIE), hvI⟩
  have hCdisj : Disjoint C (extractionUnion far) := by
    apply Finset.disjoint_left.mpr
    intro v hvC hvFar
    obtain ⟨I, hI, hvI⟩ := Finset.mem_biUnion.mp hvC
    obtain ⟨J, hJ, hvJ⟩ := Finset.mem_biUnion.mp hvFar
    have hIF := hnear hI
    have hJF := Finset.mem_of_mem_erase (hfar hJ)
    have hne : I ≠ J := by
      intro heq
      subst J
      exact (not_lt_of_ge (hnearcond I hI)) (hfarcond I hJ)
    exact (Finset.disjoint_left.mp (hdisj I hIF J hJF hne)) hvI hvJ
  have hCcard : m ≤ 2 * C.card := by
    have hcardEq : (extractionUnion F).card =
        C.card + (extractionUnion far).card := by
      rw [hUnionEq, Finset.card_union_of_disjoint hCdisj]
    have hLargeNat : 3 * m < 4 * (extractionUnion F).card := by
      have h := hlarge
      exact_mod_cast (by nlinarith : (3 * (m : ℝ)) <
        4 * ((extractionUnion F).card : ℝ))
    omega
  have hCpos : C.Nonempty := Finset.card_pos.mp (by omega : 0 < C.card)
  have hCvel : ∀ v ∈ C, 0 < v := fun v hv => hV v (hCsub hv)
  let Q₀ := near.lcm (fun I => blockScaleDenom (g P) (g I))
  let T : ℕ := m ^ 3 * R * Q₀
  obtain ⟨hGpos, hCrep, hQdvd, hQle⟩ :=
    blockScale_common_gcd near g P R (m ^ 3) hCpos hCvel
      (hg P hP) hRpos (by positivity : 0 < m ^ 3)
      (fun I hI => hg I (hnear hI)) hnearcond
      (extractedBlock_nat_height near g m
        (fun I hI => hblock I (hnear hI)))
  have hTpos : 1 ≤ T := by
    have hQpos : 0 < Q₀ := Nat.pos_of_dvd_of_pos hQdvd (hg P hP)
    dsimp [T]
    exact Nat.mul_pos (Nat.mul_pos (pow_pos hmpos 3) hRpos) hQpos
  have hnearBudget : (near.card : ℝ) *
      (c / (ε * (m : ℝ) ^ η)) ≤ (m : ℝ) := by
    have hle : near.card ≤ F.card := Finset.card_le_card hnear
    have hK : 0 ≤ c / (ε * (m : ℝ) ^ η) := by positivity
    exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hle) hK).trans hbudget
  have hQpos : 0 < Q₀ := Nat.pos_of_dvd_of_pos hQdvd (hg P hP)
  have hTlog := merge_height_log_bound m near.card Q₀ c ε η
    hm2 hQpos (by simpa [R] using hQle) hc hε hnearBudget
  refine ⟨C, C.gcd id, T, hCsub, hGpos, hTpos, rfl, hCcard, ?_, ?_⟩
  · simpa [C, T, Q₀] using hCrep
  · simpa [Cη, T, R] using hTlog

#print axioms blockScale_reduced
#print axioms blockScale_lcm_bound
#print axioms blockScale_common_gcd
#print axioms farBlock_mass_sum
#print axioms normalizedBlocks_smoothing_error_sum_actual
#print axioms extractedBlocks_smoothing_error_small
#print axioms blockPivot_mass_lower
#print axioms blockMerge
end LonelyRunner
