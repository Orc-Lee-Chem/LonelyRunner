import LonelyRunner.NearCoverDimension
import LonelyRunner.BedertLowDimensionModel
import LonelyRunner.BedertSmallHeight
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# 不可约本原近覆盖的矛盾

接通论文 `prop:dimension`、`prop:bedert` 与收尾的渐近比较。
全部门槛先于速度集及覆盖参数选取；逐点使用同一个时刻导出矛盾。
-/

namespace LonelyRunner
open Finset Filter
open scoped Topology

/-- 实际最大维数可以由自然数速度子集取到，且正非空族的维数在 `[1,|V|]`。
整数嵌入及旧速度解离定义均使用已证等价，不更换定义。 -/
theorem nearCover_actual_dimension (V : Finset ℕ) (hV : ∀ v ∈ V, 0 < v)
    (hne : V.Nonempty) :
    let d := twoDissociatedDimension (V.image (fun v : ℕ => (v : ℤ)))
    1 ≤ d ∧ d ≤ V.card ∧ ∃ D ⊆ V, TwoDissociatedSpeeds D ∧ D.card = d := by
  classical
  intro d
  obtain ⟨D, hDV, hD, hcard⟩ :=
    twoDissociatedDimension_attained (V.image (fun v : ℕ => (v : ℤ)))
  let S := V.filter (fun v : ℕ => (v : ℤ) ∈ D)
  have hSV : S ⊆ V := filter_subset _ _
  have himage : S.image (fun v : ℕ => (v : ℤ)) = D := by
    apply subset_antisymm
    · intro x hx
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hx
      exact (mem_filter.mp hv).2
    · intro x hx
      obtain ⟨v, hv, rfl⟩ := mem_image.mp (hDV hx)
      exact mem_image.mpr ⟨v, mem_filter.mpr ⟨hv, hx⟩, rfl⟩
  have hScard : S.card = d := by
    calc
      _ = (S.image (fun v : ℕ => (v : ℤ))).card :=
        (card_image_iff.mpr (fun a ha b hb he => Nat.cast_injective he)).symm
      _ = d := by rw [himage]; exact hcard
  have hS : TwoDissociatedSpeeds S :=
    (twoDissociated_speeds_iff S).mp (by rw [himage]; exact hD)
  obtain ⟨v, hv⟩ := hne
  have hv0 : (v : ℤ) ≠ 0 := by exact_mod_cast (hV v hv).ne'
  have hsingle : TwoDissociated ({(v : ℤ)} : Finset ℤ) := by
    intro c hc hs x hx
    have hmul : c (v : ℤ) * (v : ℤ) = 0 := by simpa [zsmul_eq_mul] using hs
    have hz := (mul_eq_zero.mp hmul).resolve_right hv0
    have hxv : x = (v : ℤ) := mem_singleton.mp hx
    simpa only [hxv] using hz
  have hlow : 1 ≤ d := by
    have hh := card_le_twoDissociatedDimension
      (singleton_subset_iff.mpr (mem_image.mpr ⟨v, hv, rfl⟩)) hsingle
    simpa only [card_singleton] using hh
  exact ⟨hlow, by rw [← hScard]; exact card_le_card hSV, S, hSV, hS, hScard⟩

/-- 对任意正幂，`log(2m)^2 m^(-s)` 趋于零。
实际调用 Mathlib 的对数实幂 little-o，处理 `2m` 的尺度及自然数极限。 -/
theorem nearCover_log_square_decay (s : ℝ) (hs : 0 < s) :
    Tendsto (fun m : ℕ => Real.log (2 * (m : ℝ))^2 * (m : ℝ)^(-s))
      atTop (𝓝 0) := by
  have htwom : Tendsto (fun m : ℕ => 2 * (m : ℝ)) atTop atTop := by
    simpa only [mul_comm] using
      (tendsto_natCast_atTop_atTop.atTop_mul_const (by norm_num : (0 : ℝ) < 2))
  have ht := ((isLittleO_log_rpow_rpow_atTop (2 : ℝ) hs).tendsto_div_nhds_zero).comp htwom
  have hmul := ht.mul_const ((2 : ℝ)^s)
  simp only [zero_mul] at hmul
  apply hmul.congr'
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  dsimp only [Function.comp_apply]
  rw [Real.rpow_neg hmR.le, Real.mul_rpow (by norm_num) hmR.le]
  norm_num only [Real.rpow_ofNat]
  field_simp

/-- 固定参数后先选统一门槛：模型高度进入小高度范围，且小高度增益
严格大于原近覆盖误差与模型误差之和。两个结论都由实际极限取得。 -/
theorem nearCoverContradiction_numeric (κ A b : ℝ) (hκ : 0 < κ) (hA : 0 < A) (hb : 0 < b) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → 2 ≤ m →
      2048 * A * Real.sqrt (m : ℝ) * Real.log (2 * (m : ℝ))^2 ≤ (m : ℝ)^(3/4 : ℝ) ∧
      (1/2 : ℝ) * (m : ℝ)^(-3/2-κ) + (m : ℝ)^(-100 : ℝ) <
        b / (2048 * A * (m : ℝ)^(3/2 : ℝ) * Real.log (2 * (m : ℝ))^2) := by
  let C := 2048 * A
  have hC : 0 < C := by dsimp [C]; positivity
  have hh := (nearCover_log_square_decay (1/4) (by norm_num)).const_mul C
  have he := ((nearCover_log_square_decay κ hκ).const_mul (1/2 : ℝ)).add
    (nearCover_log_square_decay (197/2) (by norm_num))
  have heC := he.const_mul C
  simp only [mul_zero, zero_add] at hh heC
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (hh.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)))
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (heC.eventually (eventually_lt_nhds hb))
  refine ⟨max N₁ N₂, ?_⟩
  intro m hm hm2
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hlog : 0 < Real.log (2 * (m : ℝ)) := Real.log_pos (by
    have hh : (2 : ℝ) ≤ m := by exact_mod_cast hm2
    linarith)
  have hheight := (hN₁ m ((le_max_left _ _).trans hm)).le
  have herr := hN₂ m ((le_max_right _ _).trans hm)
  have hpowsqrt : (m : ℝ)^(-(1/4 : ℝ)) * (m : ℝ)^(3/4 : ℝ) = Real.sqrt (m : ℝ) := by
    rw [← Real.rpow_add hmR]
    norm_num
    exact (Real.sqrt_eq_rpow _).symm
  have hheight' : C * Real.sqrt (m : ℝ) * Real.log (2 * (m : ℝ))^2 ≤ (m : ℝ)^(3/4 : ℝ) := by
    calc
      _ = (C * Real.log (2 * (m : ℝ))^2) *
          ((m : ℝ)^(-(1/4 : ℝ)) * (m : ℝ)^(3/4 : ℝ)) := by rw [hpowsqrt]; ring
      _ = (C * (Real.log (2 * (m : ℝ))^2 * (m : ℝ)^(-(1/4 : ℝ)))) *
          (m : ℝ)^(3/4 : ℝ) := by ring
      _ ≤ 1 * (m : ℝ)^(3/4 : ℝ) := mul_le_mul_of_nonneg_right hheight (by positivity)
      _ = _ := one_mul _
  have hpow₁ : (m : ℝ)^(3/2 : ℝ) * (m : ℝ)^(-3/2-κ) = (m : ℝ)^(-κ) := by
    rw [← Real.rpow_add hmR]
    congr 1
    ring
  have hpow₂ : (m : ℝ)^(3/2 : ℝ) * (m : ℝ)^(-100 : ℝ) = (m : ℝ)^(-(197/2 : ℝ)) := by
    rw [← Real.rpow_add hmR]
    norm_num
  have hden : 0 < C * (m : ℝ)^(3/2 : ℝ) * Real.log (2 * (m : ℝ))^2 := by positivity
  refine ⟨hheight', ?_⟩
  apply (lt_div_iff₀ hden).mpr
  calc
    _ = C * ((1/2 : ℝ) * (Real.log (2 * (m : ℝ))^2 * (m : ℝ)^(-κ)) +
        Real.log (2 * (m : ℝ))^2 * (m : ℝ)^(-(197/2 : ℝ))) := by
      calc
        _ = C * Real.log (2 * (m : ℝ))^2 *
          ((1/2 : ℝ) * ((m : ℝ)^(3/2 : ℝ) * (m : ℝ)^(-3/2-κ)) +
            (m : ℝ)^(3/2 : ℝ) * (m : ℝ)^(-100 : ℝ)) := by ring
        _ = _ := by rw [hpow₁, hpow₂]; ring
    _ < b := herr

/-- 对每个 `0<κ<1/4`，足够大的本原不可约近覆盖不存在。
维数、模型、渐近比较和小高度时刻全部调用已证明结果取得；
自然数起点在引入 `V,δ` 之前选定，只依赖 `κ`。 -/
theorem nearCoverContradiction :
    ∀ κ : ℝ, 0 < κ → κ < 1/4 → ∃ M : ℕ,
      ∀ (V : Finset ℕ) (δ : ℝ),
        (∀ v ∈ V, 0 < v) → M ≤ V.card →
        IrreducibleCover V δ → V.gcd id = 1 → 0 < δ → δ < 1/2 →
        let ε := 2 * δ * (V.card : ℝ) - 1
        0 < ε → ε ≤ (V.card : ℝ)^(-(1/2+κ)) → False := by
  obtain ⟨b, hb, Msmall, hsmall⟩ := bedert_small_height
  intro κ hκ hκ4
  obtain ⟨A, hA, Mdim, hdimension⟩ := nearCover_dimension_bound κ hκ hκ4
  obtain ⟨N, hnumeric⟩ := nearCoverContradiction_numeric κ A b hκ hA hb
  refine ⟨max 2 (max Mdim (max Msmall N)), ?_⟩
  intro V δ hV hM hirr hgcd hδ hδhalf ε hε hεbound
  let m := V.card
  have hm2 : 2 ≤ m := (le_max_left _ _).trans hM
  have hrest : max Mdim (max Msmall N) ≤ m := (le_max_right _ _).trans hM
  have hmDim : Mdim ≤ m := (le_max_left _ _).trans hrest
  have hmSmall : Msmall ≤ m := (le_max_left _ _).trans ((le_max_right _ _).trans hrest)
  have hmNum : N ≤ m := (le_max_right _ _).trans ((le_max_right _ _).trans hrest)
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hlog : 0 < Real.log (2 * (m : ℝ)) := Real.log_pos (by
    have hh : (2 : ℝ) ≤ m := by exact_mod_cast hm2
    linarith)
  let d := twoDissociatedDimension (V.image (fun v : ℕ => (v : ℤ)))
  obtain ⟨hd, hdm, D, hDV, hD, hDcard⟩ := nearCover_actual_dimension V hV
    (card_pos.mp (show 0 < V.card by omega))
  have hdUpper : (d : ℝ) ≤ A * Real.sqrt (m : ℝ) * Real.log (2 * (m : ℝ)) := by
    have hh := hdimension V δ hV hmDim hirr hgcd hδ hδhalf hε hεbound D hDV hD
    simpa only [hDcard] using hh
  have hcover : ∀ t : UnitAddCircle, ∃ v ∈ V, dist (v • t) 0 ≤ δ := by
    intro t
    obtain ⟨v, hv, hvt⟩ := hirr.1 t
    exact ⟨v, hv, (mem_bohrSet_iff_dist v δ hδ.le hδhalf t).mp hvt⟩
  obtain ⟨W, T, hTpos, hWcard, hWbounds, hWdim, hlogT, hWcover⟩ :=
    bedertLowDimensionModel V d hV hm2 hd hdm le_rfl δ hcover
  have hWpos : ∀ w ∈ W, 0 < w := fun w hw => (hWbounds w hw).1
  have hWheight : ∀ w ∈ W, w ≤ T := fun w hw => (hWbounds w hw).2
  have hmT : m ≤ T := by
    have hh := positiveSpeeds_card_le_height W T hWpos hWheight
    simpa only [hWcard] using hh
  have hT2 : 2 ≤ T := hm2.trans hmT
  have hlogTpos : 0 < Real.log (T : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < T by omega))
  have hmodelHeight : Real.log (T : ℝ) ≤
      2048 * A * Real.sqrt (m : ℝ) * Real.log (2 * (m : ℝ))^2 := by
    have hh := mul_le_mul_of_nonneg_right hdUpper
      (show (0 : ℝ) ≤ 2048 * Real.log (2 * (m : ℝ)) by positivity)
    exact hlogT.trans (by nlinarith)
  obtain ⟨hheight, hstrict⟩ := hnumeric m hmNum hm2
  have hheightT : Real.log (T : ℝ) ≤ (m : ℝ)^(3/4 : ℝ) := hmodelHeight.trans hheight
  obtain ⟨t, ht⟩ := hsmall W T hWpos (by simpa only [hWcard] using hmSmall)
    hT2 hWheight (by simpa only [hWcard] using hheightT)
  have hmsqrt : (m : ℝ) * Real.sqrt (m : ℝ) = (m : ℝ)^(3/2 : ℝ) := by
    calc
      _ = (m : ℝ)^(1 : ℝ) * (m : ℝ)^(1/2 : ℝ) := by rw [Real.rpow_one, ← Real.sqrt_eq_rpow]
      _ = (m : ℝ)^((1 : ℝ)+1/2) := (Real.rpow_add hmR _ _).symm
      _ = _ := by norm_num
  have hden : (m : ℝ) * Real.log (T : ℝ) ≤
      2048 * A * (m : ℝ)^(3/2 : ℝ) * Real.log (2 * (m : ℝ))^2 := by
    calc
      _ ≤ (m : ℝ) * (2048 * A * Real.sqrt (m : ℝ) * Real.log (2 * (m : ℝ))^2) :=
        mul_le_mul_of_nonneg_left hmodelHeight hmR.le
      _ = (2048 * A) * ((m : ℝ) * Real.sqrt (m : ℝ)) * Real.log (2 * (m : ℝ))^2 := by ring
      _ = _ := by rw [hmsqrt]
  have hdenpos : 0 < 2048 * A * (m : ℝ)^(3/2 : ℝ) * Real.log (2 * (m : ℝ))^2 := by positivity
  have hgain : b / (2048 * A * (m : ℝ)^(3/2 : ℝ) * Real.log (2 * (m : ℝ))^2) ≤
      b / ((m : ℝ) * Real.log (T : ℝ)) :=
    (div_le_div_iff₀ hdenpos (mul_pos hmR hlogTpos)).mpr
      (mul_le_mul_of_nonneg_left hden hb.le)
  have hpow : (m : ℝ) * (m : ℝ)^(-3/2-κ) = (m : ℝ)^(-(1/2+κ)) := by
    calc
      _ = (m : ℝ)^(1 : ℝ) * (m : ℝ)^(-3/2-κ) := by rw [Real.rpow_one]
      _ = (m : ℝ)^((1 : ℝ)+(-3/2-κ)) := (Real.rpow_add hmR _ _).symm
      _ = _ := by congr 1; ring
  have hpowcancel : ((1/2 : ℝ) * (m : ℝ)^(-3/2-κ)) * (2 * (m : ℝ)) =
      (m : ℝ)^(-(1/2+κ)) := by
    calc
      _ = (m : ℝ) * (m : ℝ)^(-3/2-κ) := by ring
      _ = _ := hpow
  have hδupper : δ ≤ 1 / (2 * (m : ℝ)) + (1/2 : ℝ) * (m : ℝ)^(-3/2-κ) := by
    apply (mul_le_mul_iff_left₀ (show (0 : ℝ) < 2 * (m : ℝ) by positivity)).mp
    rw [add_mul, div_mul_cancel₀ _ (by positivity : 2 * (m : ℝ) ≠ 0), hpowcancel]
    change 2 * δ * (m : ℝ) - 1 ≤ (m : ℝ)^(-(1/2+κ)) at hεbound
    nlinarith
  have hstrict' := hstrict.trans_le hgain
  obtain ⟨w, hw, hupper⟩ := hWcover t
  have hlower := ht w hw
  rw [hWcard] at hlower
  change 1 / (2 * (m : ℝ)) + b / ((m : ℝ) * Real.log (T : ℝ)) ≤ dist (w • t) 0 at hlower
  change dist (w • t) 0 ≤ δ + (m : ℝ)^(-100 : ℝ) at hupper
  linarith

#print axioms nearCover_actual_dimension
#print axioms nearCover_log_square_decay
#print axioms nearCoverContradiction_numeric
#print axioms nearCoverContradiction

end LonelyRunner
