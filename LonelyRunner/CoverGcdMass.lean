import LonelyRunner.CoverMomentLower
import LonelyRunner.CoverMomentUpper
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# 近覆盖子族的公共因子质量

对应论文 `lem:extract` 证明第 496–504 行，复用 `lem:moments` 的三阶矩界。
子族 `W` 无需自身覆盖圆周。
-/

open Filter
open MeasureTheory
open scoped Topology

namespace LonelyRunner

/-- 论文第 497–499 行：若二阶矩至少 `1/128` 且误差至多 `1/512`，
柯西矩不等式迫使 `ε*A₃≥(1/128)²/2`。 -/
private theorem third_moment_mass_algebra (A B ε : ℝ)
    (hA : (1 / 128 : ℝ) ≤ A) (hε : 0 < ε)
    (hεsmall : ε ≤ 1 / 512)
    (hCS : A ^ 2 ≤ ε * (B + 2 * A)) :
    (1 / 128 : ℝ) ^ 2 / 2 ≤ ε * B := by
  let c : ℝ := 1 / 128
  have hc : 0 < c := by dsimp [c]; norm_num
  have hA0 : 0 ≤ A := by dsimp [c] at hc; linarith
  have hAsq : c * A ≤ A ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr (show c ≤ A from hA)) hA0]
  have hεc : 2 * ε ≤ c / 2 := by dsimp [c]; linarith
  have hεA : 2 * ε * A ≤ c / 2 * A :=
    mul_le_mul_of_nonneg_right hεc hA0
  change c ^ 2 / 2 ≤ ε * B
  nlinarith [hAsq, hεA, hCS]

/-- 论文 `lem:extract` 第 496–504 行：充足大的近覆盖族中，
任一至少占四分之一的子族都具有统一的 `G₃` 质量。
绝对常数在 `κ` 之前选取；门槛仅依赖 `κ`。 -/
theorem coverGcdMass_lower :
    ∃ c0 : ℝ, 0 < c0 ∧
      ∀ κ : ℝ, 0 < κ → κ < 1 / 4 →
        ∃ Mκ : ℕ,
          ∀ (V : Finset ℕ) (m : ℕ) (δ : ℝ) (W : Finset ℕ),
            (∀ v ∈ V, 0 < v) → m = V.card → Mκ ≤ m →
              Covers V δ → 0 < δ → δ < 1 / 2 →
                let ε : ℝ := 2 * δ * (m : ℝ) - 1
                0 < ε → ε ≤ (m : ℝ) ^ (-(1 / 2 + κ)) →
                  W ⊆ V → m ≤ 4 * W.card →
                    c0 * (m : ℝ) / ε ≤ tripleGcdSum W := by
  obtain ⟨Cstar, hCstar, hupper⟩ := coverThirdMoment_upper
  let c : ℝ := 1 / 128
  let c0 : ℝ := c ^ 2 / (4 * Cstar)
  have hc0 : 0 < c0 := by dsimp [c0, c]; positivity
  refine ⟨c0, hc0, ?_⟩
  intro κ hκ hκ4
  obtain ⟨Cκ, hCκ, hthirdUpper⟩ := hupper (κ / 2) (by linarith)
  let cap : ℝ := min (1 / 512) (c ^ 2 / (4 * Cκ))
  have hcap : 0 < cap := by dsimp [cap, c]; positivity
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(κ / 2))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by linarith : 0 < κ / 2)).comp
      tendsto_natCast_atTop_atTop
  obtain ⟨M0, hM0⟩ := eventually_atTop.1
    (ht.eventually (eventually_lt_nhds hcap))
  refine ⟨max 8 M0, ?_⟩
  intro V m δ W hV hmEq hmM hcover hδ hδhalf ε hε hεbound hWV hWlarge
  have hm8 : 8 ≤ m := (le_max_left 8 M0).trans hmM
  have hmM0 : M0 ≤ m := (le_max_right 8 M0).trans hmM
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hpowSmall : (m : ℝ) ^ (-(κ / 2)) ≤ cap := le_of_lt (hM0 m hmM0)
  have hpowComp : (m : ℝ) ^ (-(1 / 2 + κ)) ≤
      (m : ℝ) ^ (-(κ / 2)) :=
    Real.rpow_le_rpow_of_exponent_le hm1 (by linarith)
  have hεcap : ε ≤ cap := hεbound.trans (hpowComp.trans hpowSmall)
  have hεsmall : ε ≤ 1 / 512 := hεcap.trans (min_le_left _ _)
  have hδlower : 1 / (2 * (m : ℝ)) ≤ δ :=
    cover_delta_lower_of_covers V δ hV hδ hδhalf hcover m hmEq (by omega)
  have hW : ∀ v ∈ W, 0 < v := fun v hv => hV v (hWV hv)
  have hA2 : (1 / 128 : ℝ) ≤ coverSecondMoment W δ :=
    coverSecondMoment_lower_one_div_128 W δ hW hδ hδhalf
      m hm8 hWlarge hδlower
  have hCS := coverSecondMoment_sq_le_excess_mul W δ hW hδ hδhalf
  have he0 : 0 ≤ coverExcess W δ := by
    unfold coverExcess
    exact integral_nonneg (fun t => le_max_right _ _)
  have he : coverExcess W δ ≤ ε := by
    simpa [ε, ← hmEq] using
      coverExcess_le_epsilon V W δ hV hδ hδhalf hWV hcover
  have hsumNonneg : 0 ≤ coverThirdMoment W δ + 2 * coverSecondMoment W δ := by
    by_contra hh
    have hprod := mul_nonpos_of_nonneg_of_nonpos he0 (le_of_lt (lt_of_not_ge hh))
    have hApos : 0 < coverSecondMoment W δ := by linarith
    nlinarith [sq_pos_of_pos hApos]
  have hCSε : coverSecondMoment W δ ^ 2 ≤
      ε * (coverThirdMoment W δ + 2 * coverSecondMoment W δ) :=
    hCS.trans (mul_le_mul_of_nonneg_right he hsumNonneg)
  have hA3mass : c ^ 2 / 2 ≤ ε * coverThirdMoment W δ := by
    exact third_moment_mass_algebra _ _ _ hA2 hε hεsmall hCSε
  have hδupper : δ ≤ 3 / (4 * (m : ℝ)) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (m : ℝ))).2
    dsimp [ε] at hεsmall
    nlinarith
  have hcard : W.card ≤ m := by rw [hmEq]; exact Finset.card_le_card hWV
  have hA3upper := hthirdUpper W hW m (by omega : 3 ≤ m) hcard δ hδ hδupper
  have hpowMul : (m : ℝ) ^ (-(1 / 2 + κ)) *
      (m : ℝ) ^ (1 / 2 + κ / 2) = (m : ℝ) ^ (-(κ / 2)) := by
    rw [← Real.rpow_add hm0]
    congr 1
    ring
  have hεpow : ε * (m : ℝ) ^ (1 / 2 + κ / 2) ≤
      (m : ℝ) ^ (-(κ / 2)) := by
    calc
      _ ≤ (m : ℝ) ^ (-(1 / 2 + κ)) * (m : ℝ) ^ (1 / 2 + κ / 2) :=
        mul_le_mul_of_nonneg_right hεbound (by positivity)
      _ = _ := hpowMul
  have habsorb : ε * (Cκ * (m : ℝ) ^ (1 / 2 + κ / 2)) ≤ c ^ 2 / 4 := by
    have hcapRight : cap ≤ c ^ 2 / (4 * Cκ) := min_le_right _ _
    have hcapAbs : Cκ * cap ≤ c ^ 2 / 4 := by
      calc
        Cκ * cap ≤ Cκ * (c ^ 2 / (4 * Cκ)) :=
          mul_le_mul_of_nonneg_left hcapRight hCκ.le
        _ = c ^ 2 / 4 := by field_simp
    calc
      _ = Cκ * (ε * (m : ℝ) ^ (1 / 2 + κ / 2)) := by ring
      _ ≤ Cκ * (m : ℝ) ^ (-(κ / 2)) :=
        mul_le_mul_of_nonneg_left hεpow hCκ.le
      _ ≤ Cκ * cap := mul_le_mul_of_nonneg_left hpowSmall hCκ.le
      _ ≤ c ^ 2 / 4 := hcapAbs
  have hA3mul := mul_le_mul_of_nonneg_left hA3upper hε.le
  have hA3mul' : ε * coverThirdMoment W δ ≤
      ε * (Cκ * (m : ℝ) ^ (1 / 2 + κ / 2)) +
        ε * Cstar * tripleGcdSum W / (m : ℝ) := by
    convert hA3mul using 1 <;> ring
  have hGcore : c ^ 2 / 4 ≤ ε * Cstar * tripleGcdSum W / (m : ℝ) := by
    linarith [hA3mass, hA3mul', habsorb]
  have hGcore2 : (c ^ 2 / 4) * (m : ℝ) ≤
      ε * Cstar * tripleGcdSum W := by
    exact (le_div_iff₀ hm0).mp hGcore
  have hGbound : c0 * (m : ℝ) ≤ ε * tripleGcdSum W := by
    have h : ((c ^ 2 / 4) * (m : ℝ)) / Cstar ≤
        ε * tripleGcdSum W :=
      (div_le_iff₀ hCstar).2 (by convert hGcore2 using 1 <;> ring)
    calc
      c0 * (m : ℝ) = ((c ^ 2 / 4) * (m : ℝ)) / Cstar := by
        dsimp [c0]
        ring
      _ ≤ ε * tripleGcdSum W := h
  exact (div_le_iff₀ hε).2 (by simpa [mul_comm] using hGbound)

end LonelyRunner
