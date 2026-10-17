import Tablet.SzemerediTrotter

open scoped Real

namespace LonelyRunner

/-- 中文：对任意有限平面点集与有限个互异的一维实仿射直线，点线关联数满足非加权 Szemerédi–Trotter 界。
这里的直线、关联数和绝对常数完全沿用 Tablet.SzemerediTrotter 的已证明定义与量词。 -/
theorem stIncidence :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : Finset (EuclideanSpace ℝ (Fin 2)))
        (L : Finset {ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) // IsAffineLine ℓ}),
        (LineIncidences P L : ℝ) ≤
          C * (((P.card : ℝ) * (L.card : ℝ)) ^ ((2 : ℝ) / 3) +
            (P.card : ℝ) + (L.card : ℝ)) := by
  exact SzemerediTrotter

end LonelyRunner
