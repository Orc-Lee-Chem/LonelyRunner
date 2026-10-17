/- Publication notice: ported from wpegden/crossing-consequences at
   8769d142033fce042f502bf2857afb6b1375b5c3 for Lean/Mathlib v4.34.1.
   Compatibility changes: ../docs/STPortChanges.md; upstream license: LICENSE.
   The source below this comment is byte-identical to the audited frozen source.
-/
import Tablet.PlanarRot90

open Classical
noncomputable section

-- [TABLET NODE: PlanarRot90Orthogonal]
lemma PlanarRot90Orthogonal (d : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ d (PlanarRot90 d) = 0 := by
-- BODY
  dsimp [PlanarRot90]
  rw [PiLp.inner_apply]
  simp
  ring
