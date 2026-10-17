import Tablet.PlaneFaceData
import Tablet.PlaneFaceDataOneFaceOfPolygonallyPathConnectedComplement
import Tablet.PlaneTreeDrawingComplementConnected
import Tablet.PlaneTreeLeafDeletionDrawingData
import Tablet.PlaneTreeLeafDeletionGraphData
import Tablet.PlaneTreeLeafPendantAttachment
import Tablet.PlaneTreeNoEdgeComplementConnected
import Tablet.PendantArcComplementConnected
import Tablet.OrdinaryDrawingImageCompact
import Tablet.OrdinaryDrawingImage
import Tablet.OrdinaryPolygonalDrawing
import Tablet.PolygonalArc
import Tablet.PolygonallyPathConnected
import Tablet.DrawingFaceComponent
import Tablet.ComplementComponent
import Mathlib.Combinatorics.SimpleGraph.Acyclic

open Classical
noncomputable section

-- [TABLET NODE: PlaneTreeOneFace]
lemma PlaneTreeOneFace {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [DecidableRel G.Adj] (D : OrdinaryPolygonalDrawing G)
    (hD : D.crossingSet.card = 0) (A : PlaneFaceData G D) :
    G.IsTree → @Fintype.card A.Face A.faceFintype = 1 := by
-- BODY
  intro hTree
  exact PlaneFaceDataOneFaceOfPolygonallyPathConnectedComplement G D A
    (PlaneTreeDrawingComplementConnected G D hD hTree)
    (by
      rcases (OrdinaryDrawingImageCompact G D).isBounded.exists_norm_le with ⟨R, hR⟩
      let p : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 (max R 0 + 1)
      refine ⟨p, ?_⟩
      intro hp
      have hp_norm_le : ‖p‖ ≤ R := hR p hp
      have hp_norm : ‖p‖ = max R 0 + 1 := by
        have hnonneg : 0 ≤ max R 0 + 1 := by
          nlinarith [le_max_right R 0]
        simp [p, Real.norm_eq_abs, abs_of_nonneg hnonneg]
      have hR_lt : R < max R 0 + 1 := by
        nlinarith [le_max_left R 0]
      nlinarith)
