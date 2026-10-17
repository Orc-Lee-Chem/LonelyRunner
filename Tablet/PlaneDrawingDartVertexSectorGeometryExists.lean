import Tablet.CrossingFreeEdgeInteriorDisjoint
import Tablet.DartSuccessorFromLocalClockwiseNext
import Tablet.OrdinaryPolygonalDrawing
import Tablet.OrdinaryDrawingSegmentDirectionsNotSamePositiveRay
import Tablet.PlanarClockwiseSweptTwoRayEndpointConesInSector
import Tablet.PlanarSlitDiskEndpointConesAvoidRay
import Tablet.PlaneDrawingDartGeometricClockwiseSectors
import Tablet.PlaneDrawingDartArcData
import Tablet.PlaneDrawingDartFirstGermsForRadii
import Tablet.PlaneDrawingDartSourceEndpointRayCovers
import Tablet.PlaneDrawingDartUnitFirstGermsForRadii
import Tablet.PlaneDrawingDartVertexStarData
import Tablet.PlaneDrawingDartVertexSectorGeometry
import Tablet.PolygonalArc
import Tablet.PolygonalArcCarrierCompact
import Tablet.PolygonalArcReverse
import Tablet.PositiveSeparation

open Classical
noncomputable section

-- [TABLET NODE: PlaneDrawingDartVertexSectorGeometryExists]
lemma PlaneDrawingDartVertexSectorGeometryExists {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (hD : D.crossingSet.card = 0)
    (A : PlaneDrawingDartArcData G D) :
    Nonempty (PlaneDrawingDartVertexSectorGeometry G D A) := by
-- BODY
  rcases PlaneDrawingDartGeometricClockwiseSectors G D hD A with ⟨C, _hmodel⟩
  exact ⟨C⟩
