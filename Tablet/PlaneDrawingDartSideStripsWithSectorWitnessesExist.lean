import Tablet.ConnectedSubsetContainedInUniqueComplementComponent
import Tablet.DrawingFaceComponent
import Tablet.OrdinaryDrawingImageWithoutEdge
import Tablet.PlaneDrawingDartCollarChoiceData
import Tablet.PlaneDrawingDartCollarChoiceDataExists
import Tablet.PlaneDrawingDartSectorWitnessDataFromCollarChoices
import Tablet.PlaneDrawingDartArcData
import Tablet.PlaneDrawingDartSectorWitnessData
import Tablet.PlaneDrawingDartSideStripData
import Tablet.PlaneDrawingDartSideStripDataFromCollarChoices
import Tablet.PlaneDrawingDartVertexStarData
import Tablet.PlaneDrawingDartVertexSectorGeometry
import Tablet.PlaneDrawingSelectedEdgeAwayFromEndpointCompact
import Tablet.PolygonalArc
import Tablet.PolygonalArcCarrierCompact
import Tablet.PolygonalArcCollarCompatibleOrientedTubeDataExistsBelow
import Tablet.PolygonalArcCollarControlRadiiExistsBelow
import Tablet.PolygonalArcCollarLocalSideData
import Tablet.PolygonalArcCollarLocalSideDataExistsWithEndpointLeftCones
import Tablet.PolygonalArcCollarMiddleForbiddenMarginsExists
import Tablet.PolygonalArcCollarMiddleSegmentDataExists
import Tablet.PolygonalArcCollarVertexLocalPieceData
import Tablet.PolygonalArcEndpointIsolationExists
import Tablet.PolygonalArcInitialEndpointDiskCappedTaperAttachmentStrengthening
import Tablet.PolygonalArcInitialEndpointLeftCone
import Tablet.PolygonalArcOpenSegmentSubsetRelativeInterior
import Tablet.PolygonalArcTerminalEndpointDiskCappedTaperAttachmentStrengthening
import Tablet.PolygonalArcSideStripAssembly
import Tablet.PolygonalArcTerminalEndpointLeftCone
import Tablet.PolygonalSideStrips
import Tablet.PositiveSeparation

open Classical
noncomputable section

-- [TABLET NODE: PlaneDrawingDartSideStripsWithSectorWitnessesExist]
lemma PlaneDrawingDartSideStripsWithSectorWitnessesExist {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (hD : D.crossingSet.card = 0)
    (A : PlaneDrawingDartArcData G D)
    (C : PlaneDrawingDartVertexSectorGeometry G D A) :
    ∃ S : PlaneDrawingDartSideStripData G D A C.star,
      Nonempty (PlaneDrawingDartSectorWitnessData G D A C.star S) := by
-- BODY
  obtain ⟨P⟩ := PlaneDrawingDartCollarChoiceDataExists G D hD A C
  obtain ⟨S, hleft, _hright⟩ :=
    PlaneDrawingDartSideStripDataFromCollarChoices G D A C P
  exact ⟨S, PlaneDrawingDartSectorWitnessDataFromCollarChoices G D A C P S hleft⟩
