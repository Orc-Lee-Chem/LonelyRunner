import Tablet.SimpleClosedPolygonalCurve
import Tablet.FinitePolygonalSet
import Tablet.PolygonalPathInGeneralPosition
import Tablet.PolygonalPathIntersectionMultiplicity
import Tablet.CyclicCurvePresentation
import Tablet.CyclicCurvePresentationIntersectionMultiplicity
import Tablet.CyclicPresentationTriangleGeneralPosition
import Tablet.FinitePolygonalSetCyclicCurvePresentation
import Tablet.PolygonalPathMultiplicityCyclicPresentation
import Tablet.CyclicPresentationClosedPathEvenIntersections
import Tablet.TriangleBoundaryCyclicIntersectionMultiplicity
import Tablet.TriangleBoundaryEvenIntersections

open Classical
noncomputable section

-- [TABLET NODE: ClosedPolygonalPathEvenIntersections]
lemma ClosedPolygonalPathEvenIntersections
    (J : SimpleClosedPolygonalCurve) (Γ : PolygonalPath)
    (K : FinitePolygonalSet)
    (hKJ : K.carrier = J.carrier)
    (hΓ : Γ.source = Γ.target)
    (hgp : PolygonalPathInGeneralPosition Γ K) :
    Even (PolygonalPathIntersectionMultiplicity Γ K) := by
-- BODY
  obtain ⟨R⟩ := FinitePolygonalSetCyclicCurvePresentation J K hKJ
  rw [PolygonalPathMultiplicityCyclicPresentation J Γ K hKJ hgp R]
  exact CyclicPresentationClosedPathEvenIntersections J Γ K hΓ hgp R
