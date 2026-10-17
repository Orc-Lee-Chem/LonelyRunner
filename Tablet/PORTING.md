# Source and compatibility notices

Upstream: https://github.com/wpegden/crossing-consequences

Exact upstream commit: `8769d142033fce042f502bf2857afb6b1375b5c3`.
Original toolchain: Lean `v4.30.0-rc2`, Mathlib
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`.
Released toolchain: Lean/Mathlib `v4.34.1`.

All 609 ported Lean modules are included; the final ST theorem has a transitive
closure of 589 Tablet modules. The additional 20 modules were also source-rebuilt
in the final same-machine audit. The original upstream license is preserved
verbatim as [LICENSE](LICENSE).

76 files contain proof-script/API compatibility changes relative to upstream;
see [the complete per-file record](../docs/STPortChanges.md). They additionally
carry a publication-only comment notice. Removing that exact notice reproduces
the audited frozen bytes. Definitions, statements, hypotheses and proofs below
the notices have not been edited for publication.

Modified relative to upstream:

- `ArcCrossingSegmentOccurrenceParameters.lean`
- `BigonRerouteBetaSpliceAssembly.lean`
- `CircularArcEndpointSphereBranch.lean`
- `ConnectedEulerFormula.lean`
- `CrossingLemma.lean`
- `DeleteNonbridgeReturnPathWitness.lean`
- `EndpointSidePrefixConstruction.lean`
- `EndpointSidePrefixCoreSimplePath.lean`
- `EndpointSidePrefixEventBridge.lean`
- `EndpointSidePrefixTerminalAssembly.lean`
- `EndpointSidePrefixTerminalChain.lean`
- `EndpointUnitDiskAssemblyFromLocalReplacements.lean`
- `EndpointUnitDiskLocalReplacement.lean`
- `EndpointUnitMultiplePointDisks.lean`
- `FaceDegreeLowerBound.lean`
- `FiniteAnchorListPolygonalScreening.lean`
- `FiniteConnectedIntersectionGrouping.lean`
- `FinitePolygonalSetCyclicElementarySegmentOccurrenceFamily.lean`
- `FinitePolygonalSetCyclicNormalizedSourceSuccessorOrder.lean`
- `FiniteRealAdjacentPairsExists.lean`
- `InducedSubdrawingBridge.lean`
- `JordanCurveSimultaneousCollarDataExists.lean`
- `JordanGenericRayReachesLocalSide.lean`
- `OneEdgeEndpointSectorComplementPackage.lean`
- `OrdinaryAdjacentEdgesFavorableTailFreeTerminalRefinement.lean`
- `OrdinaryAdjacentEdgesSimultaneousBigonGeometryExists.lean`
- `OrdinaryCrossingLocalBranchDataPrefixTruncation.lean`
- `OrdinaryCrossingLocalBranchDataSuffixTruncation.lean`
- `OrdinaryCrossingLocalBranchDataThreePiecePrefixLift.lean`
- `OrdinaryCrossingLocalBranchDataThreePieceSuffixLift.lean`
- `OrdinaryLabeledCrossingDiskFamilyExists.lean`
- `OrdinaryLabeledCrossingDiskFillingFamilyExists.lean`
- `OrdinaryLabeledCrossingDiskWholeEdgeAssignmentLocalization.lean`
- `PlanarNonparallelHalfOpenTerminalTriangle.lean`
- `PlanarNonparallelTerminalCellChain.lean`
- `PlanarRot90ClockwiseWedgeRayPartition.lean`
- `PlanarRot90Decomposition.lean`
- `PlanarRot90Orthogonal.lean`
- `PlanarSphereGateInwardPointAvoidance.lean`
- `PlaneDrawingDartGeometricClockwiseSectors.lean`
- `PlaneTreeLeafDeletionDrawingData.lean`
- `PointLineConsecutivePairLineFamilyDataExists.lean`
- `PolygonalArcCollarLocalTopologyDataExists.lean`
- `PolygonalArcCollarLocalTopologyDataWithEndpointCaps.lean`
- `PolygonalArcCollarMiddleTubeDataExists.lean`
- `PolygonalArcCollarSeparatedTubeDataExists.lean`
- `PolygonalArcContiguousVertexSubarc.lean`
- `PolygonalArcEndpointDiskCappedTaperModel.lean`
- `PolygonalArcEndpointTaperedWedgeModel.lean`
- `PolygonalArcFinitePolygonalSet.lean`
- `PolygonalArcInteriorPointCutDataExists.lean`
- `PolygonalArcOrderedBallCutDataExists.lean`
- `PolygonalArcOrderedThreePieceSplice.lean`
- `PolygonalArcVertexMemCarrier.lean`
- `PolygonalPathRetainedElementaryRawWalkExists.lean`
- `PolygonalPathStraightLineComplexOfRaw.lean`
- `PolygonalReplacementCircularEndpointSupportingHalfspace.lean`
- `PolygonalReplacementCircularMiddleSubarcSampledBySafeCover.lean`
- `PolygonalReplacementCircularSourceEndpointCenterOrder.lean`
- `PolygonalReplacementCircularSourceRetainedHalfspacePoint.lean`
- `PolygonalReplacementCircularTargetEndpointCenterOrder.lean`
- `PolygonalReplacementCircularTargetRetainedHalfspacePoint.lean`
- `PolygonalReplacementControlCenterDisks.lean`
- `PolygonalReplacementEdgeAssemblies.lean`
- `PolygonalReplacementEndpointBoundaryParamOrder.lean`
- `PolygonalReplacementEndpointDeletedIntervals.lean`
- `PolygonalReplacementIntersectionCenterEndpointParamOrder.lean`
- `PolygonalReplacementIntersectionCutOpenBallIff.lean`
- `PolygonalReplacementIntersectionDiskChains.lean`
- `PolygonalReplacementResidualIntervalPieceControlComplement.lean`
- `PolygonalReplacementResidualPieceSkeletonParameterBounds.lean`
- `PolygonalReplacementSourceEndpointControlDiskNeighborhood.lean`
- `PolygonalReplacementStraightResidualPieceSegment.lean`
- `PolygonalReplacementTargetEndpointControlDiskNeighborhood.lean`
- `PolygonalReplacementVertexDiskSpokes.lean`
- `SimpleClosedPolygonalCurveOfCyclicArcList.lean`
