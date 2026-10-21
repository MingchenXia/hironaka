import Lean
import Hironaka
import TranscendentalNakamaye.Pending.HironakaActualClosedContactControlledRestriction
import TranscendentalNakamaye.Pending.HironakaActualPrincipalJetMultiplication
import TranscendentalNakamaye.Pending.HironakaActualPrincipalHSFormula
import TranscendentalNakamaye.Pending.HironakaActualDirectionalNormalJet
import TranscendentalNakamaye.Pending.HironakaActualExceptionalJetHSComparison
import TranscendentalNakamaye.Pending.HironakaActualExceptionalJetRigidity
import TranscendentalNakamaye.Pending.HironakaActualInitialPivotNormality
import TranscendentalNakamaye.Pending.HironakaActualPointNormalizedCoefficientBands
import TranscendentalNakamaye.Pending.HironakaActualPointOrderRetainingHS
import TranscendentalNakamaye.Pending.HironakaActualZeroPointReducedTail

/-! Actual typed compiler roots and whole-public-environment dependency audit.
No generated body is erased or asserted structurally equal. All actual roots
remain subject to the separate kernel and transitive-axiom inventories. -/
open Lean
set_option maxHeartbeats 0
set_option maxRecDepth 10000

run_cmd do
  let env ← getEnv
  let pairs : Array (Name × Name × Nat) := #[
    (`TranscendentalNakamaye.Pending.HironakaActualClosedContactControlledRestriction, `Hironaka.Resolution.HironakaActualClosedContactControlledRestriction, 2),
    (`TranscendentalNakamaye.Pending.HironakaActualPrincipalJetMultiplication, `Hironaka.Resolution.HironakaActualPrincipalJetMultiplication, 2),
    (`TranscendentalNakamaye.Pending.HironakaActualPrincipalHSFormula, `Hironaka.Resolution.HironakaActualPrincipalHSFormula, 2),
    (`TranscendentalNakamaye.Pending.HironakaActualDirectionalNormalJet, `Hironaka.Resolution.HironakaActualDirectionalNormalJet, 2),
    (`TranscendentalNakamaye.Pending.HironakaActualExceptionalJetHSComparison, `Hironaka.Resolution.HironakaActualExceptionalJetHSComparison, 2),
    (`TranscendentalNakamaye.Pending.HironakaActualExceptionalJetRigidity, `Hironaka.Resolution.HironakaActualExceptionalJetRigidity, 2),
    (`TranscendentalNakamaye.Pending.HironakaActualInitialPivotNormality, `Hironaka.Resolution.HironakaActualInitialPivotNormality, 2),
    (`TranscendentalNakamaye.Pending.HironakaActualPointNormalizedCoefficientBands, `Hironaka.Resolution.HironakaActualPointNormalizedCoefficientBands, 3),
    (`TranscendentalNakamaye.Pending.HironakaActualPointOrderRetainingHS, `Hironaka.Resolution.HironakaActualPointOrderRetainingHS, 2),
    (`TranscendentalNakamaye.Pending.HironakaActualZeroPointReducedTail, `Hironaka.Resolution.HironakaActualZeroPointReducedTail, 1)
  ]
  let newModules : Array Name := #[
    `Hironaka.Analytic.AnalyticRegularStratumTopology,
    `Hironaka.Analytic.SubmanifoldChartedSpace,
    `Hironaka.Analytic.SubmanifoldCodRestrict,
    `Hironaka.Analytic.SubmanifoldIdealRestriction,
    `Hironaka.Analytic.TowerPreimageCompact,
    `Hironaka.MarkedIdeal.MaximalContact,
    `Hironaka.Resolution.HironakaActualAnalyticSubspace,
    `Hironaka.Resolution.HironakaActualAnalyticSubspaceIntrinsicHS,
    `Hironaka.Resolution.HironakaActualAnalyticSubspaceIntrinsicLifting,
    `Hironaka.Resolution.HironakaActualAnalyticSubspaceLocalFunctions,
    `Hironaka.Resolution.HironakaActualAnalyticSubspaceManifoldCharts,
    `Hironaka.Resolution.HironakaActualAnalyticSubspaceMaps,
    `Hironaka.Resolution.HironakaActualAnalyticSubspaceOpenRestriction,
    `Hironaka.Resolution.HironakaActualAnalyticSubspacePresentationIndependence,
    `Hironaka.Resolution.HironakaActualAnalyticSubspaceRegularityConverse,
    `Hironaka.Resolution.HironakaActualAnalyticSubspaceResidue,
    `Hironaka.Resolution.HironakaActualAnalyticVertexPerturbation,
    `Hironaka.Resolution.HironakaActualAxisTaylorRigidity,
    `Hironaka.Resolution.HironakaActualBaseResidueField,
    `Hironaka.Resolution.HironakaActualBlockProjectionIntrinsicHS,
    `Hironaka.Resolution.HironakaActualBlowupConeInverse,
    `Hironaka.Resolution.HironakaActualBoundaryContactNormalPowers,
    `Hironaka.Resolution.HironakaActualCanonicalCoefficientDomains,
    `Hironaka.Resolution.HironakaActualCanonicalNormalCoefficientData,
    `Hironaka.Resolution.HironakaActualCentreContactCoordinates,
    `Hironaka.Resolution.HironakaActualCentreCoupledSymbols,
    `Hironaka.Resolution.HironakaActualCentreDualJetConnection,
    `Hironaka.Resolution.HironakaActualCentreDualJetSpan,
    `Hironaka.Resolution.HironakaActualCentreJointJets,
    `Hironaka.Resolution.HironakaActualCentrePrincipalParts,
    `Hironaka.Resolution.HironakaActualCentrePrincipalPartsFree,
    `Hironaka.Resolution.HironakaActualCentrePrincipalPartsGraded,
    `Hironaka.Resolution.HironakaActualCentrePrincipalPartsOrderSystem,
    `Hironaka.Resolution.HironakaActualClosedContactBlowupRestriction,
    `Hironaka.Resolution.HironakaActualClosedContactControlledRestriction,
    `Hironaka.Resolution.HironakaActualCoefficientControlledTransform,
    `Hironaka.Resolution.HironakaActualCoefficientCosupportSpread,
    `Hironaka.Resolution.HironakaActualCoherentWeightedCoefficientMarked,
    `Hironaka.Resolution.HironakaActualCommonMarkPersistentCosupport,
    `Hironaka.Resolution.HironakaActualCompactFiniteHSPresentation,
    `Hironaka.Resolution.HironakaActualContactStrictTransform,
    `Hironaka.Resolution.HironakaActualConvergentTaylorRealization,
    `Hironaka.Resolution.HironakaActualCoupledNormalFreeness,
    `Hironaka.Resolution.HironakaActualCylinderPullbackOrigin,
    `Hironaka.Resolution.HironakaActualCylinderPullbackPoints,
    `Hironaka.Resolution.HironakaActualCylinderRelativeHadamard,
    `Hironaka.Resolution.HironakaActualCylinderVanishingIdealExtension,
    `Hironaka.Resolution.HironakaActualDegLexPositiveWeights,
    `Hironaka.Resolution.HironakaActualDiagramStrictHSDrop,
    `Hironaka.Resolution.HironakaActualDirectionalNormalJet,
    `Hironaka.Resolution.HironakaActualDualJetProlongation,
    `Hironaka.Resolution.HironakaActualDualJetProlongationHolomorphic,
    `Hironaka.Resolution.HironakaActualDualJetProlongationUnit,
    `Hironaka.Resolution.HironakaActualDualJetRaising,
    `Hironaka.Resolution.HironakaActualElementaryCartesianNaturality,
    `Hironaka.Resolution.HironakaActualExceptionalFibreRelations,
    `Hironaka.Resolution.HironakaActualExceptionalFilteredDivision,
    `Hironaka.Resolution.HironakaActualExceptionalJetHSComparison,
    `Hironaka.Resolution.HironakaActualExceptionalJetRigidity,
    `Hironaka.Resolution.HironakaActualFiniteJetVertexBasis,
    `Hironaka.Resolution.HironakaActualFirstSymbolTangentClosure,
    `Hironaka.Resolution.HironakaActualFixedFlatteningBlowupCoordinates,
    `Hironaka.Resolution.HironakaActualFixedFlatteningHSComparison,
    `Hironaka.Resolution.HironakaActualFormalNormalSeries,
    `Hironaka.Resolution.HironakaActualFormalNormalTruncations,
    `Hironaka.Resolution.HironakaActualFormalPolynomialJetTransfer,
    `Hironaka.Resolution.HironakaActualFormalStandardMonomialHS,
    `Hironaka.Resolution.HironakaActualGraphContactCoefficient,
    `Hironaka.Resolution.HironakaActualGraphFunctionalIdeal,
    `Hironaka.Resolution.HironakaActualHSConstantCentreAmbientConvolution,
    `Hironaka.Resolution.HironakaActualHSConstantCentreBennett,
    `Hironaka.Resolution.HironakaActualHSConstantSingularCentre,
    `Hironaka.Resolution.HironakaActualHSSingularBlowupRestart,
    `Hironaka.Resolution.HironakaActualHSSingularOriginalPrefix,
    `Hironaka.Resolution.HironakaActualHSZeroCentreVanishing,
    `Hironaka.Resolution.HironakaActualHolomorphicDualJetGeneration,
    `Hironaka.Resolution.HironakaActualHolomorphicGraphIdeal,
    `Hironaka.Resolution.HironakaActualHolomorphicStalkSurjection,
    `Hironaka.Resolution.HironakaActualHomogeneousCoefficientSummability,
    `Hironaka.Resolution.HironakaActualHomogeneousInitialTangentDerivatives,
    `Hironaka.Resolution.HironakaActualHypersurfaceBlowupHS,
    `Hironaka.Resolution.HironakaActualInitialCoordinateQuotient,
    `Hironaka.Resolution.HironakaActualInitialNormalExtension,
    `Hironaka.Resolution.HironakaActualInitialPivotNormality,
    `Hironaka.Resolution.HironakaActualInitialPolynomialContraction,
    `Hironaka.Resolution.HironakaActualInitialSymbolRegularity,
    `Hironaka.Resolution.HironakaActualIntrinsicIsoCommonGraphSquare,
    `Hironaka.Resolution.HironakaActualIntrinsicIsoPairedWindows,
    `Hironaka.Resolution.HironakaActualInvertibleIntrinsicHS,
    `Hironaka.Resolution.HironakaActualJointBaseFibre,
    `Hironaka.Resolution.HironakaActualJointTangentCuts,
    `Hironaka.Resolution.HironakaActualLocalCommonGraphModel,
    `Hironaka.Resolution.HironakaActualLocallyFiniteHistoryComparison,
    `Hironaka.Resolution.HironakaActualLocallyFiniteHistoryFactors,
    `Hironaka.Resolution.HironakaActualLocallyFiniteHistoryLimit,
    `Hironaka.Resolution.HironakaActualLocallyFiniteHistoryOverlap,
    `Hironaka.Resolution.HironakaActualMixedCoefficientOrders,
    `Hironaka.Resolution.HironakaActualMonomialDivisionBounds,
    `Hironaka.Resolution.HironakaActualMultilinearTaylorCoordinates,
    `Hironaka.Resolution.HironakaActualNormalCoordinateReindex,
    `Hironaka.Resolution.HironakaActualNormalFibreDiagramCompare,
    `Hironaka.Resolution.HironakaActualNormalFilteredOwnerDivision,
    `Hironaka.Resolution.HironakaActualNormalizedInitialRelations,
    `Hironaka.Resolution.HironakaActualOpenTowerHosts,
    `Hironaka.Resolution.HironakaActualOriginalFormalNaturality,
    `Hironaka.Resolution.HironakaActualOriginalReducedVertexBasis,
    `Hironaka.Resolution.HironakaActualOriginalVertexConvergence,
    `Hironaka.Resolution.HironakaActualOwnerAnalyticDivision,
    `Hironaka.Resolution.HironakaActualPersistentHSIdealRigidity,
    `Hironaka.Resolution.HironakaActualPersistentPointConeDerivatives,
    `Hironaka.Resolution.HironakaActualPlaneContactBlowup,
    `Hironaka.Resolution.HironakaActualPlaneContactBlowupRestriction,
    `Hironaka.Resolution.HironakaActualPointNormalizedCoefficientBands,
    `Hironaka.Resolution.HironakaActualPointNormalizedSaturation,
    `Hironaka.Resolution.HironakaActualPointOrderRetainingHS,
    `Hironaka.Resolution.HironakaActualPointTangentCoefficientHSDrop,
    `Hironaka.Resolution.HironakaActualPolydiscEvaluationAlgebra,
    `Hironaka.Resolution.HironakaActualPolydiscHolomorphicEvaluation,
    `Hironaka.Resolution.HironakaActualPolynomialAnalyticFlatness,
    `Hironaka.Resolution.HironakaActualPolynomialRehomogenization,
    `Hironaka.Resolution.HironakaActualPrincipalHSFormula,
    `Hironaka.Resolution.HironakaActualPrincipalJetMultiplication,
    `Hironaka.Resolution.HironakaActualPrincipalPartsResidueSymbols,
    `Hironaka.Resolution.HironakaActualProductHSProfileReflection,
    `Hironaka.Resolution.HironakaActualProductMixedHS,
    `Hironaka.Resolution.HironakaActualProductTruncatedQuotient,
    `Hironaka.Resolution.HironakaActualProjectionIntrinsicHS,
    `Hironaka.Resolution.HironakaActualPureNormalVertices,
    `Hironaka.Resolution.HironakaActualReducedNormalSupport,
    `Hironaka.Resolution.HironakaActualRegularIntrinsicHSProfile,
    `Hironaka.Resolution.HironakaActualRelativeCoefficientMassSlicing,
    `Hironaka.Resolution.HironakaActualRelativeExceptionalFibreRelations,
    `Hironaka.Resolution.HironakaActualRelativeFormalQuotients,
    `Hironaka.Resolution.HironakaActualRelativeNormalizedSaturation,
    `Hironaka.Resolution.HironakaActualRelativePointChartFactorization,
    `Hironaka.Resolution.HironakaActualRelativePolynomialRehomogenization,
    `Hironaka.Resolution.HironakaActualRetractContactLocalization,
    `Hironaka.Resolution.HironakaActualSelectedVertexHomogeneousBasis,
    `Hironaka.Resolution.HironakaActualSignedConeDivision,
    `Hironaka.Resolution.HironakaActualSingularCentreCodimension,
    `Hironaka.Resolution.HironakaActualSingularChartTransport,
    `Hironaka.Resolution.HironakaActualSingularSubmersionPullback,
    `Hironaka.Resolution.HironakaActualStandardNormalBases,
    `Hironaka.Resolution.HironakaActualStandardNormalIndependence,
    `Hironaka.Resolution.HironakaActualStrictExceptionalRegularity,
    `Hironaka.Resolution.HironakaActualStrictPullbackSaturation,
    `Hironaka.Resolution.HironakaActualStrictRadicalPullback,
    `Hironaka.Resolution.HironakaActualSubmanifoldGermExtension,
    `Hironaka.Resolution.HironakaActualSuppliedFlatteningNormalPowers,
    `Hironaka.Resolution.HironakaActualTangentCutLayers,
    `Hironaka.Resolution.HironakaActualTangentDisplacementZeroQuotient,
    `Hironaka.Resolution.HironakaActualTangentScalingFiltration,
    `Hironaka.Resolution.HironakaActualTargetOpenBlockProjectionHS,
    `Hironaka.Resolution.HironakaActualTaylorReconstruction,
    `Hironaka.Resolution.HironakaActualTowerLiftUniqueness,
    `Hironaka.Resolution.HironakaActualTowerPullbackAppend,
    `Hironaka.Resolution.HironakaActualTranslatedInitialHS,
    `Hironaka.Resolution.HironakaActualTriangularSubstitutionHS,
    `Hironaka.Resolution.HironakaActualTwoModelAnalyticGlueData,
    `Hironaka.Resolution.HironakaActualUnconditionalDualJetRaising,
    `Hironaka.Resolution.HironakaActualUniformCanonicalCoefficients,
    `Hironaka.Resolution.HironakaActualVertexNeumannDivision,
    `Hironaka.Resolution.HironakaActualVertexSmallRadius,
    `Hironaka.Resolution.HironakaActualWeightedCoefficientCompression,
    `Hironaka.Resolution.HironakaActualWeightedCoordinatePowerReflection,
    `Hironaka.Resolution.HironakaActualWeightedGeneratorTransformJets,
    `Hironaka.Resolution.HironakaActualZeroPointHSOrderCriterion,
    `Hironaka.Resolution.HironakaActualZeroPointReducedTail,
    `Hironaka.Resolution.HironakaBoundaryCoefficientBranchHistories,
    `Hironaka.Resolution.HironakaBoundaryCoefficientStratumResolution,
    `Hironaka.Resolution.HironakaCanonicalWordHistoryUniqueness,
    `Hironaka.Resolution.HironakaCharZeroCoefficientDescent,
    `Hironaka.Resolution.HironakaComponentwiseCanonicalCentre,
    `Hironaka.Resolution.HironakaComponentwiseCanonicalHistory,
    `Hironaka.Resolution.HironakaComponentwiseHistoryNaturality,
    `Hironaka.Resolution.HironakaDifferentialStableCylindricalIdeal,
    `Hironaka.Resolution.HironakaDiscreteCosupportCanonicalHistory,
    `Hironaka.Resolution.HironakaHomogeneousCanonicalNeighbourhoods,
    `Hironaka.Resolution.HironakaHomogeneousCanonicalResolution,
    `Hironaka.Resolution.HironakaHomogeneousCanonicalTowerMaxima,
    `Hironaka.Resolution.HironakaIntrinsicComplexAnalyticRegularLocus,
    `Hironaka.Resolution.HironakaLocalSymbolRegularity,
    `Hironaka.Resolution.HironakaMonomialBirthBlockObstruction,
    `Hironaka.Resolution.HironakaNormalCrossingsActualResidual,
    `Hironaka.Resolution.HironakaNormalCrossingsAnyMarkPrephase,
    `Hironaka.Resolution.HironakaNormalCrossingsBoundaryAvoidance,
    `Hironaka.Resolution.HironakaNormalCrossingsCanonicalChartHistories,
    `Hironaka.Resolution.HironakaNormalCrossingsCanonicalInitialStep,
    `Hironaka.Resolution.HironakaNormalCrossingsCoefficientBranchHistories,
    `Hironaka.Resolution.HironakaNormalCrossingsCoefficientRemainderPhase,
    `Hironaka.Resolution.HironakaNormalCrossingsCoefficientStratumResolution,
    `Hironaka.Resolution.HironakaNormalCrossingsDiagonalLiftOrbits,
    `Hironaka.Resolution.HironakaNormalCrossingsDoubleLocusMarkedCompatibility,
    `Hironaka.Resolution.HironakaNormalCrossingsDoubleLocusSeparation,
    `Hironaka.Resolution.HironakaNormalCrossingsFirstStepChartHistory,
    `Hironaka.Resolution.HironakaNormalCrossingsFirstStepFiniteValues,
    `Hironaka.Resolution.HironakaNormalCrossingsGlobalCanonicalResolution,
    `Hironaka.Resolution.HironakaNormalCrossingsGlobalPhaseCarrier,
    `Hironaka.Resolution.HironakaNormalCrossingsHighestSubcentreAdmissibility,
    `Hironaka.Resolution.HironakaNormalCrossingsInitialFullMaximum,
    `Hironaka.Resolution.HironakaNormalCrossingsIntrinsicStratumCentre,
    `Hironaka.Resolution.HironakaNormalCrossingsJointBranchCharts,
    `Hironaka.Resolution.HironakaNormalCrossingsOldBlockSuperlevels,
    `Hironaka.Resolution.HironakaNormalCrossingsPermittedCountDrop,
    `Hironaka.Resolution.HironakaNormalCrossingsSNCBlockCarrier,
    `Hironaka.Resolution.HironakaOpenCarrierTestTowerExtension,
    `Hironaka.Resolution.HironakaOriginalAllDepthCompactFullValues,
    `Hironaka.Resolution.HironakaOriginalAnalyticHSGenericDenominator,
    `Hironaka.Resolution.HironakaOriginalBoundTwoStepOneCutLocality,
    `Hironaka.Resolution.HironakaOriginalBoundTwoStepOneLocalReferenceComparison,
    `Hironaka.Resolution.HironakaOriginalBoundTwoStepOneLocality,
    `Hironaka.Resolution.HironakaOriginalBoundaryCanonicalPrincipalization,
    `Hironaka.Resolution.HironakaOriginalBoundaryEmptyBaseComparison,
    `Hironaka.Resolution.HironakaOriginalBoundaryEmptyFilterComparison,
    `Hironaka.Resolution.HironakaOriginalCanonicalDimensionList,
    `Hironaka.Resolution.HironakaOriginalCanonicalDimensionPartResolution,
    `Hironaka.Resolution.HironakaOriginalCanonicalElementaryPrincipalization,
    `Hironaka.Resolution.HironakaOriginalCanonicalEmptyParts,
    `Hironaka.Resolution.HironakaOriginalCanonicalIrreducibleFamily,
    `Hironaka.Resolution.HironakaOriginalCanonicalOrderedChoice,
    `Hironaka.Resolution.HironakaOriginalCanonicalOrderedResolution,
    `Hironaka.Resolution.HironakaOriginalCanonicalPartListResolution,
    `Hironaka.Resolution.HironakaOriginalCanonicalPrincipalizationSpecializations,
    `Hironaka.Resolution.HironakaOriginalCanonicalSeparationChainChoice,
    `Hironaka.Resolution.HironakaOriginalCanonicalSmoothTupleVariation,
    `Hironaka.Resolution.HironakaOriginalCanonicalSumSeparation,
    `Hironaka.Resolution.HironakaOriginalCentreAnalyticHSException,
    `Hironaka.Resolution.HironakaOriginalCoherentCompanionCountSmoothNaturality,
    `Hironaka.Resolution.HironakaOriginalCoherentHistoryYearSmoothNaturality,
    `Hironaka.Resolution.HironakaOriginalCompactSupportComponentHistory,
    `Hironaka.Resolution.HironakaOriginalCurrentCompactCutGlobalTailPhase,
    `Hironaka.Resolution.HironakaOriginalCurvePreparationCompanionSteps,
    `Hironaka.Resolution.HironakaOriginalCurveTranslationFamily,
    `Hironaka.Resolution.HironakaOriginalDiscreteFullCutCentres,
    `Hironaka.Resolution.HironakaOriginalDiscreteFullCutHistory,
    `Hironaka.Resolution.HironakaOriginalDiscretePositiveCompanion,
    `Hironaka.Resolution.HironakaOriginalDiscretePreparationFirstEntry,
    `Hironaka.Resolution.HironakaOriginalEmptyHeadPrefix,
    `Hironaka.Resolution.HironakaOriginalEmptySumStage,
    `Hironaka.Resolution.HironakaOriginalFiniteSimultaneousHSException,
    `Hironaka.Resolution.HironakaOriginalFirstMeetingPrefixUniqueness,
    `Hironaka.Resolution.HironakaOriginalFixedCompanionRunOrder,
    `Hironaka.Resolution.HironakaOriginalFixedCompanionStepOneComparison,
    `Hironaka.Resolution.HironakaOriginalFullCutCompanionHistory,
    `Hironaka.Resolution.HironakaOriginalFullCutFrozenCompanion,
    `Hironaka.Resolution.HironakaOriginalFullCutGlobalSuperlevels,
    `Hironaka.Resolution.HironakaOriginalFullCutPositiveGlobalSuperlevels,
    `Hironaka.Resolution.HironakaOriginalFullDimensionIdentity,
    `Hironaka.Resolution.HironakaOriginalGeneralControlledCompositeResidual,
    `Hironaka.Resolution.HironakaOriginalGlobalPrincipalization,
    `Hironaka.Resolution.HironakaOriginalGlobalSNCPrincipalization,
    `Hironaka.Resolution.HironakaOriginalGlobalSequencePrefixSplice,
    `Hironaka.Resolution.HironakaOriginalIndependentStoppedSource,
    `Hironaka.Resolution.HironakaOriginalIntrinsicNonpureRecipe,
    `Hironaka.Resolution.HironakaOriginalLocalCanonicalIrreducibleFamily,
    `Hironaka.Resolution.HironakaOriginalLocalCanonicalOrderedResolution,
    `Hironaka.Resolution.HironakaOriginalLocalCanonicalPartListResolution,
    `Hironaka.Resolution.HironakaOriginalLocalCanonicalPrincipalization,
    `Hironaka.Resolution.HironakaOriginalLocalCanonicalSumSeparation,
    `Hironaka.Resolution.HironakaOriginalLocalNonpureCanonicalResolution,
    `Hironaka.Resolution.HironakaOriginalLocalPureBoundaryCanonicalPrefix,
    `Hironaka.Resolution.HironakaOriginalLocalPureBoundaryIndependentSource,
    `Hironaka.Resolution.HironakaOriginalLocalPureHeadHosts,
    `Hironaka.Resolution.HironakaOriginalNonpureCanonicalResolution,
    `Hironaka.Resolution.HironakaOriginalNonpureCanonicalSpecializations,
    `Hironaka.Resolution.HironakaOriginalNonzeroCanonicalPrincipalization,
    `Hironaka.Resolution.HironakaOriginalOrderCutFiniteLevelCentres,
    `Hironaka.Resolution.HironakaOriginalOrderedTreeSmoothPullback,
    `Hironaka.Resolution.HironakaOriginalPrescribedLocalIrreducibleFamily,
    `Hironaka.Resolution.HironakaOriginalPureBoundaryCanonicalPrefix,
    `Hironaka.Resolution.HironakaOriginalPureBoundaryIndependentSource,
    `Hironaka.Resolution.HironakaOriginalPureBoundaryTerminalPrefix,
    `Hironaka.Resolution.HironakaOriginalPureCanonicalSpecializations,
    `Hironaka.Resolution.HironakaOriginalPureHeadChoice,
    `Hironaka.Resolution.HironakaOriginalReferenceValueBoundedStep,
    `Hironaka.Resolution.HironakaOriginalReferenceValueCanonicalNextTransform,
    `Hironaka.Resolution.HironakaOriginalReferenceValueCanonicalTailTransform,
    `Hironaka.Resolution.HironakaOriginalSmoothCentreFamilyGerm,
    `Hironaka.Resolution.HironakaOriginalSmoothCurveFullHSVariation,
    `Hironaka.Resolution.HironakaOriginalSmoothCurveWholeTupleBadBlowup,
    `Hironaka.Resolution.HironakaOriginalSmoothIntrinsicRegularLoci,
    `Hironaka.Resolution.HironakaOriginalSmoothSubmersionIntrinsicHS,
    `Hironaka.Resolution.HironakaOriginalStageReconstruction,
    `Hironaka.Resolution.HironakaOriginalStoppedBoundaryTransport,
    `Hironaka.Resolution.HironakaOriginalStoppedPrefixSmoothComparison,
    `Hironaka.Resolution.HironakaOriginalSubmersionHSNeighborhoods,
    `Hironaka.Resolution.HironakaOriginalTerminalProperProjection,
    `Hironaka.Resolution.HironakaOriginalTranslationFamilyHS,
    `Hironaka.Resolution.HironakaPDerivStablePolynomialXSaturation,
    `Hironaka.Resolution.HironakaReducedComplexAnalyticGluing,
    `Hironaka.Resolution.HironakaReducedComplexAnalyticMorphismCharts,
    `Hironaka.Resolution.HironakaReducedComplexAnalyticSpaces,
    `Hironaka.Resolution.HironakaRelativeNormalActualHSConvolution,
    `Hironaka.Resolution.HironakaRelativeNormalNormalPowerSpread,
    `Hironaka.Resolution.HironakaRelativeNormalTranslatedTaylorFunctions,
    `Hironaka.Resolution.HironakaSharpActualChronologicalOpenNaturality,
    `Hironaka.Resolution.HironakaSharpActualCurveStoppedPrefixSharpGeometry,
    `Hironaka.Resolution.HironakaSharpActualDistinctCountOpenNaturality,
    `Hironaka.Resolution.HironakaSharpActualDynamicMaximumOpen,
    `Hironaka.Resolution.HironakaSharpActualFamilyDefectOpenNaturality,
    `Hironaka.Resolution.HironakaSharpActualFiniteDeepPhase,
    `Hironaka.Resolution.HironakaSharpActualFirstDefectDimensionDrop,
    `Hironaka.Resolution.HironakaSharpActualFullBornIncidence,
    `Hironaka.Resolution.HironakaSharpActualFullMaximumWeightedPartition,
    `Hironaka.Resolution.HironakaSharpActualInitialFullCompatibility,
    `Hironaka.Resolution.HironakaSharpActualMaximumMemberOrders,
    `Hironaka.Resolution.HironakaSharpActualMemberOrderStrata,
    `Hironaka.Resolution.HironakaSharpActualRelativeSaturationOpenNaturality,
    `Hironaka.Resolution.HironakaSharpActualTraceIncidence,
    `Hironaka.Resolution.HironakaSharpOriginalFirstBlowupOpenComparison,
    `Hironaka.Resolution.HironakaSharpOriginalFirstDefectOpenNaturality,
    `Hironaka.Resolution.HironakaSmoothCentreNearbyCanonicalLayers,
    `Hironaka.Resolution.HironakaSmoothCentreRealDomainActualAmbientHS,
    `Hironaka.Resolution.HironakaSmoothCentreRealDomainActualCentrePowerStalk,
    `Hironaka.Resolution.HironakaSmoothCentreRealDomainActualCentreRingSheaf,
    `Hironaka.Resolution.HironakaSmoothCentreRealDomainActualCentreRingSheafStalk,
    `Hironaka.Resolution.HironakaSmoothCentreRealDomainActualIdealPresheaf,
    `Hironaka.Resolution.HironakaSmoothCentreRealDomainActualNormalAssociatedModuleRingPresheaf,
    `Hironaka.Resolution.HironakaSmoothCentreRealDomainActualNormalAssociatedModuleRingSheaf,
    `Hironaka.Resolution.HironakaSmoothCentreRealDomainActualNormalAssociatedRingPresheaf,
    `Hironaka.Resolution.HironakaSmoothCentreRealDomainActualNormalAssociatedRingScalars,
    `Hironaka.Resolution.HironakaSmoothCentreRealDomainActualNormalAssociatedRingSheaf,
    `Hironaka.Resolution.HironakaSmoothCentreRealDomainActualNormalAssociatedRingStalk,
    `Hironaka.Resolution.HironakaSmoothCentreRealDomainActualNormalAssociatedSheaf,
    `Hironaka.Resolution.HironakaSmoothCentreRealDomainActualNormalLayerScalars,
    `Hironaka.Resolution.HironakaSmoothCentreRealDomainActualNormalLayerSheaf,
    `Hironaka.Resolution.HironakaSmoothCentreRealDomainActualNormalLayerStalk,
    `Hironaka.Resolution.HironakaSmoothCentreRealDomainActualRemainderQuotientStalk,
    `Hironaka.Resolution.HironakaSmoothCentreRealDomainActualSheafStalk,
    `Hironaka.Resolution.HironakaSmoothCentreRealDomainCoefficientAlgebra,
    `Hironaka.Resolution.HironakaSmoothCentreRealDomainDeformation,
    `Hironaka.Resolution.HironakaSmoothCentreRealDomainFinitePolynomialModel,
    `Hironaka.Resolution.HironakaSmoothCentreRealDomainGraphDictionary,
    `Hironaka.Resolution.HironakaSmoothCentreRealDomainInitialEquality,
    `Hironaka.Resolution.HironakaSmoothCentreRealDomainInitialRelations,
    `Hironaka.Resolution.HironakaSmoothCentreRealDomainIntrinsicStalkFreeness,
    `Hironaka.Resolution.HironakaSmoothCentreRealDomainNearbyFreeness,
    `Hironaka.Resolution.HironakaSmoothCentreRealDomainNearbyInitialKernel,
    `Hironaka.Resolution.HironakaSmoothCentreRealDomainOriginalCentreOpen,
    `Hironaka.Resolution.HironakaSmoothCentreRealDomainOriginalStalkFreeness,
    `Hironaka.Resolution.HironakaSmoothCentreRealDomainSaturation,
    `Hironaka.Resolution.HironakaSmoothSubmersionOriginalGlobalFiniteFunctor,
    `Hironaka.Resolution.HironakaSmoothSubmersionOriginalGlobalFunctor,
    `Hironaka.Resolution.HironakaSmoothSubmersionOriginalGlobalIntrinsicUniqueness,
    `Hironaka.Resolution.HironakaSmoothSubmersionOriginalGlobalMap,
    `Hironaka.Resolution.HironakaSmoothSubmersionOriginalGlobalSubmersion,
    `Hironaka.Resolution.HironakaSmoothSubmersionOriginalLocalChartArrow,
    `Hironaka.Resolution.HironakaSmoothSubmersionOriginalLocalGlobalArrow,
    `Hironaka.Resolution.HironakaSmoothSubmersionOriginalSourceChartCompatibility,
    `Hironaka.Resolution.HironakaSmoothSubmersionOriginalSourceChartMap,
    `Hironaka.Resolution.HironakaSmoothSubmersionOriginalTargetChartCompatibility,
    `Hironaka.Resolution.HironakaStrictFilteredGradedQuotient,
    `Hironaka.Resolution.HironakaStrictFilteredRegularElement,
    `Hironaka.Resolution.HironakaSupportDisjointCanonicalCentre,
    `Hironaka.Support.CoefficientIdealTowerOperationsOriginalExact,
    `Hironaka.Support.CoefficientRestrictionSupportOriginalExact,
    `Hironaka.Support.CoefficientRestrictionTowerIffOriginalExact,
    `Hironaka.Support.CompactBlowupSurjectiveOriginalExact,
    `Hironaka.Support.DerivativeIdealTowerOriginalExact,
    `Hironaka.Support.DropMembersContainingCentresOriginalExact,
    `Hironaka.Support.EmbeddedOriginalRegularPrefixExact,
    `Hironaka.Support.HolGermMkSubPrimeOriginalExact,
    `Hironaka.Support.IrreducibleFullDimensionOpenOriginalExact,
    `Hironaka.Support.LocalGiraudRegularZeroSetOriginalExact,
    `Hironaka.Support.MarkedIdealOperationsMonotoneControlledOriginalExact,
    `Hironaka.Support.MemberInterTowerAlongOriginalExact,
    `Hironaka.Support.NormalCrossingsWellFormedSublistOriginalExact,
    `Hironaka.Support.NormalDerivativeChartIdealOriginalExact,
    `Hironaka.Support.OrderMultiplicativityCosupportOriginalExact,
    `Hironaka.Support.RestrictEmptyTowerAppendOriginalExact,
    `Hironaka.Support.RestrictEmptyTowerCentresOverOriginalExact,
    `Hironaka.Support.StepOneCanonicalStepDropOriginalExact,
    `Hironaka.Support.SubmanifoldRestrictLeOriginalExact
  ]
  let upstreamOnlyNames : Array Name := #[
    `Hironaka.AnalyticIrreducibleComponents.dim_eq_of_carrier_eq_univ,
    `Hironaka.AnalyticIrreducibleComponents.eq_of_regularAtDim_univ,
    `Hironaka.AnalyticIrreducibleComponents.eq_univ_of_isClosedConnectedSubmanifold_self,
    `Hironaka.AnalyticIrreducibleComponents.exists_subvariety_univ,
    `Hironaka.CoefficientIdealRestriction.N_coeffMarked,
    `Hironaka.EmbeddedFromResolution.mem_regularOpen_iff,
    `Hironaka.EmbeddedFromResolution.strictTransform_eq_connectedComponentIn,
    `Hironaka.EmbeddedFromResolution.strictTransform_eq_connectedComponentIn_maxLocus,
    `Hironaka.MarkedIdealOperationsTransform.controlledTransform_sumIdeal_idealPow,
    `Hironaka.MaximalContact.IsMaximalOrder.controlledTransform_of_subset_cosupport,
    `Hironaka.OrderMultiplicativity.cosupport_sumIdeal_idealPow,
    `Hironaka.StepFourOnStrictTransform.fderiv_coordinateMap_val_injective,
    `Hironaka.StepOneWellFounded.exists_isGeoResolution_of_wellFoundedLT,
    `Hironaka.StepOneWellFounded.exists_isGeoResolution_stepOneInvM,
    `Hironaka.StepOneWellFounded.isAdmissibleCentre_maxLocus_stepOneInvM,
    `Hironaka.StepOneWellFounded.stepDrop_of_resolutionInvariant,
    `Hironaka.StepOneWellFounded.stepOneInvM_lt_of_isCanonical_append
  ]
  for name in upstreamOnlyNames do
    unless (env.find? name).isNone do
      throwError "Upstream-only blueprint binding is actually exported locally: {name}"
  let expectedPublic : Nat :=
    60
  let frontendTag (ci : ConstantInfo) : Option Nat :=
    if ci.type.isConstOf ``ParserDescr then some 0
    else if ci.type.isConstOf ``Macro then some 1
    else if ci.type.isConstOf ``PrettyPrinter.Unexpander then some 2 else none
  let mut generated : Array (Name × ConstantInfo) := #[]
  let mut publicNames : Array Name := #[]
  for (oldModule,newModule,clauses) in pairs do
    for module in #[oldModule,newModule] do
      let some idx := env.header.moduleNames.findIdx? (· == module)
        | throwError "Missing actual notation owner {module}"
      let mut counts : Array Nat := #[0,0,0]
      for ci in env.header.moduleData[idx]!.constants do
        let some tag := frontendTag ci | continue
        unless ci matches .defnInfo _ do
          throwError "Typed notation root is not a definition: {ci.name}"
        unless (privateToUserName? ci.name).isSome do
          throwError "Typed notation root is not private: {ci.name}"
        unless (ci.value? (allowOpaque := true)).isSome do
          throwError "Missing whole generated body {ci.name}"
        generated := generated.push (module,ci)
        if module == newModule then publicNames := publicNames.push ci.name
        counts := counts.set! tag (counts[tag]!+1)
      unless counts == #[clauses,clauses,clauses] do
        throwError "Unexpected exact notation type inventory {module}: {counts}"
  unless generated.size == 2*expectedPublic && publicNames.size == expectedPublic do
    throwError "Unexpected actual typed notation inventory: {generated.size}/{publicNames.size}"
  let mut rows : Array Json := #[]
  for (module,ci) in generated do
    let typeName := if ci.type.isConstOf ``ParserDescr then "Lean.ParserDescr"
      else if ci.type.isConstOf ``Macro then "Lean.Macro"
      else "Lean.PrettyPrinter.Unexpander"
    rows := rows.push (Json.mkObj [
      ("actual_module_owner",toJson module.toString),
      ("actual_name",toJson ci.name.toString),
      ("actual_type",toJson typeName),
      ("kind",toJson "definition"),
      ("whole_value_present",toJson true)])
  let mut moduleCount := 0
  let mut newModuleCount := 0
  let mut constantsCount := 0
  let mut otherCount := 0
  let mut theoremCount := 0
  let mut typeEdges := 0
  let mut valueEdges := 0
  let mut references : Array Json := #[]
  for idx in [:env.header.moduleNames.size] do
    let module := env.header.moduleNames[idx]!
    unless module.toString == "Hironaka" || module.toString.startsWith "Hironaka." do continue
    moduleCount := moduleCount+1
    if newModules.contains module then newModuleCount := newModuleCount+1
    for ci in env.header.moduleData[idx]!.constants do
      constantsCount := constantsCount+1
      if ci matches .thmInfo _ then theoremCount := theoremCount+1
      if newModules.contains module && (frontendTag ci).isSome &&
          !publicNames.contains ci.name then
        throwError "Unclassified actual frontend root in new module {module}: {ci.name}"
      if publicNames.contains ci.name then continue
      otherCount := otherCount+1
      for dep in ci.type.getUsedConstants do
        typeEdges := typeEdges+1
        if publicNames.contains dep then
          references := references.push (Json.mkObj [
            ("module",toJson module.toString),("name",toJson ci.name.toString),
            ("field",toJson "type"),("direct_constant",toJson dep.toString)])
      for dep in ((ci.value? (allowOpaque := true)).map Expr.getUsedConstants).getD #[] do
        valueEdges := valueEdges+1
        if publicNames.contains dep then
          references := references.push (Json.mkObj [
            ("module",toJson module.toString),("name",toJson ci.name.toString),
            ("field",toJson "whole_value"),("direct_constant",toJson dep.toString)])
  unless moduleCount ==
    1533
    do throwError "Unexpected whole standalone module count {moduleCount}"
  unless newModuleCount == newModules.size do
    throwError "New physical module is absent from actual import closure: {newModuleCount}/{newModules.size}"
  unless otherCount+expectedPublic == constantsCount do
    throwError "Actual root inventory lost a generated root"
  unless references.isEmpty do
    throwError "Parser roots occur in actual other types/bodies: {references}"
  let output := Json.mkObj [
    ("status",toJson "PASS_ACTUAL_COMPILER_TYPES_AND_NO_LOGICAL_CONSTANT_DEPENDENTS"),
    ("actual_original_and_public_parser_roots",Json.arr rows),
    ("all_public_moduleData_modules",toJson moduleCount),
    ("actual_new_moduleData_modules",toJson newModuleCount),
    ("all_public_moduleData_constants",toJson constantsCount),
    ("all_public_moduleData_theorems",toJson theoremCount),
    ("other_actual_constants_scanned",toJson otherCount),
    ("direct_type_constant_edges_scanned",toJson typeEdges),
    ("direct_entire_value_constant_edges_scanned",toJson valueEdges),
    ("direct_references_to_public_parser_roots",Json.arr references),
    ("actual_upstream_only_public_names_verified_absent",toJson (upstreamOnlyNames.map Name.toString)),
    ("parser_body_structural_equality_claimed",toJson false),
    ("roots_excluded_from_kernel_or_axiom_inventory",toJson 0)]
  IO.FS.writeFile
    "audit/canonical-elementary-family-and-local-producers-20261021/all-notation-isolation-final-attempt01/all-notation-logical-isolation.json"
    output.pretty
  logInfo m!"PARSER_LOGICAL_ISOLATION modules={moduleCount} new={newModuleCount} constants={constantsCount} other={otherCount} references={references.size}"
