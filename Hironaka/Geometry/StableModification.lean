import Hironaka.Geometry.StableModification.Abhyankar
import Hironaka.Geometry.StableModification.Blowups.Basic
import Hironaka.Geometry.StableModification.Blowups.BaseChange
import Hironaka.Geometry.StableModification.Blowups.Extension
import Hironaka.Geometry.StableModification.Blowups.NodeChart
import Hironaka.Geometry.StableModification.Blowups.SmoothChart
import Hironaka.Geometry.StableModification.Blowups.StrictlySemistable
import Hironaka.Geometry.StableModification.Blowups.TransportSection
import Hironaka.Geometry.StableModification.Blowups.Transport
import Hironaka.Geometry.StableModification.Blowups.SeparationSections
import Hironaka.Geometry.StableModification.Blowups.SeparationCharts
import Hironaka.Geometry.StableModification.Blowups.SeparationLift
import Hironaka.Geometry.StableModification.Blowups.Separation
import Hironaka.Geometry.StableModification.Blowups.SeparationMarks
import Hironaka.Geometry.StableModification.RiemannZariski
import Hironaka.Geometry.StableModification.RiemannZariski.Refinement
import Hironaka.Geometry.StableModification.DeJong.Interface
import Hironaka.Geometry.StableModification.DeJong.Dimension
import Hironaka.Geometry.StableModification.DeJong.Reductions
import Hironaka.Geometry.StableModification.DeJong.Induction
import Hironaka.Geometry.StableModification.DeJong.Fibration
import Hironaka.Geometry.StableModification.DeJong.BaseStep
import Hironaka.Geometry.StableModification.DeJong.Main
import Hironaka.Geometry.StableModification.LocalUniformization.ModelValuation
import Hironaka.Geometry.StableModification.LocalUniformization.ModelCentre
import Hironaka.Geometry.StableModification.LocalUniformization.ModelStages
import Hironaka.Geometry.StableModification.LocalUniformization.ModelLocus
import Hironaka.Geometry.StableModification.LocalUniformization.Reduction
import Hironaka.Geometry.StableModification.LocalUniformization.GlobalNormal
import Hironaka.Geometry.StableModification.LocalUniformization.GlobalBase
import Hironaka.Geometry.StableModification.LocalUniformization.GlobalCentre
import Hironaka.Geometry.StableModification.LocalUniformization.GlobalChart
import Hironaka.Geometry.StableModification.LocalUniformization.GlobalClosed
import Hironaka.Geometry.StableModification.LocalUniformization.GlobalTransport
import Hironaka.Geometry.StableModification.LocalUniformization.GlobalResidue
import Hironaka.Geometry.StableModification.LocalUniformization.GlobalField
import Hironaka.Geometry.StableModification.LocalUniformization.GlobalChartMap
import Hironaka.Geometry.StableModification.LocalUniformization.GlobalStageTools
import Hironaka.Geometry.StableModification.LocalUniformization.GlobalSmoothStage
import Hironaka.Geometry.StableModification.LocalUniformization.GlobalNodeStage
import Hironaka.Geometry.StableModification.LocalUniformization.Cofinal
import Hironaka.Geometry.StableModification.LocalUniformization.CurveAlgebra
import Hironaka.Geometry.StableModification.LocalUniformization.CurveFinite
import Hironaka.Geometry.StableModification.LocalUniformization.CurveLocal
import Hironaka.Geometry.StableModification.LocalUniformization.CurveCofinal
import Hironaka.Geometry.StableModification.LocalUniformization.CurveLine
import Hironaka.Geometry.StableModification.LocalUniformization.CurveEtale
import Hironaka.Geometry.StableModification.LocalUniformization.CurveUniformization
import Hironaka.Geometry.StableModification.LocalUniformization.Curve
import Hironaka.Geometry.StableModification.Omega.Basic
import Hironaka.Geometry.StableModification.Omega.SpecDerivation
import Hironaka.Geometry.StableModification.Omega.Affine
import Hironaka.Geometry.StableModification.Omega.Dualizing
import Hironaka.Geometry.StableModification.Omega.Smooth
import Hironaka.Geometry.StableModification.Omega.NodeAlgebra
import Hironaka.Geometry.StableModification.Omega.Node
import Hironaka.Geometry.StableModification.Omega.NodeSingular
import Hironaka.Geometry.StableModification.Omega.InvertibleNode
import Hironaka.Geometry.StableModification.Omega.InvertibleSmooth
import Hironaka.Geometry.StableModification.Omega.EtaleNode
import Hironaka.Geometry.StableModification.Omega.EtaleBaseChange
import Hironaka.Geometry.StableModification.Omega.EtaleOmega
import Hironaka.Geometry.StableModification.Omega.EtaleDescent
import Hironaka.Geometry.StableModification.Omega.EtaleChart
import Hironaka.Geometry.StableModification.Omega.InvertibleNodal
import Hironaka.Geometry.StableModification.Omega.Invertible
import Hironaka.Geometry.StableModification.Omega.RosenlichtAlgebra
import Hironaka.Geometry.StableModification.Omega.RosenlichtEtale
import Hironaka.Geometry.StableModification.Omega.RosenlichtFibre
import Hironaka.Geometry.StableModification.Omega.BaseChange
import Hironaka.Geometry.StableModification.Omega.BaseChangeFibre
import Hironaka.Geometry.StableModification.Omega.BaseChangeFibreUnramified
import Hironaka.Geometry.StableModification.Omega.RosenlichtComponentDegree
import Hironaka.Geometry.StableModification.Omega.RosenlichtComponentPullback
import Hironaka.Geometry.StableModification.Omega.RosenlichtComponent
import Hironaka.Geometry.StableModification.Omega.RosenlichtComponentSmooth
import Hironaka.Geometry.StableModification.Omega.RosenlichtComponentNode
import Hironaka.Geometry.StableModification.Omega.PoleChartAlgebra
import Hironaka.Geometry.StableModification.Omega.PoleChartEtale
import Hironaka.Geometry.StableModification.Omega.PoleChart
import Hironaka.Geometry.StableModification.Omega.ComponentNormalization
import Hironaka.Geometry.StableModification.Omega.ComponentNormalizationSmooth
import Hironaka.Geometry.StableModification.Omega.ComponentNormalizationUnramified
import Hironaka.Geometry.StableModification.Omega.ComponentDegree
import Hironaka.Geometry.StableModification.Projectivity.LineBundle
import Hironaka.Geometry.StableModification.Projectivity.Reduction
import Hironaka.Geometry.StableModification.Projectivity.LineBundleTwist
import Hironaka.Geometry.StableModification.Projectivity.LineBundleTwistFunctor
import Hironaka.Geometry.StableModification.Projectivity.LineBundleOps
import Hironaka.Geometry.StableModification.Projectivity.LineBundleOpsInvertible
import Hironaka.Geometry.StableModification.Projectivity.LineBundleOpsHyperplane
import Hironaka.Geometry.StableModification.Projectivity.LineBundleOpsIso
import Hironaka.Geometry.StableModification.Projectivity.SectionsMap
import Hironaka.Geometry.StableModification.Projectivity.SectionsMapFibre
import Hironaka.Geometry.StableModification.Projectivity.SectionsMapGenerated
import Hironaka.Geometry.StableModification.Projectivity.SerreIdeal
import Hironaka.Geometry.StableModification.Projectivity.RelativeAlgebra
import Hironaka.Geometry.StableModification.Projectivity.RelativeCech
import Hironaka.Geometry.StableModification.Projectivity.RelativeFibre
import Hironaka.Geometry.StableModification.Projectivity.RelativeFinite
import Hironaka.Geometry.StableModification.Projectivity.RelativeOnto
import Hironaka.Geometry.StableModification.Projectivity.RelativeTwist
import Hironaka.Geometry.StableModification.Projectivity.RelativeSerre
import Hironaka.Geometry.StableModification.Projectivity.RelativeGenerated
import Hironaka.Geometry.StableModification.Projectivity.RelativeQuasiFinite
import Hironaka.Geometry.StableModification.Projectivity.RelativeAssembly
import Hironaka.Geometry.StableModification.Projectivity.RelativeCore
import Hironaka.Geometry.StableModification.Projectivity.RelativeCoverProj
import Hironaka.Geometry.StableModification.Projectivity.RelativeCoverLinear
import Hironaka.Geometry.StableModification.Projectivity.RelativeCover
import Hironaka.Geometry.StableModification.Projectivity.RelativeCoverFinite
import Hironaka.Geometry.StableModification.Projectivity.Relative
import Hironaka.Geometry.StableModification.Projectivity.StableHypotheses
import Hironaka.Geometry.StableModification.Projectivity.StableFibre
import Hironaka.Geometry.StableModification.Projectivity.ConnectedFibre
import Hironaka.Geometry.StableModification.Projectivity.ValuationSections
import Hironaka.Geometry.StableModification.Projectivity.ValuationProj
import Hironaka.Geometry.StableModification.CurvesField.AmpleTwoChart
import Hironaka.Geometry.StableModification.CurvesField.AmpleSerre
import Hironaka.Geometry.StableModification.CurvesField.AmpleAffine
import Hironaka.Geometry.StableModification.CurvesField.AmpleSection
import Hironaka.Geometry.StableModification.CurvesField.AmpleFiber
import Hironaka.Geometry.StableModification.CurvesField.AmplePositiveChart
import Hironaka.Geometry.StableModification.CurvesField.AmplePositiveDegree
import Hironaka.Geometry.StableModification.CurvesField.AmplePositiveBasic
import Hironaka.Geometry.StableModification.CurvesField.AmplePositiveIntegral
import Hironaka.Geometry.StableModification.CurvesField.AmplePositiveNormalization
import Hironaka.Geometry.StableModification.CurvesField.AmplePositiveEngine
import Hironaka.Geometry.StableModification.CurvesField.AmplePositiveTwoSection
import Hironaka.Geometry.StableModification.Perfection.Field
import Hironaka.Geometry.StableModification.Perfection.Normalization
import Hironaka.Geometry.StableModification.Perfection.Stabilization
import Hironaka.Geometry.StableModification.Perfection.SeparablePoints
import Hironaka.Geometry.StableModification.Perfection.LevelTransfer
import Hironaka.Geometry.StableModification.Perfection.Residue
import Hironaka.Geometry.StableModification.Perfection.Global
import Hironaka.Geometry.StableModification.Resolution.Local
import Hironaka.Geometry.StableModification.Resolution.Strictify
import Hironaka.Geometry.StableModification.Resolution.GlobalParameters
import Hironaka.Geometry.StableModification.Resolution.GlobalNodeModel
import Hironaka.Geometry.StableModification.Resolution.GlobalModelIdeals
import Hironaka.Geometry.StableModification.Resolution.GlobalFlat
import Hironaka.Geometry.StableModification.Resolution.GlobalChart
import Hironaka.Geometry.StableModification.Resolution.GlobalNodeChart
import Hironaka.Geometry.StableModification.Resolution.GlobalStep
import Hironaka.Geometry.StableModification.Resolution.GlobalBlowup
import Hironaka.Geometry.StableModification.Resolution.GlobalStages
import Hironaka.Geometry.StableModification.Resolution.GlobalFinal
import Hironaka.Geometry.StableModification.Resolution.GlobalSections
import Hironaka.Geometry.StableModification.Resolution.GlobalInitial
import Hironaka.Geometry.StableModification.Resolution.GlobalResolution
import Hironaka.Geometry.StableModification.ValCurves.ModificationsFiniteness
import Hironaka.Geometry.StableModification.Valuation.FiniteHeight
import Hironaka.Geometry.StableModification.Valuation.RankOneBridge
import Hironaka.Geometry.StableModification.Valuation.SepClosed
import Hironaka.Geometry.StableModification.Valuation.Bounded
import Hironaka.Geometry.StableModification.Valuation.InterfaceStatement
import Hironaka.Geometry.StableModification.Valuation.MainUniformizationBasic
import Hironaka.Geometry.StableModification.Valuation.MainUniformizationHeight
import Hironaka.Geometry.StableModification.Valuation.MainUniformizationAnalytic
import Hironaka.Geometry.StableModification.Valuation.MainUniformization
import Hironaka.Geometry.StableModification.Valuation.MainInterface
import Hironaka.Geometry.StableModification.Valuation.Composition
import Hironaka.Geometry.StableModification.Valuation.Unramified
import Hironaka.Geometry.StableModification.Valuation.UnramifiedEtale
import Hironaka.Geometry.StableModification.Valuation.CompositionUnramified
import Hironaka.Geometry.StableModification.Valuation.Decompletion
import Hironaka.Geometry.StableModification.Valuation.DVRCoordinate
import Hironaka.Geometry.StableModification.ValuationRing.Nagata
import Hironaka.Geometry.StableModification.ValuationRing.ElementaryDivisors
import Hironaka.Geometry.StableModification.ValuationRing.FibreDimension
import Hironaka.Geometry.StableModification.ValuationRing.Composite
import Hironaka.Geometry.StableModification.ValuationRing.HenselSections
import Hironaka.Geometry.StableModification.CurvesField.RiemannRochAlgebra
import Hironaka.Geometry.StableModification.CurvesField.CohomologyTwoCover
import Hironaka.Geometry.StableModification.CurvesField.CohomologyTwist
import Hironaka.Geometry.StableModification.CurvesField.CohomologyTwistLocal
import Hironaka.Geometry.StableModification.CurvesField.RiemannRoch
import Hironaka.Geometry.StableModification.CurvesField.CohomologyP1
import Hironaka.Geometry.StableModification.CurvesField.RiemannRochTemkin
import Hironaka.Geometry.StableModification.CurvesField.CohomologyP1Proj
import Hironaka.Geometry.StableModification.CurvesField.DualityLattice
import Hironaka.Geometry.StableModification.CurvesField.DualityDifferent
import Hironaka.Geometry.StableModification.CurvesField.DualityCurve
import Hironaka.Geometry.StableModification.CurvesField.DualityP1
import Hironaka.Geometry.StableModification.CurvesField.DualitySchemeComparison
import Hironaka.Geometry.StableModification.CurvesField.DualitySchemeIntegral
import Hironaka.Geometry.StableModification.CurvesField.DualitySchemeCharts
import Hironaka.Geometry.StableModification.CurvesField.DualitySchemeSeparable
import Hironaka.Geometry.StableModification.CurvesField.DualitySchemeExistence
import Hironaka.Geometry.StableModification.CurvesField.OmegaDegree
import Hironaka.Geometry.StableModification.CurvesField.OmegaDegreeProjective
import Hironaka.Geometry.StableModification.CurvesField.OmegaDegreeSmooth
import Hironaka.Geometry.StableModification.CurvesField.Delta
import Hironaka.Geometry.StableModification.CurvesField.Trees
import Hironaka.Geometry.StableModification.CurvesField.GenusEuler
import Hironaka.Geometry.StableModification.CurvesField.GenusLocal
import Hironaka.Geometry.StableModification.CurvesField.GenusCech
import Hironaka.Geometry.StableModification.CurvesField.GenusFormula
import Hironaka.Geometry.StableModification.CurvesField.GenusNormalization
import Hironaka.Geometry.StableModification.CurvesField.StableDown
import Hironaka.Geometry.StableModification.CurvesField.GenusReducedAlgebra
import Hironaka.Geometry.StableModification.CurvesField.GenusReducedEuler
import Hironaka.Geometry.StableModification.CurvesField.GenusReduced
import Hironaka.Geometry.StableModification.CurvesField.StableDownSchemeTop
import Hironaka.Geometry.StableModification.CurvesField.StableDownScheme
import Hironaka.Geometry.StableModification.CurvesField.StableDownSchemeCount
import Hironaka.Geometry.StableModification.CurvesField.OrdinaryCompletionBranches
import Hironaka.Geometry.StableModification.CurvesField.OrdinaryCompletion
import Hironaka.Geometry.StableModification.CurvesField.OrdinaryCompletionLocalization
import Hironaka.Geometry.StableModification.CurvesField.StableDownGeometricLocal
import Hironaka.Geometry.StableModification.CurvesField.StableDownGeometric
import Hironaka.Geometry.StableModification.CurvesField.StableDownGeometricFibre
import Hironaka.Geometry.StableModification.CurvesField.StableDownGeometricGraph
import Hironaka.Geometry.StableModification.CurvesField.StableDownGeometricCor
import Hironaka.Geometry.StableModification.CurvesField.StableDownGeometricNormalization
import Hironaka.Geometry.StableModification.CurvesField.OrdinaryGluingDVR
import Hironaka.Geometry.StableModification.CurvesField.OrdinaryGluingBranches
import Hironaka.Geometry.StableModification.CurvesField.OrdinaryGluingCompletion
import Hironaka.Geometry.StableModification.CurvesField.OrdinaryGluingLocal
import Hironaka.Geometry.StableModification.CurvesField.OrdinaryGluing
import Hironaka.Geometry.StableModification.BlowDown.Normalization
import Hironaka.Geometry.StableModification.BlowDown.NormalizationCurve
import Hironaka.Geometry.StableModification.BlowDown.Genus
import Hironaka.Geometry.StableModification.BlowDown.Criterion
import Hironaka.Geometry.StableModification.BlowDown.ClosedLocus
import Hironaka.Geometry.StableModification.BlowDown.GraphConnected
import Hironaka.Geometry.StableModification.BlowDown.NodalReduced
import Hironaka.Geometry.StableModification.BlowDown.FibreIso
import Hironaka.Geometry.StableModification.BlowDown.Marks
import Hironaka.Geometry.StableModification.BlowDown.Localize
import Hironaka.Geometry.StableModification.BlowDown.StabilityCount
import Hironaka.Geometry.StableModification.BlowDown.StabilityTop
import Hironaka.Geometry.StableModification.BlowDown.StabilityFibre
import Hironaka.Geometry.StableModification.BlowDown.StabilityCriterion
import Hironaka.Geometry.StableModification.BlowDown.StabilityLocal
import Hironaka.Geometry.StableModification.BlowDown.ClosureComponent
import Hironaka.Geometry.StableModification.BlowDown.ExcSpecializeGenus
import Hironaka.Geometry.StableModification.BlowDown.ExcSpecialize
import Hironaka.Geometry.StableModification.BlowDown.NoClosedExc
import Hironaka.Geometry.StableModification.BlowDown.DominationGraph
import Hironaka.Geometry.StableModification.BlowDown.Domination
import Hironaka.Geometry.StableModification.BlowDown.DominationStable
import Hironaka.Geometry.StableModification.BlowDown.ProjectiveBookkeeping
import Hironaka.Geometry.StableModification.BlowDown.ContractionDimension
import Hironaka.Geometry.StableModification.BlowDown.Contraction
import Hironaka.Geometry.StableModification.BlowDown.ContractionStep
import Hironaka.Geometry.StableModification.BlowDown.ContractionMarks
import Hironaka.Geometry.StableModification.BlowDown.ContractionStein
import Hironaka.Geometry.StableModification.BlowDown.Stable
import Hironaka.Geometry.StableModification.BlowDown.StableComb
import Hironaka.Geometry.StableModification.BlowDown.ContractingMap
import Hironaka.Geometry.StableModification.BlowDown.SectionsLocal
import Hironaka.Geometry.StableModification.BlowDown.SectionsDivisor
import Hironaka.Geometry.StableModification.BlowDown.SectionsHyperplane
import Hironaka.Geometry.StableModification.BlowDown.VanishingCore
import Hironaka.Geometry.StableModification.BlowDown.VanishingGenus
import Hironaka.Geometry.StableModification.BlowDown.VanishingNakayama
import Hironaka.Geometry.StableModification.BlowDown.VanishingFibre
import Hironaka.Geometry.StableModification.BlowDown.VanishingTwist
import Hironaka.Geometry.StableModification.BlowDown.ContractingExists
import Hironaka.Geometry.StableModification.BlowDown.ComponentGenusAlgebra
import Hironaka.Geometry.StableModification.BlowDown.ComponentGenusSplit
import Hironaka.Geometry.StableModification.BlowDown.ComponentGenus
import Hironaka.Geometry.StableModification.BlowDown.NumericalDescentAlgebra
import Hironaka.Geometry.StableModification.BlowDown.NumericalDescentEuler
import Hironaka.Geometry.StableModification.BlowDown.NumericalDescentScheme
import Hironaka.Geometry.StableModification.BlowDown.NumericalDescentSmooth
import Hironaka.Geometry.StableModification.BlowDown.NumericalDescentFibre
import Hironaka.Geometry.StableModification.BlowDown.NumericalDescent
import Hironaka.Geometry.StableModification.BlowDown.ClosureLocalAlgebra
import Hironaka.Geometry.StableModification.BlowDown.ClosureLocalNode
import Hironaka.Geometry.StableModification.BlowDown.ClosureLocalHypersurface
import Hironaka.Geometry.StableModification.BlowDown.ClosureLocalChart
import Hironaka.Geometry.StableModification.BlowDown.ClosureLocalScheme
import Hironaka.Geometry.StableModification.BlowDown.Unconditional
import Hironaka.Geometry.StableModification.BlowDown.ClosureLocalPoints
import Hironaka.Geometry.StableModification.BlowDown.ClosureLocalReduced
import Hironaka.Geometry.StableModification.BlowDown.ClosureLocalAssembly
import Hironaka.Geometry.StableModification.BlowDown.UnconditionalFinal
import Hironaka.Geometry.StableModification.Gluing.GammaFinite
import Hironaka.Geometry.StableModification.Gluing.RefinementProjective
import Hironaka.Geometry.StableModification.Gluing.RefinementProjectiveBirational
import Hironaka.Geometry.StableModification.Gluing.Setup
import Hironaka.Geometry.StableModification.Gluing.Normalization
import Hironaka.Geometry.StableModification.Gluing.BadLocus
import Hironaka.Geometry.StableModification.Gluing.LocalModels
import Hironaka.Geometry.StableModification.Gluing.Extension
import Hironaka.Geometry.StableModification.Gluing.ExtensionAssembly
import Hironaka.Geometry.StableModification.Gluing.SetupAssembly
import Hironaka.Geometry.StableModification.Gluing.BlowupProjectiveFlat
import Hironaka.Geometry.StableModification.Gluing.BlowupProjective
import Hironaka.Geometry.StableModification.Gluing.BlowupProjectiveNode
import Hironaka.Geometry.StableModification.Gluing.CofinalProjectiveTransport
import Hironaka.Geometry.StableModification.Gluing.CofinalProjectiveStage
import Hironaka.Geometry.StableModification.Gluing.CofinalProjective
import Hironaka.Geometry.StableModification.Gluing.NodalUnconditional
import Hironaka.Geometry.StableModification.Gluing.MarksSections
import Hironaka.Geometry.StableModification.Gluing.MarksGeneric
import Hironaka.Geometry.StableModification.Gluing.MarksLift
import Hironaka.Geometry.StableModification.Gluing.MarksLocal
import Hironaka.Geometry.StableModification.Gluing.MarksModel
import Hironaka.Geometry.StableModification.Gluing.MarksNodal
import Hironaka.Geometry.StableModification.Gluing.ExistenceVal
import Hironaka.Geometry.StableModification.Gluing.SeparationProjectiveTransport
import Hironaka.Geometry.StableModification.Gluing.SeparationProjective
import Hironaka.Geometry.StableModification.Gluing.MarksSeparation
import Hironaka.Geometry.StableModification.Gluing.UniquenessValSetup
import Hironaka.Geometry.StableModification.Gluing.UniquenessValMarks
import Hironaka.Geometry.StableModification.Gluing.UniquenessJoin
import Hironaka.Geometry.StableModification.Gluing.UniquenessValBridge
import Hironaka.Geometry.StableModification.Gluing.UniquenessVal
import Hironaka.Geometry.StableModification.Gluing.MarksNodalFinal
import Hironaka.Geometry.StableModification.Gluing.ExistenceValFinal
import Hironaka.Geometry.StableModification.Gluing.UniquenessValFinal
import Hironaka.Geometry.StableModification.Global.Statements
import Hironaka.Geometry.StableModification.Global.StatementsBaseChange
import Hironaka.Geometry.StableModification.Global.Alteration
import Hironaka.Geometry.StableModification.Global.Glue
import Hironaka.Geometry.StableModification.Global.SetupMarks
import Hironaka.Geometry.StableModification.Global.SetupModel
import Hironaka.Geometry.StableModification.Global.GlueModel
import Hironaka.Geometry.StableModification.Global.SetupModelTransport
import Hironaka.Geometry.StableModification.Global.Cover
import Hironaka.Geometry.StableModification.Global.CoverGlue
import Hironaka.Geometry.StableModification.Global.Pairwise
import Hironaka.Geometry.StableModification.Global.Setup
import Hironaka.Geometry.StableModification.Global.Spread
import Hironaka.Geometry.StableModification.Global.SpreadPiece
import Hironaka.Geometry.StableModification.Global.MainModel
import Hironaka.Geometry.StableModification.Global.MainPieces
import Hironaka.Geometry.StableModification.Global.Main
import Hironaka.Geometry.StableModification.Global.DeJongTheorem
import Hironaka.Geometry.StableModification.Global.StableOpenStatement
import Hironaka.Geometry.StableModification.Global.SpreadPieceConnFibre
import Hironaka.Geometry.StableModification.Global.SpreadPieceConn
import Hironaka.Geometry.StableModification.Global.MainConn
import Hironaka.Geometry.StableModification.Global.StableOpenAscent
import Hironaka.Geometry.StableModification.Global.StableOpenReduce
import Hironaka.Geometry.StableModification.Cohomology.FiniteCoordinates
import Hironaka.Geometry.StableModification.Cohomology.FiniteSerre
import Hironaka.Geometry.StableModification.Cohomology.FiniteComparison
import Hironaka.Geometry.StableModification.Cohomology.FiniteProjective
import Hironaka.Geometry.StableModification.Cohomology.BaseChange
import Hironaka.Geometry.StableModification.Cohomology.MumfordAlgebra
import Hironaka.Geometry.StableModification.Cohomology.MumfordCorollaries
import Hironaka.Geometry.StableModification.Cohomology.Mumford
import Hironaka.Geometry.StableModification.Cohomology.ValuationLaurent
import Hironaka.Geometry.StableModification.Cohomology.ValuationCoherent
import Hironaka.Geometry.StableModification.Cohomology.ValuationPerfect
import Hironaka.Geometry.StableModification.Cohomology.Valuation
import Hironaka.Geometry.StableModification.Cohomology.CurveCover
import Hironaka.Geometry.StableModification.Cohomology.CurveHypersurface
import Hironaka.Geometry.StableModification.Cohomology.PullbackQcoh
import Hironaka.Geometry.StableModification.Cohomology.SteinCoherent
import Hironaka.Geometry.StableModification.Cohomology.SteinFinite
import Hironaka.Geometry.StableModification.Cohomology.SteinProjective
import Hironaka.Geometry.StableModification.Cohomology.SteinReduced
import Hironaka.Geometry.StableModification.Cohomology.ConnectedAlgebra
import Hironaka.Geometry.StableModification.Cohomology.ConnectedStep
import Hironaka.Geometry.StableModification.Cohomology.Connected
import Hironaka.Geometry.StableModification.Cohomology.ConnectedBirationalCore
import Hironaka.Geometry.StableModification.Cohomology.ConnectedBirationalCech
import Hironaka.Geometry.StableModification.Cohomology.ConnectedBirationalCharts
import Hironaka.Geometry.StableModification.Cohomology.ConnectedBirational
import Hironaka.Geometry.StableModification.Cohomology.ConnectedBirationalHeightTop
import Hironaka.Geometry.StableModification.Cohomology.ConnectedBirationalHeightClosure
import Hironaka.Geometry.StableModification.Cohomology.ConnectedBirationalHeightCharts
import Hironaka.Geometry.StableModification.Cohomology.ConnectedBirationalHeight
import Hironaka.Geometry.StableModification.Cohomology.Cech
import Hironaka.Geometry.StableModification.Flattening.Torsion
import Hironaka.Geometry.StableModification.Flattening.Valuation
import Hironaka.Geometry.StableModification.Flattening.Chart
import Hironaka.Geometry.StableModification.Flattening.Main
import Hironaka.Geometry.StableModification.Limits.System
import Hironaka.Geometry.StableModification.Limits.Descent
import Hironaka.Geometry.StableModification.Limits.FlatDescent
import Hironaka.Geometry.StableModification.Limits.SpreadDimension
import Hironaka.Geometry.StableModification.Limits.SpreadFlat
import Hironaka.Geometry.StableModification.Limits.SpreadNodal
import Hironaka.Geometry.StableModification.Limits.SpreadProperty
import Hironaka.Geometry.StableModification.Limits.SpreadAffine
import Hironaka.Geometry.StableModification.Limits.SpreadMarks
import Hironaka.Geometry.StableModification.Limits.SpreadModificationIso
import Hironaka.Geometry.StableModification.Limits.SpreadModificationProjective
import Hironaka.Geometry.StableModification.Limits.SpreadModification
import Hironaka.Geometry.StableModification.Curves.Basic
import Hironaka.Geometry.StableModification.Curves.StandardModels
import Hironaka.Geometry.StableModification.Curves.SemistableOpen
import Hironaka.Geometry.StableModification.Curves.SemistableNormalEtale
import Hironaka.Geometry.StableModification.Curves.SemistableNormalMorse
import Hironaka.Geometry.StableModification.Curves.SemistableNormalLocal
import Hironaka.Geometry.StableModification.Curves.SemistableNormalNode
import Hironaka.Geometry.StableModification.Curves.SemistableNormalHypersurface
import Hironaka.Geometry.StableModification.Curves.SemistableNormalAlgebra
import Hironaka.Geometry.StableModification.Curves.SemistableNormalSmooth
import Hironaka.Geometry.StableModification.Curves.SemistableNormalScheme
import Hironaka.Geometry.StableModification.Valuation.Analytic.Basic
import Hironaka.Geometry.StableModification.Valuation.Analytic.Hensel
import Hironaka.Geometry.StableModification.Valuation.Analytic.OrthogonalBasis
import Hironaka.Geometry.StableModification.Valuation.Analytic.Defect
import Hironaka.Geometry.StableModification.Valuation.Analytic.Krasner
import Hironaka.Geometry.StableModification.Valuation.Analytic.SepClosedCompletion
import Hironaka.Geometry.StableModification.Valuation.Analytic.Cosets
import Hironaka.Geometry.StableModification.Valuation.Analytic.TypeFour.Basic
import Hironaka.Geometry.StableModification.Valuation.Analytic.TypeFour.Taylor
import Hironaka.Geometry.StableModification.Valuation.Analytic.TypeFour.Dirty
import Hironaka.Geometry.StableModification.Valuation.Analytic.TypeFour.Generator
import Hironaka.Geometry.StableModification.Valuation.Analytic.Annulus
import Hironaka.Geometry.StableModification.Valuation.Analytic.TypeThree
import Hironaka.Geometry.StableModification.Valuation.Analytic.CoefficientField
import Hironaka.Geometry.StableModification.Valuation.Analytic.Gauss
import Hironaka.Geometry.StableModification.Valuation.Analytic.Schauder
import Hironaka.Geometry.StableModification.Valuation.Analytic.TypeTwo
import Hironaka.Geometry.StableModification.Valuation.Analytic.Inertia
import Hironaka.Geometry.StableModification.Valuation.Analytic.Kummer
import Hironaka.Geometry.StableModification.Valuation.Analytic.Towers
import Hironaka.Geometry.StableModification.Valuation.Analytic.ArtinSchreier
import Hironaka.Geometry.StableModification.Valuation.Analytic.ImmediateDegreeP
import Hironaka.Geometry.StableModification.Valuation.Analytic.CritMinZero
import Hironaka.Geometry.StableModification.Valuation.Analytic.OneDim
import Hironaka.Geometry.StableModification.Valuation.Analytic.Continuity
import Hironaka.Geometry.StableModification.Valuation.Analytic.OneDimGalois
import Hironaka.Geometry.StableModification.Valuation.Analytic.OneDimTypes
import Hironaka.Geometry.StableModification.Valuation.Analytic.Uniformization
import Hironaka.Geometry.StableModification.Valuation.Analytic.OneDimStable
import Hironaka.Geometry.StableModification.Valuation.FunctionField.Places
import Hironaka.Geometry.StableModification.Valuation.FunctionField.PoleNorm
import Hironaka.Geometry.StableModification.Valuation.FunctionField.FrobeniusBasis

/-!
# Temkin's stable modification route (Claude team)

Umbrella module for the Claude team's moduli-free route to de Jong's stable pointed extension
(de Jong 2.24, 2.19, 4.17–4.21), following M. Temkin, *Stable modification of relative curves*,
J. Algebraic Geom. 19 (2010) (`references/temkin10-stable-modification`). Decision D-DJ1 and the plans
are in `.archon-horizon/scratch/dja/`; the blueprint chapters are `blueprint/src/sm-*.tex`.

* `StableModification.Abhyankar`: Abhyankar's inequality and finite height of valuations (Temkin §2.1).
* `StableModification.Blowups`: explicit blow-ups of the node and smooth models over a domain (strictly semistable
  charts, isomorphism off the centre), extension of a modification of an open, base change (Temkin §4.3); étale
  transport of chart blow-ups over a strictly henselian base and boundary separation (Temkin Lemma 4.3.2).
* `StableModification.RiemannZariski`: Riemann–Zariski spaces of valuation rings (Temkin §3.2), and the refinement
  of finitely many pieces into opens of one proper (generically étale) modification (Temkin 3.2.3, 3.2.6).
* `StableModification.DeJong`: the main-chain interface (nodal curves, producer propositions), dimension lemmas,
  dimension-indexed reductions, the conditional induction `deJongAlterationTheorem_of_producers`, and the
  Temkin-ready fibration (`TemkinReadyFibration k`: outright in characteristic 0, from `PurelyInseparableSmoothing k`
  in characteristic p), and the base step `baseStep : BaseStep k` (de Jong 4.22 with Temkin; unconditional).
* `StableModification.LocalUniformization`: Temkin's local uniformization (Prop 4.3.1) in the node and smooth
  model situations, the reduction of cofinality to the centre claim, and the global statement
  (`exists_dominates_isStrictlySemistable`: strictly semistable modifications are cofinal among normal modifications;
  `isNormalScheme_of_isStrictlySemistable`); `LocalUniformization.Curve*`: Temkin Prop 4.3.3, finitely many strictly
  semistable affine quasi-modifications cover `RZ_L(C)` (`exists_finite_isStrictlySemistable_cover`).
* `StableModification.Omega`: the sheaf of relative differentials `Ω¹_{X/S}` (universal property, affine description)
  and `ω = j_*Ω¹` on the smooth locus; invertible for smooth curves; on node charts `R[u,v]/(uv − h)` the smooth
  locus is `D(u) ∪ D(v)` and `ω` is free of rank one on basic opens (generator `du/u = −dv/v`).
  `Omega.Invertible*`, `Omega.Etale*`: `ω` is invertible for nodal curves with smooth generic fibre over an integral
  normal locally Noetherian base (`isInvertibleModule_dualizingSheaf_of_isNodalCurve`; étale node charts and descent).
  `Omega.Rosenlicht*`, `Omega.BaseChange`: Rosenlicht's module at a node (`isRosenlicht_iff`, residues of
  `du/u = −dv/v`), the geometric fibre of an étale node chart, and the base change map of `Ω¹` with its effect on the
  generator (`baseChange_generator_spec`).
  `Omega.BaseChangeFibre*`, `Omega.RosenlichtComponent*`: the smooth locus commutes with base change to geometric
  fibres, and the degree of the pullback of `ω` to a normalized fibre component, `2p_a − 2 + #E`
  (`degree_pullback_dualizingSheaf_of_isNodalCurve`, with the pole charts at the nodes as the hypothesis
  `HasPoleCharts`, proved in `Omega.PoleChart`); `Omega.ComponentNormalization*`, `Omega.ComponentDegree`: the
  normalization of a component of a geometric fibre is smooth and unramified over the fibre, and
  `deg ν^*ω = 2g(Z̃) − 2 + #E` unconditionally (`degree_pullback_dualizingSheaf_component`, with marks
  `degree_twist_component`).
* `StableModification.Projectivity`: Temkin's Thm 1.1 route (PLAN-OM3): reduction of relative projectivity to a finite
  map to `ℙᴺ` (`isRelativelyProjective_of_finite_fibres`), line-bundle data with twists, powers, products, invertible
  modules, Cartier data and hyperplane bundles (`LineBundleData`), `FiberAmple`, `LocallyRelativelyProjective`, and the
  map `toProjectiveSpace` defined by generating sections; `Projectivity.SerreIdeal`: blow-ups of finite-type ideal
  sheaves on schemes projective over a ring are projective (`isProjectiveOver_blowupStructure_comp_of_fg`).
  `Projectivity.Relative*`: the local-to-global theorem (PLAN-OM3 M4): a locally relatively projective `β` over a
  projective base, with a good section on each closed fibre, is relatively projective
  (`isRelativelyProjective_of_fiberSections`, valuation-ring case `…_valuation`).
  `Projectivity.{StableHypotheses,StableFibre,ConnectedFibre}` (lane OM3D, partial): fibre facts and connected geometric
  fibres of the stable model (input of T59), from the valuation-level projectivity `ValuationProjectivity`.
  `Projectivity.Valuation*`: the valuation-level projectivity (PLAN-OM3 M7), `Valuation.valuationProjectivity` and
  `Valuation.isProjectiveOver_of_valuationSubring` (a locally relatively projective nodal curve over a projective curve
  over a finite-height valuation ring of an algebraically closed field is projective).
  `CurvesField.Ample*`: fibre-ampleness from a section of `L^n` on a projective curve over an infinite field
  (`CurvesField.fiberAmple_of_positive`, `serreAmple_of_section`; the fibre may be non-reduced).
  `CurvesField.AmplePositive*`: Riemann–Roch for two-chart presentations and ampleness from positive degree on an
  integral curve or its normalization (`serreAmple_of_degree_pos_of_isIntegral`).
* `StableModification.Perfection`: purely inseparable base change gives a smooth normalization of the generic fibre
  and separable residue fields; `Perfection.Global` proves the scheme-level `PurelyInseparableSmoothing k` and hence
  `TemkinReadyFibration k` for every algebraically closed `k`.
* `StableModification.Resolution`: the resolution endgame; `Resolution.Local` is de Jong's local model of a nodal curve
  over a regular base with SNC degeneration divisor (3.1, 3.3, 3.5, 4.23–4.25); `Resolution.Strictify` turns a
  normal crossings divisor on a regular projective variety into a strict one by blowups (2.4); `Resolution.Global*`
  proves `SemistableResolution k` (de Jong 3.2, 3.4, 4.23–4.28: `Resolution.Global.semistableResolution`).
* `StableModification.ValCurves`: modifications of curves over a valuation ring (Temkin §4.2): the sets `Γ(C')`,
  `Γ₀(C')`, finiteness of the modification locus, domination (Prop 4.2.3).
* `StableModification.Valuation`: the valuation side of Temkin (§2, §6): finite height and coarsenings, the
  height-one/rank-one bridge, separably closed valued fields; `Valuation.Analytic`: complete rank-one fields
  (normed/valued bridge, Hensel, defect and Cartesian extensions, r-orthogonal bases, Krasner density, completions
  of separably closed fields are algebraically closed); composite valuations, standard-unramified extensions,
  bounded extensions, the interface statement `UniformizationEtaleStatement` of Temkin 2.1.8 (proved:
  `uniformizationEtaleStatement`, by induction on the height of the base), decompletion with
  prescribed residue (Temkin 2.2.1) and the DVR étale coordinate; Artin–Schreier
  cosets and one-dimensional analytic fields of types 2, 3 and 4 (Temkin 6.1, 6.2.4, 6.2.5, 6.2.7–6.2.9; type 2 via
  coefficient fields and orthonormal Schauder bases); inertia, wild inertia, Kummer and Artin–Schreier steps,
  p-towers, immediate degree-p extensions and Frobenius degrees (Temkin 6.1, 6.3); function fields of
  one variable (places are DVRs, finiteness of poles, the pole-order norm, Frobenius bases: Temkin 6.2.6);
  uniformization of one-dimensional analytic fields in equal characteristic (Temkin 6.3.1(i), (iii), 2.1.10).
* `StableModification.ValuationRing`: algebra and geometry over valuation rings (Nagata: flat + finite type ⇒
  finitely presented, coherence), elementary divisors, fibre transcendence degrees, composite-valuation chains,
  Hensel sections, ….
* `StableModification.CurvesField`: curves over fields (Temkin App. B): δ-invariants and ordinary points in gluing form,
  incidence graphs, exceptional trees and the uniqueness of the stable blow-down (combinatorial core).
  `CurvesField.{RiemannRoch,Cohomology*}`: two-chart Čech cohomology, twists by a unit, weak Riemann–Roch, Serre
  vanishing and global generation for divisor twists, `H*(ℙ¹, O(n))`, and the corrected vanishing step of Temkin
  Prop 4.4.6 (`isZero_cohomology_one_temkin`).
  `CurvesField.Duality*`: Serre duality for the two-chart complexes of a finite separable cover of `ℙ¹` (Dedekind's
  `Ω¹_{A/k} = A^∨ dt`), `h⁰(Ω) = g`, `deg Ω = 2g − 2` in Riemann–Roch form, and the case `ℙ¹`.
  `CurvesField.{DualityScheme*,OmegaDegree*}`: the same for a normal (e.g. smooth) projective integral curve over
  `k = k̄` and its sheaf `Ω¹` (`omegaDegree_of_smooth`: `h⁰(Ω) = p_a`, `h¹(Ω) = 1`, `χ(Ω) − χ(O) = 2p_a − 2`).
  `CurvesField.Genus*`, `StableDown`: the δ-formula for an affine finite-cokernel map, the genus formula for integral
  projective curves via the normalization (Lemma B.1), and Cor B.2 in numerical and local-algebra form;
  `CurvesField.GenusReduced*`, `StableDownScheme*`: Lemma B.1 for reduced curves and the scheme-level δ-count of Cor B.2.
  `CurvesField.{OrdinaryCompletion*,StableDownGeometric*}`: Temkin's Cor B.2 at scheme level with `C`'s normalization
  (`stabdown_scheme_normalization_iff`) and the variant for ℙ¹-tree components (`stabdown_scheme_of_isP1Tree`).
  `CurvesField.OrdinaryGluing*`: the converse for `n ≤ 2`, an ordinary point in gluing form is smooth or an ordinary
  double point in the completed sense (`ordinaryPointCompletion_of_isAlgClosed`).
* `StableModification.BlowDown`: Temkin §4.4 (part): the relative normalization of a projective modification onto a
  normal curve is an isomorphism and has reduced closed fibre (`prop:sm-normalization-reduced`), constancy of `χ` and
  of the arithmetic genus along the fibres, the numerical stability criterion, closedness of the modification locus;
  `BlowDown.{NodalReduced,FibreIso,Marks,Localize,Stability*}`: reduced nodal fibres, Temkin's Lemma 4.4.2 at scheme
  level for all contracted points of a fibre (`stability_criterion_fibre`, `stability_criterion_fibre_iff`) and its
  local form;
  `BlowDown.{ClosureComponent,ExcSpecialize*,NoClosedExc}`: closures of fibre components over `V/𝔭`, exceptional
  components specialize to exceptional ones (`exists_isCombExceptional_closedFibre`), Temkin's Lemma 4.4.4 in the
  direction "`E₀ = ∅` ⇒ stable" (`isStableModification_of_forall_not_isCombExceptional`), and `componentGenus_nonneg`;
  the inputs `ClosureComponentLocal`, `NodalComponentGenus`, `NumericalDescent` are named hypotheses;
  `BlowDown.Domination*`: Temkin's Cor 4.4.3(1), a semistable modification and a fibrewise stable one dominated by a
  common semistable modification are comparable (`dominates_of_fibreStable`), and uniqueness of the stable one
  (`nonempty_iso_of_fibreStable`);
  `BlowDown.{ProjectiveBookkeeping,Contraction*,Stable*}`: Temkin's Lemma 4.4.5 (the blow-down of an exceptional
  component is semistable) and the iteration of Prop 4.4.6 to a stable, numerically stable modification
  (`exists_isStableModification_of_isSemistableStage`), with the contracting morphism as the named hypothesis
  `ContractingMorphismExists`, proved for `C` projective over `V` by `BlowDown.ContractingExists.contractingMorphismExists`
  (sections through a hyperplane section, vanishing via `0 → I_Z → O_{Y∖D} → O_Z → 0`, Nakayama, the map to
  `ℙ¹_C`).
  `BlowDown.{ComponentGenus*,NumericalDescent*,ClosureLocal*,Unconditional}`: `NodalComponentGenus` and `NumericalDescent`
  proved; `BlowDown.{ClosureLocalPoints,ClosureLocalReduced,ClosureLocalAssembly,UnconditionalFinal}`:
  `ExcSpecialize.closureComponentLocal`, hence the stable blow-down for `C` projective with no named hypothesis
  (`UnconditionalFinal.exists_isStableModification_of_isSemistableStage_of_isProjectiveOver`).
* `StableModification.Cohomology`: Čech cohomology of quasi-coherent modules for finite affine covers (independence of
  the cover, long exact sequence, affine vanishing, affine pushforward); API guide in `Cohomology/Cech.lean`;
  finiteness over a Noetherian base for projective schemes (Serre), base change of Čech complexes, and the Mumford
  complex (perfect universal model, constant Euler characteristic, top-degree base change); the same over any
  valuation ring by coherence (`exists_mumfordComplex_valuation`), and vanishing above degree one from two affine
  hypersurface complements (`CurveCover`), which exist for projective curves over a local ring with infinite residue
  field (`CurveHypersurface`); quasi-coherence of pullbacks (`PullbackQcoh`); Stein finiteness over a valuation ring
  (`isFinite_fromNormalization_of_isRelativelyProjective`) and reducedness of the closed fibre (`Stein*`).
  `Cohomology.Connected*`: fibres of a projective flat scheme over a finite-height valuation ring are connected when the
  generic fibre is (Zariski, S-fibre form; `isConnected_fiber_of_isProjectiveOver`), and `h⁰ = 1` for the closed fibre.
  `Cohomology.ConnectedBirational*`: fibres of a projective birational map onto a normal curve over a valuation ring
  are connected (height one, or no generization of the point in the modification locus);
  `Cohomology.ConnectedBirationalHeight*`: the same in finite height for `B` projective over `V` with separably closed
  residue fraction fields (`isConnected_preimage_singleton_of_isProjectiveOver`).
* `StableModification.Flattening`: weak flattening after a generically étale alteration (Temkin §3.4 with P =
  flatness): proves `FlatteningAfterGEAlteration k`.
* `StableModification.Gluing`: the global semistable model over a finite-height valuation ring (PLAN-T5 §2.2):
  `Γ₀` is finite for every modification (`finite_gammaZeroSet_of_flat`, ERRATA T62), projective RZ refinements
  (`exists_projective_refinement`), the normalization `Nor(C′)`, the finite bad locus, local models and extension by
  the identity (`exists_nodal_modification`, with projective cofinality as the named hypothesis
  `ProjectiveCofinality`, proved by `Gluing.CofinalProjective.projectiveCofinality`: Temkin's Prop 4.3.1 with projective
  outputs, via native blow-ups of finite-type ideal sheaves; unconditional form
  `exists_nodal_modification_of_isAlgClosed`).
  `Gluing.Marks*` (lane T45B, partial): marks as sections and their lifts, semistable pairs from disjoint smooth
  sections, local marked models (named hypothesis `ProjectiveSeparation`), insertion with the identity piece.
  `Gluing.{MarksNodal,ExistenceVal}` (lane T45E): the marked nodal model and existence of stable modifications over
  valuation rings, `Gluing.ExistenceVal.valuationStableExistence` (from `ProjectiveSeparationAlgClosed` and
  `ClosureComponentLocal`); `Gluing.{SeparationProjective*,MarksSeparation}` (lane T45D): separation of marks with
  projectivity tracked (`exists_separation_marks_projective`) and the local marked model without a separation
  hypothesis (`exists_local_marked_model_of_piece`).
  `Gluing.Uniqueness*` (lane T45F): the join, normalization lifts, the bridge from numerical to combinatorial
  stability, and uniqueness over valuation rings `Gluing.UniquenessVal.valuationStableUniqueness` (from
  `ProjectiveSeparationAlgClosed`).
  `Gluing.{MarksNodalFinal,ExistenceValFinal,UniquenessValFinal}` (lane T45G): existence and uniqueness over valuation
  rings with no hypotheses (`Gluing.valuationStableExistence`, `Gluing.valuationStableUniqueness`), and
  `Gluing.deJongAlterationTheorem[_conn,_of_rational]`: de Jong's theorem from the spreading input and projectivity.
* `StableModification.Global`: the global assembly of Temkin's theorem (PLAN-T5 Layer 5): algebraic RZ refinements are
  alterations, spreading of stable models, comparison pieces, rigidity and gluing; `Global.temkinStableModification`
  proves `DeJong.TemkinStableModification k` and `Global.deJongAlterationTheorem` de Jong's theorem from the four named
  inputs `ValuationStableExistence`, `ValuationStableUniqueness`, `StableOpenNbhd k`, `StableModificationProjectivity k`.
  `Global.{StableOpen*,SpreadPieceConn*,MainConn}` (lane T51B): the corrected `StableOpenNbhdConn` (ERRATA DJA-O36), the
  consumer chain with it (`deJongAlterationTheorem_conn`), invariance of numerical stability under change of
  algebraically closed field, and the reduction to rational points of normal varieties (`StableOpenNbhdRational`,
  `deJongAlterationTheorem_of_rational`).
* `StableModification.Limits`: approximation over the system of finitely generated subalgebras of a valuation ring
  (Temkin 3.1, 3.2.2): descent of finitely presented objects, morphisms, isomorphisms, closed immersions,
  separatedness and étale algebras; descent of flatness along directed unions of Noetherian subalgebras (EGA IV
  11.2.6 as used by Temkin 3.1), with generic flatness and the local flatness criterion.
  `Limits.Spread*`: semistable pairs over the limit descend to a finite level (`exists_isSemistablePair_model`;
  flat, smooth and étale descent, purity of fibres); `Limits.SpreadModification*`: projective (η-)modifications with
  semistable source descend to a finite level (`exists_semistable_projective_etaModification`).
* `StableModification.Curves`: Temkin's notions (nodal fibres, η-modifications, exceptional components, stable
  modifications, the bridge to `HasStableModification`) and the standard smooth and node models; `Curves.SemistableOpen`:
  the nodal locus of a flat finitely presented curve is open and its image complement gives the nodal base (Temkin
  Lemma 5.1(i)); `Curves.SemistableNormal*`: the étale-local form `uv − c` of a node (Stacks 0CBY, Morse lemma in
  families) and normality of nodal curves with smooth generic fibre over an integral normal base
  (`isNormalScheme_of_isNodalCurve`).
-/
