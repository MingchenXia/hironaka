import DeJongAlterations.StableModificationBridge.StableOpenNormalRational
import DeJongAlterations.StableModificationBridge.AlterationProjectivityClosed
import DeJongAlterations.Geometry.AlgebraicFieldAlterationReduction

/-! The native unconditional alteration theorem, over algebraically closed
and arbitrary fields. Blueprint: `sm-bridge-alteration-unconditional.tex`. -/

noncomputable section
universe u

namespace DeJongAlterations.StableModificationBridge.AlterationUnconditional

/-- The native alteration theorem over an algebraically closed field, with all
valuation, stable-open and projectivity inputs genuinely discharged. -/
theorem deJongAlterationTheorem_algClosed (k : Type u) [Field k] [IsAlgClosed k] :
    DeJongAlterationTheorem k :=
  StableModification.Global.deJongAlterationTheorem_conn_genericSmooth
    StableModification.Gluing.ExistenceValFinal.valuationStableExistence
    StableModification.Gluing.UniquenessValFinal.valuationStableUniqueness
    (StableOpenNormalRational.stableOpenNbhdConnGenericSmooth k)
    StableProjectivityMarkedOmega.stableModificationProjectivity

/-- The native alteration theorem over EVERY field, without perfectness,
geometric-integrality or mathematical producer assumptions. -/
theorem deJongAlterationTheorem (k : Type u) [Field k] : DeJongAlterationTheorem k :=
  Geometry.AlgebraicFieldAlterationReduction.deJongAlterationTheorem_of_algebraicClosure k
    (deJongAlterationTheorem_algClosed (AlgebraicClosure k))

end DeJongAlterations.StableModificationBridge.AlterationUnconditional
