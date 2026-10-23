import DeJongAlterations.Algebra.NodeFittingExternalStalkQuotient
import DeJongAlterations.Algebra.NodeFittingModuleFaithfullyFlat
import DeJongAlterations.Algebra.CompletionRegularityBasics
import DeJongAlterations.Geometry.NodeCompletedLocalGeometricChartCoherent
import DeJongAlterations.Geometry.NodeCompletedLocalGeometricChartPoint

/-! # ENTIRE ORIGINAL relative Fitting ideals at EVERY actual geometric-fibre stalk

The actual completed coherent differential comparison is constructed internally
from the original family. Faithfully flat completion reflects the whole ideals.
There is no node-model or differential/Fitting-comparison certificate input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct IsLocalRing

namespace DeJongAlterations.Algebra.NodeFittingOriginalGeometricStalk

open NodeFittingModule NodeFittingOmegaCharts NodeFittingIdealSheaf
  NodeFittingExternalStalkQuotient
  Geometry.NodeCompletedLocalGeometricChart
  Geometry.NodeCompletedLocalGeometricChartCompletion
  Geometry.NodeCompletedLocalGeometricChartCoherent
  Geometry.NodeCompletedLocalGeometricChartPoint
  NodeGeometricCompletionCoherentDifferentials

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 3000

universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
  (s : S) (K : Type u) [Field K] [Algebra (S.residueField s) K]

local notation "Y" => OriginalGeometricScheme f s K
local notation "π" => pullback.fst f (originalFieldMap s K)
local notation "q" => pullback.snd f (originalFieldMap s K)

local instance targetFieldAlgebra (y : Y) : Algebra K ((Y).presheaf.stalk y) :=
  Scheme.stalkAlgebra q y

/-- Native finite presentation of Ω at the SAME actual geometric point is internal and model-free. -/
theorem geometricStalkOmega_finitePresentation (y : Y) :
    Module.FinitePresentation ((Y).presheaf.stalk y)
      (KaehlerDifferential K ((Y).presheaf.stalk y)) := by
  let : IsNoetherianRing ((Y).presheaf.stalk y) :=
    Geometry.NodeCompletedLocalCoherentUV.stalk_isNoetherianRing q y
  let : Algebra.EssFiniteType K ((Y).presheaf.stalk y) :=
    Geometry.NodeCompletedLocalCoherentUV.stalkAlgebra_essFiniteType q y
  exact Module.finitePresentation_of_finite _ _

/-- The full ORIGINAL pulled ideal is the native field-relative differential Fitting ideal at this actual chart point. -/
theorem originalFittingStalkIdeal_eq_nativeOmega_at_chart (C : Chart f) (hs : s ∈ C.base.1)
    (z : ChartScheme f C s hs K) (i : ℕ) :
    letI := geometricStalkOmega_finitePresentation f s K (chartMap f C s hs K z)
    stalkIdeal ((NodeFittingOmegaGluing.idealSheaf f i).comap π) (chartMap f C s hs K z) =
      fittingIdeal (R := (Y).presheaf.stalk (chartMap f C s hs K z))
        (M := KaehlerDifferential K ((Y).presheaf.stalk (chartMap f C s hs K z))) i := by
  let y := chartMap f C s hs K z
  let R := (Y).presheaf.stalk y
  let H := (Y).completedLocalRing y
  let := C.algebra f
  let := C.differentialFinitePresentation f
  let := originalStalkAlgebra f C s hs K z
  let := originalCompletedAlgebra f C s hs K z
  let : IsNoetherianRing R := Geometry.NodeCompletedLocalCoherentUV.stalk_isNoetherianRing q y
  let : Algebra.EssFiniteType K R :=
    Geometry.NodeCompletedLocalCoherentUV.stalkAlgebra_essFiniteType q y
  let := geometricStalkOmega_finitePresentation f s K y
  let : Module.FaithfullyFlat R H := CompletionRegularityBasics.faithfullyFlat R
  let e : H ⊗[R] (R ⊗[Γ(X, C.source.1)]
      KaehlerDifferential Γ(S, C.base.1) Γ(X, C.source.1)) ≃ₗ[H]
      H ⊗[R] KaehlerDifferential K R :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange Γ(X, C.source.1) R H H
      (KaehlerDifferential Γ(S, C.base.1) Γ(X, C.source.1))).trans
      ((actualRelativeCoherentEquiv f C s hs K z).trans
        (completedOmegaTensorEquiv K R (maximalIdeal R)).symm)
  have hfit := fittingIdeal_eq_of_faithfullyFlat_baseChange H e i
  rw [pulledFittingStalkIdeal_eq_chart_image f π i C y (originalPoint_mem f C s hs K z)]
  change (C.ideal f i).map (algebraMap Γ(X, C.source.1) R) = _
  exact (fittingIdeal_baseChange (R := Γ(X, C.source.1))
    (M := KaehlerDifferential Γ(S, C.base.1) Γ(X, C.source.1)) R i).trans hfit

/-- EVERY SAME actual geometric point has the ENTIRE original ideal equality, with its chart chosen internally. -/
theorem originalFittingStalkIdeal_eq_nativeOmega (y : Y) (i : ℕ) :
    letI := geometricStalkOmega_finitePresentation f s K y
    stalkIdeal ((NodeFittingOmegaGluing.idealSheaf f i).comap π) y =
      fittingIdeal (R := (Y).presheaf.stalk y)
        (M := KaehlerDifferential K ((Y).presheaf.stalk y)) i := by
  obtain ⟨C, hs, z, rfl⟩ := exists_originalChartPoint f s K y
  exact originalFittingStalkIdeal_eq_nativeOmega_at_chart f s K C hs z i

end DeJongAlterations.Algebra.NodeFittingOriginalGeometricStalk
