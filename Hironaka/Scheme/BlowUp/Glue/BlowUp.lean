/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.Defs
public import Hironaka.Scheme.BlowUp.Glue.Charts
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The blow-up of a scheme along an ideal sheaf: charts

The interface of the gluing `blowUpOf` restated for the blow-up `blowUp I` of a scheme `X` along
an ideal sheaf `I` [Sta, Tag 01OF]: its components
`blowUp.ι I U : affineBlowUp (I.ideal U) ⟶ blowUp I`, the pullback squares
`π⁻¹(U) ≅ affineBlowUp (I.ideal U)`, its affine charts `blowUp.chart I U a` with their base maps,
covering and overlaps, and properness of the blow-up map `IdealSheafData.blowUpπ I` for locally
Noetherian `X`. The exceptional ideal `I·𝒪_B = I.comap (blowUpπ I)`, the ideal sheaf of the
exceptional divisor `π⁻¹(Z)`, is `IdealSheafData.exceptionalDivisor I` (`BlowUp/Defs.lean`).
-/

@[expose] public section

namespace AlgebraicGeometry

open Scheme.IdealSheafData

open AlgebraicGeometry CategoryTheory

universe u

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The component `affineBlowUp (I.ideal U) ⟶ blowUp I` of the gluing, an open immersion with
image `π⁻¹(U)`. -/
noncomputable def Scheme.IdealSheafData.blowUp.ι (U : X.affineOpens) : affineBlowUp
    (I.ideal U) ⟶ blowUp I :=
  blowUpOf.ι I (affineBlowUpNatTrans_equifibered I) U

/-- **The global chart** of `a ∈ I(U)`, `Spec Γ(X, U)[I(U)/a] ⟶ blowUp I` [Sta, Tag 0804];
[Hau14, Theorem 4.19]. -/
noncomputable def Scheme.IdealSheafData.blowUp.chart (U : X.affineOpens) (a : I.ideal U) :
    Spec (.of (affineBlowUpAlgebra (I.ideal U) a)) ⟶ blowUp I :=
  blowUpOf.chart I (affineBlowUpNatTrans_equifibered I) U a

theorem Scheme.IdealSheafData.blowUp.chart_eq (U : X.affineOpens) (a : I.ideal U) :
    blowUp.chart I U a = affineBlowUp.chart (I.ideal U) a ≫ blowUp.ι I U :=
  rfl

instance Scheme.IdealSheafData.blowUp.isOpenImmersion_ι (U : X.affineOpens) : IsOpenImmersion
    (blowUp.ι I U) :=
  blowUpOf.isOpenImmersion_ι I _ U

instance Scheme.IdealSheafData.blowUp.isOpenImmersion_chart (U : X.affineOpens) (a : I.ideal U) :
    IsOpenImmersion (blowUp.chart I U a) :=
  blowUpOf.isOpenImmersion_chart I _ U a

/-- Over the base, the component `ι U` is `affineBlowUp.π` followed by `Spec Γ(X, U) ≅ U ⊆ X`
[Sta, Tag 01LH]. -/
theorem Scheme.IdealSheafData.blowUp.ι_π (U : X.affineOpens) :
    blowUp.ι I U ≫ blowUpπ I =
      (affineBlowUp.π (I.ideal U) ≫ (affineOpens_isAffineOpen U).isoSpec.inv) ≫ U.1.ι :=
  blowUpOf.ι_π I _ U

/-- Over every affine open `U`, `π⁻¹(U) ≅ affineBlowUp (I.ideal U)` as a pullback square
[Sta, Tag 0804]. -/
theorem Scheme.IdealSheafData.blowUp.isPullback_ι (U : X.affineOpens) :
    IsPullback (affineBlowUp.π (I.ideal U) ≫ (affineOpens_isAffineOpen U).isoSpec.inv)
      (blowUp.ι I U) U.1.ι (blowUpπ I) :=
  blowUpOf.isPullback I _ U

/-- The component `ι U` has image `π⁻¹(U)`. -/
theorem Scheme.IdealSheafData.blowUp.opensRange_ι (U : X.affineOpens) :
    (blowUp.ι I U).opensRange = blowUpπ I ⁻¹ᵁ U.1 :=
  blowUpOf.opensRange_ι I _ U

/-- Over the base, the global chart of `a` is `Spec (Γ(X, U) → Γ(X, U)[I(U)/a])` followed by
`Spec Γ(X, U) ≅ U ⊆ X` [Hau14, Theorem 4.19]. -/
theorem Scheme.IdealSheafData.blowUp.chart_π (U : X.affineOpens) (a : I.ideal U) :
    blowUp.chart I U a ≫ blowUpπ I =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (affineBlowUpAlgebra (I.ideal U) a))) ≫
        (affineOpens_isAffineOpen U).isoSpec.inv ≫ U.1.ι :=
  blowUpOf.chart_π I _ U a

/-- The global charts of `U` cover `π⁻¹(U)` [Sta, Tag 0804]. -/
theorem Scheme.IdealSheafData.blowUp.iSup_opensRange_chart (U : X.affineOpens) :
    ⨆ a : I.ideal U, (blowUp.chart I U a).opensRange = blowUpπ I ⁻¹ᵁ U.1 :=
  blowUpOf.iSup_opensRange_chart I _ U

/-- Chart overlaps: inside the global chart of `a` the chart of `b` is `D(b/a)`. -/
theorem Scheme.IdealSheafData.blowUp.chart_preimage_chart (U : X.affineOpens) (a b : I.ideal U) :
    blowUp.chart I U a ⁻¹ᵁ (blowUp.chart I U b).opensRange =
      PrimeSpectrum.basicOpen (affineBlowUpAlgebra.ratio (I.ideal U) a b) :=
  blowUpOf.chart_preimage_chart I _ U a b

/-- For `X` locally Noetherian the blow-up map is proper [Sta, Tag 02NS]. -/
theorem Scheme.IdealSheafData.blowUp.isProper_π [IsLocallyNoetherian X] : IsProper (blowUpπ I) :=
  blowUpOf.isProper_π I _

end AlgebraicGeometry
