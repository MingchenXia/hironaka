/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.AffineBlowUp.Chart
public import Hironaka.Scheme.BlowUp.Glue.AffineBlowUpFunctor
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Hironaka.Scheme.BlowUp.AffineBlowUp.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Charts and properness of the glued blow-up

For the blow-up `blowUpOf I h` (glued from the affine blow-ups over the affine opens of `X`, given
the pullback squares `h`):

* the components `blowUpOf.ι I h U : affineBlowUp (I.ideal U) ⟶ blowUpOf I h` are open immersions
  with image `π⁻¹(U)` (Mathlib's `toBase_preimage_eq_opensRange_ι`);
* the **global charts** `blowUpOf.chart I h U a := affineBlowUp.chart (I.ideal U) a ≫ ι U`
  [Sta, Tag 0804]; [Hau14, Theorem 4.19]: open immersions, lying over
  `Spec (Γ(X, U) → Γ(X, U)[I(U)/a])` followed by `Spec Γ(X, U) ≅ U ⊆ X`, covering `π⁻¹(U)` as `a`
  runs through `I(U)`, and with the chart of `b` cut out of the chart of `a` by the basic open
  `D(b/a)` (from the affine statements of `Hironaka.Scheme.BlowUp.AffineBlowUp.Chart` and the local
  description `blowUpOf.isPullback`);
* **properness** of `blowUpOf.π I h` for `X` locally Noetherian [Sta, Tag 02NS]: `IsProper` is
  Zariski-local on the target, over each affine open `U` the blow-up map restricts to
  `affineBlowUp.π (I.ideal U)` up to the isomorphisms of the local description, and `I(U)` is
  finitely generated because `Γ(X, U)` is Noetherian (`affineBlowUp.isProper_π`).

The membership criterion of the charts is in `Hironaka.Scheme.BlowUp.Glue.GlobalCharts`, transported
from the affine criterion of the universal property.
-/

@[expose] public section

namespace AlgebraicGeometry

open AlgebraicGeometry CategoryTheory

universe u

variable {X : Scheme.{u}} (I : X.IdealSheafData) (h : (affineBlowUpNatTrans I).Equifibered)

/-- The components of the gluing are open immersions: `ι U` is the base change of the open
immersion `U ⊆ X` along `π` (the pullback square `blowUpOf.isPullback`). -/
instance blowUpOf.isOpenImmersion_ι (U : X.affineOpens) : IsOpenImmersion (blowUpOf.ι I h U) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (blowUpOf.isPullback I h U) inferInstance

/-- The component `ι U` has image `π⁻¹(U)` [Sta, Tag 0804] (Mathlib's
`toBase_preimage_eq_opensRange_ι`). -/
theorem blowUpOf.opensRange_ι (U : X.affineOpens) :
    (blowUpOf.ι I h U).opensRange = blowUpOf.π I h ⁻¹ᵁ U.1 := by
  have this : blowUpOf.π I h ⁻¹ᵁ (U.1.ι).opensRange = (blowUpOf.ι I h U).opensRange :=
    (relativeGluingDataOf I h).toBase_preimage_eq_opensRange_ι U
  rw [Scheme.Opens.opensRange_ι] at this
  exact this.symm

/-- **The global chart** of `a ∈ I(U)`, `Spec Γ(X, U)[I(U)/a] ⟶ blowUpOf I h`: the affine chart of
`affineBlowUp (I.ideal U)` followed by the component `ι U` [Sta, Tag 0804];
[Hau14, Theorem 4.19]. -/
noncomputable def blowUpOf.chart (U : X.affineOpens) (a : I.ideal U) :
    Spec (.of (affineBlowUpAlgebra (I.ideal U) a)) ⟶ blowUpOf I h :=
  affineBlowUp.chart (I.ideal U) a ≫ blowUpOf.ι I h U

/-- The global charts are open immersions (composites of open immersions). -/
instance blowUpOf.isOpenImmersion_chart (U : X.affineOpens) (a : I.ideal U) :
    IsOpenImmersion (blowUpOf.chart I h U a) := by
  unfold blowUpOf.chart
  infer_instance

/-- Over the base, the global chart of `a` is `Spec (Γ(X, U) → Γ(X, U)[I(U)/a])` followed by
`Spec Γ(X, U) ≅ U ⊆ X` [Hau14, Theorem 4.19] (from `affineBlowUp.chart_π` and `ι_toBase`). -/
theorem blowUpOf.chart_π (U : X.affineOpens) (a : I.ideal U) :
    blowUpOf.chart I h U a ≫ blowUpOf.π I h =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (affineBlowUpAlgebra (I.ideal U) a))) ≫
        (affineOpens_isAffineOpen U).isoSpec.inv ≫ U.1.ι := by
  unfold blowUpOf.chart
  rw [Category.assoc, blowUpOf.ι_π]
  simp only [Category.assoc]
  rw [← Category.assoc (affineBlowUp.chart (I.ideal U) a), affineBlowUp.chart_π]

/-- The global charts of `U` cover `π⁻¹(U)` [Sta, Tag 0804] (from
`affineBlowUp.iSup_opensRange_chart` and `blowUpOf.opensRange_ι`). -/
theorem blowUpOf.iSup_opensRange_chart (U : X.affineOpens) :
    ⨆ a : I.ideal U, (blowUpOf.chart I h U a).opensRange = blowUpOf.π I h ⁻¹ᵁ U.1 := by
  have h1 : ∀ a : I.ideal U, (blowUpOf.chart I h U a).opensRange =
      blowUpOf.ι I h U ''ᵁ (affineBlowUp.chart (I.ideal U) a).opensRange := fun a =>
    Scheme.Hom.opensRange_comp _ _
  simp_rw [h1]
  rw [← Scheme.Hom.image_iSup, affineBlowUp.iSup_opensRange_chart,
    Scheme.Hom.image_top_eq_opensRange, blowUpOf.opensRange_ι]

/-- Chart overlaps (from `affineBlowUp.chart_preimage_chart`): inside the global chart of `a` the
chart of `b` is the basic open `D(b/a)`. -/
theorem blowUpOf.chart_preimage_chart (U : X.affineOpens) (a b : I.ideal U) :
    blowUpOf.chart I h U a ⁻¹ᵁ (blowUpOf.chart I h U b).opensRange =
      PrimeSpectrum.basicOpen (affineBlowUpAlgebra.ratio (I.ideal U) a b) := by
  unfold blowUpOf.chart
  rw [Scheme.Hom.opensRange_comp, Scheme.Hom.comp_preimage, Scheme.Hom.preimage_image_eq,
    affineBlowUp.chart_preimage_chart]

/-- For `X` locally Noetherian the blow-up map is proper [Sta, Tag 02NS].  `IsProper` is
Zariski-local on the target; over an affine open `U` the restriction of `π` is, up to the
isomorphism `π⁻¹(U) ≅ affineBlowUp (I.ideal U)`, the blow-up map `affineBlowUp.π (I.ideal U)`
followed by `Spec Γ(X, U) ≅ U`, proper by `affineBlowUp.isProper_π` because `I(U)` is finitely
generated (`Γ(X, U)` is Noetherian). -/
theorem blowUpOf.isProper_π [IsLocallyNoetherian X] : IsProper (blowUpOf.π I h) := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsProper)
    (fun U : X.affineOpens => (U : X.Opens)) (iSup_affineOpens_eq_top X) fun U => ?_
  have sq := blowUpOf.isPullback I h U
  have he := (isPullback_morphismRestrict (blowUpOf.π I h) U.1).isoIsPullback_hom_fst _ _ sq
  rw [← he]
  have := IsLocallyNoetherian.component_noetherian U
  have h₁ : IsProper (affineBlowUp.π (I.ideal U)) :=
    affineBlowUp.isProper_π _ (IsNoetherian.noetherian _)
  infer_instance

end AlgebraicGeometry
