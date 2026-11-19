import Hironaka.Algebra.AffinePrimeDimension
import Hironaka.Geometry.CartierPureCodimension
import Hironaka.Geometry.RationalCoordinateMapGenericFiberOpenDimension

/-!
# The true dimension of each actual Cartier support component

The source is the genuine reduced vanishing-ideal closed subscheme of a
native support component. Cartier codimension computes its actual
affine prime height; the genuine finite-type field dimension formula
then computes the entire original component dimension.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Hironaka.Geometry.CartierBoundaryComponentDimension

open Scheme.IdealSheafData SpecIdealSheaf ReducedClosedSubscheme

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : Scheme.{u}}

/-- The actual reduced closed scheme of the original native support component. -/
def componentScheme (D : X.IdealSheafData) (C : DivisorComponent D) : Scheme.{u} :=
  (vanishingIdeal C.val).subscheme

/-- Its original native closed immersion into the ambient scheme. -/
def componentInclusion (D : X.IdealSheafData) (C : DivisorComponent D) : componentScheme D C ⟶ X :=
  (vanishingIdeal C.val).subschemeι

instance componentScheme_isIntegral (D : X.IdealSheafData) (C : DivisorComponent D) :
    IsIntegral (componentScheme D C) := by
  let : IsReduced (componentScheme D C) := isReduced_vanishingIdeal_subscheme C.val
  let : IrreducibleSpace (componentScheme D C) :=
    Subtype.irreducibleSpace (SNCLocality.divisorComponent_isIrreducible D C)
  exact isIntegral_of_irreducibleSpace_of_isReduced _

instance componentInclusion_isClosedImmersion (D : X.IdealSheafData) (C : DivisorComponent D) :
    IsClosedImmersion (componentInclusion D C) := by
  delta componentInclusion
  infer_instance

/-- Every nonempty actual affine component ideal is a genuine prime of height one. -/
theorem component_affine_height [IsIntegral X] [IsLocallyNoetherian X]
    (D : X.IdealSheafData) (hD : IsEffectiveCartierDivisor D)
    (C : DivisorComponent D) (U : X.affineOpens)
    (hmeet : ((C.val : Set X) ∩ Set.range U.2.fromSpec).Nonempty) :
    let I := (vanishingIdeal C.val).ideal U
    I.IsPrime ∧ I.height = 1 := by
  let A := Γ(X, U.1)
  let f := U.2.fromSpec
  let E := vanishingIdeal C.val
  let I := E.ideal U
  have hEI : E.comap f = specIdealSheaf A I := BlowupCartier.comap_fromSpec E U
  have hsupp : ((specIdealSheaf A I).support : Set (Spec A)) =
      f ⁻¹' (C.val : Set X) := by
    rw [← hEI, support_comap]
    rfl
  have hirr := SNCLocality.divisorComponent_isIrreducible D C
  have hirr' := hirr.preimage f.isOpenEmbedding hmeet
  have hrad : I.radical = I :=
    congrArg (fun E : X.IdealSheafData => E.ideal U) (radical_vanishingIdeal C.val)
  let : I.IsPrime :=
    (PrimeSpectrum.isIrreducible_zeroLocus_iff_of_radical I
      (Ideal.radical_eq_iff.mp hrad)).mp (by
        rw [← specIdealSheaf_support, hsupp]
        exact hirr')
  let q : Spec A := (⟨I, inferInstance⟩ : PrimeSpectrum A)
  have hq : IsGenericPoint q (f ⁻¹' (C.val : Set X)) := by
    exact (PrimeSpectrum.closure_singleton (⟨I, inferInstance⟩ : PrimeSpectrum A)).trans
      ((specIdealSheaf_support A I).symm.trans hsupp)
  have hfq : IsGenericPoint (f q) (C.val : Set X) := by
    have h := hq.image f.continuous
    have hcl := SNCLocality.componentRestrict_closure f D C hmeet
    change closure (f '' (f ⁻¹' (C.val : Set X))) = (C.val : Set X) at hcl
    rwa [hcl] at h
  obtain ⟨S, hS, hSC⟩ := C.property
  have hgeneric : IsGenericPoint (f q) ((Subtype.val : D.support → X) '' S) := hSC.symm ▸ hfq
  have hdim := CartierPureCodimension.hasPureCodimension D hD S hS (f q) hgeneric
  have hdim' : ringKrullDim ((Spec A).presheaf.stalk q) = 1 :=
    (ringKrullDim_eq_of_ringEquiv (asIso (f.stalkMap q)).commRingCatIsoToRingEquiv).symm.trans hdim
  have hheight : I.height = 1 := by
    rw [ringKrullDim_stalk_eq_coheight, ← idealHeight_eq_coheight] at hdim'
    exact_mod_cast hdim'
  exact ⟨inferInstance, hheight⟩

variable {k : Type u} [Field k]

/-- Every genuine Cartier component has exactly one less than its original finite-type dimension. -/
theorem component_dimension_add_one (p : X ⟶ Spec (.of k)) [IsVariety p]
    (D : X.IdealSheafData) (hD : IsEffectiveCartierDivisor D) (C : DivisorComponent D) :
    topologicalKrullDim (componentScheme D C) + 1 = topologicalKrullDim X := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let pC := componentInclusion D C ≫ p
  let : IsVariety pC := .mk
  obtain ⟨x, hxC⟩ := (SNCLocality.divisorComponent_isIrreducible D C).1
  obtain ⟨U, hUa, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (x := x) (U := (⊤ : X.Opens)) trivial
  let Ua : X.affineOpens := ⟨U, hUa⟩
  let : Nonempty U := ⟨⟨x, hxU⟩⟩
  have hmeet : ((C.val : Set X) ∩ Set.range hUa.fromSpec).Nonempty := by
    refine ⟨x, hxC, ?_⟩
    rwa [hUa.range_fromSpec]
  let I := (vanishingIdeal C.val).ideal Ua
  obtain ⟨hprime, hheight⟩ := component_affine_height D hD C Ua hmeet
  let : I.IsPrime := hprime
  let := RationalCoordinateMap.sectionAlgebra p Ua
  let : Algebra.FiniteType k Γ(X, U) := FunctionFieldDimension.affineSections_finiteType p Ua
  let : IsDomain Γ(X, U) := IsIntegral.component_integral U
  have hXdim : ringKrullDim Γ(X, U) = topologicalKrullDim X := by
    obtain ⟨d, hd, htr⟩ := FunctionFieldDimension.exists_dimension_and_trdeg p
    exact (FunctionFieldDimension.affineSections_dimension_eq p Ua d htr).trans hd.symm
  have hCdim : ringKrullDim (Γ(X, U) ⧸ I) = topologicalKrullDim (componentScheme D C) := by
    let : Nonempty (Spec ((vanishingIdeal C.val).subschemeCover.X Ua)) := by
      change Nonempty (PrimeSpectrum (Γ(X, U) ⧸ I))
      infer_instance
    have heq := FunctionFieldDimension.topologicalKrullDim_eq_of_openImmersion pC
      ((vanishingIdeal C.val).subschemeCover.f Ua)
    change topologicalKrullDim (PrimeSpectrum (Γ(X, U) ⧸ I)) = _ at heq
    rwa [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim] at heq
  have h := Algebra.AffinePrimeDimension.height_add_quotient_dimension k Γ(X, U) I
  rw [hheight, hCdim, hXdim] at h
  simpa only [WithBot.coe_one, add_comm] using h

end Hironaka.Geometry.CartierBoundaryComponentDimension
