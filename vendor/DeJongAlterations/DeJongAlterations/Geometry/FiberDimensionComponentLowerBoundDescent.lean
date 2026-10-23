import DeJongAlterations.Geometry.FiberDimensionGenericFinite
import DeJongAlterations.Geometry.FiberDimensionCurveComponents

/-!
# Actual quasi-finite point descent from a finite component projection

An actual surjective preimmersion induces homeomorphisms of actual fibers.
This descends quasi-finite points and applies on the open part of an actual
irreducible component of a topologically Noetherian scheme.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.Geometry.FiberDimensionComponentLowerBoundDescent

open FiberDimensionGenericFinite

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Z X S : Scheme.{u}}

/-- Actual isolated fiber points descend through the native fiber homeomorphism of a surjective preimmersion. -/
theorem quasiFiniteAt_of_surjective_preimmersion (i : Z ⟶ X)
    [IsPreimmersion i] [Surjective i] (f : X ⟶ S)
    [LocallyOfFiniteType f] [LocallyOfFiniteType (i ≫ f)] (z : Z)
    (hq : (i ≫ f).QuasiFiniteAt z) : f.QuasiFiniteAt (i z) := by
  let s := (i ≫ f) z
  let ψ := fiberProjection i f s
  have : IsPreimmersion ψ := by
    dsimp only [ψ, fiberProjection]
    infer_instance
  have : Surjective ψ := inferInstance
  have hh : IsHomeomorph ψ :=
    isHomeomorph_iff_isEmbedding_surjective.mpr ⟨ψ.isEmbedding, ψ.surjective⟩
  have hpoint : ψ ((i ≫ f).asFiber z) = f.asFiber (i z) := by
    apply (f.fiberι s).isEmbedding.injective
    dsimp only [ψ]
    rw [← Scheme.Hom.comp_apply, fiberProjection_fiberι]
    simp only [Scheme.Hom.comp_apply]
    exact (congrArg i ((i ≫ f).fiberι_asFiber z)).trans (f.fiberι_asFiber (i z)).symm
  apply Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr
  have hopen := hh.isOpenMap _ (Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mp hq)
  simpa only [Set.image_singleton, hpoint] using hopen

/-- Finiteness on an actual integral component implies quasi-finiteness at its original generic point. -/
theorem quasiFiniteAt_genericPoint_of_finite_component [NoetherianSpace X]
    (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (f : X ⟶ S) [LocallyOfFiniteType f] [IsFinite (i ≫ f)]
    (hcomp : Set.range i ∈ irreducibleComponents X) :
    f.QuasiFiniteAt (i (genericPoint Z)) := by
  obtain ⟨O, hO, hOne, hOsub⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hcomp
  let U : X.Opens := ⟨O, hO⟩
  have hrestr (z : (i ⁻¹ᵁ U).toScheme) :
      U.ι ((i ∣_ U) z) = i ((i ⁻¹ᵁ U).ι z) := by
    simpa only [Scheme.Hom.comp_apply] using
      congrArg (fun h : (i ⁻¹ᵁ U).toScheme ⟶ X => h z) (morphismRestrict_ι i U)
  have hpre : (i ⁻¹ᵁ U : Set Z).Nonempty := by
    obtain ⟨x, hx⟩ := hOne
    obtain ⟨z, hz⟩ := hOsub hx
    exact ⟨z, by change i z ∈ O; rw [hz]; exact hx⟩
  have hη : i (genericPoint Z) ∈ U :=
    ((genericPoint_spec Z).mem_open_set_iff (i ⁻¹ᵁ U).isOpen).mpr (by simpa using hpre)
  have : Surjective (i ∣_ U) := ⟨fun x => by
    obtain ⟨z, hz⟩ := hOsub x.property
    refine ⟨⟨z, ?_⟩, ?_⟩
    · change i z ∈ U
      simpa only [hz] using x.property
    · apply Subtype.ext
      exact (hrestr _).trans hz⟩
  let z : (i ⁻¹ᵁ U).toScheme := ⟨genericPoint Z, hη⟩
  have hw : (i ∣_ U) ≫ U.ι ≫ f = (i ⁻¹ᵁ U).ι ≫ (i ≫ f) := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
  have hq : ((i ∣_ U) ≫ U.ι ≫ f).QuasiFiniteAt z := by
    rw [hw]
    exact Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion.mpr
      ((i ≫ f).quasiFiniteAt (genericPoint Z))
  have hdesc := quasiFiniteAt_of_surjective_preimmersion (i ∣_ U) (U.ι ≫ f) z hq
  have hfull := Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion.mp hdesc
  rw [hrestr] at hfull
  change f.QuasiFiniteAt (i (genericPoint Z)) at hfull
  exact hfull

end DeJongAlterations.Geometry.FiberDimensionComponentLowerBoundDescent
