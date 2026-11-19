import Hironaka.Geometry.CurveFibrationBaseChangeSmooth
import Mathlib.AlgebraicGeometry.Stalk

/-!
# Generic geometric integrality from the original connected smooth fibres

Actual domain stalks force native components to be disjoint. Connected
Noetherian smooth field schemes are therefore integral, and proper
geometrically connected smooth field schemes are geometrically integral.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hironaka.Geometry.CurveFibrationBaseChange

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Two native components through one point coincide when actual stalks are domains. -/
theorem component_eq_of_domain_stalks (T : Scheme.{u})
    (hdom : ∀ x : T, IsDomain (T.presheaf.stalk x))
    (C D : Set T) (hC : C ∈ irreducibleComponents T) (hD : D ∈ irreducibleComponents T)
    (x : T) (hxC : x ∈ C) (hxD : x ∈ D) : C = D := by
  let : IsDomain (T.presheaf.stalk x) := hdom x
  have hr : IsIrreducible (Set.range (T.fromSpecStalk x)) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (Spec (T.presheaf.stalk x))).image
        (T.fromSpecStalk x) (T.fromSpecStalk x).continuous.continuousOn
  obtain ⟨E, hE, hrE⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ hr
  have hCE : C ⊆ E := by
    have hη := hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents C hC)
    have hηr : hC.1.genericPoint ∈ Set.range (T.fromSpecStalk x) := by
      rw [Scheme.range_fromSpecStalk]
      exact hη.specializes hxC
    rw [← hη.def]
    exact closure_minimal (Set.singleton_subset_iff.mpr (hrE hηr))
      (isClosed_of_mem_irreducibleComponents E hE)
  have hDE : D ⊆ E := by
    have hη := hD.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents D hD)
    have hηr : hD.1.genericPoint ∈ Set.range (T.fromSpecStalk x) := by
      rw [Scheme.range_fromSpecStalk]
      exact hη.specializes hxD
    rw [← hη.def]
    exact closure_minimal (Set.singleton_subset_iff.mpr (hrE hηr))
      (isClosed_of_mem_irreducibleComponents E hE)
  exact (hCE.antisymm (hC.2 hE.1 hCE)).trans (hDE.antisymm (hD.2 hE.1 hDE)).symm

/-- Connectedness and genuine domain stalks force whole irreducibility in a Noetherian scheme. -/
theorem irreducibleSpace_of_connected_domain_stalks (T : Scheme.{u})
    [NoetherianSpace T] [ConnectedSpace T]
    (hdom : ∀ x : T, IsDomain (T.presheaf.stalk x)) : IrreducibleSpace T := by
  let x : T := Classical.choice inferInstance
  let C := irreducibleComponent x
  have hC : C ∈ irreducibleComponents T := irreducibleComponent_mem_irreducibleComponents x
  have hcompl : Cᶜ = ⋃₀ (irreducibleComponents T \ {C}) := by
    ext y
    constructor
    · intro hy
      refine Set.mem_sUnion.mpr ⟨irreducibleComponent y, ⟨
        irreducibleComponent_mem_irreducibleComponents y, ?_⟩, mem_irreducibleComponent⟩
      intro h
      have he : irreducibleComponent y = C := Set.mem_singleton_iff.mp h
      exact hy (he ▸ mem_irreducibleComponent)
    · rintro ⟨D, ⟨hD, hDC⟩, hyD⟩ hyC
      exact hDC (Set.mem_singleton_iff.mpr
        (component_eq_of_domain_stalks T hdom D C hD hC y hyD hyC))
  have hclosed : IsClosed Cᶜ := by
    rw [hcompl, Set.sUnion_eq_biUnion]
    exact NoetherianSpace.finite_irreducibleComponents.sdiff.isClosed_biUnion
      (fun D hD => isClosed_of_mem_irreducibleComponents D hD.1)
  have hopen : IsOpen C := by simpa only [compl_compl] using hclosed.isOpen_compl
  have huniv : C = Set.univ :=
    (show IsClopen C from ⟨isClosed_of_mem_irreducibleComponents C hC, hopen⟩).eq_univ
      hC.1.nonempty
  apply (irreducibleSpace_def T).mpr
  change IsIrreducible (Set.univ : Set T)
  rw [← huniv]
  exact hC.1

/-- Connected Noetherian smooth field schemes are actually integral, by native component maximality. -/
theorem isIntegral_of_smooth_connected {K : Type u} [Field K] {T : Scheme.{u}}
    (p : T ⟶ Spec (.of K)) [Smooth p] [NoetherianSpace T] [ConnectedSpace T] :
    IsIntegral T := by
  have hreg : IsRegularScheme T := RegularSmooth.isRegularScheme_of_smooth p
  have hdom : ∀ x : T, IsDomain (T.presheaf.stalk x) := by
    intro x
    let : IsRegularLocalRing (T.presheaf.stalk x) := hreg x
    exact Hironaka.Algebra.RegularLocalDomain.isDomain_of_isRegularLocalRing _
  let : IrreducibleSpace T := irreducibleSpace_of_connected_domain_stalks T hdom
  let : IsReduced T := isReduced_of_smooth_field p
  exact isIntegral_of_irreducibleSpace_of_isReduced T

/-- Actual proper smooth geometrically connected field schemes are genuinely geometrically integral. -/
theorem geometricallyIntegral_of_proper_smooth_connected {K : Type u} [Field K]
    {T : Scheme.{u}} (p : T ⟶ Spec (.of K)) [IsProper p] [Smooth p]
    [GeometricallyConnected p] : GeometricallyIntegral p where
  geometrically_isIntegral := by
    intro L _ e Q a b h
    let : Smooth b := MorphismProperty.of_isPullback h inferInstance
    let : IsProper b := MorphismProperty.of_isPullback h inferInstance
    let : ConnectedSpace Q :=
      GeometricallyConnected.geometrically_connectedSpace e a b h
    let : IsLocallyNoetherian Q := LocallyOfFiniteType.isLocallyNoetherian b
    let : CompactSpace Q := QuasiCompact.compactSpace_of_compactSpace b
    let : AlgebraicGeometry.IsNoetherian Q := ⟨⟩
    exact isIntegral_of_smooth_connected b

/-- Paper generic smoothness and all-fibre geometric connectedness derive the SAME native generic GI. -/
theorem genericFiber_geometricallyIntegral_of_paper_fibres {X S : Scheme.{u}} [IsIntegral S]
    (f : X ⟶ S) [IsProper f] [GeometricallyConnected f]
    [Smooth (f.fiberToSpecResidueField (genericPoint S))] :
    GeometricallyIntegral (f.fiberToSpecResidueField (genericPoint S)) := by
  let : IsProper (f.fiberToSpecResidueField (genericPoint S)) := by
    change IsProper (pullback.snd f (S.fromSpecResidueField (genericPoint S)))
    infer_instance
  exact geometricallyIntegral_of_proper_smooth_connected _

end Hironaka.Geometry.CurveFibrationBaseChange
