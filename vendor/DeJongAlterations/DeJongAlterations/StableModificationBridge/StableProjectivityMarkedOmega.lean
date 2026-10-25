/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.StableModificationBridge.StableMarkedComponentDegree
import DeJongAlterations.StableModificationBridge.StableOpenMarkedSupportCount
import DeJongAlterations.StableModificationBridge.StableFamilyResidueNoContraction
import DeJongAlterations.StableModificationBridge.OriginalCanonicalGoodSection
import DeJongAlterations.Geometry.ClosedFibreCanonicalDegree
import DeJongAlterations.Geometry.ClosedFibreCanonicalProjective
import DeJongAlterations.Geometry.CurveFibrationMarkedOpenSmooth

/-! ONE actual original marked dualizing bundle gives native closed-fibre positivity
and actual stable-modification projectivity, without auxiliary producers.
Blueprint: `stable-projectivity-marked-omega.tex`. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace DeJongAlterations.StableModificationBridge.StableProjectivityMarkedOmega
open StableModification StableModification.Projectivity Cohomology CurvesField
open StableProjectivityClosedFibres
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

/-- ONE original omega(D') bundle works on ALL actual CLOSED beta fibres,
with SAME native canonical normalizations/maps/coefficients. No positivity,
connectedness/no-contracted-clopen, good section or projectivity certificate input. -/
theorem stableClosedFibrePositiveLineBundle {k : Type u} [Field k] [IsAlgClosed k] :
    StableClosedFibrePositiveLineBundle k := by
  intro S pS hSvar _ hSp C g D hC hm hsm _ hgi S' _ hS'n ψ _ hψp C' β D' hst hn hloc
  let : IsVariety pS := hSvar
  let q := pullback.snd g ψ
  let f := β ≫ q
  let pY := q ≫ ψ ≫ pS
  have hY : IsProjectiveOver pY := isProjectiveOver_pullback_snd_comp hSp hC hψp
  let : IsProper pS := hSp.isProper
  let : IsProper (g ≫ pS) := hC.isProper
  let : IsProper g := IsProper.of_comp g pS
  let : IsProper q := inferInstance
  let : IsProper β := hst.toIsSchematicModification.toIsProper
  let : IsProper f := inferInstance
  let : IsProper (ψ ≫ pS) := hψp.isProper
  let : IsProper pY := hY.isProper
  let : IsLocallyNoetherian S' := LocallyOfFiniteType.isLocallyNoetherian (ψ ≫ pS)
  let : DeJong.IsNodalCurve f := hst.isSemistablePair.nodal
  let : IsSeparated (f ≫ ψ ≫ pS) := inferInstance
  let : IsAffineHom (pullback.diagonal (terminal.from C')) :=
    CurvesField.Ample.isAffineHom_diagonal_of_isSeparated (f ≫ ψ ≫ pS)
  have hψη : ψ (genericPoint S') = genericPoint S := genericPoint_map_of_isDominant ψ
  let : IsIso (Curves.fiberMap β q (genericPoint S')) := hst.isIso_fiberMap
  let : Smooth (q.fiberToSpecResidueField (genericPoint S')) :=
    Global.smooth_fiber_pullback_snd g hsm ψ hψη
  let : Smooth (f.fiberToSpecResidueField (genericPoint S')) := by
    change Smooth ((β ≫ q).fiberToSpecResidueField (genericPoint S'))
    rw [← Curves.fiberMap_fiberToSpecResidueField β q (genericPoint S')]
    infer_instance
  have hgen : ∀ x : C', f x = genericPoint S' → DeJong.IsSmoothAt f x := by
    intro x hx
    exact (DeJong.isSmoothAt_iff_mem_smoothLocus f x).mpr
      (Geometry.CurveFibrationMarkedOpen.genericFiber_le_smoothLocus f x hx)
  obtain ⟨E, hEi, hEs, L, ⟨e⟩⟩ := StableMarkedDualizingBundle.exists_markedDualizingBundle
    f hS'n hgen D' hst.isSemistablePair
  have hEi' : ∀ i, ∃ h : IsAffineOpen (E.U i),
      D'.ideal ⟨E.U i, h⟩ = Ideal.span {E.f i} := by
    intro i
    obtain ⟨h, _, hi⟩ := hEi i
    exact ⟨h, hi⟩
  refine ⟨L, ?_⟩
  intro y hy
  let a := Geometry.ClosedFibreComponent.basePoint q y
  let hpT := CurvesField.isProjectiveOver_fiber_of_locallyRelativelyProjective hloc y
  let : IsProper (β.fiberToSpecResidueField y) := hpT.isProper
  let : CompactSpace (β.fiber y) := Ample.compactSpace_of_quasiCompact (β.fiberToSpecResidueField y)
  let : IsAffineHom (pullback.diagonal (terminal.from (β.fiber y))) :=
    Ample.isAffineHom_diagonal_of_isSeparated (β.fiberToSpecResidueField y)
  let : CompactSpace (pullback (C := Scheme.{u}) f a) :=
    Ample.compactSpace_of_quasiCompact (pullback.snd f a)
  let : IsAffineHom (pullback.diagonal (terminal.from (pullback (C := Scheme.{u}) f a))) :=
    Ample.isAffineHom_diagonal_of_isSeparated (pullback.snd f a)
  change ∀ η ∈ genericPoints (β.fiber y), ¬ IsClosed ({η} : Set (β.fiber y)) → _
  intro η _ hηnc
  have : IsAlgClosed (IsLocalRing.ResidueField
      ((pullback (C := Scheme.{u}) g ψ).presheaf.stalk y)) :=
    isAlgClosed_residueField_of_isClosed pY y hy
  let v := Geometry.ClosedFibreComponent.fibreInTotalCurve β q y η
  have hv : v ∈ genericPoints (pullback (C := Scheme.{u}) f a) :=
    Geometry.ClosedFibreComponent.image_mem_genericPoints β q y
      (Omega.ComponentDegree.topologicalKrullDim_fibre_le_one f a) η hηnc
  have hN := Geometry.ClosedFibreComponent.isProjectiveOver_canonicalNormalization β q y hpT η
  have hno := noContractedClopen_stableFamily_residue pS hSp g D hC hm hsm hgi
    ψ hψp β D' hst hloc y
  obtain ⟨P, M, hP, hM, hdeg⟩ := StableMarkedComponentDegree.exists_lineBundle_component_degree
    f D' a v hv hN hS'n hgen hst.isSemistablePair E hEi' hEs L e
  have hpos := StableOpenMarkedSupportCount.marked_component_number_pos β q D' a
    (hn _ a) hno v hv (Geometry.ClosedFibreComponent.contracted_closure β q y η) hN P M hP hM
  change 0 < DualityScheme.eulerCharOf
      ((L.pullback (Genus.normalizationPointsMap ({η} : Set (β.fiber y)) ≫ β.fiberι y)).twist
        (unitModule (Genus.normalizationPoints ({η} : Set (β.fiber y)))) 1)
        (structureCoeff (Genus.normalizationPointsMap ({η} : Set (β.fiber y)) ≫
          β.fiberToSpecResidueField y)) -
      Genus.eulerChar (Genus.normalizationPoints ({η} : Set (β.fiber y)))
        (structureCoeff (Genus.normalizationPointsMap ({η} : Set (β.fiber y)) ≫
          β.fiberToSpecResidueField y))
  rw [Geometry.ClosedFibreComponent.canonicalNormalization_degree_eq β q y L η]
  rw [hdeg]
  exact hpos

/-- The actual stable-modification projectivity input, with BOTH genuine natural
producers proved and no external hsec/hpos or model certificate. -/
theorem stableModificationProjectivity {k : Type u} [Field k] [IsAlgClosed k] :
    Global.StableModificationProjectivity k :=
  stableModificationProjectivity_of_closedFibres
    OriginalCanonicalGoodSection.algClosedCurveGoodSection stableClosedFibrePositiveLineBundle

end DeJongAlterations.StableModificationBridge.StableProjectivityMarkedOmega
