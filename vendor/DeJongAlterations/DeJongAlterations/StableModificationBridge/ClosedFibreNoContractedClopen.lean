/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.Geometry.ResidueFibreConnected
import DeJongAlterations.Geometry.ClosedFibreCanonicalComponent
import DeJongAlterations.StableModification.Global.SpreadPieceConnFibre
import DeJongAlterations.StableModification.Projectivity.ValuationProj

/-! # No contracted clopen piece over the original residue-field point -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

namespace DeJongAlterations.StableModificationBridge

universe u

open StableModification

set_option backward.isDefEq.respectTransparency false

/-- Native surjectivity and pure relative dimension one exclude contraction on a
preconnected fibre at the unchanged original residue-field point. -/
theorem noContractedClopen_of_preconnected_residueFibre {X Y S : Scheme.{u}}
    (β : X ⟶ Y) [Surjective β] (q : Y ⟶ S)
    (hdim : DeJong.HasPureFiberDimension q 1) (y : Y)
    [PreconnectedSpace
      (pullback (C := Scheme.{u}) (β ≫ q) (Y.fromSpecResidueField y ≫ q))] :
    Global.NoContractedClopen β q (Y.fromSpecResidueField y ≫ q) := by
  let a := Y.fromSpecResidueField y ≫ q
  let z : Spec (Y.residueField y) := IsLocalRing.closedPoint _
  have hne : ((pullback.snd q a) ⁻¹' {z}).Nonempty := by
    refine ⟨Geometry.ClosedFibreComponent.residueSection q y z, ?_⟩
    change (Geometry.ClosedFibreComponent.residueSection q y ≫ pullback.snd q a) z = z
    simp [Geometry.ClosedFibreComponent.residueSection, a,
      Geometry.ClosedFibreComponent.basePoint]
  have hnt : (Set.univ : Set (pullback (C := Scheme.{u}) q a)).Nontrivial :=
    (Global.nontrivial_preimage_snd_of_hasPureFiberDimension hdim a hne).mono
      (Set.subset_univ _)
  have hs : Surjective (Curves.pullbackCompMap β q a) := by
    rw [Curves.pullbackCompMap_eq]
    infer_instance
  intro Z hZ hZne hsub
  have : Nonempty (pullback (C := Scheme.{u}) (β ≫ q) a) := ⟨hZne.some⟩
  have : ConnectedSpace (pullback (C := Scheme.{u}) (β ≫ q) a) := ⟨inferInstance⟩
  have hZu : Z = Set.univ := hZ.eq_univ hZne
  apply hnt.not_subsingleton
  rintro u _ v _
  obtain ⟨x, rfl⟩ := hs.surj u
  obtain ⟨w, rfl⟩ := hs.surj v
  exact hsub ⟨x, hZu.symm ▸ Set.mem_univ x, rfl⟩
    ⟨w, hZu.symm ▸ Set.mem_univ w, rfl⟩

section OriginalFamily

variable {k : Type u} [Field k] {S' Y X : Scheme.{u}} [IsIntegral S'] [IsIntegral Y]
  (pS' : S' ⟶ Spec (.of k)) (q : Y ⟶ S') [Flat q] [LocallyOfFinitePresentation q]
  [LocallyOfFiniteType (q ≫ pS')] (hq : DeJong.IsRelativelyProjective pS' q)
  (hqgen : q (genericPoint Y) = genericPoint S') (β : X ⟶ Y) [Surjective β]
  [DeJong.IsNodalCurve (β ≫ q)]
  (hsm : Smooth ((β ≫ q).fiberToSpecResidueField (genericPoint S')))
  (hgi : GeometricallyIntegral ((β ≫ q).fiberToSpecResidueField (genericPoint S')))
  (hloc : Projectivity.LocallyRelativelyProjective (q ≫ pS') β)

include hq hqgen hsm hgi hloc in
/-- The existing valuation-centre theorem produces the actual no-contracted-clopen
condition on the unchanged original residue-field fibre, without field descent input. -/
theorem noContractedClopen_residue_of_valuationProjectivity
    (hVal : Projectivity.ValuationProjectivity.{u})
    (hdim : DeJong.HasPureFiberDimension q 1) (y : Y) :
    Global.NoContractedClopen β q (Y.fromSpecResidueField y ≫ q) := by
  obtain ⟨K, hK, hKa, ā, hā, _, hconn⟩ :=
    Projectivity.exists_geometricPoint_connected pS' q hq hqgen β hsm hgi hloc hVal y
  let : Field K := hK
  let : IsAlgClosed K := hKa
  let : PreconnectedSpace (pullback (C := Scheme.{u}) (β ≫ q) (ā ≫ q)) := hconn
  let := Geometry.ResidueFibre.preconnectedSpace_of_geometricPoint (β ≫ q) q y ā hā
  exact noContractedClopen_of_preconnected_residueFibre β q hdim y

include hq hqgen hsm hgi hloc in
/-- The proved valuation projectivity theorem internally produces absence of
contracted clopen pieces over each unchanged original residue-field point. -/
theorem noContractedClopen_residue
    (hdim : DeJong.HasPureFiberDimension q 1) (y : Y) :
    Global.NoContractedClopen β q (Y.fromSpecResidueField y ≫ q) :=
  noContractedClopen_residue_of_valuationProjectivity pS' q hq hqgen β hsm hgi hloc
    Projectivity.Valuation.valuationProjectivity hdim y

end OriginalFamily

end DeJongAlterations.StableModificationBridge
