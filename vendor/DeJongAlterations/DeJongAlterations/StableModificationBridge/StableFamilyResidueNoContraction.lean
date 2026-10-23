/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.StableModificationBridge.ClosedFibreNoContractedClopen
import DeJongAlterations.StableModification.Projectivity.Reduction

/-! # The actual original stable family supplies its residue-field noncontraction -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

namespace DeJongAlterations.StableModificationBridge

universe u

open StableModification

set_option backward.isDefEq.respectTransparency false

/-- Properness and the original dense isomorphism open give actual surjectivity. -/
theorem surjective_of_schematicModification {X Y : Scheme.{u}} [IsIntegral Y]
    (β : X ⟶ Y) (hβ : Curves.IsSchematicModification β) : Surjective β := by
  let : IsProper β := hβ.toIsProper
  obtain ⟨V, hV, _, hiso⟩ := hβ.exists_isIso
  let : IsSchemeTheoreticallyDominant V.ι := hV
  let : IsIso (β ∣_ V) := hiso
  have hηV : genericPoint Y ∈ V :=
    ((genericPoint_spec Y).mem_open_set_iff V.isOpen).mpr
      (by obtain ⟨v, hv⟩ := Curves.nonempty_of_isSchemeTheoreticallyDominant V
          exact ⟨v, trivial, hv⟩)
  have : IsDominant β := by
    apply DeJong.isDominant_of_genericPoint_mem_range
    obtain ⟨v, hv⟩ := (β ∣_ V).surjective ⟨_, hηV⟩
    refine ⟨(β ⁻¹ᵁ V).ι v, ?_⟩
    change ((β ⁻¹ᵁ V).ι ≫ β) v = _
    rw [← morphismRestrict_ι, Scheme.Hom.comp_apply, hv]
    rfl
  infer_instance

/-- Only nontriviality of the actual original topological target fibre is needed. -/
theorem noContractedClopen_residue_of_nontrivial_fibre {X Y S : Scheme.{u}}
    (β : X ⟶ Y) [Surjective β] (q : Y ⟶ S) (y : Y)
    [PreconnectedSpace
      (pullback (C := Scheme.{u}) (β ≫ q) (Y.fromSpecResidueField y ≫ q))]
    (hnt : (q ⁻¹' {q y}).Nontrivial) :
    Global.NoContractedClopen β q (Y.fromSpecResidueField y ≫ q) := by
  let a := Y.fromSpecResidueField y ≫ q
  let z : Spec (Y.residueField y) := IsLocalRing.closedPoint _
  obtain ⟨x₁, hx₁, x₂, hx₂, hne⟩ := hnt
  have ha : a z = q y := by
    simp [a]
  obtain ⟨w₁, hw₁, _⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := q) (g := a) x₁ z (hx₁.trans ha.symm)
  obtain ⟨w₂, hw₂, _⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := q) (g := a) x₂ z (hx₂.trans ha.symm)
  have hw : w₁ ≠ w₂ := fun h => hne (hw₁.symm.trans ((congrArg _ h).trans hw₂))
  have hs : Surjective (Curves.pullbackCompMap β q a) := by
    rw [Curves.pullbackCompMap_eq]
    infer_instance
  intro Z hZ hZne hsub
  have : Nonempty (pullback (C := Scheme.{u}) (β ≫ q) a) := ⟨hZne.some⟩
  have : ConnectedSpace (pullback (C := Scheme.{u}) (β ≫ q) a) := ⟨inferInstance⟩
  have hZu : Z = Set.univ := hZ.eq_univ hZne
  obtain ⟨v₁, hv₁⟩ := hs.surj w₁
  obtain ⟨v₂, hv₂⟩ := hs.surj w₂
  apply hw
  exact hsub ⟨v₁, hZu.symm ▸ Set.mem_univ v₁, hv₁⟩
    ⟨v₂, hZu.symm ▸ Set.mem_univ v₂, hv₂⟩

/-- Exact applicability to the original stable-modification family: all generic,
surjectivity, connectedness and nontriviality inputs are produced internally. -/
theorem noContractedClopen_stableFamily_residue {k : Type u} [Field k]
    {S C S' C' : Scheme.{u}} [IsIntegral S] [IsIntegral S']
    (pS : S ⟶ Spec (.of k)) (hSp : IsProjectiveOver pS)
    (g : C ⟶ S) (D : C.IdealSheafData) (hC : IsProjectiveOver (g ≫ pS))
    (hm : DeJong.IsMultipointedCurve g D)
    (hsm : Smooth (g.fiberToSpecResidueField (genericPoint S)))
    (hgi : GeometricallyIntegral (g.fiberToSpecResidueField (genericPoint S)))
    (ψ : S' ⟶ S) [IsAlteration ψ] (hψp : IsProjectiveOver (ψ ≫ pS))
    (β : C' ⟶ pullback (C := Scheme.{u}) g ψ) (D' : C'.IdealSheafData)
    (hst : Curves.IsStableModification β (pullback.snd g ψ)
      (D.comap (pullback.fst g ψ)) D')
    (hloc : Projectivity.LocallyRelativelyProjective (pullback.snd g ψ ≫ ψ ≫ pS) β)
    (y : pullback (C := Scheme.{u}) g ψ) :
    Global.NoContractedClopen β (pullback.snd g ψ)
      ((pullback (C := Scheme.{u}) g ψ).fromSpecResidueField y ≫ pullback.snd g ψ) := by
  let q := pullback.snd g ψ
  have hψη : ψ (genericPoint S') = genericPoint S := genericPoint_map_of_isDominant ψ
  let : Flat g := hm.flat
  let : LocallyOfFinitePresentation g := hm.locallyOfFinitePresentation
  let : IsIntegral (pullback (C := Scheme.{u}) g ψ) :=
    Global.isIntegral_pullback_of_generic g hgi ψ hψη
  let : IsProper pS := hSp.isProper
  let : IsProper (ψ ≫ pS) := hψp.isProper
  have hqproj : IsProjectiveOver (q ≫ ψ ≫ pS) :=
    Projectivity.isProjectiveOver_pullback_snd_comp hSp hC hψp
  let : IsProper (q ≫ ψ ≫ pS) := hqproj.isProper
  have hqrel : DeJong.IsRelativelyProjective (ψ ≫ pS) q :=
    Projectivity.isRelativelyProjective_of_isProjectiveOver (ψ ≫ pS) q hqproj
  have hqgi : GeometricallyIntegral (q.fiberToSpecResidueField (genericPoint S')) := by
    have h := hgi
    rw [← hψη] at h
    exact MorphismProperty.of_isPullback (P := @GeometricallyIntegral)
      (Global.isPullback_fiber_pullback_snd g ψ (genericPoint S')) h
  let : GeometricallyIntegral (q.fiberToSpecResidueField (genericPoint S')) := hqgi
  let : IsIntegral (q.fiber (genericPoint S')) :=
    GeometricallyIntegral.isIntegral_of_subsingleton
      (q.fiberToSpecResidueField (genericPoint S'))
  have : IsDominant q := by
    apply DeJong.isDominant_of_genericPoint_mem_range
    exact ⟨q.fiberι (genericPoint S') (Nonempty.some inferInstance), by
      have h := Scheme.Hom.range_fiberι q (genericPoint S')
      exact h.le ⟨_, rfl⟩⟩
  have hqgen := genericPoint_map_of_isDominant q
  let : Surjective β := surjective_of_schematicModification β hst.toIsSchematicModification
  let : DeJong.IsNodalCurve (β ≫ q) := hst.isSemistablePair.nodal
  let : IsIso (Curves.fiberMap β q (genericPoint S')) := hst.isIso_fiberMap
  let : Smooth (q.fiberToSpecResidueField (genericPoint S')) :=
    Global.smooth_fiber_pullback_snd g hsm ψ hψη
  have hsm' : Smooth ((β ≫ q).fiberToSpecResidueField (genericPoint S')) := by
    rw [← Curves.fiberMap_fiberToSpecResidueField β q (genericPoint S')]
    infer_instance
  have hgi' : GeometricallyIntegral ((β ≫ q).fiberToSpecResidueField (genericPoint S')) := by
    rw [← Curves.fiberMap_fiberToSpecResidueField β q (genericPoint S')]
    rw [MorphismProperty.cancel_left_of_respectsIso (P := @GeometricallyIntegral)]
    infer_instance
  obtain ⟨K, hK, hKa, ā, hā, _, hconn⟩ :=
    Projectivity.exists_geometricPoint_connected (ψ ≫ pS) q hqrel hqgen β hsm' hgi' hloc
      Projectivity.Valuation.valuationProjectivity y
  let : Field K := hK
  let : IsAlgClosed K := hKa
  let : PreconnectedSpace (pullback (C := Scheme.{u}) (β ≫ q) (ā ≫ q)) := hconn
  let := Geometry.ResidueFibre.preconnectedSpace_of_geometricPoint (β ≫ q) q y ā hā
  apply noContractedClopen_residue_of_nontrivial_fibre β q y
  exact Global.nontrivial_preimage_snd_of_hasPureFiberDimension hm.pureFibers ψ ⟨y, rfl⟩

end DeJongAlterations.StableModificationBridge
