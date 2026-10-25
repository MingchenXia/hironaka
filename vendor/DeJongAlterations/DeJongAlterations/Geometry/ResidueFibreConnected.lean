/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.StableModification.Projectivity.ConnectedFibre

/-! # Connectedness at the same original residue-field point -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology

namespace DeJongAlterations.Geometry.ResidueFibre

universe u

set_option backward.isDefEq.respectTransparency false

/-- The original map from a field spectrum factors through its actual image residue field. -/
theorem exists_residueFactorization {Y : Scheme.{u}} {K : Type u} [Field K]
    (ā : Spec (.of K) ⟶ Y) (y : Y) (hy : ∀ z, ā z = y) :
    ∃ ι : Y.residueField y ⟶ .of K,
      Spec.map ι ≫ Y.fromSpecResidueField y = ā := by
  have h := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Y ā
  have he := hy (IsLocalRing.closedPoint K)
  subst y
  exact ⟨_, h⟩

/-- Preconnectedness of the original field extension fibre descends to the same residue fibre. -/
theorem preconnectedSpace_of_geometricPoint {X Y S : Scheme.{u}}
    (f : X ⟶ S) (q : Y ⟶ S) (y : Y) {K : Type u} [Field K]
    (ā : Spec (.of K) ⟶ Y) (hy : ∀ z, ā z = y)
    [PreconnectedSpace (pullback (C := Scheme.{u}) f (ā ≫ q))] :
    PreconnectedSpace
      (pullback (C := Scheme.{u}) f (Y.fromSpecResidueField y ≫ q)) := by
  obtain ⟨ι, hι⟩ := exists_residueFactorization ā y hy
  let a := Y.fromSpecResidueField y ≫ q
  have he : Spec.map ι ≫ a = ā ≫ q := by
    dsimp [a]
    rw [← Category.assoc, hι]
  have : PreconnectedSpace (pullback (C := Scheme.{u}) f (Spec.map ι ≫ a)) := by
    rw [he]
    infer_instance
  have : Surjective (Spec.map ι) :=
    ⟨fun x => ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
  let e := pullbackLeftPullbackSndIso f a (Spec.map ι)
  have : PreconnectedSpace
      (pullback (C := Scheme.{u}) (pullback.snd f a) (Spec.map ι)) :=
    StableModification.Projectivity.preconnectedSpace_of_surjective
      (Scheme.homeoOfIso e.symm).continuous (Scheme.homeoOfIso e.symm).surjective
  exact StableModification.Projectivity.preconnectedSpace_of_surjective
    (pullback.fst (pullback.snd f a) (Spec.map ι)).continuous
    (fun x => Surjective.surj x)

end DeJongAlterations.Geometry.ResidueFibre
