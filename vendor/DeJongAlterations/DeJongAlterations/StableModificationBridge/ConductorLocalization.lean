/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.StableModificationBridge.LocalizedAnnihilator
import DeJongAlterations.StableModificationBridge.FiniteAlgebraConductor

/-!
# Intrinsic full conductors localize along the original finite-algebra diagram

The original structure-map cokernel is localized by the native `Genus.cokerMap`; its finite
annihilator and the entire intrinsic conductor therefore respect the same original ring maps.

Blueprint: `conductor-localization.tex`.
-/

universe u

open DeJongAlterations.StableModification

namespace DeJongAlterations.StableModificationBridge.ConductorLocalization

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  (A' B' : Type u) [CommRing A'] [CommRing B'] [Algebra A' B'] [Algebra A A']
  [Algebra B B'] [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B']
  (S : Submonoid A) [IsLocalization S A']
  [IsLocalization (Algebra.algebraMapSubmonoid B S) B']

include S

theorem baseIdeal_map_eq [Module.Finite A B] :
    (FiniteAlgebraConductor.baseIdeal A B).map (algebraMap A A') =
      FiniteAlgebraConductor.baseIdeal A' B' := by
  have : Module.Finite A (CurvesField.Genus.Coker A B) := inferInstance
  let : IsLocalizedModule S (CurvesField.Genus.cokerMap A' B' :
      CurvesField.Genus.Coker A B →ₗ[A] CurvesField.Genus.Coker A' B') :=
    CurvesField.Genus.isLocalizedModule_cokerMap_of_submonoid S
  exact LocalizedAnnihilator.map_annihilator_eq S A' (CurvesField.Genus.cokerMap A' B')

theorem ideal_map_eq [Module.Finite A B] :
    (FiniteAlgebraConductor.ideal A B).map (algebraMap B B') =
      FiniteAlgebraConductor.ideal A' B' := by
  calc
    (FiniteAlgebraConductor.ideal A B).map (algebraMap B B') =
        ((FiniteAlgebraConductor.baseIdeal A B).map (algebraMap A B)).map (algebraMap B B') := by
      rw [FiniteAlgebraConductor.map_baseIdeal_eq]
    _ = (FiniteAlgebraConductor.baseIdeal A B).map ((algebraMap B B').comp (algebraMap A B)) :=
      Ideal.map_map _ _
    _ = (FiniteAlgebraConductor.baseIdeal A B).map ((algebraMap A' B').comp (algebraMap A A')) := by
      congr 1
      ext a
      exact (IsScalarTower.algebraMap_apply A B B' a).symm.trans
        (IsScalarTower.algebraMap_apply A A' B' a)
    _ = ((FiniteAlgebraConductor.baseIdeal A B).map (algebraMap A A')).map (algebraMap A' B') :=
      (Ideal.map_map _ _).symm
    _ = (FiniteAlgebraConductor.baseIdeal A' B').map (algebraMap A' B') := by
      rw [baseIdeal_map_eq A' B' S]
    _ = FiniteAlgebraConductor.ideal A' B' := FiniteAlgebraConductor.map_baseIdeal_eq A' B'

end DeJongAlterations.StableModificationBridge.ConductorLocalization
