/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.Geometry.BlowupProjectiveEmbeddingForms
import DeJongAlterations.StableModification.Resolution.GlobalFlat
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Actual flat pullback of entire finite ideal-sheaf intersections

The native affine coefficient maps and the existing genuine flat ideal-intersection theorem
produce the whole native ideal-sheaf equality.

Blueprint: `flat-ideal-sheaf-intersection.tex`.
-/

universe u

open AlgebraicGeometry CategoryTheory
open Scheme.IdealSheafData

namespace DeJongAlterations.Geometry.FlatIdealSheafIntersection

noncomputable section

theorem comap_iInf {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [IsAffineHom f]
    {ι : Type u} [Finite ι] (I : ι → Y.IdealSheafData) :
    (⨅ i, I i).comap f = ⨅ i, (I i).comap f := by
  classical
  let : Fintype ι := Fintype.ofFinite _
  let V (U : Y.affineOpens) : X.affineOpens := ⟨f ⁻¹ᵁ U.1, U.2.preimage f⟩
  apply ext_of_iSup_eq_top V
    (by change (⨆ U : Y.affineOpens, f ⁻¹ᵁ U.1) = ⊤
        rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top])
  intro U
  let φ := f.appLE U.1 (V U).1 le_rfl
  let : Algebra Γ(Y, U.1) Γ(X, (V U).1) := φ.hom.toAlgebra
  let : Module.Flat Γ(Y, U.1) Γ(X, (V U).1) := f.flat_appLE U.2 (V U).2 le_rfl
  rw [BlowupProjectiveEmbedding.ideal_comap_affine _ f (V U) U le_rfl]
  simp only [ideal_iInf, iInf_apply]
  have h := StableModification.Resolution.Global.map_finsetInf_of_flat
    (R := Γ(Y, U.1)) (S := Γ(X, (V U).1)) Finset.univ (fun i => (I i).ideal U)
  simpa only [Finset.inf_eq_iInf, Finset.mem_univ, iInf_true, RingHom.algebraMap_toAlgebra,
    BlowupProjectiveEmbedding.ideal_comap_affine _ f (V U) U le_rfl] using h

end

end DeJongAlterations.Geometry.FlatIdealSheafIntersection
