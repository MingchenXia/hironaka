/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.StableModificationBridge.FiniteAlgebraConductor
import DeJongAlterations.StableModification.CurvesField.GenusReduced
import DeJongAlterations.StableModification.Projectivity.LineBundleTwist
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Actual normalization section descent from the intrinsic conductor

The full conductor ideal, equivalently the extension of the original cokernel annihilator,
produces original coefficients. Their compatibility is proved by the native injective structure
maps and the original transition/restriction triangles, giving an exact whole-section pullback
equality and uniqueness. The native reduced normalization supplies the required injectivity.

Construction and finite support of the intrinsic conductor as an ideal sheaf, and assembly of
positive-degree sections across components, remain separate producers.

Blueprint: `normalization-conductor-descent.tex`.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Limits
open DeJongAlterations.StableModification
open DeJongAlterations.StableModification.Projectivity

namespace DeJongAlterations.StableModificationBridge.NormalizationConductorDescent

noncomputable section

open Projectivity.LineBundleData

variable {X Y : Scheme.{u}}

theorem pullback_injective (ν : Y ⟶ X) [QuasiCompact ν] [IsSchemeTheoreticallyDominant ν]
    (L : LineBundleData X) (m : ℤ) (W : X.Opens) :
    Function.Injective (fun s : L.Sections m W => s.pullback ν) := by
  intro s s' h
  apply Sections.ext
  intro i
  apply ν.app_injective (W ⊓ L.U i)
  exact congrArg (fun z => z.coeff i) h

theorem existsUnique_descent_of_conductor (ν : Y ⟶ X) [QuasiCompact ν]
    [IsSchemeTheoreticallyDominant ν] (L : LineBundleData X) (m : ℤ) (W : X.Opens)
    (t : (L.pullback ν).Sections m (ν ⁻¹ᵁ W))
    (hcond : ∀ i,
      letI : Algebra Γ(X, W ⊓ L.U i) Γ(Y, ν ⁻¹ᵁ (W ⊓ L.U i)) := (ν.app _).hom.toAlgebra
      t.coeff i ∈ FiniteAlgebraConductor.ideal Γ(X, W ⊓ L.U i) Γ(Y, ν ⁻¹ᵁ (W ⊓ L.U i))) :
    ∃! s : L.Sections m W, s.pullback ν = t := by
  classical
  have hcoeff : ∀ i, ∃ a : Γ(X, W ⊓ L.U i), ν.app (W ⊓ L.U i) a = t.coeff i := by
    intro i
    let : Algebra Γ(X, W ⊓ L.U i) Γ(Y, ν ⁻¹ᵁ (W ⊓ L.U i)) := (ν.app _).hom.toAlgebra
    exact FiniteAlgebraConductor.exists_preimage_of_mem _ _ (hcond i)
  choose a ha using hcoeff
  have hcompat : ∀ i j, X.presheaf.map (homOfLE (L.le_left W i j)).op (a i) =
      L.transPow m W i j * X.presheaf.map (homOfLE (L.le_right W i j)).op (a j) := by
    intro i j
    apply ν.app_injective (W ⊓ (L.U i ⊓ L.U j))
    rw [app_res, map_mul, app_res, ha i, ha j]
    have htrans : ν.app (W ⊓ (L.U i ⊓ L.U j)) (L.transPow m W i j) =
        (L.pullback ν).transPow m (ν ⁻¹ᵁ W) i j :=
      (L.pullback_trans_zpow m ν (inf_le_right : W ⊓ (L.U i ⊓ L.U j) ≤ L.U i ⊓ L.U j)).symm
    rw [htrans]
    exact t.coeff_compat i j
  let s : L.Sections m W := Sections.mk a hcompat
  have hs : s.pullback ν = t := by
    apply Sections.ext
    intro i
    exact ha i
  exact ⟨s, hs, fun s' hs' => pullback_injective ν L m W (hs'.trans hs.symm)⟩

theorem existsUnique_descent_of_cokernel_annihilator (ν : Y ⟶ X) [QuasiCompact ν]
    [IsSchemeTheoreticallyDominant ν] (L : LineBundleData X) (m : ℤ) (W : X.Opens)
    (t : (L.pullback ν).Sections m (ν ⁻¹ᵁ W))
    (hcond : ∀ i,
      letI : Algebra Γ(X, W ⊓ L.U i) Γ(Y, ν ⁻¹ᵁ (W ⊓ L.U i)) := (ν.app _).hom.toAlgebra
      t.coeff i ∈ (FiniteAlgebraConductor.baseIdeal Γ(X, W ⊓ L.U i)
        Γ(Y, ν ⁻¹ᵁ (W ⊓ L.U i))).map (ν.app (W ⊓ L.U i)).hom) :
    ∃! s : L.Sections m W, s.pullback ν = t := by
  apply existsUnique_descent_of_conductor ν L m W t
  intro i
  let : Algebra Γ(X, W ⊓ L.U i) Γ(Y, ν ⁻¹ᵁ (W ⊓ L.U i)) := (ν.app _).hom.toAlgebra
  rw [← FiniteAlgebraConductor.map_baseIdeal_eq]
  exact hcond i

theorem isSchemeTheoreticallyDominant_normalizationPoints {K : Type u} [Field K]
    [IsReduced X] [IsAffineHom (pullback.diagonal (terminal.from X))]
    (p : X ⟶ Spec (.of K)) [LocallyOfFiniteType p] (S : Set X) [Finite S]
    (hS : S = genericPoints X) : IsSchemeTheoreticallyDominant (CurvesField.Genus.normalizationPointsMap S) := by
  have : IsFinite (CurvesField.Genus.normalizationPointsMap S) :=
    CurvesField.Genus.isFinite_normalizationPointsMap p
  constructor
  apply Scheme.IdealSheafData.ext
  funext U
  rw [Scheme.Hom.ker_apply]
  exact (RingHom.injective_iff_ker_eq_bot _).mp
    (CurvesField.Genus.normalizationPoints_app_injective hS U.1 U.2)

theorem existsUnique_normalizationPoints_descent {K : Type u} [Field K]
    [IsReduced X] [IsAffineHom (pullback.diagonal (terminal.from X))]
    (p : X ⟶ Spec (.of K)) [LocallyOfFiniteType p] (S : Set X) [Finite S]
    (hS : S = genericPoints X) (L : LineBundleData X) (m : ℤ) (W : X.Opens)
    (t : (L.pullback (CurvesField.Genus.normalizationPointsMap S)).Sections m
      ((CurvesField.Genus.normalizationPointsMap S) ⁻¹ᵁ W))
    (hcond : ∀ i,
      let ν := CurvesField.Genus.normalizationPointsMap S
      letI : Algebra Γ(X, W ⊓ L.U i) Γ(CurvesField.Genus.normalizationPoints S,
        ν ⁻¹ᵁ (W ⊓ L.U i)) := (ν.app _).hom.toAlgebra
      t.coeff i ∈ (FiniteAlgebraConductor.baseIdeal Γ(X, W ⊓ L.U i)
        Γ(CurvesField.Genus.normalizationPoints S, ν ⁻¹ᵁ (W ⊓ L.U i))).map (ν.app _).hom) :
    ∃! s : L.Sections m W, s.pullback (CurvesField.Genus.normalizationPointsMap S) = t := by
  have : IsFinite (CurvesField.Genus.normalizationPointsMap S) :=
    CurvesField.Genus.isFinite_normalizationPointsMap p
  have := isSchemeTheoreticallyDominant_normalizationPoints p S hS
  exact existsUnique_descent_of_cokernel_annihilator _ L m W t hcond

end

end DeJongAlterations.StableModificationBridge.NormalizationConductorDescent
