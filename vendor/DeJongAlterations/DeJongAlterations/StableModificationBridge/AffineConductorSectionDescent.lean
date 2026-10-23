/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.StableModificationBridge.SchemeConductor
import DeJongAlterations.StableModificationBridge.NormalizationConductorDescent
import DeJongAlterations.StableModificationBridge.IdealPowerVanishing

/-!
# Affine intrinsic conductor membership produces actual original whole sections

Affine preimages of original trivializing opens suffice: native sheaf gluing supplies the
original entire coefficients, then the original line-bundle transition maps prove compatibility.

Blueprint: `affine-conductor-section-descent.tex`.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Limits
open DeJongAlterations.StableModification
open DeJongAlterations.StableModification.Projectivity
open DeJongAlterations.StableModification.Cohomology

namespace DeJongAlterations.StableModificationBridge.AffineConductorSectionDescent

noncomputable section

open LineBundleData IdealPowerVanishing

variable {X Y : Scheme.{u}}

theorem exists_preimage_of_affine_conductor (ν : Y ⟶ X) [QuasiCompact ν]
    [IsSchemeTheoreticallyDominant ν] (W : X.Opens) (b : Γ(Y, ν ⁻¹ᵁ W))
    (hcond : ∀ (U : X.affineOpens) (hU : U.1 ≤ W),
      letI := (ν.app U).hom.toAlgebra
      Y.presheaf.map (homOfLE (ν.preimage_mono hU)).op b ∈
        FiniteAlgebraConductor.ideal Γ(X, U) Γ(Y, ν ⁻¹ᵁ U.1)) :
    ∃ a : Γ(X, W), ν.app W a = b := by
  classical
  let J := {U : X.affineOpens // U.1 ≤ W}
  let V : J → X.Opens := fun U => U.1.1
  have hcov : W ≤ ⨆ j, V j := by
    intro x hx
    obtain ⟨U, hU, hxU, hUW⟩ := exists_isAffineOpen_mem_and_subset hx
    exact Opens.mem_iSup.mpr ⟨⟨⟨U, hU⟩, hUW⟩, hxU⟩
  have hcoeff : ∀ j : J, ∃ a : Γ(X, V j), ν.app (V j) a =
      Y.presheaf.map (homOfLE (ν.preimage_mono j.2)).op b := by
    intro j
    let := (ν.app j.1).hom.toAlgebra
    exact FiniteAlgebraConductor.exists_preimage_of_mem _ _ (hcond j.1 j.2)
  choose a ha using hcoeff
  let G : TopCat.Sheaf Ab X := ⟨(unitModule X).presheaf, (unitModule X).isSheaf⟩
  have hcompat : TopCat.Presheaf.IsCompatible G.1 V a := by
    intro j k
    apply ν.app_injective (V j ⊓ V k)
    change ν.app _ (X.presheaf.map (homOfLE inf_le_left).op (a j)) =
      ν.app _ (X.presheaf.map (homOfLE inf_le_right).op (a k))
    rw [app_res, app_res, ha j, ha k]
    exact (res_res _ _ (ν.preimage_mono (inf_le_left.trans j.2)) b).trans
      (res_res _ _ (ν.preimage_mono (inf_le_left.trans j.2)) b).symm
  obtain ⟨aW, haW, -⟩ := G.existsUnique_gluing' V W (fun j => homOfLE j.2) hcov a hcompat
  let aW' : Γ(X, W) := aW
  have haW' (j : J) : X.presheaf.map (homOfLE j.2).op aW' = a j := haW j
  refine ⟨aW', ?_⟩
  let H : TopCat.Sheaf Ab Y := ⟨(unitModule Y).presheaf, (unitModule Y).isSheaf⟩
  apply H.eq_of_locally_eq' (fun j => ν ⁻¹ᵁ V j) (ν ⁻¹ᵁ W)
    (fun j => homOfLE (ν.preimage_mono j.2))
  · intro y hy
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (hcov hy)
    exact Opens.mem_iSup.mpr ⟨j, hj⟩
  · intro j
    change res (ν.preimage_mono j.2) (ν.app W aW') = res (ν.preimage_mono j.2) b
    rw [← app_res ν j.2 aW', haW' j, ha j]

theorem existsUnique_descent_of_source_ideal (ν : Y ⟶ X) [IsFinite ν]
    [IsSchemeTheoreticallyDominant ν] (L : LineBundleData X) (m : ℤ)
    (t : (L.pullback ν).Sections m ⊤)
    (hcond : ∀ (U : X.affineOpens) (i : L.ι) (hU : U.1 ≤ L.U i),
      coefficientOnAffine t ⟨ν ⁻¹ᵁ U.1, U.2.preimage ν⟩ (ν.preimage_mono hU) ∈
        (SchemeConductor.sourceIdealSheaf ν).ideal ⟨ν ⁻¹ᵁ U.1, U.2.preimage ν⟩) :
    ∃! s : L.Sections m ⊤, s.pullback ν = t := by
  classical
  have hcoeff : ∀ i, ∃ a : Γ(X, ⊤ ⊓ L.U i), ν.app (⊤ ⊓ L.U i) a = t.coeff i := by
    intro i
    apply exists_preimage_of_affine_conductor ν (⊤ ⊓ L.U i) (t.coeff i)
    intro U hU
    let := (ν.app U).hom.toAlgebra
    have hc := hcond U i (hU.trans inf_le_right)
    rw [SchemeConductor.sourceIdealSheaf_ideal_preimage] at hc
    exact hc
  choose a ha using hcoeff
  have hcompat : ∀ i j, X.presheaf.map (homOfLE (L.le_left ⊤ i j)).op (a i) =
      L.transPow m ⊤ i j * X.presheaf.map (homOfLE (L.le_right ⊤ i j)).op (a j) := by
    intro i j
    apply ν.app_injective (⊤ ⊓ (L.U i ⊓ L.U j))
    rw [app_res, map_mul, app_res, ha i, ha j]
    have htrans : ν.app (⊤ ⊓ (L.U i ⊓ L.U j)) (L.transPow m ⊤ i j) =
        (L.pullback ν).transPow m ⊤ i j :=
      (L.pullback_trans_zpow m ν (inf_le_right : ⊤ ⊓ (L.U i ⊓ L.U j) ≤ L.U i ⊓ L.U j)).symm
    rw [htrans]
    exact t.coeff_compat i j
  let s : L.Sections m ⊤ := Sections.mk a hcompat
  have hs : s.pullback ν = t := by
    apply Sections.ext
    intro i
    exact ha i
  exact ⟨s, hs, fun s' hs' =>
    NormalizationConductorDescent.pullback_injective ν L m ⊤ (hs'.trans hs.symm)⟩

end

end DeJongAlterations.StableModificationBridge.AffineConductorSectionDescent
