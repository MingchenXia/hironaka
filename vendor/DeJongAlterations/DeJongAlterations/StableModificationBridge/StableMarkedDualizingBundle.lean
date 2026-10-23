/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.StableModificationBridge.StableMarkedCartierLineBundle
import DeJongAlterations.StableModification.Projectivity.LineBundleOpsInvertible
import DeJongAlterations.StableModification.Omega.Invertible

/-! The original marked dualizing module and canonical map, with original
Cartier equations and coefficient identities. Blueprint:
`stable-marked-dualizing-bundle.tex`. -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.StableModificationBridge.StableMarkedDualizingBundle

open StableModification StableModification.Projectivity

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

/-- Refine the ORIGINAL free-generator and line-bundle covers. Every generator
is free on EVERY smaller open via the native coefficient equivalence. -/
def twistLocalGenerators {X : Scheme.{u}} {M : X.Modules}
    (G : LocalGenerators M) (L : LineBundleData X) (m : ℤ) :
    LocalGenerators (L.twist M m) where
  ι := G.ι × L.ι
  U i := G.U i.1 ⊓ L.U i.2
  iSup_eq_top := by
    apply top_unique
    intro x _
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (G.iSup_eq_top.symm ▸ (show x ∈ (⊤ : X.Opens) from trivial))
    obtain ⟨j, hj⟩ := L.exists_mem_U x
    exact Opens.mem_iSup.mpr ⟨(i, j), hi, hj⟩
  σ i := L.ofLocal M m inf_le_right
    (M.presheaf.map (homOfLE (inf_le_left : G.U i.1 ⊓ L.U i.2 ≤ G.U i.1)).op (G.σ i.1))
  free i := by
    intro V hV
    have he (r : Γ(X, V)) :
        L.toLocal M m (hV.trans inf_le_right)
          (r • (L.twist M m).presheaf.map (homOfLE hV).op
            (L.ofLocal M m inf_le_right
              (M.presheaf.map (homOfLE (inf_le_left : G.U i.1 ⊓ L.U i.2 ≤ G.U i.1)).op
                (G.σ i.1)))) =
        r • M.presheaf.map (homOfLE (hV.trans inf_le_left)).op (G.σ i.1) := by
      rw [L.toLocal_smul]
      change r • L.toLocal M m (hV.trans inf_le_right)
        (L.twistRestrict M m hV _) = _
      rw [L.toLocal_restrict M m
        (inf_le_right : G.U i.1 ⊓ L.U i.2 ≤ L.U i.2) hV, L.toLocal_ofLocal,
        Cohomology.presheaf_map_map M _ _ (hV.trans inf_le_left)]
    constructor
    · intro r s hrs
      apply (G.free i.1 V (hV.trans inf_le_left)).1
      exact (he r).symm.trans ((congrArg (L.toLocal M m (hV.trans inf_le_right)) hrs).trans (he s))
    · intro z
      obtain ⟨r, hr⟩ := (G.free i.1 V (hV.trans inf_le_left)).2
        (L.toLocal M m (hV.trans inf_le_right) z)
      refine ⟨r, (L.localEquiv M m (hV.trans inf_le_right)).injective ?_⟩
      exact (he r).trans hr

/-- Multiplication by the ACTUAL canonical section of the actual Cartier equations. -/
def markedTwistMap {X : Scheme.{u}} (E : LocalEquations X) (M : X.Modules) :
    M ⟶ E.toLineBundleData.twist M 1 :=
  E.toLineBundleData.toTwistZeroHom M ≫
    (by simpa only [add_zero] using
      (LineBundleData.smulTwistHom M E.canonicalSection 0))

/-- On every ORIGINAL chart and subopen, the whole actual map multiplies by
that SAME original Cartier equation. -/
theorem markedTwistMap_toLocal {X : Scheme.{u}} (E : LocalEquations X) (M : X.Modules)
    (i : E.ι) {W : X.Opens} (hW : W ≤ E.U i) (s : Γ(M, W)) :
    E.toLineBundleData.toLocal M 1 hW ((markedTwistMap E M).app W s) =
      res hW (E.f i) • s := by
  change M.presheaf.map (homOfLE (le_inf le_rfl hW)).op
    ((E.canonicalSection.restrict (le_top : W ≤ ⊤)).coeff i •
      M.presheaf.map (homOfLE (inf_le_left : W ⊓ E.U i ≤ W)).op s) = _
  rw [Scheme.Modules.map_smul, Cohomology.presheaf_map_map_self]
  congr 1
  change res (le_inf le_rfl hW) (res _ (res _ (E.f i))) = res hW (E.f i)
  rw [res_res_trans, res_res_trans]

/-- The original marking internally produces the ACTUAL marked dualizing module
and a genuine line-bundle representation, retaining its whole original ideal and support. -/
theorem exists_markedDualizingBundle {X S : Scheme.{u}} (f : X ⟶ S)
    [DeJong.IsNodalCurve f] [IsIntegral S] [IsLocallyNoetherian S]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (hS : IsNormalScheme S)
    (hgen : ∀ x : X, f x = genericPoint S → DeJong.IsSmoothAt f x)
    (D : X.IdealSheafData) (hD : DeJong.IsSemistablePair f D) :
    ∃ E : LocalEquations X,
      (∀ i, ∃ h : IsAffineOpen (E.U i), IsRegular (E.f i) ∧
        D.ideal ⟨E.U i, h⟩ = Ideal.span {E.f i}) ∧
      (∀ x : X, x ∈ E.canonicalSection.nonvanishingLocus ↔ x ∉ (D.support : Set X)) ∧
      ∃ L : LineBundleData X,
        Nonempty (L.twist (unitModule X) 1 ≅ E.toLineBundleData.twist (Omega.dualizingSheaf f) 1) := by
  obtain ⟨E, hE, hs⟩ := StableMarkedCartierLineBundle.exists_localEquations_of_isSemistablePair
    f hS hgen D hD
  let G := LocalGenerators.ofIsInvertibleModule
    (Omega.isInvertibleModule_dualizingSheaf_of_isNodalCurve f hS hgen)
  let H := twistLocalGenerators G E.toLineBundleData 1
  exact ⟨E, hE, hs, H.toLineBundleData, ⟨H.twistIso⟩⟩

end DeJongAlterations.StableModificationBridge.StableMarkedDualizingBundle
