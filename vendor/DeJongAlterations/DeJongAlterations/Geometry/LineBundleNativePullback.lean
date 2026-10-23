/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.Geometry.LineBundleIsoEuler
import DeJongAlterations.StableModification.Omega.RosenlichtComponentPullback
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-! # Native pullback of the same original compatible-family line-bundle twist -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace DeJongAlterations.StableModification.Projectivity.LineBundleData

universe u

open Cohomology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Scheme.{u}} (L : LineBundleData Y) (m : ℤ) (f : X ⟶ Y)

/-- The genuine native adjoint of the whole original compatible-family section map. -/
def nativePullbackTwistHom :
    (Scheme.Modules.pullback f).obj (L.twist (unitModule Y) m) ⟶
      (L.pullback f).twist (unitModule X) m :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
    (twistSectionsPullbackHom L m f)

/-- Every original section satisfies the exact native adjunction triangle on every subopen. -/
theorem nativePullbackTwistHom_app_pullbackSectionLE {W : Y.Opens} {V : X.Opens}
    (hVW : V ≤ f ⁻¹ᵁ W) (s : Γ(L.twist (unitModule Y) m, W)) :
    (nativePullbackTwistHom L m f).app V
        (pullbackSectionLE f (L.twist (unitModule Y) m) hVW s) =
      ((L.pullback f).twist (unitModule X) m).presheaf.map (homOfLE hVW).op
        ((twistSectionsPullbackHom L m f).app W s) := by
  rw [pullbackSectionLE_apply, Scheme.Modules.Hom.app_map]
  congr 1
  have h := (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_unit
    (L.twist (unitModule Y) m) ((L.pullback f).twist (unitModule X) m)
    (nativePullbackTwistHom L m f)
  rw [nativePullbackTwistHom, Equiv.apply_symm_apply] at h
  rw [h]
  rfl

/-- Native original affine base change and the same original coefficient `1` prove bijectivity. -/
theorem bijective_nativePullbackTwistHom_app {W : Y.Opens} (hW : IsAffineOpen W)
    {i : L.ι} (hWi : W ≤ L.U i) {V : X.Opens} (hV : IsAffineOpen V)
    (hVW : V ≤ f ⁻¹ᵁ W) :
    Function.Bijective ((nativePullbackTwistHom L m f).app V) := by
  let σ : Γ(L.twist (unitModule Y) m, W) := ofLocal (unitModule Y) m hWi (1 : Γ(Y, W))
  have hσ : Function.Bijective (fun r : Γ(Y, W) => r • σ) := by
    have he : (fun r : Γ(Y, W) => r • σ) =
        (localEquiv (unitModule Y) m (L := L) hWi).symm := by
      funext r
      apply (localEquiv (unitModule Y) m (L := L) hWi).injective
      simp [σ, localEquiv_apply, toLocal_ofLocal]
    rw [he]
    exact (localEquiv (unitModule Y) m (L := L) hWi).symm.bijective
  have hb := Omega.RosenlichtComponent.bijective_smul_pullbackSectionLE f
    (L.twist (unitModule Y) m) hW hV hVW σ hσ
  let E : Γ((L.pullback f).twist (unitModule X) m, V) ≃ₗ[Γ(X, V)] Γ(X, V) :=
    localEquiv (unitModule X) m (L := L.pullback f)
      (hVW.trans (f.preimage_mono hWi))
  have h1 : E ((nativePullbackTwistHom L m f).app V
      (pullbackSectionLE f (L.twist (unitModule Y) m) hVW σ)) = (1 : Γ(X, V)) := by
    rw [nativePullbackTwistHom_app_pullbackSectionLE]
    change toLocal (unitModule X) m (hVW.trans (f.preimage_mono hWi))
      ((L.pullback f).twistRestrict (unitModule X) m hVW
        (Sections.pullback f (L := L) (m := m) σ)) = (1 : Γ(X, V))
    rw [toLocal_restrict]
    have ht := toLocal_pullback L m f hWi (show L.Sections m W from σ)
    have ht' := congrArg ((unitModule X).presheaf.map (homOfLE hVW).op) ht
    refine ht'.trans ?_
    have hs : toLocal (unitModule Y) m hWi σ = (1 : Γ(Y, W)) :=
      toLocal_ofLocal (unitModule Y) m hWi (1 : Γ(Y, W))
    change X.presheaf.map (homOfLE hVW).op
      ((f.app W).hom (toLocal (unitModule Y) m hWi σ)) = (1 : Γ(X, V))
    rw [hs, map_one, map_one]
  have hscalar (r : Γ(X, V)) : E ((nativePullbackTwistHom L m f).app V
      (r • pullbackSectionLE f (L.twist (unitModule Y) m) hVW σ)) = r := by
    rw [Scheme.Modules.Hom.app_smul, map_smul, h1]
    exact mul_one r
  constructor
  · intro z₁ z₂ hz
    obtain ⟨r₁, rfl⟩ := hb.surjective z₁
    obtain ⟨r₂, rfl⟩ := hb.surjective z₂
    congr 1
    have h := congrArg E hz
    simpa only [hscalar] using h
  · intro z
    refine ⟨E z • pullbackSectionLE f (L.twist (unitModule Y) m) hVW σ, E.injective ?_⟩
    exact hscalar (E z)

/-- The original affine opens on which the actual whole pullback comparison has two free frames. -/
def nativePullbackTwistBasis :=
  {V : X.Opens // IsAffineOpen V ∧ ∃ (i : L.ι) (W : Y.Opens),
    IsAffineOpen W ∧ W ≤ L.U i ∧ V ≤ f ⁻¹ᵁ W}

/-- These are a genuine basis, internally obtained from the original trivializing charts. -/
theorem isBasis_nativePullbackTwistBasis :
    Opens.IsBasis (Set.range (fun V : nativePullbackTwistBasis L f => V.1)) := by
  rw [Opens.isBasis_iff_nbhd]
  intro U x hx
  have hfx : f x ∈ ⨆ i, L.U i := L.iSup_eq_top.symm ▸ trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hfx
  obtain ⟨W, hW, hfxW, hWi⟩ := exists_isAffineOpen_mem_and_subset (x := f x) (U := L.U i) hi
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset
    (x := x) (U := U ⊓ f ⁻¹ᵁ W) ⟨hx, hfxW⟩
  exact ⟨V, ⟨⟨V, hV, i, W, hW, hWi, hVU.trans inf_le_right⟩, rfl⟩,
    hxV, hVU.trans inf_le_left⟩

/-- Every actual native adjoint comparison is an isomorphism, for arbitrary schemes and maps. -/
instance isIso_nativePullbackTwistHom : IsIso (nativePullbackTwistHom L m f) := by
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf X.ringCatSheaf)]
  apply TopCat.Sheaf.isIso_iff_isIso_basis (isBasis_nativePullbackTwistBasis L f)
  intro V
  rw [ConcreteCategory.isIso_iff_bijective]
  obtain ⟨hV, i, W, hW, hWi, hVW⟩ := V.2
  exact bijective_nativePullbackTwistHom_app L m f hW hWi hV hVW

/-- The actual original native pullback and the original pulled-back transition data agree. -/
def nativePullbackTwistIso :
    (Scheme.Modules.pullback f).obj (L.twist (unitModule Y) m) ≅
      (L.pullback f).twist (unitModule X) m := asIso (nativePullbackTwistHom L m f)

end DeJongAlterations.StableModification.Projectivity.LineBundleData
