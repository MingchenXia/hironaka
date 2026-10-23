import DeJongAlterations.StableModificationBridge.GeneratedSectionRatio
import DeJongAlterations.StableModification.Projectivity.LineBundleOpsIso
import DeJongAlterations.StableModification.Projectivity.LineBundleOpsHyperplane
import DeJongAlterations.StableModification.Cohomology.FiniteProjective

/-!
# The whole hyperplane comparison of the original generated section map

The original local coefficient ratios identify the native hyperplane cocycle with the original
line-bundle power cocycle. Every coefficient and restriction map remains the actual one.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Limits

namespace DeJongAlterations.StableModificationBridge.GeneratedSectionHyperplane

open StableModification.Projectivity Geometry.ProjectiveIdeal GeneratedSectionRatio

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {N : ℕ}

private theorem localValue_res {L : LineBundleData X} {m : ℤ} (t : L.Sections m ⊤)
    {V W : X.Opens} (hVW : V ≤ W) (k : L.ι) (hWk : W ≤ L.U k) :
    X.presheaf.map (homOfLE hVW).op (LineBundleData.localValue t k hWk) =
      LineBundleData.localValue t k (hVW.trans hWk) := by
  change res hVW (res (le_inf le_top hWk) (t.coeff k)) = _
  exact res_res _ _ _ _

/-- The actual native coordinates of the whole original projective space. -/
abbrev nativeCoordinates (R : Type u) [CommRing R] (N : ℕ) :=
  StableModification.Cohomology.ProjectiveCoordinates.ofClosedImmersion
    (𝟙 (projectiveSpace R N))

/-- The hyperplane datum of the original native projective coordinates. -/
abbrev nativeHyperplane (R : Type u) [CommRing R] (N : ℕ) :=
  LineBundleData.hyperplane (nativeCoordinates R N)

/-- The whole original coefficient-ratio identity holds on arbitrary opens, not only affine
ones. It is obtained by actual affine localization and equality in every original stalk. -/
theorem toProjectiveSpace_ratio_open {L : LineBundleData X} {m : ℤ}
    (p : X ⟶ Spec (.of R)) {s : Fin (N + 1) → L.Sections m ⊤}
    (hs : LineBundleData.Generates s) (W : X.Opens) (k : L.ι) (hWk : W ≤ L.U k)
    (i : Fin (N + 1)) (hWi : W ≤ (s i).nonvanishingLocus) (j : Fin (N + 1)) :
    (LineBundleData.toProjectiveSpace p hs).appLE (nativeCoordinateOpen i) W
        (by rw [LineBundleData.toProjectiveSpace_preimage_coordinate]; exact hWi)
        (nativeFormSection i (MvPolynomial.X j)) * LineBundleData.localValue (s i) k hWk =
      LineBundleData.localValue (s j) k hWk := by
  apply TopCat.Presheaf.section_ext X.sheaf W
  intro x hx
  obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset hx
  have H := toProjectiveSpace_ratio p hs ⟨V, hV⟩ k (hVW.trans hWk) i (hVW.trans hWi) j
  have Hres : X.presheaf.map (homOfLE hVW).op
      ((LineBundleData.toProjectiveSpace p hs).appLE (nativeCoordinateOpen i) W
        (by rw [LineBundleData.toProjectiveSpace_preimage_coordinate]; exact hWi)
        (nativeFormSection i (MvPolynomial.X j)) * LineBundleData.localValue (s i) k hWk) =
      X.presheaf.map (homOfLE hVW).op (LineBundleData.localValue (s j) k hWk) := by
    rw [map_mul]
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
    exact (congrArg (fun z : Γ(X, V) =>
      (LineBundleData.toProjectiveSpace p hs).appLE (nativeCoordinateOpen i) V
        (by rw [LineBundleData.toProjectiveSpace_preimage_coordinate]; exact hVW.trans hWi)
        (nativeFormSection i (MvPolynomial.X j)) * z)
          (localValue_res (s i) hVW k hWk)).trans
      (H.trans (localValue_res (s j) hVW k hWk).symm)
  have Hg := congrArg (X.presheaf.germ V x hxV) Hres
  exact (X.presheaf.germ_res_apply (homOfLE hVW) x hxV _).symm.trans
    (Hg.trans (X.presheaf.germ_res_apply (homOfLE hVW) x hxV _))

/-- The entire transition of the actual pulled-back native hyperplane bundle is the original
coordinate-section pullback. -/
theorem nativeHyperplane_pullback_trans (g : X ⟶ projectiveSpace R N)
    (a b : ULift.{u} (Fin (N + 1))) {W : X.Opens}
    (hW : W ≤ ((nativeHyperplane R N).pullback g).U a ⊓
      ((nativeHyperplane R N).pullback g).U b) :
    (((nativeHyperplane R N).pullback g).trans hW : Γ(X, W)) =
      g.appLE (nativeCoordinateOpen a.down) W (hW.trans inf_le_left)
        (nativeFormSection a.down (MvPolynomial.X b.down)) := by
  rw [LineBundleData.coe_trans, LineBundleData.coe_pullback_u]
  change X.presheaf.map (homOfLE hW).op
    (g.app ((nativeHyperplane R N).U a ⊓ (nativeHyperplane R N).U b)
      (LineBundleData.ratioRes (nativeCoordinates R N) a b)) = _
  have hr : (nativeCoordinates R N).ratio a b =
      nativeFormSection a.down (MvPolynomial.X b.down) := by
    change Scheme.Hom.app (𝟙 (projectiveSpace R N)) (nativeCoordinateOpen a.down) _ = _
    rfl
  rw [LineBundleData.ratioRes, hr]
  have hW' : W ≤ g ⁻¹ᵁ ((nativeHyperplane R N).U a ⊓ (nativeHyperplane R N).U b) := by
    change W ≤ g ⁻¹ᵁ ((nativeHyperplane R N).U a) ⊓
      g ⁻¹ᵁ ((nativeHyperplane R N).U b)
    exact hW
  change (g.appLE _ W hW')
    ((projectiveSpace R N).presheaf.map (homOfLE inf_le_left).op _) = _
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  rfl

end DeJongAlterations.StableModificationBridge.GeneratedSectionHyperplane
