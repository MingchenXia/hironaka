import DeJongAlterations.StableModificationBridge.GeneratedSectionHyperplane
import DeJongAlterations.StableModificationBridge.LineBundlePowerComparison
import DeJongAlterations.Geometry.LineBundleNativePullback

/-!
# Whole original line-bundle/hyperplane comparison

The comparison units and their cocycle are produced from the actual generating sections and
the entire original coefficient-ratio identities. No isomorphism certificate is supplied.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace DeJongAlterations.StableModificationBridge.GeneratedSectionBundleIso

open StableModification.Projectivity Geometry.ProjectiveIdeal
  GeneratedSectionHyperplane LineBundlePowerComparison

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {N : ℕ}
  {L : LineBundleData X} {m : ℤ} (p : X ⟶ Spec (.of R))
  {s : Fin (N + 1) → L.Sections m ⊤} (hs : LineBundleData.Generates s)

/-- The native hyperplane datum pulled back along the actual original section map. -/
abbrev generatedHyperplane :=
  (nativeHyperplane R N).pullback (LineBundleData.toProjectiveSpace p hs)

/-- The original section coefficient is a whole-ring unit on its genuine nonvanishing chart. -/
def comparisonUnit (k : L.ι) (a : ULift.{u} (Fin (N + 1))) :
    Γ(X, L.U k ⊓ (generatedHyperplane p hs).U a)ˣ :=
  (isUnit_of_basicOpen_eq
    (f := LineBundleData.localValue (s a.down) k inf_le_left) (by
    rw [LineBundleData.basicOpen_localValue]
    apply inf_eq_left.mpr
    change L.U k ⊓ (LineBundleData.toProjectiveSpace p hs ⁻¹ᵁ nativeCoordinateOpen a.down) ≤
      (s a.down).nonvanishingLocus
    rw [LineBundleData.toProjectiveSpace_preimage_coordinate]
    exact inf_le_right)).unit

/-- Comparison units have the original whole section coefficients as values. -/
theorem comparisonUnit_val (k : L.ι) (a : ULift.{u} (Fin (N + 1))) :
    (comparisonUnit p hs k a : Γ(X, L.U k ⊓ (generatedHyperplane p hs).U a)) =
      LineBundleData.localValue (s a.down) k inf_le_left := by
  exact IsUnit.unit_spec _

/-- Restriction of the comparison unit is restriction of that same original coefficient. -/
theorem comparisonUnit_restrict (k : L.ι) (a : ULift.{u} (Fin (N + 1))) {W : X.Opens}
    (hW : W ≤ L.U k ⊓ (generatedHyperplane p hs).U a) :
    X.presheaf.map (homOfLE hW).op (comparisonUnit p hs k a : Γ(X, _)) =
      LineBundleData.localValue (s a.down) k (hW.trans inf_le_left) := by
  rw [comparisonUnit_val, LineBundleData.localValue, LineBundleData.localValue,
    LineBundleData.ringMap_map]

/-- The actual comparison units satisfy the original comparison cocycle on every overlap. -/
theorem comparisonUnit_compat (i j : L.ι) (a b : ULift.{u} (Fin (N + 1)))
    {W : X.Opens} (hWi : W ≤ L.U i) (hWj : W ≤ L.U j)
    (hWa : W ≤ (generatedHyperplane p hs).U a)
    (hWb : W ≤ (generatedHyperplane p hs).U b) :
    (generatedHyperplane p hs).trans (le_inf hWa hWb) *
      LineBundleData.resUnit (le_inf hWi hWa) (comparisonUnit p hs i a) =
    (L.pow m).trans (le_inf hWi hWj) *
      LineBundleData.resUnit (le_inf hWj hWb) (comparisonUnit p hs j b) := by
  have hWa' : W ≤ (s a.down).nonvanishingLocus := by
    rw [← LineBundleData.toProjectiveSpace_preimage_coordinate p hs a.down]
    exact hWa
  apply Units.ext
  change ((generatedHyperplane p hs).trans (le_inf hWa hWb) : Γ(X, W)) *
      X.presheaf.map (homOfLE (le_inf hWi hWa)).op
        (comparisonUnit p hs i a : Γ(X, _)) =
    ((L.pow m).trans (le_inf hWi hWj) : Γ(X, W)) *
      X.presheaf.map (homOfLE (le_inf hWj hWb)).op
        (comparisonUnit p hs j b : Γ(X, _))
  rw [comparisonUnit_restrict p hs i a (le_inf hWi hWa),
    comparisonUnit_restrict p hs j b (le_inf hWj hWb),
    nativeHyperplane_pullback_trans (LineBundleData.toProjectiveSpace p hs) a b
      (le_inf hWa hWb), LineBundleData.pow_trans]
  exact (toProjectiveSpace_ratio_open p hs W i hWi a.down hWa' b.down).trans
    (LineBundleData.localValue_transition (s b.down) j i hWj hWi)

/-- The original section coefficients internally give the whole hyperplane comparison
cocycle. The source is the same original line-bundle power. -/
def generatedIsoData : LineBundleData.IsoData (L.pow m) (generatedHyperplane p hs) where
  w k a := comparisonUnit p hs k a
  compat i j a b {W} hW :=
    comparisonUnit_compat p hs i j a b (W := W)
      ((hW.trans inf_le_left).trans inf_le_left)
      ((hW.trans inf_le_right).trans inf_le_left)
      ((hW.trans inf_le_left).trans inf_le_right)
      ((hW.trans inf_le_right).trans inf_le_right)

/-- The entire original positive or negative power module is the entire native hyperplane
pullback module of the actual generated section map. -/
def generatedPowerHyperplaneIso :
    L.twist (unitModule X) m ≅ (generatedHyperplane p hs).twist (unitModule X) 1 :=
  (powerTwistIso L (unitModule X) m).symm ≪≫
    (generatedIsoData p hs).twistIso (unitModule X) 1

/-- The same whole comparison with Mathlib's actual module pullback functor. -/
def generatedNativeHyperplaneIso :
    L.twist (unitModule X) m ≅
      (Scheme.Modules.pullback (LineBundleData.toProjectiveSpace p hs)).obj
        ((nativeHyperplane R N).twist (unitModule (projectiveSpace R N)) 1) :=
  generatedPowerHyperplaneIso p hs ≪≫
    (LineBundleData.nativePullbackTwistIso (nativeHyperplane R N) 1
      (LineBundleData.toProjectiveSpace p hs)).symm

end DeJongAlterations.StableModificationBridge.GeneratedSectionBundleIso
