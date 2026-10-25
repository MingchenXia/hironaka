import DeJongAlterations.StableModificationBridge.StableOpenPolarizationPullback
import DeJongAlterations.Geometry.AffineHyperplanePositiveDegree

/-! SAME original affine polarization internally supplies the actual nearby normalized Euler degree. -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
noncomputable section
universe u

namespace DeJongAlterations.StableModificationBridge.StableOpenNearbyNormalizedDegree

open StableModification Projectivity Cohomology CurvesField CurvesField.Genus
open Omega.ComponentNormalization Omega.ComponentDegree

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- All actual normalized geometry and the whole power comparison are internally produced;
the actual target ring is retained while the original geometric K coefficient action is unchanged. -/
theorem degree_pos_of_original_affine_polarization {X C V : Scheme.{u}} [V.IsSeparated]
    (β : X ⟶ C) (q : C ⟶ V) [DeJong.IsNodalCurve (β ≫ q)]
    {K : Type u} [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ V)
    [CompactSpace (pullback (C := Scheme.{u}) (β ≫ q) a)]
    [IsAffineHom (pullback.diagonal (terminal.from (pullback (C := Scheme.{u}) (β ≫ q) a)))]
    (hp : IsProjectiveOver (pullback.snd (β ≫ q) a))
    (v : pullback (C := Scheme.{u}) (β ≫ q) a)
    (hv : v ∈ genericPoints (pullback (C := Scheme.{u}) (β ≫ q) a))
    (hcon : (Curves.pullbackCompMap β q a '' closure {v}).Subsingleton)
    (L : LineBundleData X) (W : C.Opens) (hW : β (pullback.fst (β ≫ q) a v) ∈ W)
    {R : Type u} [CommRing R] {P : Scheme.{u}} {c : R →+* Γ(P, ⊤)}
    (D : ProjectiveCoordinates P R c) (h : (β ⁻¹ᵁ W).toScheme ⟶ P) [IsAffineHom h]
    (m : ℕ) (hm : 0 < m)
    (e : (L.pullback (β ⁻¹ᵁ W).ι).twist (unitModule (β ⁻¹ᵁ W).toScheme) (m : ℤ) ≅
      ((LineBundleData.hyperplane D).pullback h).twist (unitModule (β ⁻¹ᵁ W).toScheme) 1) :
    0 < DualityScheme.eulerCharOf ((L.pullback (componentMap (β ≫ q) a v)).twist
      (unitModule (componentNormalization (β ≫ q) a v)) 1)
      (structureCoeff (componentStructure (β ≫ q) a v)) -
      eulerChar (componentNormalization (β ≫ q) a v)
        (structureCoeff (componentStructure (β ≫ q) a v)) := by
  let N := componentNormalization (β ≫ q) a v
  let π := normalizationPointsMap ({v} : Set (pullback (C := Scheme.{u}) (β ≫ q) a))
  let ν := componentMap (β ≫ q) a v
  have : IsFinite π := isFinite_normalizationPointsMap_singleton v (pullback.snd (β ≫ q) a)
  let : CompactSpace N := compactSpace_of_isAffineHom π
  let : IsAffineHom (pullback.diagonal (terminal.from N)) :=
    isAffineHom_diagonal_of_isAffineHom π
  obtain ⟨b, hb, hba⟩ := StableOpenPolarizationPullback.exists_affine_normalization_lift
    β q a v hcon W hW
  let : IsAffineHom b := hba
  have hN := isProjectiveOver_normalizationPoints v (pullback.snd (β ≫ q) a) hp
  have hdim := topologicalKrullDim_normalizationPoints_le v (pullback.snd (β ≫ q) a)
    (topologicalKrullDim_fibre_le_one (β ≫ q) a)
  have hη : ¬ IsClosed ({genericPoint N} : Set N) := by
    intro hc
    have hi := π.isClosedMap _ hc
    rw [Set.image_singleton, normalizationPointsMap_genericPoint] at hi
    exact not_mem_genericPoints_fibre (β ≫ q) a hi hv
  have ep := StableOpenPolarizationPullback.originalPullbackPowerIso L
    (LineBundleData.hyperplane D) (β ⁻¹ᵁ W) b ν hb h (m : ℤ) e
  have hpos := Geometry.CurveLineBundle.degree_pos_of_affine_hyperplane_power_iso
    hN hdim hη (L.pullback ν) m hm D (b ≫ h) ep
  simpa only [Positive.degree, DualityScheme.eulerCharOf_unit] using hpos

end DeJongAlterations.StableModificationBridge.StableOpenNearbyNormalizedDegree
