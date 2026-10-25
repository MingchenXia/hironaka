import DeJongAlterations.Geometry.BlowupProjectiveEmbeddingForms

/-!
# The genuine blowup cover subordinate to projective coordinate opens

The chosen subcategory contains all affine opens lying under some original
projective coordinate open. It still covers the native blowup and is locally
directed by the actual affine Rees restriction morphisms.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

namespace DeJongAlterations.Geometry.BlowupProjectiveEmbedding

open ProjectiveIdeal BlowupGluing

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R] {n : ℕ} {X : Scheme.{u}}

/-- All native affine-site opens subordinate to some actual projective coordinate open. -/
def SubordinateAffineSite (j : X ⟶ projectiveSpace R n) :=
  { U : X.AffineZariskiSite // ∃ i : Fin (n + 1), U.1 ≤ j ⁻¹ᵁ nativeCoordinateOpen i }

instance (j : X ⟶ projectiveSpace R n) : PartialOrder (SubordinateAffineSite j) :=
  inferInstanceAs (PartialOrder { U : X.AffineZariskiSite //
    ∃ i : Fin (n + 1), U.1 ≤ j ⁻¹ᵁ nativeCoordinateOpen i })

/-- The canonical projective-coordinate-subordinate cover uses the original affine Rees blowups. -/
def subordinateCover (D : X.IdealSheafData) (j : X ⟶ projectiveSpace R n) :
    (blowup D).OpenCover :=
  Scheme.Cover.mkOfCovers (SubordinateAffineSite j)
    (fun U => (blowupCover D).X U.1) (fun U => chartInclusion D U.1) (by
      intro b
      have hb : j (blowupStructure D b) ∈
          ⨆ i : Fin (n + 1), nativeCoordinateOpen (R := R) i := by
        rw [iSup_nativeCoordinateOpen_eq_top]
        trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hb
      obtain ⟨U, hU, hbU, hUi⟩ := exists_isAffineOpen_mem_and_subset
        (show blowupStructure D b ∈ j ⁻¹ᵁ nativeCoordinateOpen i from hi)
      let V : X.AffineZariskiSite := ⟨U, hU⟩
      have hbr : b ∈ (chartInclusion D V).opensRange := by
        rw [chartInclusion_opensRange]
        exact hbU
      obtain ⟨y, hy⟩ := hbr
      exact ⟨⟨V, i, hUi⟩, y, hy⟩)

instance subordinateCover_partialOrder (D : X.IdealSheafData)
    (j : X ⟶ projectiveSpace R n) : PartialOrder (subordinateCover D j).I₀ :=
  inferInstanceAs (PartialOrder (SubordinateAffineSite j))

local instance blowupCover_partialOrder (D : X.IdealSheafData) :
    PartialOrder (blowupCover D).I₀ :=
  inferInstanceAs (PartialOrder X.AffineZariskiSite)

/-- This actual subordinate cover inherits directedness from the full native affine-site cover. -/
instance subordinateCover_locallyDirected (D : X.IdealSheafData)
    (j : X ⟶ projectiveSpace R n) : (subordinateCover D j).LocallyDirected where
  trans {U V} h := (blowupCover D).trans (homOfLE h.le)
  trans_id U := by
    exact (blowupCover D).trans_id U.1
  trans_comp h k := by
    exact (blowupCover D).trans_comp (homOfLE h.le) (homOfLE k.le)
  w h := by
    exact (blowupCover D).trans_map (homOfLE h.le)
  directed {U V} x := by
    obtain ⟨W, hWU, hWV, y, hy⟩ := (blowupCover D).exists_lift_trans_eq x
    obtain ⟨i, hi⟩ := U.2
    let W' : SubordinateAffineSite j :=
      ⟨W, i, (Scheme.AffineZariskiSite.toOpens_mono hWU.le).trans hi⟩
    exact ⟨W', homOfLE hWU.le, homOfLE hWV.le, y, hy⟩
  property_trans h := by
    exact Scheme.Cover.LocallyDirected.property_trans
      (𝒰 := blowupCover D) (homOfLE h.le)

end DeJongAlterations.Geometry.BlowupProjectiveEmbedding
