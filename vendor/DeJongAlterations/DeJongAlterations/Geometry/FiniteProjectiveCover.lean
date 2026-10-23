import DeJongAlterations.Geometry.FiniteProjectiveTuple
import DeJongAlterations.Geometry.BlowupProjectiveEmbeddingCover

/-!
# The actual affine cover subordinate to inverse projective coordinates

This is an open cover of the original source scheme, indexed by all genuine
affine-site opens lying in an inverse coordinate chart. Native affine-site
intersection refinements make the cover locally directed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.Geometry.FiniteProjective

open ProjectiveIdeal BlowupProjectiveEmbedding

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} {n : ℕ}

/-- The genuine original-source cover by all subordinate native affine opens. -/
def originalCover (g : Y ⟶ projectiveSpace R n) : Y.OpenCover :=
  Scheme.Cover.mkOfCovers (SubordinateAffineSite g)
    (fun U => U.1.1.toScheme) (fun U => U.1.1.ι) (by
      intro y
      have hy : g y ∈ ⨆ i : Fin (n + 1), nativeCoordinateOpen (R := R) i := by
        rw [iSup_nativeCoordinateOpen_eq_top]
        trivial
      obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hy
      obtain ⟨U, hU, hyU, hUi⟩ := exists_isAffineOpen_mem_and_subset
        (show y ∈ g ⁻¹ᵁ nativeCoordinateOpen i from hi)
      exact ⟨⟨⟨U, hU⟩, i, hUi⟩, ⟨y, hyU⟩, rfl⟩)

instance originalCover_partialOrder (g : Y ⟶ projectiveSpace R n) :
    PartialOrder (originalCover g).I₀ :=
  inferInstanceAs (PartialOrder (SubordinateAffineSite g))

/-- Genuine native affine-site overlap refinements give local directedness. -/
instance originalCover_locallyDirected (g : Y ⟶ projectiveSpace R n) :
    (originalCover g).LocallyDirected where
  trans {U V} h := (Scheme.AffineZariskiSite.directedCover Y).trans (homOfLE h.le)
  trans_id U := by
    exact (Scheme.AffineZariskiSite.directedCover Y).trans_id U.1
  trans_comp h k := by
    exact (Scheme.AffineZariskiSite.directedCover Y).trans_comp (homOfLE h.le) (homOfLE k.le)
  w h := by
    exact (Scheme.AffineZariskiSite.directedCover Y).trans_map (homOfLE h.le)
  directed {U V} x := by
    obtain ⟨W, hWU, hWV, y, hy⟩ :=
      (Scheme.AffineZariskiSite.directedCover Y).exists_lift_trans_eq x
    obtain ⟨i, hi⟩ := U.2
    let W' : SubordinateAffineSite g :=
      ⟨W, i, (Scheme.AffineZariskiSite.toOpens_mono hWU.le).trans hi⟩
    exact ⟨W', homOfLE hWU.le, homOfLE hWV.le, y, hy⟩
  property_trans h := by
    exact Scheme.Cover.LocallyDirected.property_trans
      (𝒰 := Scheme.AffineZariskiSite.directedCover Y) (homOfLE h.le)

end DeJongAlterations.Geometry.FiniteProjective
