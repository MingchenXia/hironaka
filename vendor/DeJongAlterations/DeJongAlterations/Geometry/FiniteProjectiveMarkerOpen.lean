import DeJongAlterations.Geometry.FiniteProjectiveMap
import DeJongAlterations.Geometry.FiniteProjectiveAffineCharts

/-!
# Exact marker-coordinate preimages of the constructed global morphism

The native global projective map has the original inverse coordinate charts
as the literal preimages of its coordinate-power markers.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial Opposite

namespace DeJongAlterations.Geometry.FiniteProjective

open ProjectiveIdeal BlowupProjectiveEmbedding

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} {n : ℕ}
    {p : Y ⟶ Spec (.of R)} {g : Y ⟶ projectiveSpace R n}

/-- Actual marker values cut out exactly the corresponding original coordinate open. -/
theorem localMarker_basicOpen (T : GeneratingTuple p g) (U : Y.affineOpens)
    (i k : Fin (n + 1)) (hk : U.1 ≤ chartOpen g k) :
    Y.basicOpen (localValue (T.finSections (T.finMarker i)) U k hk) = U.1 ⊓ chartOpen g i := by
  dsimp only [localValue]
  rw [T.finMarker_val, map_pow, Scheme.basicOpen_pow _ _ T.degree_pos,
    Scheme.basicOpen_res, chartRatio_basicOpen]
  rw [← inf_assoc, inf_eq_left.mpr hk]

/-- The exact marker preimage holds for each actual native local tuple map. -/
theorem tupleChartMap_preimage_marker (T : GeneratingTuple p g) (U : Y.affineOpens)
    (i k : Fin (n + 1)) (hk : U.1 ≤ chartOpen g k) :
    tupleChartMap T U k hk ⁻¹ᵁ nativeCoordinateOpen (T.finMarker i) =
      U.1.ι ⁻¹ᵁ chartOpen g i := by
  rw [tupleChartMap, Scheme.Hom.comp_preimage, affineTupleMap_preimage_coordinate]
  change U.1.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen _ = _
  rw [Scheme.Opens.toSpecΓ_preimage_basicOpen, localMarker_basicOpen,
    Scheme.Hom.preimage_inf]
  simp only [Scheme.Opens.ι_preimage_self, top_inf_eq]

/-- The actual glued morphism restricts to the prescribed map in any original trivialization. -/
@[reassoc]
theorem tupleProjectiveMap_restrict_of_le (T : GeneratingTuple p g) (U : Y.affineOpens)
    (i : Fin (n + 1)) (hi : U.1 ≤ chartOpen g i) :
    U.1.ι ≫ tupleProjectiveMap T = tupleChartMap T U i hi := by
  let V : SubordinateAffineSite g := ⟨⟨U.1, U.2⟩, i, hi⟩
  exact (tupleProjectiveMap_restrict T V).trans
    (tupleChartMap_coordinate T U i (originalCoordinate g V) hi (originalCoordinate_le g V))

/-- The actual whole global marker preimage is the original inverse coordinate open. -/
theorem tupleProjectiveMap_preimage_marker (T : GeneratingTuple p g) (i : Fin (n + 1)) :
    tupleProjectiveMap T ⁻¹ᵁ nativeCoordinateOpen (T.finMarker i) = chartOpen g i := by
  ext y
  obtain ⟨U, x, rfl⟩ := (originalCover g).exists_eq y
  change tupleProjectiveMap T (U.1.1.ι x) ∈ nativeCoordinateOpen (T.finMarker i) ↔
    U.1.1.ι x ∈ chartOpen g i
  rw [← Scheme.Hom.comp_apply, tupleProjectiveMap_restrict]
  exact congrArg (fun W : U.1.1.toScheme.Opens => x ∈ W)
    (tupleChartMap_preimage_marker T ⟨U.1.1, U.1.2⟩ i (originalCoordinate g U)
      (originalCoordinate_le g U)) |>.to_iff

end DeJongAlterations.Geometry.FiniteProjective
