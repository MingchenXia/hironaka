import DeJongAlterations.Geometry.FiniteProjectiveMarkerOpen
import DeJongAlterations.Geometry.FiniteProjectiveAffineClosed
import DeJongAlterations.Geometry.ProperQuasiProjective

/-!
# Actual projective immersion for an affine morphism into projective space

The intrinsically constructed generating tuple has closed affine coordinate
maps on the original inverse charts. Its exact marker preimages make these
local immersions into an immersion of the original whole scheme.
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

/-- On each original inverse affine chart, the native tuple map is an actual immersion. -/
theorem tupleChartMap_self_isImmersion [IsAffineHom g]
    (T : GeneratingTuple p g) (i : Fin (n + 1)) :
    IsImmersion (tupleChartMap T ⟨chartOpen g i, chartOpen_isAffine g i⟩ i le_rfl) := by
  let U : Y.affineOpens := ⟨chartOpen g i, chartOpen_isAffine g i⟩
  have hv (a : Fin (T.dimension + 1)) :
      localValue (T.finSections a) U i le_rfl = (T.finSections a).val i := by
    change Y.presheaf.map (𝟙 (op (chartOpen g i))) ((T.finSections a).val i) = _
    rw [Y.presheaf.map_id]
    rfl
  have hgen : letI := (affineBaseCoefficients p U).toAlgebra
      Algebra.adjoin R (Set.range (fun a => localValue (T.finSections a) U i le_rfl)) = ⊤ := by
    simp only [hv]
    exact T.finSections_generate i
  have : IsImmersion (affineTupleMap (affineBaseCoefficients p U)
      (fun a => localValue (T.finSections a) U i le_rfl) (T.localSpan U i le_rfl)) :=
    affineTupleMap_isImmersion _ _ _ (T.finMarker i) (T.localMarker U i le_rfl) hgen
  change IsImmersion (U.2.isoSpec.hom ≫ _)
  infer_instance

/-- The actual glued global tuple morphism is an immersion of the original whole source. -/
theorem tupleProjectiveMap_isImmersion [IsAffineHom g] (T : GeneratingTuple p g) :
    IsImmersion (tupleProjectiveMap T) := by
  let : MorphismProperty.RespectsRight (@IsImmersion : MorphismProperty Scheme.{u})
      @IsOpenImmersion :=
    ⟨fun i hi f hf => by let := hi; let := hf; infer_instance⟩
  apply IsZariskiLocalAtTarget.of_forall_source_exists_preimage (P := @IsImmersion)
  intro x
  have hx : g x ∈ ⨆ i : Fin (n + 1), nativeCoordinateOpen (R := R) i := by
    rw [iSup_nativeCoordinateOpen_eq_top]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  refine ⟨nativeCoordinateOpen (T.finMarker i), ?_, ?_⟩
  · change x ∈ tupleProjectiveMap T ⁻¹ᵁ nativeCoordinateOpen (T.finMarker i)
    rw [tupleProjectiveMap_preimage_marker]
    exact hi
  · rw [tupleProjectiveMap_preimage_marker,
      tupleProjectiveMap_restrict_of_le T ⟨chartOpen g i, chartOpen_isAffine g i⟩ i le_rfl]
    exact tupleChartMap_self_isImmersion T i

/-- An actual affine morphism into projective space and finite-type coefficient
structure internally produce an original-source projective immersion. -/
theorem isQuasiProjectiveOver_of_affine_to_projective
    (p : Y ⟶ Spec (.of R)) [LocallyOfFiniteType p]
    (g : Y ⟶ projectiveSpace R n) [IsAffineHom g] : IsQuasiProjectiveOver p := by
  obtain ⟨T⟩ := exists_generatingTuple p g
  exact ⟨T.dimension, tupleProjectiveMap T, tupleProjectiveMap_isImmersion T,
    tupleProjectiveMap_structure T⟩

end DeJongAlterations.Geometry.FiniteProjective
