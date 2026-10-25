import DeJongAlterations.Geometry.FiniteProjectiveLocal
import DeJongAlterations.Geometry.FiniteProjectiveCover
import DeJongAlterations.Geometry.FiniteProjectiveAffineMap

/-!
# The actual global projective morphism of the generating twisted tuple

The affine native unit-ideal projective maps glue on the original source.
Their transition identities follow from whole-ring unit scaling and the
genuine section restriction maps, preserving the original structure morphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial Opposite

namespace DeJongAlterations.Geometry.FiniteProjective

open ProjectiveIdeal BlowupGluing BlowupProjectiveEmbedding

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} {n : ℕ}
    {p : Y ⟶ Spec (.of R)} {g : Y ⟶ projectiveSpace R n}

/-- An actual original coordinate containing the subordinate affine open. -/
def originalCoordinate (g : Y ⟶ projectiveSpace R n) (U : SubordinateAffineSite g) :
    Fin (n + 1) := U.2.choose

/-- Its actual containment, obtained from the definition of the subordinate site. -/
theorem originalCoordinate_le (g : Y ⟶ projectiveSpace R n) (U : SubordinateAffineSite g) :
    U.1.1 ≤ chartOpen g (originalCoordinate g U) := U.2.choose_spec

/-- The actual native tuple morphism on one original affine open. -/
def tupleChartMap (T : GeneratingTuple p g) (U : Y.affineOpens) (i : Fin (n + 1))
    (hi : U.1 ≤ chartOpen g i) : U.1.toScheme ⟶ projectiveSpace R T.dimension :=
  U.2.isoSpec.hom ≫ affineTupleMap (affineBaseCoefficients p U)
    (fun a => localValue (T.finSections a) U i hi) (T.localSpan U i hi)

/-- Changing original coordinate preserves the actual native local tuple map. -/
theorem tupleChartMap_coordinate (T : GeneratingTuple p g) (U : Y.affineOpens)
    (i k : Fin (n + 1)) (hi : U.1 ≤ chartOpen g i) (hk : U.1 ≤ chartOpen g k) :
    tupleChartMap T U k hk = tupleChartMap T U i hi := by
  obtain ⟨v, hv⟩ := (localRatio_isUnit g U k i hk hi).pow T.degree
  have hval : (fun a => localValue (T.finSections a) U k hk) =
      (fun a => (v : Γ(Y, U.1)) * localValue (T.finSections a) U i hi) := by
    funext a
    rw [localValue_transition (T.finSections a) U k i hk hi, hv, mul_comm]
  dsimp only [tupleChartMap]
  congr 1
  exact (affineTupleMap_congr rfl hval _
    (generator_span_unit ⊤ _ (T.localSpan U i hi) v)).trans
      (affineTupleMap_unit _ _ _ v)

/-- Actual affine-site restriction preserves the original native tuple morphism. -/
theorem tupleChartMap_naturality (T : GeneratingTuple p g)
    {U V : Y.AffineZariskiSite} (h : U ⟶ V) (i k : Fin (n + 1))
    (hi : U.1 ≤ chartOpen g i) (hk : V.1 ≤ chartOpen g k) :
    Y.homOfLE (Scheme.AffineZariskiSite.toOpens_mono h.le) ≫
      tupleChartMap T ⟨V.1, V.2⟩ k hk = tupleChartMap T ⟨U.1, U.2⟩ i hi := by
  let hkU := (Scheme.AffineZariskiSite.toOpens_mono h.le).trans hk
  have hspec : Y.homOfLE (Scheme.AffineZariskiSite.toOpens_mono h.le) ≫ V.2.isoSpec.hom =
      U.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (coefficientMap h)) :=
    (Scheme.Opens.toSpecΓ_SpecMap_presheaf_map U.1 V.1
      (Scheme.AffineZariskiSite.toOpens_mono h.le)).symm
  have hspan : Ideal.span (Set.range (fun a =>
      coefficientMap h (localValue (T.finSections a) ⟨V.1, V.2⟩ k hk))) = ⊤ := by
    simpa only [localValue_restrict] using T.localSpan ⟨U.1, U.2⟩ k hkU
  change _ ≫ (V.2.isoSpec.hom ≫ _) = _
  rw [← Category.assoc, hspec, Category.assoc, affineTupleMap_naturality _ _ _ _ hspan]
  change U.2.isoSpec.hom ≫ _ = _
  have H := affineTupleMap_congr (affineBaseCoefficients_restrict p h)
    (funext (fun a => localValue_restrict (T.finSections a) h k hk)) hspan
    (T.localSpan ⟨U.1, U.2⟩ k hkU)
  exact (congrArg (fun q => U.2.isoSpec.hom ≫ q) H).trans
    (tupleChartMap_coordinate T ⟨U.1, U.2⟩ i k hi hkU)

/-- The native chart morphism retains the original coefficient structure map. -/
@[reassoc]
theorem tupleChartMap_structure (T : GeneratingTuple p g) (U : Y.affineOpens)
    (i : Fin (n + 1)) (hi : U.1 ≤ chartOpen g i) :
    tupleChartMap T U i hi ≫ projectiveSpaceStructure R T.dimension = U.1.ι ≫ p := by
  rw [tupleChartMap, Category.assoc, affineTupleMap_structure, affineBaseCoefficients_structure,
    ← Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec]

/-- The actual maps on the native subordinate affine cover. -/
def originalCoverMap (T : GeneratingTuple p g) (U : SubordinateAffineSite g) :
    (originalCover g).X U ⟶ projectiveSpace R T.dimension :=
  tupleChartMap T ⟨U.1.1, U.1.2⟩ (originalCoordinate g U) (originalCoordinate_le g U)

/-- Native local compatibility is supplied by the actual restriction theorem. -/
theorem originalCoverMap_compatible (T : GeneratingTuple p g)
    {U V : SubordinateAffineSite g} (h : U ⟶ V) :
    (originalCover g).trans h ≫ originalCoverMap T V = originalCoverMap T U := by
  exact tupleChartMap_naturality T (homOfLE h.le)
    (originalCoordinate g U) (originalCoordinate g V)
    (originalCoordinate_le g U) (originalCoordinate_le g V)

/-- The actual global native projective morphism constructed from the generating tuple. -/
def tupleProjectiveMap (T : GeneratingTuple p g) : Y ⟶ projectiveSpace R T.dimension :=
  (originalCover g).glueMorphismsOfLocallyDirected (originalCoverMap T)
    (fun _ => originalCoverMap_compatible T _)

/-- Its actual restriction is the original local native unit-ideal tuple morphism. -/
@[reassoc]
theorem tupleProjectiveMap_restrict (T : GeneratingTuple p g) (U : SubordinateAffineSite g) :
    U.1.1.ι ≫ tupleProjectiveMap T = originalCoverMap T U :=
  (originalCover g).map_glueMorphismsOfLocallyDirected (originalCoverMap T)
    (fun _ => originalCoverMap_compatible T _) U

/-- The original whole source and its original coefficient morphism are retained exactly. -/
@[reassoc]
theorem tupleProjectiveMap_structure (T : GeneratingTuple p g) :
    tupleProjectiveMap T ≫ projectiveSpaceStructure R T.dimension = p := by
  apply (originalCover g).hom_ext
  intro U
  change U.1.1.ι ≫ _ = U.1.1.ι ≫ _
  rw [← Category.assoc, tupleProjectiveMap_restrict]
  exact tupleChartMap_structure T ⟨U.1.1, U.1.2⟩ _ _

end DeJongAlterations.Geometry.FiniteProjective
