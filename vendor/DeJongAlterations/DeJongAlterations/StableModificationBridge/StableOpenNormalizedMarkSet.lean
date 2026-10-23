import DeJongAlterations.StableModification.Omega.ComponentDegree
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! The literal ORIGINAL normalized marking scheme is finite étale, and its native support is finite.
The private field-flatness argument adapts the repository's proved Hironaka native proof in
`Hironaka/Scheme/Smooth/ExceptionalBaseChange.lean`, with no external project import.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
noncomputable section
universe u

namespace DeJongAlterations.StableModificationBridge.StableOpenNormalizedMarkSet

open StableModification
open CurvesField.Genus Omega.ComponentNormalization Omega.ComponentDegree

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem flat_of_ringEquiv_field {k A B : Type*} [Field k] [CommRing A] [CommRing B]
    (e : k ≃+* A) (φ : A →+* B) : φ.Flat := by
  have h : φ = (φ.comp e.toRingHom).comp e.symm.toRingHom := by
    ext x
    simp
  rw [h]
  refine RingHom.Flat.comp (RingHom.Flat.of_bijective e.symm.bijective) ?_
  algebraize [φ.comp e.toRingHom]
  exact Module.Flat.of_free

private theorem flat_to_spec_field {k : Type u} [Field k] {Z : Scheme.{u}}
    (f : Z ⟶ Spec (.of k)) : Flat f := by
  refine Flat.of_stalkMap f fun z => ?_
  have : IsIso (StructureSheaf.toStalk k (f z)) := by
    have he : f z = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    rw [he, ← stalkClosedPointIso_inv (.of k)]
    infer_instance
  exact flat_of_ringEquiv_field
    (asIso (StructureSheaf.toStalk k (f z))).commRingCatIsoToRingEquiv (f.stalkMap z).hom

/-- The LITERAL original pulled-back marking scheme is itself finite étale over the SAME K,
with the ENTIRE original subscheme/normalization structure map; no reduced replacement is given. -/
theorem finite_etale_original_pullback_marking {X S : Scheme.{u}}
    (f : X ⟶ S) [DeJong.IsNodalCurve f] [IsProper f]
    (D : X.IdealSheafData) (hpair : DeJong.IsSemistablePair f D)
    {K : Type u} [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ S)
    [CompactSpace (pullback (C := Scheme.{u}) f a)]
    [IsAffineHom (pullback.diagonal (terminal.from (pullback (C := Scheme.{u}) f a)))]
    (v : pullback (C := Scheme.{u}) f a)
    (hv : v ∈ genericPoints (pullback (C := Scheme.{u}) f a)) :
    IsFinite ((D.comap (componentMap f a v)).subschemeι ≫ componentStructure f a v) ∧
      Etale ((D.comap (componentMap f a v)).subschemeι ≫ componentStructure f a v) := by
  let q := pullback.snd f a
  let π := normalizationPointsMap ({v} : Set (pullback (C := Scheme.{u}) f a))
  let Dₐ := D.comap (pullback.fst f a)
  let I := Dₐ.comap π
  have hI : D.comap (componentMap f a v) = I :=
    Scheme.IdealSheafData.comap_comp D π (pullback.fst f a)
  rw [hI]
  let r := I.subschemeι ≫ componentStructure f a v
  have : IsFinite π := isFinite_normalizationPointsMap_singleton v q
  have : IsProper (componentStructure f a v) := by
    change IsProper (π ≫ q)
    infer_instance
  have : IsProper r := by dsimp [r]; infer_instance
  have : LocallyOfFinitePresentation r := inferInstance
  have : FormallyUnramified π := formallyUnramified_componentNormalization f a hv
  have : FormallyUnramified (pullback.snd π Dₐ.subschemeι) :=
    MorphismProperty.pullback_snd (P := @FormallyUnramified) _ _ inferInstance
  have : Etale (Dₐ.subschemeι ≫ q) := (Curves.IsSemistablePair.pullback hpair a).etale
  have hr : r = (Dₐ.comapIso π).hom ≫ pullback.snd π Dₐ.subschemeι ≫ Dₐ.subschemeι ≫ q := by
    change I.subschemeι ≫ π ≫ q = _
    rw [← Scheme.IdealSheafData.comapIso_hom_fst_assoc, pullback.condition_assoc]
  have hun : FormallyUnramified (pullback.snd π Dₐ.subschemeι ≫ Dₐ.subschemeι ≫ q) :=
    MorphismProperty.comp_mem @FormallyUnramified _ _ inferInstance inferInstance
  have : FormallyUnramified r := by
    rw [hr]
    exact MorphismProperty.comp_mem @FormallyUnramified _ _ inferInstance hun
  have : Flat r := flat_to_spec_field r
  have : Etale r := Etale.of_formallyUnramified_of_flat r
  have : LocallyQuasiFinite r := Curves.locallyQuasiFinite_of_etale r
  exact ⟨IsFinite.of_isProper_of_locallyQuasiFinite r, inferInstance⟩

/-- The original semistable marking internally gives its exact finite native normalized support,
actual closed points, and original smooth images. -/
theorem exists_original_mark_finset {X S : Scheme.{u}}
    (f : X ⟶ S) [DeJong.IsNodalCurve f] [IsProper f]
    (D : X.IdealSheafData) (hpair : DeJong.IsSemistablePair f D)
    {K : Type u} [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ S)
    [CompactSpace (pullback (C := Scheme.{u}) f a)]
    [IsAffineHom (pullback.diagonal (terminal.from (pullback (C := Scheme.{u}) f a)))]
    (v : pullback (C := Scheme.{u}) f a)
    (hv : v ∈ genericPoints (pullback (C := Scheme.{u}) f a)) :
    ∃ M : Finset (componentNormalization f a v),
      (∀ y, y ∈ M ↔ componentMap f a v y ∈ (D.support : Set X)) ∧
      (∀ y ∈ M, IsClosed ({y} : Set (componentNormalization f a v))) ∧
      (∀ y ∈ M, componentMap f a v y ∈ f.smoothLocus) := by
  classical
  let I := D.comap (componentMap f a v)
  let r := I.subschemeι ≫ componentStructure f a v
  obtain ⟨hfin, het⟩ := finite_etale_original_pullback_marking f D hpair a v hv
  have : IsFinite r := hfin
  have : Etale r := het
  have : IsLocallyArtinian I.subscheme := IsLocallyArtinian.of_locallyQuasiFinite r
  have : CompactSpace I.subscheme := QuasiCompact.compactSpace_of_compactSpace r
  have : Finite I.subscheme := finite_of_compact_of_discrete
  have hrange : Set.range I.subschemeι =
      {y : componentNormalization f a v | componentMap f a v y ∈ (D.support : Set X)} := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_comap]
    rfl
  have hM : {y : componentNormalization f a v |
      componentMap f a v y ∈ (D.support : Set X)}.Finite := by
    rw [← hrange]
    exact Set.finite_range I.subschemeι
  refine ⟨hM.toFinset, fun y => by rw [Set.Finite.mem_toFinset]; rfl, ?_, ?_⟩
  · intro y hy
    have hy' : y ∈ Set.range I.subschemeι := by
      rw [hrange]
      exact (Set.Finite.mem_toFinset hM).mp hy
    obtain ⟨d, rfl⟩ := hy'
    simpa only [Set.image_singleton] using
      I.subschemeι.isClosedEmbedding.isClosedMap _ (isClosed_singleton (x := d))
  · intro y hy
    exact hpair.support_subset_smoothLocus ((Set.Finite.mem_toFinset hM).mp hy)

end DeJongAlterations.StableModificationBridge.StableOpenNormalizedMarkSet
