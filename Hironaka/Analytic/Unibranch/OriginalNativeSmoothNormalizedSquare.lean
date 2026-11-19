import Hironaka.Analytic.Unibranch.OriginalNativeSmoothCanonicalSquare
import Hironaka.Analytic.Unibranch.OriginalBimeromorphicSourceIso
import Hironaka.Resolution.HironakaG1DeletedSmoothHistory

/-! Delete precisely the empty physical stages of the SAME actual canonical
source Q. Its true recipe stays on Q; morphism-level normalization uses actual
trace Cartesian uniqueness and a genuine native quotient isomorphism.
Blueprint first: `original-native-smooth-normalized-square.tex`. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeSmoothNormalizedSquare
noncomputable section
open Hironaka Hironaka.BlowupSequences
  Hironaka BlowupTowers HironakaG1DeletedSmoothHistory
  HironakaSmoothSubmersionOrderedCompressedImagePullback HironakaStageCenters
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps HironakaReducedComplexAnalyticSpaces
  HironakaIntrinsicComplexAnalyticRegularLocus HironakaG11IntrinsicRegularOpenImmersion
  HironakaResolutionSpace HironakaResolutionSpaceComplex SourceReducedComplexSpace
  OriginalNativeSmoothLocalProduct OriginalNativeSmoothCanonicalSquare

/-- A true identity-deletion trace internally constructs the inverse of its ACTUAL endpoint map. -/
theorem exists_id_deletion_biholomorphism {n : ℕ} {A B C : CMfd.{0} n}
    {Q : BlowupTower A B} {S : BlowupTower A C} {e : C → B} {L : List ℕ}
    (H : IsDeletedSmoothHistory (id : A → A) S Q e L) :
    ∃ E : C ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ B, (E : C → B) = e := by
  obtain ⟨v,hv,_hunique⟩ := H.toTrace.universal n B Q.proj id Q.contMDiff_proj contMDiff_id (fun _ => rfl)
  have hve : v ∘ e = id :=
    (H.toTrace.universal n C S.proj e S.contMDiff_proj H.toTrace.isSubmersion.contMDiff
      (fun z => (H.toTrace.proj_comm z).symm)).unique
      ⟨hv.1.comp H.toTrace.isSubmersion.contMDiff,
        fun z => (hv.2.1 (e z)).trans (H.toTrace.proj_comm z),fun z => hv.2.2 (e z)⟩
      ⟨contMDiff_id,fun _ => rfl,fun _ => rfl⟩
  exact ⟨{toEquiv := ⟨e,v,fun z => congrFun hve z,hv.2.2⟩
          contMDiff_toFun := H.toTrace.isSubmersion.contMDiff
          contMDiff_invFun := hv.1},rfl⟩

variable {X Y : SourceReducedComplexSpace} {f : X ⟶ Y} {x : X.obj.left}
  {V : Opens X.obj.left} {T : Opens Y.obj.left}

/-- A deletion of precisely the source Q in the same actual local canonical output. -/
structure NormalizedSource (a : LocalCanonicalPullback f x V T) where
  endpoint : CMfd.{0} a.window.sourceDim
  tower : BlowupTower (CMfd.of (n := a.window.sourceDim) (sourceOpen a.window a.neighbourhood)) endpoint
  biholomorphism : endpoint ≃ₘ⟮𝓘(ℂ,ComplexModel a.window.sourceDim),𝓘(ℂ,ComplexModel a.window.sourceDim)⟯ a.sourceEnd
  retained : List ℕ
  deletion : IsDeletedSmoothHistory id tower a.sourceTower biholomorphism retained

theorem exists_normalized_source (a : LocalCanonicalPullback f x V T) : Nonempty (NormalizedSource a) := by
  obtain ⟨C,S,e,L,H⟩ := exists_deleted_smooth_history Manifold.IsSubmersion.id a.sourceTower
  obtain ⟨E,hE⟩ := exists_id_deletion_biholomorphism H
  exact ⟨⟨C,S,E,L,hE.symm ▸ H⟩⟩

/-- Ordinary original inputs internally generate both the true canonical source and its normalization. -/
theorem exists_original_normalized_source (f : X ⟶ Y) (x : X.obj.left) (hsm : IsSmoothAt f x)
    (hsing : f.hom.left.base x ∈ intrinsicSingularLocus Y.obj)
    (V : Opens X.obj.left) (T : Opens Y.obj.left) (hxV : x ∈ V) (hfxT : f.hom.left.base x ∈ T) :
    ∃ a : LocalCanonicalPullback f x V T, Nonempty (NormalizedSource a) := by
  obtain ⟨a⟩ := exists_local_canonical_pullback f x hsm hsing V T hxV hfxT
  exact ⟨a,exists_normalized_source a⟩

namespace NormalizedSource
variable {a : LocalCanonicalPullback f x V T} (b : NormalizedSource a)

theorem physical_accounting : StageCentres (fun _ C => C.Nonempty) b.tower ∧
    b.retained.length = b.tower.length ∧ b.retained.Pairwise (· < ·) ∧
    ∀ j ∈ b.retained, j < a.sourceTower.length :=
  ⟨b.deletion.nonempty_centres,b.deletion.physical_accounting⟩

/-- WHOLE conventional strict carriers, not only the good open or a support approximation. -/
theorem whole_strict (W : Set (sourceOpen a.window a.neighbourhood)) :
    strictTransform a.window.sourceDim b.tower.proj W =
      b.biholomorphism ⁻¹' strictTransform a.window.sourceDim a.sourceTower.proj W := by
  have hproj : b.tower.proj = a.sourceTower.proj ∘ b.biholomorphism :=
    funext fun z => (b.deletion.toTrace.proj_comm z).symm
  have hexc : exceptionalLocus a.window.sourceDim b.biholomorphism = ∅ :=
    Set.eq_empty_iff_forall_notMem.mpr fun z =>
      MarkedIdealBiholomorphism.notMem_exceptionalLocus_of_inverse
        b.biholomorphism.contMDiff b.biholomorphism.symm.contMDiff
        b.biholomorphism.apply_symm_apply b.biholomorphism.symm_apply_apply z
  calc
    _ = strictTransform a.window.sourceDim (a.sourceTower.proj ∘ b.biholomorphism) W :=
      congrArg (fun p => strictTransform a.window.sourceDim p W) hproj
    _ = strictTransform a.window.sourceDim b.biholomorphism
        (strictTransform a.window.sourceDim a.sourceTower.proj W) :=
      StrictTransformComposition.strictTransform_comp a.sourceTower.contMDiff_proj b.biholomorphism.contMDiff W
    _ = _ := by
      change closure (b.biholomorphism ⁻¹' strictTransform a.window.sourceDim a.sourceTower.proj W \
        exceptionalLocus a.window.sourceDim b.biholomorphism) = _
      rw [hexc,sdiff_empty]
      exact (isClosed_closure.preimage b.biholomorphism.contMDiff.continuous).closure_eq

theorem old_boundary_dictionary (E : List (Set (sourceOpen a.window a.neighbourhood)))
    (hE : ∀ H ∈ E, IsClosed H) :
    oldBoundaryAlong E b.tower = (oldBoundaryAlong E a.sourceTower).map (b.biholomorphism ⁻¹' ·) := by
  have h := b.deletion.old_boundary_dictionary E hE
  have hmap : ∀ F : List (Set (sourceOpen a.window a.neighbourhood)),
      F.map (fun H => (id : sourceOpen a.window a.neighbourhood → _) ⁻¹' H) = F := by
    intro F
    induction F with
    | nil => rfl
    | cons H F ih => exact congrArg (List.cons H) ih
  exact (congrArg (fun F => oldBoundaryAlong F b.tower) (hmap E)).symm.trans h

theorem born_boundary_dictionary :
    bornBoundaryAlong b.tower =
      selectBirths ((bornBoundaryAlong a.sourceTower).map (b.biholomorphism ⁻¹' ·)) b.retained :=
  b.deletion.born_boundary_dictionary

theorem omitted_birth_empty (j : ℕ) (hj : j < a.sourceTower.length) (hjL : j ∉ b.retained) :
    b.biholomorphism ⁻¹' (bornBoundaryAlong a.sourceTower).getD j ∅ = ∅ :=
  b.deletion.omitted_birth_empty j hj hjL

theorem strict_analytic : IsComplexAnalyticSubset (n := a.window.sourceDim)
    (strictTransform a.window.sourceDim b.tower.proj (sourceCarrier a.window a.neighbourhood)) :=
  (b.whole_strict (sourceCarrier a.window a.neighbourhood)).symm ▸
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage b.biholomorphism.contMDiff
      (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
        (strictResolution_of_geometry (sourceCarrier_analytic a.window a.neighbourhood) a.sourceGeometry).isClosedSubmanifold)

def strictSpace : SourceReducedComplexSpace :=
  ofClosedAnalytic (strictTransform a.window.sourceDim b.tower.proj (sourceCarrier a.window a.neighbourhood))
    (strict_analytic b)

def rawIso : (strictSpace b).obj.left ≅ a.sourceStrictSpace.obj.left :=
  actualSubspaceBiholomorphicIso b.biholomorphism
    (strictTransform a.window.sourceDim b.tower.proj (sourceCarrier a.window a.neighbourhood))
    (strictTransform a.window.sourceDim a.sourceTower.proj (sourceCarrier a.window a.neighbourhood))
    (Set.ext_iff.mp (b.whole_strict (sourceCarrier a.window a.neighbourhood)))

/-- The actual whole quotient isomorphism, with the original complex scalar triangle. -/
def nativeIso : strictSpace b ≅ a.sourceStrictSpace :=
  ObjectProperty.isoMk sourceReducedComplexSpaceProperty (Over.isoMk (rawIso b)
    (actualSubspaceMap_point b.biholomorphism.contMDiff
      (fun z hz => (Set.ext_iff.mp (b.whole_strict (sourceCarrier a.window a.neighbourhood)) z).mp hz)))

def projection : strictSpace b ⟶ sourceSpace a.window a.neighbourhood :=
  (nativeIso b).hom ≫ a.sourceResolution

def lift : strictSpace b ⟶ a.targetStrictSpace :=
  (nativeIso b).hom ≫ a.nativeLift

private theorem projection_mapsTo :
    ∀ z ∈ strictTransform a.window.sourceDim b.tower.proj (sourceCarrier a.window a.neighbourhood),
      b.tower.proj z ∈ sourceCarrier a.window a.neighbourhood := by
  intro z hz
  have hzQ := (Set.ext_iff.mp (b.whole_strict (sourceCarrier a.window a.neighbourhood)) z).mp hz
  have hp := (strictResolution_of_geometry (sourceCarrier_analytic a.window a.neighbourhood)
    a.sourceGeometry).strictTransform_subset_preimage hzQ
  change a.sourceTower.proj (b.biholomorphism z) ∈ sourceCarrier a.window a.neighbourhood at hp
  exact Eq.mp (congrArg (fun p => p ∈ sourceCarrier a.window a.neighbourhood)
    (b.deletion.toTrace.proj_comm z)) hp

/-- The FULL native normalized projection is induced by its literal physical tower projection. -/
theorem projection_is_actual : (projection b).hom.left =
    actualSubspaceMap b.tower.contMDiff_proj (projection_mapsTo b) := by
  let hQ := strictResolution_of_geometry (sourceCarrier_analytic a.window a.neighbourhood) a.sourceGeometry
  have hcomp := actualSubspaceMap_comp (n := a.window.sourceDim) (m := a.window.sourceDim) (p := a.window.sourceDim)
    (C := strictTransform a.window.sourceDim b.tower.proj (sourceCarrier a.window a.neighbourhood))
    (D := strictTransform a.window.sourceDim a.sourceTower.proj (sourceCarrier a.window a.neighbourhood))
    (E := sourceCarrier a.window a.neighbourhood) (f := b.biholomorphism) (g := a.sourceTower.proj)
    b.biholomorphism.contMDiff hQ.contMDiff
    (fun z hz => (Set.ext_iff.mp (b.whole_strict (sourceCarrier a.window a.neighbourhood)) z).mp hz)
    (fun _ hz => hQ.strictTransform_subset_preimage hz)
  exact hcomp.symm.trans (actualSubspaceMap_congr
    (n := a.window.sourceDim) (m := a.window.sourceDim)
    (M := b.endpoint) (N := sourceOpen a.window a.neighbourhood)
    (funext b.deletion.toTrace.proj_comm) _ _ _ _)

/-- The same actual native square after deleting precisely the empty source stages. -/
theorem native_square : projection b ≫ baseProjection a.window a.neighbourhood =
    lift b ≫ a.targetResolution := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun q => (nativeIso b).hom ≫ q) a.native_square).trans (Category.assoc _ _ _).symm)

/-- The SAME full original f-square, with true old canonical provenance retained on Q. -/
theorem original_square : projection b ≫ (sourceInclusion a.window a.neighbourhood ≫ f) =
    lift b ≫ (a.targetResolution ≫ targetInclusion a.window a.neighbourhood) := by
  rw [base_square,← Category.assoc,native_square,Category.assoc]

theorem source_properties : IsResolution (projection b) ∧
    Function.Surjective (projection b).hom.left.base ∧ IsProperMap (projection b).hom.left.base ∧
    IsIsoOver (projection b)
      ((sourceInclusion a.window a.neighbourhood).hom.left.base ⁻¹' intrinsicRegularLocus X.obj) := by
  have hSmooth : (strictSpace b).IsSmooth := by
    intro z
    obtain ⟨d,hd⟩ := a.source_properties.1.1 ((nativeIso b).hom.hom.left.base z)
    refine ⟨d,?_⟩
    have hj : LocallyRingedSpace.IsOpenImmersion (nativeIso b).hom.hom.left := by
      change LocallyRingedSpace.IsOpenImmersion (isoLeft (nativeIso b)).hom
      infer_instance
    exact (intrinsicRegularAtDim_map_iff (nativeIso b).hom.hom.left hj
      (Over.w (nativeIso b).hom.hom) z d).mp hd
  refine ⟨⟨hSmooth,a.source_properties.1.2.precomp_iso (nativeIso b)⟩,?_,?_,
    a.source_properties.2.2.2.precomp_iso (nativeIso b)⟩
  · exact a.source_properties.2.1.comp (isoHomeomorph (nativeIso b)).surjective
  · exact a.source_properties.2.2.1.comp (isoHomeomorph (nativeIso b)).isProperMap

end NormalizedSource
end
end Hironaka.Analytic.Unibranch.OriginalNativeSmoothNormalizedSquare
