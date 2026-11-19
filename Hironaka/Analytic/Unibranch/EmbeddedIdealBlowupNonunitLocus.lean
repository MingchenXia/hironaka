import Hironaka.Analytic.Unibranch.OriginalFiniteIdealGraphDensity
import Hironaka.Analytic.Unibranch.EmbeddedBlowup

/-!
# The intrinsic nonunit locus of the same native whole ideal

Actual local stalk maps and the whole local ideal dictionaries derive the
trace of the canonical native ideal nonunit locus. Covering original open
immersions then derive original analyticity, closedness and thinness.
No reduced-centre ideal, centre containment or global countability is used.
Blueprint: `embedded-ideal-blowup-nonunit-locus.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace Topology CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupNonunitLocus

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences Hironaka
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaActualAnalyticSubspace
  HironakaSingularModuleSheafStalk HironakaNativePulledIdealSheaf
  SourceReducedComplexSpace OriginalFiniteIdealGraphDensity

noncomputable section

variable {X : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf))

/-- The canonical nonunit locus of the SAME original native inclusion-stalk image. -/
def nonunitLocus : Set X.obj.left :=
  {x | LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b x) ≠ ⊤}

private theorem local_map_ideal_eq_top_iff {R S : Type} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (f : R →+* S) [IsLocalHom f] (I : Ideal R) :
    Ideal.map f I = ⊤ ↔ I = ⊤ := by
  constructor
  · intro h
    by_contra hI
    have hlt : Ideal.map f I < ⊤ :=
      (Ideal.map_mono (IsLocalRing.le_maximalIdeal hI)).trans_lt
        (IsLocalRing.map_maximalIdeal_lt_top f)
    exact hlt.ne h
  · rintro rfl
    exact Ideal.map_top f

variable {ι : Type} {n : ι → ℕ} {M Y : ι → Type}
  [∀ i, TopologicalSpace (M i)] [∀ i, TopologicalSpace (Y i)]
  [∀ i, ChartedSpace (ComplexModel (n i)) (M i)] [∀ i, IsComplexManifold (n i) (M i)]
  [∀ i, ChartedSpace (ComplexModel (n i)) (Y i)]
  {C W : ∀ i, Set (M i)} {π : ∀ i, Y i → M i}
  (hW : ∀ i, IsComplexAnalyticSubset (n := n i) (W i))
  (hπ : ∀ i, IsBlowupAlong (n i) (C i) (π i))
  (J : ∀ i, ofClosedAnalytic (W i) (hW i) ⟶ X)
  [hJopen : ∀ i, LocallyRingedSpace.IsOpenImmersion (J i).hom.left]
  (hJ : ∀ i (y : W i),
    Ideal.map ((actualSubspaceInclusion (n := n i) (W i)).stalkMap y).hom
      (actualWholeSheafStalkIdeal (vanishingIdeal (n := n i) (C i)) y.val) =
        nativePulledIdealStalkIdeal (J i).hom.left B b y)

include hπ hJ

omit hJopen in
/-- The target nonunit trace is DERIVED from ENTIRE original ideal equality. -/
theorem chart_mem_nonunitLocus (i : ι) (w : W i) :
    w.val ∈ C i ↔ (J i).hom.left.base w ∈ nonunitLocus B b := by
  have hunit : w.val ∉ C i ↔
      LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b
        ((J i).hom.left.base w)) = ⊤ := by
    calc
      _ ↔ actualWholeSheafStalkIdeal (vanishingIdeal (n := n i) (C i)) w.val = ⊤ :=
        (actualWholeVanishing_eq_top_iff _ (hπ i).1.1 w.val).symm
      _ ↔ Ideal.map ((actualSubspaceInclusion (n := n i) (W i)).stalkMap w).hom
          (actualWholeSheafStalkIdeal (vanishingIdeal (n := n i) (C i)) w.val) = ⊤ :=
        (local_map_ideal_eq_top_iff ((actualSubspaceInclusion (n := n i) (W i)).stalkMap w).hom _).symm
      _ ↔ nativePulledIdealStalkIdeal (J i).hom.left B b w = ⊤ :=
        iff_of_eq (congrArg (fun I => I = ⊤) (hJ i w))
      _ ↔ _ := nativePulledIdealStalkIdeal_eq_top_iff (J i).hom.left B b w
  change w.val ∈ C i ↔ _ ≠ ⊤
  simpa only [not_not] using (not_congr hunit)

variable (hcover : ∀ x : X.obj.left, ∃ (i : ι) (w : W i), (J i).hom.left.base w = x)

include hcover in
/-- The SAME intrinsic nonunit locus is analytic in the ORIGINAL category. -/
theorem nonunitLocus_isAnalyticSubset : X.IsAnalyticSubset (nonunitLocus B b) := by
  intro x
  obtain ⟨i, w, rfl⟩ := hcover x
  have hC := AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold (hπ i).1
  obtain ⟨e, he, A, hA, htrace⟩ :=
    (isAnalyticSubset_preimage_val (hW i) hC) w
  let eX : LocalEmbedding X :=
    { dim := e.dim
      ambient := e.ambient
      carrier := e.carrier
      analytic := e.analytic
      map := e.map ≫ (J i).hom.left
      isOpenImmersion :=
        @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ e.map e.isOpenImmersion _ (hJopen i)
      overPoint := by rw [Category.assoc, Over.w (J i).hom]; exact e.overPoint }
  refine ⟨eX, ?_, A, hA, ?_⟩
  · obtain ⟨u, hu⟩ := he
    exact ⟨u, congrArg (J i).hom.left.base hu⟩
  · have heq : eX.toPoint ⁻¹' nonunitLocus B b =
        e.toPoint ⁻¹' ((Subtype.val : W i → M i) ⁻¹' C i) := by
      ext u
      exact (chart_mem_nonunitLocus B b hW hπ J hJ i (e.toPoint u)).symm
    exact heq.trans htrace

include hcover in
/-- Closedness is a consequence of the proved original analytic-subset property. -/
theorem nonunitLocus_isClosed : IsClosed (nonunitLocus B b) :=
  (nonunitLocus_isAnalyticSubset B b hW hπ J hJ hcover).isClosed

include hcover in
omit hJopen in
/-- Honest local off-centre densities prove thinness of the SAME global locus. -/
theorem nonunitLocus_interior_eq_empty (hd : ∀ i, W i ⊆ closure (W i \ C i)) :
    interior (nonunitLocus B b) = ∅ := by
  rw [interior_eq_empty_iff_dense_compl, dense_iff_closure_eq, eq_univ_iff_forall]
  intro x
  obtain ⟨i, w, rfl⟩ := hcover x
  have himage : (Subtype.val : W i → M i) '' {u : W i | u.val ∉ C i} = W i \ C i := by
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u.property, hu⟩
    · rintro ⟨hyW, hyC⟩
      exact ⟨⟨y, hyW⟩, hyC, rfl⟩
  have hw : w ∈ closure {u : W i | u.val ∉ C i} := by
    rw [closure_subtype]
    change w.val ∈ closure ((Subtype.val : W i → M i) '' {u : W i | u.val ∉ C i})
    rw [himage]
    exact hd i w.property
  apply closure_mono (s := (J i).hom.left.base '' {u : W i | u.val ∉ C i}) ?_
    (mem_closure_image (J i).hom.left.base.hom.continuous.continuousAt hw)
  rintro _ ⟨u, hu, rfl⟩
  exact (not_congr (chart_mem_nonunitLocus B b hW hπ J hJ i u)).mp hu

end

end Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupNonunitLocus
