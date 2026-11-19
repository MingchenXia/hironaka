import Hironaka.Analytic.Unibranch.HironakaG11SingularCentreModification
import Hironaka.Analytic.Unibranch.OriginalAnalyticCover

/-!
# Gluing compatible local centres on open-immersion covers (goal G11, route step 1)

The canonical resolution algorithm produces its centres LOCALLY, one window (local embedding) at a
time. This file proves the gluing step that turns local centres which agree on overlaps into ONE
global closed centre of the original complex space, and one global blowup step from them.

* Set level (`IsCompatible`, `glue`): local subsets `A i ⊆ β i` along maps `f i : β i → α` are
  compatible when they agree on overlaps; then the glued set `⋃ f i '' A i` has exactly the
  preimages `A i` (`preimage_glue`), compatibility is the existence of SOME global set with those
  preimages (`isCompatible_iff_exists_preimage`), the glued set is the unique such set on its cover
  (`glue_eq_of_preimage`), and it is closed when the local pieces are closed and supported in a
  locally finite family of compact footprints (`isClosed_glue`). No injectivity is needed.
* Complex spaces: this generalizes `OriginalAnalyticCover` (which assumes pairwise DISJOINT ranges)
  to compatible families on open-immersion covers (`unionImages_isAnalyticSubset_of_compatible`,
  `unionImages_interior_eq_empty_of_compatible`) and to PARTIAL covers of a closed set
  (`isAnalyticSubset_of_isClosed_of_openImmersion`).
* `LocalSmoothCentres X ι`: the interface consumed by the G11 driver — windows `(e i, O i)` of `X`
  (a local embedding and an open subset of its ambient space) with a closed submanifold
  `C i ⊆ O i` inside the carrier. If the family is `Compatible` (agrees on overlaps in `X`), its
  glued support `S` has the window traces `C i` (`preimage_support`); if moreover `S` is closed
  (e.g. finitely many windows with compact footprints covering `S`,
  `isClosed_support_of_compact_footprints`) and contained in the singular locus, there is one
  actual blowup of `X` along `S` which is a singular-centre step (`exists_singularCentreBlowup`).

No compactness of `X`, global embedding, or resolution hypothesis is used.
Blueprint: `hironaka-g11-resume-compatible-centres.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG11CompatibleAnalyticCover

open Hironaka Hironaka.BlowupSequences
  Hironaka HironakaIntrinsicComplexAnalyticRegularLocus
  HironakaReducedComplexAnalyticSpaces
  SourceReducedComplexSpace SmoothCentreModification OriginalAnalyticClosedSubspaceSmoothCentres
  HironakaG11SingularCentreModification OriginalAnalyticCover

noncomputable section

/-! ### Set-level gluing -/

section Sets

variable {ι : Type*} {α : Type*} {β : ι → Type*}

/-- Local subsets `A i ⊆ β i` are *compatible* along the maps `f i : β i → α` if they agree on
overlaps: whenever two local points have the same image, the second lies in its subset as soon
as the first does (by symmetry of the quantifiers, this is an `iff`). -/
def IsCompatible (f : ∀ i, β i → α) (A : ∀ i, Set (β i)) : Prop :=
  ∀ i k (y : β i) (z : β k), f i y = f k z → y ∈ A i → z ∈ A k

/-- The glued global set: the union of the images of the local subsets. -/
def glue (f : ∀ i, β i → α) (A : ∀ i, Set (β i)) : Set α := ⋃ i, f i '' A i

variable {f : ∀ i, β i → α} {A : ∀ i, Set (β i)}

theorem mem_glue {x : α} : x ∈ glue f A ↔ ∃ i, ∃ y ∈ A i, f i y = x := by
  simp only [glue, mem_iUnion, mem_image]

/-- **Gluing.** Compatible local subsets are exactly the preimages of the glued set. -/
theorem preimage_glue (h : IsCompatible f A) (i : ι) : f i ⁻¹' glue f A = A i := by
  ext y
  constructor
  · intro hy
    obtain ⟨k, z, hz, hzy⟩ := mem_glue.mp hy
    exact h k i z y hzy hz
  · intro hy
    exact mem_glue.mpr ⟨i, y, hy, rfl⟩

/-- Local subsets cut out by one global set are compatible. -/
theorem isCompatible_of_preimage (S : Set α) (hS : ∀ i, f i ⁻¹' S = A i) : IsCompatible f A := by
  intro i k y z hyz hy
  rw [← hS k]
  rw [← hS i] at hy
  change f k z ∈ S
  rw [← hyz]
  exact hy

/-- Compatibility is exactly the existence of a global set with the given local traces. -/
theorem isCompatible_iff_exists_preimage :
    IsCompatible f A ↔ ∃ S : Set α, ∀ i, f i ⁻¹' S = A i :=
  ⟨fun h => ⟨glue f A, preimage_glue h⟩, fun ⟨S, hS⟩ => isCompatible_of_preimage S hS⟩

/-- On the part covered by the maps, the glued set is the ONLY global set with the given
local traces. -/
theorem glue_eq_of_preimage (S : Set α) (hS : ∀ i, f i ⁻¹' S = A i)
    (hcov : S ⊆ ⋃ i, range (f i)) : glue f A = S := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, y, hy, rfl⟩ := mem_glue.mp hx
    rw [← hS i] at hy
    exact hy
  · intro hx
    obtain ⟨i, y, rfl⟩ := mem_iUnion.mp (hcov hx)
    exact mem_glue.mpr ⟨i, y, by rw [← hS i]; exact hx, rfl⟩

theorem glue_subset_iff {T : Set α} : glue f A ⊆ T ↔ ∀ i, A i ⊆ f i ⁻¹' T := by
  simp only [glue, iUnion_subset_iff, image_subset_iff]

theorem glue_subset_iUnion_range : glue f A ⊆ ⋃ i, range (f i) :=
  iUnion_mono fun _ => image_subset_range _ _

/-- The glued set only depends on the local pieces inside any family of footprints whose images
cover it. -/
theorem glue_eq_iUnion_inter (h : IsCompatible f A) (K : ∀ i, Set (β i))
    (hcov : glue f A ⊆ ⋃ i, f i '' K i) : glue f A = ⋃ i, f i '' (A i ∩ K i) := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨i, y, hy, rfl⟩ := mem_iUnion.mp (hcov hx)
    have hyA : y ∈ A i := by
      rw [← preimage_glue h i]
      exact hx
    exact mem_iUnion.mpr ⟨i, y, ⟨hyA, hy⟩, rfl⟩
  · exact iUnion_mono fun i => image_mono inter_subset_left

/-- **Closedness of the glued set.** Closed compatible local pieces supported in a locally finite
family of compact footprints glue to a closed set. -/
theorem isClosed_glue [TopologicalSpace α] [∀ i, TopologicalSpace (β i)] [T2Space α]
    (h : IsCompatible f A) (hf : ∀ i, Continuous (f i)) (hA : ∀ i, IsClosed (A i))
    (K : ∀ i, Set (β i)) (hK : ∀ i, IsCompact (K i)) (hlf : LocallyFinite fun i => f i '' K i)
    (hcov : glue f A ⊆ ⋃ i, f i '' K i) : IsClosed (glue f A) := by
  rw [glue_eq_iUnion_inter h K hcov]
  apply (hlf.subset fun i => image_mono inter_subset_right).isClosed_iUnion
  intro i
  exact (((hK i).inter_left (hA i)).image (hf i)).isClosed

end Sets

/-! ### Compatible families on open-immersion covers of complex spaces -/

section Cover

variable {ι : Type*} {X : SourceReducedComplexSpace} {Y : ι → SourceReducedComplexSpace}

theorem unionImages_eq_glue (j : ∀ i, Y i ⟶ X) (A : ∀ i, Set (Y i).obj.left) :
    unionImages j A = glue (fun i => (j i).hom.left.base) A := rfl

/-- The disjoint case of `OriginalAnalyticCover` is a special case of compatibility. -/
theorem isCompatible_of_pairwise_disjoint (j : ∀ i, Y i ⟶ X)
    (hj : ∀ i, LocallyRingedSpace.IsOpenImmersion (j i).hom.left)
    (hdisj : Pairwise (fun i k => Disjoint (range (j i).hom.left.base) (range (j k).hom.left.base)))
    (A : ∀ i, Set (Y i).obj.left) : IsCompatible (fun i => (j i).hom.left.base) A :=
  isCompatible_of_preimage (unionImages j A) (preimage_unionImages_eq j hj hdisj A)

/-- Compatible local subsets are the literal traces of their union. -/
theorem preimage_unionImages_eq_of_compatible (j : ∀ i, Y i ⟶ X) (A : ∀ i, Set (Y i).obj.left)
    (h : IsCompatible (fun i => (j i).hom.left.base) A) (i : ι) :
    (j i).hom.left.base ⁻¹' unionImages j A = A i :=
  preimage_glue h i

/-- Compatible local analytic sets on an open-immersion cover glue to an analytic set. -/
theorem unionImages_isAnalyticSubset_of_compatible (j : ∀ i, Y i ⟶ X)
    (hj : ∀ i, LocallyRingedSpace.IsOpenImmersion (j i).hom.left)
    (hcover : ∀ x : X.obj.left, ∃ (i : ι) (y : (Y i).obj.left), (j i).hom.left.base y = x)
    (A : ∀ i, Set (Y i).obj.left) (h : IsCompatible (fun i => (j i).hom.left.base) A)
    (hA : ∀ i, (Y i).IsAnalyticSubset (A i)) :
    X.IsAnalyticSubset (unionImages j A) := by
  apply isAnalyticSubset_of_openImmersion_cover j hj hcover
  intro i
  rw [preimage_unionImages_eq_of_compatible j A h i]
  exact hA i

/-- Compatible local thin sets on an open-immersion cover glue to a thin set. -/
theorem unionImages_interior_eq_empty_of_compatible (j : ∀ i, Y i ⟶ X)
    (hj : ∀ i, LocallyRingedSpace.IsOpenImmersion (j i).hom.left)
    (hcover : ∀ x : X.obj.left, ∃ (i : ι) (y : (Y i).obj.left), (j i).hom.left.base y = x)
    (A : ∀ i, Set (Y i).obj.left) (h : IsCompatible (fun i => (j i).hom.left.base) A)
    (hA : ∀ i, interior (A i) = ∅) :
    interior (unionImages j A) = ∅ := by
  apply interior_eq_empty_of_openImmersion_cover j hj hcover
  intro i
  rw [preimage_unionImages_eq_of_compatible j A h i]
  exact hA i

/-- **Analyticity from a PARTIAL cover.** A closed set whose points are all covered by open
immersions with analytic traces is analytic: away from the set, a local embedding inside its
open complement has empty trace. -/
theorem isAnalyticSubset_of_isClosed_of_openImmersion (j : ∀ i, Y i ⟶ X)
    (hj : ∀ i, LocallyRingedSpace.IsOpenImmersion (j i).hom.left)
    (Z : Set X.obj.left) (hZc : IsClosed Z)
    (hcover : ∀ x ∈ Z, ∃ (i : ι) (y : (Y i).obj.left), (j i).hom.left.base y = x)
    (hZ : ∀ i, (Y i).IsAnalyticSubset ((j i).hom.left.base ⁻¹' Z)) :
    X.IsAnalyticSubset Z := by
  intro x
  by_cases hx : x ∈ Z
  · obtain ⟨i, y, hy⟩ := hcover x hx
    obtain ⟨e, ⟨z, hz⟩, A, hA, htrace⟩ := hZ i y
    let f : LocalEmbedding X :=
      { dim := e.dim
        ambient := e.ambient
        carrier := e.carrier
        analytic := e.analytic
        map := e.map ≫ (j i).hom.left
        isOpenImmersion :=
          @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ e.map e.isOpenImmersion
            (j i).hom.left (hj i)
        overPoint := by
          rw [Category.assoc, Over.w (j i).hom]
          exact e.overPoint }
    refine ⟨f, ⟨z, ?_⟩, A, hA, ?_⟩
    · change (j i).hom.left.base (e.toPoint z) = x
      rw [hz, hy]
    · exact htrace
  · obtain ⟨e, hxe, hsub, -⟩ := LocalEmbedding.exists_domain x hZc.isOpen_compl hx
    refine ⟨e, hxe, ∅, isComplexAnalyticSubset_empty, ?_⟩
    ext c
    simp only [mem_preimage, preimage_empty, mem_empty_iff_false, iff_false]
    exact hsub ⟨c, rfl⟩

/-- Compatible local analytic sets with CLOSED union are analytic, without covering `X`. -/
theorem unionImages_isAnalyticSubset_of_isClosed (j : ∀ i, Y i ⟶ X)
    (hj : ∀ i, LocallyRingedSpace.IsOpenImmersion (j i).hom.left)
    (A : ∀ i, Set (Y i).obj.left) (h : IsCompatible (fun i => (j i).hom.left.base) A)
    (hA : ∀ i, (Y i).IsAnalyticSubset (A i)) (hcl : IsClosed (unionImages j A)) :
    X.IsAnalyticSubset (unionImages j A) := by
  apply isAnalyticSubset_of_isClosed_of_openImmersion j hj _ hcl
  · intro x hx
    obtain ⟨i, y, -, hy⟩ := mem_glue.mp hx
    exact ⟨i, y, hy⟩
  · intro i
    rw [preimage_unionImages_eq_of_compatible j A h i]
    exact hA i

/-- Compatible closed local pieces with compact footprints in `X` (compact subsets of the
ranges, locally finite, covering the union) have closed union. -/
theorem isClosed_unionImages_of_compact_footprints (j : ∀ i, Y i ⟶ X)
    (hj : ∀ i, LocallyRingedSpace.IsOpenImmersion (j i).hom.left)
    (A : ∀ i, Set (Y i).obj.left) (h : IsCompatible (fun i => (j i).hom.left.base) A)
    (hA : ∀ i, IsClosed (A i)) (L : ι → Set X.obj.left) (hL : ∀ i, IsCompact (L i))
    (hLr : ∀ i, L i ⊆ range (j i).hom.left.base) (hlf : LocallyFinite L)
    (hcov : unionImages j A ⊆ ⋃ i, L i) : IsClosed (unionImages j A) := by
  have : T2Space X.obj.left := X.property.1
  have himg : ∀ i, (j i).hom.left.base '' ((j i).hom.left.base ⁻¹' L i) = L i :=
    fun i => image_preimage_eq_of_subset (hLr i)
  refine isClosed_glue h (fun i => (hj i).base_open.continuous) hA
    (fun i => (j i).hom.left.base ⁻¹' L i) (fun i => ?_) ?_ ?_
  · exact ((hj i).base_open.isInducing.isCompact_preimage_iff (hLr i)).mpr (hL i)
  · simpa only [himg] using hlf
  · simp only [himg]
    exact hcov

/-- The singular locus of `X` pulls back to the singular locus of an open subspace. -/
theorem preimage_intrinsicSingularLocus_of_isOpenImmersion {Y' : SourceReducedComplexSpace}
    (j : Y' ⟶ X) (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left) :
    j.hom.left.base ⁻¹' intrinsicSingularLocus X.obj = intrinsicSingularLocus Y'.obj := by
  have h := HironakaG11IntrinsicRegularOpenImmersion.preimage_intrinsicRegularLocus j.hom.left hj
    (Over.w j.hom)
  change j.hom.left.base ⁻¹' (intrinsicRegularLocus X.obj)ᶜ = (intrinsicRegularLocus Y'.obj)ᶜ
  rw [preimage_compl, h]

end Cover

/-! ### Local smooth centres on windows of a complex space -/

/-- **Local smooth centres on windows** (the interface between the local canonical algorithm and
the global G11 sequence). For every index `i`: a local embedding `emb i` of `X`, an open subset
`window i` of its ambient space, and a closed complex submanifold `centre i` of `window i`
contained in the carrier. The window `i` of `X` is the actual open subspace
`givenWindowMorphism (emb i) (window i)`; the local centre is the trace `C i ∩ carrier`. -/
structure LocalSmoothCentres (X : SourceReducedComplexSpace) (ι : Type*) where
  /-- The local embedding of the `i`-th window. -/
  emb : ι → LocalEmbedding X
  /-- The open subset of the ambient space of `emb i` cut out as the `i`-th window. -/
  window : ∀ i, Opens (emb i).ambient
  /-- The local centre, a subset of the window ambient. -/
  centre : ∀ i, Set (window i)
  /-- The local centre is a closed complex submanifold of the window ambient. -/
  isClosedSubmanifold : ∀ i, IsClosedSubmanifold (emb i).dim (centre i)
  /-- The local centre lies in the carrier of the local embedding. -/
  centre_subset : ∀ i, centre i ⊆ (Subtype.val : window i → (emb i).ambient) ⁻¹' (emb i).carrier

namespace LocalSmoothCentres

variable {X : SourceReducedComplexSpace} {ι : Type*} (F : LocalSmoothCentres X ι)

/-- The carrier of the `i`-th window (the model points inside `window i`). -/
abbrev windowCarrier (i : ι) : Set (F.window i) :=
  (Subtype.val : F.window i → (F.emb i).ambient) ⁻¹' (F.emb i).carrier

/-- The `i`-th window as an original complex space. -/
abbrev windowSpace (i : ι) : SourceReducedComplexSpace :=
  ofClosedAnalytic (F.windowCarrier i)
    (AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val (F.emb i).analytic (F.window i))

/-- The actual open immersion of the `i`-th window into `X`. -/
abbrev windowMap (i : ι) : F.windowSpace i ⟶ X :=
  givenWindowMorphism (F.emb i) (F.window i)

instance windowMap_isOpenImmersion (i : ι) :
    LocallyRingedSpace.IsOpenImmersion (F.windowMap i).hom.left :=
  givenWindowMorphism_isOpenImmersion (F.emb i) (F.window i)

/-- The trace of the `i`-th local centre on the window: the window points lying in it. -/
abbrev trace (i : ι) : Set (F.windowSpace i).obj.left :=
  (Subtype.val : F.windowCarrier i → F.window i) ⁻¹' F.centre i

/-- The local centres AGREE ON OVERLAPS in `X`. -/
def Compatible : Prop :=
  IsCompatible (fun i => (F.windowMap i).hom.left.base) F.trace

/-- The glued global centre: the union of the images of the local centres. -/
def support : Set X.obj.left :=
  unionImages F.windowMap F.trace

theorem mem_support {x : X.obj.left} :
    x ∈ F.support ↔ ∃ i, ∃ d ∈ F.trace i, (F.windowMap i).hom.left.base d = x :=
  mem_glue

/-- Local centres cut out by one global set are compatible. -/
theorem compatible_of_preimage (S : Set X.obj.left)
    (hS : ∀ i, (F.windowMap i).hom.left.base ⁻¹' S = F.trace i) : F.Compatible :=
  isCompatible_of_preimage S hS

/-- **The glued centre has the given local traces.** -/
theorem preimage_support (hc : F.Compatible) (i : ι) :
    (F.windowMap i).hom.left.base ⁻¹' F.support = F.trace i :=
  preimage_glue hc i

/-- Uniqueness: a global set with the given local traces, covered by the windows, is the glued
centre. -/
theorem support_eq_of_preimage (S : Set X.obj.left)
    (hS : ∀ i, (F.windowMap i).hom.left.base ⁻¹' S = F.trace i)
    (hcov : S ⊆ ⋃ i, range (F.windowMap i).hom.left.base) : F.support = S :=
  glue_eq_of_preimage S hS hcov

theorem support_subset_iff {T : Set X.obj.left} :
    F.support ⊆ T ↔ ∀ i, F.trace i ⊆ (F.windowMap i).hom.left.base ⁻¹' T :=
  glue_subset_iff

/-- The glued centre lies in the singular locus of `X` iff every local centre lies in the
singular locus of its window (the local model). -/
theorem support_subset_intrinsicSingularLocus_iff :
    F.support ⊆ intrinsicSingularLocus X.obj ↔
      ∀ i, F.trace i ⊆ intrinsicSingularLocus (F.windowSpace i).obj := by
  rw [F.support_subset_iff]
  refine forall_congr' fun i => ?_
  rw [preimage_intrinsicSingularLocus_of_isOpenImmersion (F.windowMap i)
    (F.windowMap_isOpenImmersion i)]

/-- Reindexing a family (e.g. selecting finitely many of its windows). -/
def reindex {κ : Type*} (σ : κ → ι) : LocalSmoothCentres X κ where
  emb k := F.emb (σ k)
  window k := F.window (σ k)
  centre k := F.centre (σ k)
  isClosedSubmanifold k := F.isClosedSubmanifold (σ k)
  centre_subset k := F.centre_subset (σ k)

theorem compatible_reindex (hc : F.Compatible) {κ : Type*} (σ : κ → ι) :
    (F.reindex σ).Compatible :=
  fun k l y z h hy => hc (σ k) (σ l) y z h hy

theorem support_reindex_subset {κ : Type*} (σ : κ → ι) : (F.reindex σ).support ⊆ F.support := by
  intro x hx
  obtain ⟨k, d, hd, hdx⟩ := (F.reindex σ).mem_support.mp hx
  exact F.mem_support.mpr ⟨σ k, d, hd, hdx⟩

/-- A subfamily whose windows still cover the glued centre has the SAME glued centre. -/
theorem support_reindex_eq (hc : F.Compatible) {κ : Type*} (σ : κ → ι)
    (hcov : F.support ⊆ ⋃ k, range (F.windowMap (σ k)).hom.left.base) :
    (F.reindex σ).support = F.support :=
  (F.reindex σ).support_eq_of_preimage F.support (fun k => F.preimage_support hc (σ k)) hcov

/-- The local trace is an analytic subset of the window. -/
theorem trace_isAnalyticSubset (i : ι) : (F.windowSpace i).IsAnalyticSubset (F.trace i) :=
  isAnalyticSubset_preimage_val _
    (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
      (F.isClosedSubmanifold i))

/-- The local trace is closed in the window. -/
theorem trace_isClosed (i : ι) : IsClosed (F.trace i) :=
  (F.trace_isAnalyticSubset i).isClosed

/-- **Closedness from compact footprints.** If compact subsets `L i` of the window ranges in `X`
form a locally finite family (e.g. finitely many) covering the glued centre, the glued centre
is closed. -/
theorem isClosed_support_of_compact_footprints (hc : F.Compatible) (L : ι → Set X.obj.left)
    (hL : ∀ i, IsCompact (L i)) (hLr : ∀ i, L i ⊆ range (F.windowMap i).hom.left.base)
    (hlf : LocallyFinite L) (hcov : F.support ⊆ ⋃ i, L i) : IsClosed F.support :=
  isClosed_unionImages_of_compact_footprints F.windowMap
    (fun i => F.windowMap_isOpenImmersion i) F.trace hc F.trace_isClosed L hL hLr hlf hcov

/-- The finite case of `isClosed_support_of_compact_footprints`. -/
theorem isClosed_support_of_finite [Finite ι] (hc : F.Compatible) (L : ι → Set X.obj.left)
    (hL : ∀ i, IsCompact (L i)) (hLr : ∀ i, L i ⊆ range (F.windowMap i).hom.left.base)
    (hcov : F.support ⊆ ⋃ i, L i) : IsClosed F.support :=
  F.isClosed_support_of_compact_footprints hc L hL hLr (locallyFinite_of_finite L) hcov

/-- A compatible family with closed glued centre has an ANALYTIC glued centre. -/
theorem isAnalyticSubset_support (hc : F.Compatible) (hcl : IsClosed F.support) :
    X.IsAnalyticSubset F.support :=
  unionImages_isAnalyticSubset_of_isClosed F.windowMap (fun i => F.windowMap_isOpenImmersion i)
    F.trace hc F.trace_isAnalyticSubset hcl

/-- A compatible family whose windows cover `X` has an analytic (hence closed) glued centre. -/
theorem isAnalyticSubset_support_of_cover (hc : F.Compatible)
    (hcover : ∀ x : X.obj.left, ∃ (i : ι) (y : (F.windowSpace i).obj.left),
      (F.windowMap i).hom.left.base y = x) :
    X.IsAnalyticSubset F.support :=
  unionImages_isAnalyticSubset_of_compatible F.windowMap (fun i => F.windowMap_isOpenImmersion i)
    hcover F.trace hc F.trace_isAnalyticSubset

/-- The ordinary local smooth-centre geometry of the glued centre (the input of the smooth-centre
blowup producers). -/
theorem local_smooth_geometry (hc : F.Compatible) (x : X.obj.left) (hx : x ∈ F.support) :
    ∃ (e : LocalEmbedding X) (O : Opens e.ambient) (C : Set O)
      (_hC : IsClosedSubmanifold e.dim C)
      (_hCW : C ⊆ (Subtype.val : O → e.ambient) ⁻¹' e.carrier)
      (d : ((Subtype.val : O → e.ambient) ⁻¹' e.carrier)),
      (givenWindowMorphism e O).hom.left.base d = x ∧
      (givenWindowMorphism e O).hom.left.base ⁻¹' F.support =
        (Subtype.val : ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) → O) ⁻¹' C := by
  obtain ⟨i, d, -, hd⟩ := F.mem_support.mp hx
  exact ⟨F.emb i, F.window i, F.centre i, F.isClosedSubmanifold i, F.centre_subset i, d, hd,
    F.preimage_support hc i⟩

/-- **One global blowup step from compatible local smooth centres.** A compatible family of local
smooth centres whose glued centre is closed and contained in the singular locus gives an actual
blowup of `X` along the glued centre (realized by the original analytic closed subspace), which is
a singular-centre step, surjective and an isomorphism off the glued centre. -/
theorem exists_singularCentreBlowup (hc : F.Compatible) (hcl : IsClosed F.support)
    (hsing : F.support ⊆ intrinsicSingularLocus X.obj) :
    ∃ (hS : X.IsAnalyticSubset F.support) (Y : SourceReducedComplexSpace) (p : Y ⟶ X),
      IsSmoothCentreBlowup p (OriginalAnalyticClosedSubspace.inclusion X F.support hS) ∧
      IsSingularCentreStep p ∧ IsSingularCentreModification p ∧
      Function.Surjective p.hom.left.base ∧ IsIsoOver p F.supportᶜ := by
  have hS := F.isAnalyticSubset_support hc hcl
  have hthin :=
    OriginalSingularContainedCentreThinness.interior_eq_empty_of_subset_intrinsicSingularLocus
      X F.support hsing
  obtain ⟨Y, p, hblow, _hmod, hsurj, hiso⟩ :=
    OriginalLocallySmoothAnalyticCentreBlowup.exists_smoothCentreBlowup_of_local_smooth_centres
      X F.support hS hthin (F.local_smooth_geometry hc)
  have hrange := OriginalAnalyticClosedSubspace.inclusion_range X F.support hS
  have hstep : IsSingularCentreStep p :=
    ⟨_, OriginalAnalyticClosedSubspace.inclusion X F.support hS, hblow, by
      rw [hrange]; exact hsing⟩
  exact ⟨hS, Y, p, hblow, hstep, hstep.isSingularCentreModification, hsurj, hiso⟩

/-- Every blowup along the glued centre (by ANY closed-centre morphism with that range) of a
family in the singular locus is a singular-centre step. -/
theorem isSingularCentreStep_of_blowup (hsing : F.support ⊆ intrinsicSingularLocus X.obj)
    {Y S : SourceReducedComplexSpace} (p : Y ⟶ X) (i : S ⟶ X)
    (hi : range i.hom.left.base = F.support) (hp : IsSmoothCentreBlowup p i) :
    IsSingularCentreStep p :=
  ⟨S, i, hp, by rw [hi]; exact hsing⟩

end LocalSmoothCentres

end

end Hironaka.Analytic.Unibranch.HironakaG11CompatibleAnalyticCover
