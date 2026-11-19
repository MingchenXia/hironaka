import Hironaka.Analytic.Unibranch.ComplexSpaceAnalyticSubsets

/-!
# Original analytic and thin sets on actual open-immersion covers

The SAME global union of actual local subset images has exactly the original
local preimages when the genuine ranges are disjoint. Full original local
embeddings/scalars derive intrinsic analytic descent; true open-map interior
identities derive thinness. No finite decomposition or global PB packet.
Blueprint: `original-analytic-cover.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology

namespace Hironaka.Analytic.Unibranch.OriginalAnalyticCover

open SourceReducedComplexSpace

noncomputable section

variable {ι : Type*} {X : SourceReducedComplexSpace} {Y : ι → SourceReducedComplexSpace}

/-- Intrinsic analyticity of the SAME subset is local for genuine ORIGINAL
open-immersion covers, with full local sheaf maps and scalar triangles. -/
theorem isAnalyticSubset_of_openImmersion_cover
    (j : ∀ i, Y i ⟶ X)
    (hj : ∀ i, LocallyRingedSpace.IsOpenImmersion (j i).hom.left)
    (hcover : ∀ x : X.obj.left, ∃ (i : ι) (y : (Y i).obj.left), (j i).hom.left.base y = x)
    (Z : Set X.obj.left) (hZ : ∀ i, (Y i).IsAnalyticSubset ((j i).hom.left.base ⁻¹' Z)) :
    X.IsAnalyticSubset Z := by
  intro x
  obtain ⟨i, y, hy⟩ := hcover x
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

/-- Literal original empty-interior conditions descend on actual original
open-immersion covers, without a connectedness or analytic-set assumption. -/
theorem interior_eq_empty_of_openImmersion_cover
    (j : ∀ i, Y i ⟶ X)
    (hj : ∀ i, LocallyRingedSpace.IsOpenImmersion (j i).hom.left)
    (hcover : ∀ x : X.obj.left, ∃ (i : ι) (y : (Y i).obj.left), (j i).hom.left.base y = x)
    (Z : Set X.obj.left) (hZ : ∀ i, interior ((j i).hom.left.base ⁻¹' Z) = ∅) :
    interior Z = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨i, y, hy⟩ := hcover x
  have heq : (j i).hom.left.base ⁻¹' interior Z =
      interior ((j i).hom.left.base ⁻¹' Z) :=
    (hj i).base_open.isOpenMap.preimage_interior_eq_interior_preimage
      (j i).hom.left.base.hom.continuous Z
  have hm : y ∈ (j i).hom.left.base ⁻¹' interior Z := by
    change (j i).hom.left.base y ∈ interior Z
    rwa [hy]
  rw [heq, hZ i] at hm
  exact hm

/-- The SAME actual union of original local subset images. -/
def unionImages (j : ∀ i, Y i ⟶ X) (A : ∀ i, Set (Y i).obj.left) : Set X.obj.left :=
  ⋃ i, (j i).hom.left.base '' A i

/-- Disjoint actual open-immersion ranges INTERNALLY derive the literal local
trace of the SAME global union; no desired trace equality is supplied. -/
theorem preimage_unionImages_eq
    (j : ∀ i, Y i ⟶ X)
    (hj : ∀ i, LocallyRingedSpace.IsOpenImmersion (j i).hom.left)
    (hdisj : Pairwise (fun i k => Disjoint (range (j i).hom.left.base) (range (j k).hom.left.base)))
    (A : ∀ i, Set (Y i).obj.left) (i : ι) :
    (j i).hom.left.base ⁻¹' unionImages j A = A i := by
  ext y
  constructor
  · intro hy
    obtain ⟨k, z, hz, hzy⟩ := mem_iUnion.mp hy
    by_cases hki : k = i
    · subst k
      have hzy' : z = y := (hj i).base_open.injective hzy
      exact hzy' ▸ hz
    · exact (Set.disjoint_left.mp (hdisj hki) ⟨z, hzy⟩ ⟨y, rfl⟩).elim
  · intro hy
    exact mem_iUnion.mpr ⟨i, y, hy, rfl⟩

/-- Actual local original analytic sets give one global ORIGINAL analytic set
with precisely those literal preimages on the actual disjoint cover. -/
theorem unionImages_isAnalyticSubset
    (j : ∀ i, Y i ⟶ X)
    (hj : ∀ i, LocallyRingedSpace.IsOpenImmersion (j i).hom.left)
    (hcover : ∀ x : X.obj.left, ∃ (i : ι) (y : (Y i).obj.left), (j i).hom.left.base y = x)
    (hdisj : Pairwise (fun i k => Disjoint (range (j i).hom.left.base) (range (j k).hom.left.base)))
    (A : ∀ i, Set (Y i).obj.left) (hA : ∀ i, (Y i).IsAnalyticSubset (A i)) :
    X.IsAnalyticSubset (unionImages j A) := by
  apply isAnalyticSubset_of_openImmersion_cover j hj hcover
  intro i
  rw [preimage_unionImages_eq j hj hdisj A i]
  exact hA i

/-- The SAME global union of actual local thin sets is thin on the original
space; no finite indexing or replacement exceptional subset is required. -/
theorem unionImages_interior_eq_empty
    (j : ∀ i, Y i ⟶ X)
    (hj : ∀ i, LocallyRingedSpace.IsOpenImmersion (j i).hom.left)
    (hcover : ∀ x : X.obj.left, ∃ (i : ι) (y : (Y i).obj.left), (j i).hom.left.base y = x)
    (hdisj : Pairwise (fun i k => Disjoint (range (j i).hom.left.base) (range (j k).hom.left.base)))
    (A : ∀ i, Set (Y i).obj.left) (hA : ∀ i, interior (A i) = ∅) :
    interior (unionImages j A) = ∅ := by
  apply interior_eq_empty_of_openImmersion_cover j hj hcover
  intro i
  rw [preimage_unionImages_eq j hj hdisj A i]
  exact hA i

end

end Hironaka.Analytic.Unibranch.OriginalAnalyticCover
