import Hironaka.Analytic.Unibranch.HironakaG11CompatibleLevelSets
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.Blowup.BlowupRestrictOpen

/-!
# Compatible smooth centres on MANIFOLD windows (goal G11, route steps 1 and 5)

After the first blowup the windows of the canonical algorithm are no longer open subsets of some
`ℂ^N`: their ambient spaces are blown-up complex manifolds (the stages of `BlowupTower`s, bundled as
`CMfd`), and the windows are open immersions of closed analytic subspaces of them. This file states
the gluing interface for such windows and reduces it to `LocalSmoothCentres` through the charts of
the ambient manifolds:

* `ManifoldWindows X ι`: complex manifolds `M i`, closed analytic `W i ⊆ M i`, open immersions
  `W i ⟶ X`; `ManifoldSmoothCentres X ι` adds closed submanifolds `C i ⊆ W i` of `M i`.
* the gluing calculus (`preimage_support`, `isAnalyticSubset_support`,
  `isClosed_support_of_compact_footprints`, `support_subset_intrinsicSingularLocus_iff`);
* `toLocal`: the chart windows (one for each ambient point), a `LocalSmoothCentres` family with the
  SAME glued centre (`support_toLocal`) and compatible when the manifold family is
  (`compatible_toLocal`), whence one global singular-centre blowup
  (`exists_singularCentreBlowup`);
* `ManifoldWindows.withLevelSets`: centres as level sets of local invariants at a global bound,
  compatible in the overlap form produced by `HironakaG11InvTransport.inv_eq_on_overlap`
  (`withLevelSets_compatible`) — the record-agnostic interface.

Blueprint: `hironaka-g11-resume-compatible-centres.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG11ManifoldWindowCentres

open Hironaka Hironaka.BlowupSequences
  Hironaka HironakaIntrinsicComplexAnalyticRegularLocus
  HironakaResolutionSpaceComplex SourceReducedComplexSpace SmoothCentreModification
  OriginalAnalyticClosedSubspaceSmoothCentres HironakaG11SingularCentreModification
  OriginalAnalyticCover HironakaG11CompatibleAnalyticCover HironakaG11CompatibleLevelSets
  ResolutionDriver BlowupTowers

noncomputable section

/-- The chart trace of a closed submanifold is a closed submanifold of the chart image. -/
theorem isClosedSubmanifold_chartTrace {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] {C : Set M}
    (hC : IsClosedSubmanifold n C) (m : M) :
    IsClosedSubmanifold n (chartTrace (n := n) C m) :=
  MarkedIdealBiholomorphism.isClosedSubmanifold_preimage (chartDiffeo (n := n) m).symm.contMDiff
    (chartDiffeo (n := n) m).contMDiff (chartDiffeo (n := n) m).symm_apply_apply
    (chartDiffeo (n := n) m).apply_symm_apply
    (BlowupRestrictOpen.isClosedSubmanifold_preimage_val hC (chartDomain (n := n) m))

/-- **Manifold windows** of a complex space `X`: for every index, a complex manifold, a closed
analytic subset of it, and an open immersion of the corresponding reduced closed subspace into
`X`. -/
structure ManifoldWindows (X : SourceReducedComplexSpace) (ι : Type*) where
  /-- The dimension of the `i`-th ambient manifold. -/
  dim : ι → ℕ
  /-- The `i`-th ambient manifold. -/
  ambient : ∀ i, CMfd.{0} (dim i)
  /-- The closed analytic subset of the ambient manifold carrying the window. -/
  carrier : ∀ i, Set (ambient i)
  analytic : ∀ i, IsComplexAnalyticSubset (n := dim i) (carrier i)
  /-- The open immersion of the window into `X`. -/
  map : ∀ i, ofClosedAnalytic (carrier i) (analytic i) ⟶ X
  isOpenImmersion : ∀ i, LocallyRingedSpace.IsOpenImmersion (map i).hom.left

/-- **Smooth centres on manifold windows**: closed complex submanifolds of the ambient manifolds,
contained in the window carriers. -/
structure ManifoldSmoothCentres (X : SourceReducedComplexSpace) (ι : Type*)
    extends ManifoldWindows X ι where
  /-- The local centre. -/
  centre : ∀ i, Set (ambient i)
  isClosedSubmanifold : ∀ i, IsClosedSubmanifold (dim i) (centre i)
  centre_subset : ∀ i, centre i ⊆ carrier i

namespace ManifoldSmoothCentres

variable {X : SourceReducedComplexSpace} {ι : Type*} (F : ManifoldSmoothCentres X ι)

/-- The trace of the `i`-th centre on the `i`-th window. -/
abbrev trace (i : ι) : Set (ofClosedAnalytic (F.carrier i) (F.analytic i)).obj.left :=
  (Subtype.val : F.carrier i → F.ambient i) ⁻¹' F.centre i

/-- The local centres agree on overlaps in `X`. -/
def Compatible : Prop :=
  IsCompatible (fun i => (F.map i).hom.left.base) F.trace

/-- The glued global centre. -/
def support : Set X.obj.left :=
  unionImages F.map F.trace

theorem mem_support {x : X.obj.left} :
    x ∈ F.support ↔ ∃ i, ∃ d ∈ F.trace i, (F.map i).hom.left.base d = x :=
  mem_glue

theorem preimage_support (hc : F.Compatible) (i : ι) :
    (F.map i).hom.left.base ⁻¹' F.support = F.trace i :=
  preimage_glue hc i

theorem support_subset_iff {T : Set X.obj.left} :
    F.support ⊆ T ↔ ∀ i, F.trace i ⊆ (F.map i).hom.left.base ⁻¹' T :=
  glue_subset_iff

theorem support_subset_intrinsicSingularLocus_iff :
    F.support ⊆ intrinsicSingularLocus X.obj ↔
      ∀ i, F.trace i ⊆ intrinsicSingularLocus (ofClosedAnalytic (F.carrier i) (F.analytic i)).obj := by
  rw [F.support_subset_iff]
  refine forall_congr' fun i => ?_
  rw [preimage_intrinsicSingularLocus_of_isOpenImmersion (F.map i) (F.isOpenImmersion i)]

theorem trace_isAnalyticSubset (i : ι) :
    (ofClosedAnalytic (F.carrier i) (F.analytic i)).IsAnalyticSubset (F.trace i) :=
  isAnalyticSubset_preimage_val _
    (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
      (F.isClosedSubmanifold i))

theorem trace_isClosed (i : ι) : IsClosed (F.trace i) :=
  (F.trace_isAnalyticSubset i).isClosed

theorem isClosed_support_of_compact_footprints (hc : F.Compatible) (L : ι → Set X.obj.left)
    (hL : ∀ i, IsCompact (L i)) (hLr : ∀ i, L i ⊆ range (F.map i).hom.left.base)
    (hlf : LocallyFinite L) (hcov : F.support ⊆ ⋃ i, L i) : IsClosed F.support :=
  isClosed_unionImages_of_compact_footprints F.map F.isOpenImmersion F.trace hc F.trace_isClosed
    L hL hLr hlf hcov

theorem isClosed_support_of_finite [Finite ι] (hc : F.Compatible) (L : ι → Set X.obj.left)
    (hL : ∀ i, IsCompact (L i)) (hLr : ∀ i, L i ⊆ range (F.map i).hom.left.base)
    (hcov : F.support ⊆ ⋃ i, L i) : IsClosed F.support :=
  F.isClosed_support_of_compact_footprints hc L hL hLr (locallyFinite_of_finite L) hcov

theorem isAnalyticSubset_support (hc : F.Compatible) (hcl : IsClosed F.support) :
    X.IsAnalyticSubset F.support :=
  unionImages_isAnalyticSubset_of_isClosed F.map F.isOpenImmersion F.trace hc
    F.trace_isAnalyticSubset hcl

/-! ### Chart windows -/

/-- The local embedding of `X` given by the chart at `m` of the `i`-th ambient manifold,
followed by the `i`-th window. -/
def chartEmb (i : ι) (m : F.ambient i) : LocalEmbedding X :=
  let e := LocalEmbedding.ofChart (F.carrier i) (F.analytic i) m
  { dim := e.dim
    ambient := e.ambient
    carrier := e.carrier
    analytic := e.analytic
    map := e.map ≫ (F.map i).hom.left
    isOpenImmersion :=
      @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ e.map e.isOpenImmersion
        (F.map i).hom.left (F.isOpenImmersion i)
    overPoint := by
      rw [Category.assoc, Over.w (F.map i).hom]
      exact e.overPoint }

/-- **The chart windows**: one `LocalSmoothCentres` window for every point of every ambient
manifold, with centre the chart trace of the manifold centre. -/
def toLocal : LocalSmoothCentres X (Σ i, F.ambient i) where
  emb a := F.chartEmb a.1 a.2
  window _ := ⊤
  centre a := (Subtype.val : (⊤ : Opens (F.chartEmb a.1 a.2).ambient) → _) ⁻¹'
    chartTrace (n := F.dim a.1) (F.centre a.1) a.2
  isClosedSubmanifold a :=
    BlowupRestrictOpen.isClosedSubmanifold_preimage_val
      (isClosedSubmanifold_chartTrace (F.isClosedSubmanifold a.1) a.2) ⊤
  centre_subset a := fun _ hu => F.centre_subset a.1 hu

/-- The point of the manifold window seen by a point of a chart window. -/
def chartPoint (a : Σ i, F.ambient i) (d : F.toLocal.windowCarrier a) :
    (ofClosedAnalytic (F.carrier a.1) (F.analytic a.1)).obj.left :=
  (LocalEmbedding.ofChart (F.carrier a.1) (F.analytic a.1) a.2).toPoint ⟨d.val.val, d.prop⟩

theorem toLocal_windowMap_apply (a : Σ i, F.ambient i) (d : F.toLocal.windowCarrier a) :
    (F.toLocal.windowMap a).hom.left.base d = (F.map a.1).hom.left.base (F.chartPoint a d) :=
  rfl

theorem mem_toLocal_trace (a : Σ i, F.ambient i) (d : F.toLocal.windowCarrier a) :
    d ∈ F.toLocal.trace a ↔ F.chartPoint a d ∈ F.trace a.1 :=
  Iff.rfl

theorem compatible_toLocal (hc : F.Compatible) : F.toLocal.Compatible :=
  fun a b y z hyz hy => hc a.1 b.1 (F.chartPoint a y) (F.chartPoint b z) hyz hy

/-- Every window point is seen by its own chart window. -/
theorem exists_chartPoint_eq (i : ι) (c : (ofClosedAnalytic (F.carrier i) (F.analytic i)).obj.left) :
    ∃ d : F.toLocal.windowCarrier ⟨i, c.val⟩, F.chartPoint ⟨i, c.val⟩ d = c := by
  let p : chartDomain (n := F.dim i) c.val := ⟨c.val, mem_chartDomain (n := F.dim i) c.val⟩
  have hp : (chartDiffeo (n := F.dim i) c.val).symm (chartDiffeo (n := F.dim i) c.val p) = p :=
    (chartDiffeo (n := F.dim i) c.val).symm_apply_apply p
  have hmem : chartDiffeo (n := F.dim i) c.val p ∈ chartTrace (n := F.dim i) (F.carrier i) c.val := by
    change (((chartDiffeo (n := F.dim i) c.val).symm (chartDiffeo (n := F.dim i) c.val p) :
      chartDomain (n := F.dim i) c.val) : F.ambient i) ∈ F.carrier i
    rw [hp]
    exact c.property
  refine ⟨⟨⟨chartDiffeo (n := F.dim i) c.val p, trivial⟩, hmem⟩, ?_⟩
  apply Subtype.ext
  change (((chartDiffeo (n := F.dim i) c.val).symm (chartDiffeo (n := F.dim i) c.val p) :
    chartDomain (n := F.dim i) c.val) : F.ambient i) = c.val
  rw [hp]

/-- **The chart windows have the SAME glued centre.** -/
theorem support_toLocal (hc : F.Compatible) : F.toLocal.support = F.support := by
  apply F.toLocal.support_eq_of_preimage F.support
  · intro a
    ext d
    exact Set.ext_iff.mp (F.preimage_support hc a.1) (F.chartPoint a d)
  · intro x hx
    obtain ⟨i, c, -, rfl⟩ := F.mem_support.mp hx
    obtain ⟨d, hd⟩ := F.exists_chartPoint_eq i c
    refine mem_iUnion.mpr ⟨⟨i, c.val⟩, d, ?_⟩
    rw [toLocal_windowMap_apply, hd]

/-- **One global blowup step from compatible smooth centres on manifold windows.** -/
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
  have hGeom := F.toLocal.local_smooth_geometry (F.compatible_toLocal hc)
  rw [F.support_toLocal hc] at hGeom
  obtain ⟨Y, p, hblow, _hmod, hsurj, hiso⟩ :=
    OriginalLocallySmoothAnalyticCentreBlowup.exists_smoothCentreBlowup_of_local_smooth_centres
      X F.support hS hthin hGeom
  have hrange := OriginalAnalyticClosedSubspace.inclusion_range X F.support hS
  have hstep : IsSingularCentreStep p :=
    ⟨_, OriginalAnalyticClosedSubspace.inclusion X F.support hS, hblow, by
      rw [hrange]; exact hsing⟩
  exact ⟨hS, Y, p, hblow, hstep, hstep.isSingularCentreModification, hsurj, hiso⟩

/-- Centres given as level sets of local invariants are compatible in the overlap form. -/
theorem compatible_of_levelSet_overlap {Λ : Type*} (D : ∀ i, Set (F.ambient i))
    (g : ∀ i, F.ambient i → Λ) (lam : Λ) (hcentre : ∀ i, F.centre i = D i ∩ g i ⁻¹' {lam})
    (hDg : ∀ i k (y : F.carrier i) (z : F.carrier k),
      (F.map i).hom.left.base y = (F.map k).hom.left.base z →
        y.val ∈ D i → z.val ∈ D k ∧ g k z.val = g i y.val) :
    F.Compatible := by
  have h := isCompatible_levelSet_of_overlap (f := fun i => (F.map i).hom.left.base)
    (D := fun i => (Subtype.val : F.carrier i → F.ambient i) ⁻¹' D i)
    (fun i (y : F.carrier i) => g i y.val) hDg {lam}
  intro i k y z hyz hy
  have hy' : y.val ∈ D i ∩ g i ⁻¹' {lam} := by
    rw [← hcentre i]
    exact hy
  have hz := h i k y z hyz hy'
  change z.val ∈ F.centre k
  rw [hcentre k]
  exact hz

end ManifoldSmoothCentres

/-- **Centres as level sets at a global bound on manifold windows** (record-agnostic): local
domains `D i ⊆ W i` (e.g. cosupports of the window records along their towers), local invariants
`g i` bounded by `λ` on `D i` whose maximum loci are closed submanifolds (e.g. the canonical
centres); the centres are the `λ`-level sets. -/
def ManifoldWindows.withLevelSets {X : SourceReducedComplexSpace} {ι : Type*}
    {Λ : Type*} [LinearOrder Λ] (W : ManifoldWindows X ι) (D : ∀ i, Set (W.ambient i))
    (g : ∀ i, W.ambient i → Λ) (lam : Λ) (hlam : ∀ i, ∀ y ∈ D i, g i y ≤ lam)
    (hmax : ∀ i, IsClosedSubmanifold (W.dim i) (maxLocus (g i) (D i)))
    (hDW : ∀ i, D i ⊆ W.carrier i) : ManifoldSmoothCentres X ι where
  toManifoldWindows := W
  centre i := D i ∩ g i ⁻¹' {lam}
  isClosedSubmanifold i := isClosedSubmanifold_levelSet (D i) (g i) lam (hlam i) (hmax i)
  centre_subset i := inter_subset_left.trans (hDW i)

/-- **The level-set centres are compatible** when the domains and values agree on overlaps of the
windows in `X`, in the overlap form of the transport lemmas. -/
theorem ManifoldWindows.withLevelSets_compatible {X : SourceReducedComplexSpace} {ι : Type*}
    {Λ : Type*} [LinearOrder Λ] (W : ManifoldWindows X ι) (D : ∀ i, Set (W.ambient i))
    (g : ∀ i, W.ambient i → Λ) (lam : Λ) (hlam : ∀ i, ∀ y ∈ D i, g i y ≤ lam)
    (hmax : ∀ i, IsClosedSubmanifold (W.dim i) (maxLocus (g i) (D i)))
    (hDW : ∀ i, D i ⊆ W.carrier i)
    (hDg : ∀ i k (y : W.carrier i) (z : W.carrier k),
      (W.map i).hom.left.base y = (W.map k).hom.left.base z →
        y.val ∈ D i → z.val ∈ D k ∧ g k z.val = g i y.val) :
    (W.withLevelSets D g lam hlam hmax hDW).Compatible :=
  (W.withLevelSets D g lam hlam hmax hDW).compatible_of_levelSet_overlap D g lam
    (fun _ => rfl) hDg

theorem ManifoldWindows.withLevelSets_centre_subset_maxLocus {X : SourceReducedComplexSpace}
    {ι : Type*} {Λ : Type*} [LinearOrder Λ] (W : ManifoldWindows X ι)
    (D : ∀ i, Set (W.ambient i)) (g : ∀ i, W.ambient i → Λ) (lam : Λ)
    (hlam : ∀ i, ∀ y ∈ D i, g i y ≤ lam)
    (hmax : ∀ i, IsClosedSubmanifold (W.dim i) (maxLocus (g i) (D i)))
    (hDW : ∀ i, D i ⊆ W.carrier i) (i : ι) :
    (W.withLevelSets D g lam hlam hmax hDW).centre i ⊆ maxLocus (g i) (D i) :=
  levelSet_subset_maxLocus (D i) (g i) lam (hlam i)

end

end Hironaka.Analytic.Unibranch.HironakaG11ManifoldWindowCentres
