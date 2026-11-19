import Hironaka.Analytic.Unibranch.HironakaG11BlowupLocality
import Hironaka.Analytic.Unibranch.HironakaG11ManifoldWindowCentres
import Hironaka.Analytic.Unibranch.HironakaG11GluedCentreIteration

/-!
# Window towers of the glued G11 sequence (goal G11, route step 5)

The global G11 sequence blows up glued centres; by the locality of blowups
(`HironakaG11BlowupLocality`) each window of the base is followed by a window of every later
stage, whose ambient manifold is blown up along the local centre and whose carrier is the strict
transform. This file states that step on manifold windows and turns terminating window towers
into global termination:

* `subset_closure_diff_iff`, `interior_eq_empty_of_subset_closure_diff`: thin traces;
  `ManifoldSmoothCentres.carrier_subset_closure_diff`: centres in the singular locus have thin
  traces on their windows (the density hypothesis of the strict-transform blowup).
* `ManifoldSmoothCentres.exists_singularCentreBlowup_windows`: a compatible family of smooth centres
  on manifold windows, with closed glued centre in the singular locus, has ONE global
  singular-centre blowup `p : Y ⟶ X` and, for every window `i`, a blowup `π i : Z i → M i` of its
  ambient manifold along its centre and an open immersion `L i` of the strict transform of the
  window carrier into `Y` with `L i ≫ p = (strict transform projection) ≫ (window i)` and
  `range (L i) = p⁻¹ (range (window i))`; `blowupWindows` bundles them as `ManifoldWindows Y ι`,
  which cover `Y` when the old windows cover `X` (`blowupWindows_cover`).
* `range_eq_preimage_towerComp`, `preimage_subset_regular_of_isSmooth`,
  **`exists_isSmooth_of_window_towers`**, `hasSingularCentreResolution_of_window_towers`: if the
  first windows cover the compact base and every window tower reaches a smooth stage (e.g. a stage
  whose carrier is a closed submanifold, `isSmooth_window_of_isClosedSubmanifold`), some stage of
  the global tower is smooth.

The choice of the centres (the canonical invariant, lane G11B) is NOT made here; nothing proves
or assumes G11. Blueprint: `hironaka-g11-resume-window-towers.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG11WindowTowers

open Hironaka Hironaka.BlowupSequences
  Hironaka HironakaIntrinsicComplexAnalyticRegularLocus
  SourceReducedComplexSpace SmoothCentreModification OriginalIntrinsicSingularLocus
  HironakaG11SingularCentreModification HironakaG11CompatibleAnalyticCover
  HironakaG11ManifoldWindowCentres HironakaG11BlowupLocality HironakaG11GluedCentreIteration
  BlowupTowers EmbeddedBlowup

noncomputable section

/-! ### Thin traces -/

section Thin

variable {M : Type*} [TopologicalSpace M] {W C : Set M}

/-- A subset `C` of `W` has a thin trace on `W` iff `W` lies in the closure of `W \ C`. -/
theorem subset_closure_diff_iff :
    W ⊆ closure (W \ C) ↔ interior ((Subtype.val : W → M) ⁻¹' C) = ∅ := by
  rw [interior_eq_empty_iff_dense_compl, dense_iff_closure_eq, eq_univ_iff_forall]
  have himage : (Subtype.val : W → M) '' (((Subtype.val : W → M) ⁻¹' C)ᶜ) = W \ C := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · intro hx
      exact ⟨⟨x, hx.1⟩, hx.2, rfl⟩
  constructor
  · intro h w
    rw [closure_subtype, himage]
    exact h w.property
  · intro h x hx
    have hw := h ⟨x, hx⟩
    rw [closure_subtype, himage] at hw
    exact hw

/-- A centre with thin trace on `W` and contained in `W` has empty interior. -/
theorem interior_eq_empty_of_subset_closure_diff (hCW : C ⊆ W) (h : W ⊆ closure (W \ C)) :
    interior C = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hxc := h (hCW (interior_subset hx))
  obtain ⟨y, hyU, hyW, hyC⟩ := mem_closure_iff.mp hxc (interior C) isOpen_interior hx
  exact hyC (interior_subset hyU)

end Thin

/-! ### One glued step on manifold windows, with the blown-up windows -/

namespace ManifoldSmoothCentres

variable {X : SourceReducedComplexSpace} {ι : Type*} (F : ManifoldSmoothCentres X ι)

/-- Centres in the singular locus have thin traces on their windows. -/
theorem carrier_subset_closure_diff (hsing : F.support ⊆ intrinsicSingularLocus X.obj) (i : ι) :
    F.carrier i ⊆ closure (F.carrier i \ F.centre i) := by
  rw [subset_closure_diff_iff]
  exact OriginalSingularContainedCentreThinness.interior_eq_empty_of_subset_intrinsicSingularLocus
    _ (F.trace i) ((F.support_subset_intrinsicSingularLocus_iff.mp hsing) i)

theorem interior_centre_eq_empty (hsing : F.support ⊆ intrinsicSingularLocus X.obj) (i : ι) :
    interior (F.centre i) = ∅ :=
  interior_eq_empty_of_subset_closure_diff (F.centre_subset i) (carrier_subset_closure_diff F hsing i)

/-- **The blown-up windows.** Given blowups `π i : Z i → M i` of the window ambients along the local
centres and open immersions `L i` of the strict transforms of the window carriers into `Y`, the
manifold windows of `Y`. -/
def blowupWindows {Y : SourceReducedComplexSpace} (Z : ∀ i, CMfd.{0} (F.dim i))
    (π : ∀ i, Z i → F.ambient i) (hπ : ∀ i, IsBlowupAlong (F.dim i) (F.centre i) (π i))
    (L : ∀ i, ofClosedAnalytic (strictTransform (F.dim i) (π i) (F.carrier i))
      (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
        (hπ i) (F.analytic i)) ⟶ Y)
    (hL : ∀ i, LocallyRingedSpace.IsOpenImmersion (L i).hom.left) : ManifoldWindows Y ι where
  dim := F.dim
  ambient := Z
  carrier i := strictTransform (F.dim i) (π i) (F.carrier i)
  analytic i := HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
    (hπ i) (F.analytic i)
  map := L
  isOpenImmersion := hL

/-- **One global singular-centre blowup together with its blown-up windows.** A compatible family
of smooth centres on manifold windows, with closed glued centre in the singular locus, has a global
blowup `p : Y ⟶ X` along the glued centre (a singular-centre step) such that, for every window,
the blowup `π i : Z i → M i` of its ambient manifold along its local centre and the strict
transform of the window carrier give an open immersion `L i` into `Y` with
`L i ≫ p = (strict transform projection) ≫ (window i)` and range the preimage of the window. -/
theorem exists_singularCentreBlowup_windows (hc : F.Compatible) (hcl : IsClosed F.support)
    (hsing : F.support ⊆ intrinsicSingularLocus X.obj) :
    ∃ (hS : X.IsAnalyticSubset F.support) (Y : SourceReducedComplexSpace) (p : Y ⟶ X),
      IsSmoothCentreBlowup p (OriginalAnalyticClosedSubspace.inclusion X F.support hS) ∧
      IsSingularCentreStep p ∧ IsSingularCentreModification p ∧
      Function.Surjective p.hom.left.base ∧ IsIsoOver p F.supportᶜ ∧
      ∃ (Z : ∀ i, CMfd.{0} (F.dim i)) (π : ∀ i, Z i → F.ambient i)
        (hπ : ∀ i, IsBlowupAlong (F.dim i) (F.centre i) (π i))
        (L : ∀ i, ofClosedAnalytic (strictTransform (F.dim i) (π i) (F.carrier i))
          (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
            (hπ i) (F.analytic i)) ⟶ Y),
        ∀ i, LocallyRingedSpace.IsOpenImmersion (L i).hom.left ∧
          L i ≫ p = strictTransformMorphism (hπ i) (F.analytic i) ≫ F.map i ∧
          range (L i).hom.left.base = p.hom.left.base ⁻¹' range (F.map i).hom.left.base := by
  obtain ⟨hS, Y, p, hblow, hstep, hmod, hsurj, hiso⟩ := F.exists_singularCentreBlowup hc hcl hsing
  refine ⟨hS, Y, p, hblow, hstep, hmod, hsurj, hiso, ?_⟩
  have hex : ∀ i, ∃ (Z : CMfd.{0} (F.dim i)) (π : Z → F.ambient i),
      IsBlowupAlong (F.dim i) (F.centre i) π := fun i =>
    ResolutionDriver.exists_blowup (F.centre i) (F.isClosedSubmanifold i)
      (interior_centre_eq_empty F hsing i)
  choose Z π hπ using hex
  have hrange := OriginalAnalyticClosedSubspace.inclusion_range X F.support hS
  have hloc : ∀ i, ∃ L : ofClosedAnalytic (strictTransform (F.dim i) (π i) (F.carrier i))
      (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
        (hπ i) (F.analytic i)) ⟶ Y,
      LocallyRingedSpace.IsOpenImmersion L.hom.left ∧
        L ≫ p = strictTransformMorphism (hπ i) (F.analytic i) ≫ F.map i ∧
        range L.hom.left.base = p.hom.left.base ⁻¹' range (F.map i).hom.left.base := by
    intro i
    have hW := strictTransformMorphism_isIdealBlowup (hπ i) (F.analytic i) (F.centre_subset i)
      (carrier_subset_closure_diff F hsing i)
    have htr : (F.map i).hom.left.base ⁻¹'
        range (OriginalAnalyticClosedSubspace.inclusion X F.support hS).hom.left.base =
          (Subtype.val : F.carrier i → F.ambient i) ⁻¹' F.centre i := by
      rw [hrange]
      exact F.preimage_support hc i
    have hW' : IsIdealBlowup (strictTransformMorphism (hπ i) (F.analytic i))
        (HironakaIntrinsicReducedCentreIdealSheaf.intrinsicReducedCentreIdealModule
          (ofClosedAnalytic (F.carrier i) (F.analytic i)).obj.left ((F.map i).hom.left.base ⁻¹'
            range (OriginalAnalyticClosedSubspace.inclusion X F.support hS).hom.left.base))
        (HironakaIntrinsicReducedCentreIdealSheaf.intrinsicReducedCentreIdealInclusion
          (ofClosedAnalytic (F.carrier i) (F.analytic i)).obj.left ((F.map i).hom.left.base ⁻¹'
            range (OriginalAnalyticClosedSubspace.inclusion X F.support hS).hom.left.base)) := by
      rw [htr]
      exact hW
    obtain ⟨L, ⟨hL, -⟩, hLo, hLr⟩ :=
      exists_openImmersion_of_isSmoothCentreBlowup hblow (F.isOpenImmersion i) hW'
    exact ⟨L, hLo, hL, hLr⟩
  choose L hL using hloc
  exact ⟨Z, π, hπ, L, hL⟩

/-- The blown-up windows cover everything over the old windows. -/
theorem blowupWindows_cover {Y : SourceReducedComplexSpace} {p : Y ⟶ X}
    (Z : ∀ i, CMfd.{0} (F.dim i)) (π : ∀ i, Z i → F.ambient i)
    (hπ : ∀ i, IsBlowupAlong (F.dim i) (F.centre i) (π i))
    (L : ∀ i, ofClosedAnalytic (strictTransform (F.dim i) (π i) (F.carrier i))
      (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
        (hπ i) (F.analytic i)) ⟶ Y)
    (hL : ∀ i, LocallyRingedSpace.IsOpenImmersion (L i).hom.left)
    (hLr : ∀ i, range (L i).hom.left.base = p.hom.left.base ⁻¹' range (F.map i).hom.left.base)
    (hcover : ∀ x : X.obj.left, ∃ i, x ∈ range (F.map i).hom.left.base) (y : Y.obj.left) :
    ∃ i, y ∈ range ((blowupWindows F Z π hπ L hL).map i).hom.left.base := by
  obtain ⟨i, hi⟩ := hcover (p.hom.left.base y)
  refine ⟨i, ?_⟩
  change y ∈ range (L i).hom.left.base
  rw [hLr i]
  exact hi

/-- A manifold window whose carrier is a closed submanifold is smooth (the form in which local
embedded resolutions of the window towers feed `exists_isSmooth_of_window_towers`). -/
theorem isSmooth_window_of_isClosedSubmanifold {Y : SourceReducedComplexSpace} {ι : Type*}
    (G : ManifoldWindows Y ι) (i : ι) (h : IsClosedSubmanifold (G.dim i) (G.carrier i)) :
    (ofClosedAnalytic (G.carrier i) (G.analytic i)).IsSmooth :=
  isSmooth_ofClosedAnalytic_of_isClosedSubmanifold h

end ManifoldSmoothCentres

/-! ### Window towers and local termination -/

section Tower

variable {X : ℕ → SourceReducedComplexSpace} (p : ∀ k, X (k + 1) ⟶ X k)

/-- Windows whose ranges are successive preimages are the preimages of the first window under the
composites of the tower. -/
theorem range_eq_preimage_towerComp {W : ℕ → SourceReducedComplexSpace} (j : ∀ k, W k ⟶ X k)
    (hr : ∀ k, range (j (k + 1)).hom.left.base =
      (p k).hom.left.base ⁻¹' range (j k).hom.left.base) :
    ∀ k, range (j k).hom.left.base =
      (towerComp p k).hom.left.base ⁻¹' range (j 0).hom.left.base
  | 0 => rfl
  | k + 1 => by
    rw [hr k, range_eq_preimage_towerComp j hr k]
    rfl

/-- **A smooth window stage gives regularity over the first window.** -/
theorem preimage_subset_regular_of_isSmooth {W : ℕ → SourceReducedComplexSpace}
    (j : ∀ k, W k ⟶ X k) (hj : ∀ k, LocallyRingedSpace.IsOpenImmersion (j k).hom.left)
    (hr : ∀ k, range (j (k + 1)).hom.left.base =
      (p k).hom.left.base ⁻¹' range (j k).hom.left.base)
    {N : ℕ} (hN : (W N).IsSmooth) :
    (towerComp p N).hom.left.base ⁻¹' range (j 0).hom.left.base ⊆
      intrinsicRegularLocus (X N).obj := by
  rw [← range_eq_preimage_towerComp p j hr N]
  rintro _ ⟨w, rfl⟩
  have h := HironakaG11IntrinsicRegularOpenImmersion.preimage_intrinsicRegularLocus (j N).hom.left
    (hj N) (Over.w (j N).hom)
  have hw : w ∈ intrinsicRegularLocus (W N).obj := hN w
  rw [← h] at hw
  exact hw

/-- **Local termination from window towers.** Let `p` be a tower of singular-centre modifications
of a compact space, and let windows `j i k : W i k ⟶ X k` (open immersions) form towers over it
(`range (j i (k+1)) = p_k⁻¹ (range (j i k))`, e.g. the blown-up windows of
`exists_singularCentreBlowup_windows`). If the first windows cover `X 0` and every window tower
reaches a smooth stage, some stage of the tower is smooth. -/
theorem exists_isSmooth_of_window_towers [CompactSpace (X 0).obj.left]
    (hp : ∀ k, IsSingularCentreModification (p k)) {ι : Type*}
    {W : ι → ℕ → SourceReducedComplexSpace} (j : ∀ i k, W i k ⟶ X k)
    (hj : ∀ i k, LocallyRingedSpace.IsOpenImmersion (j i k).hom.left)
    (hr : ∀ i k, range (j i (k + 1)).hom.left.base =
      (p k).hom.left.base ⁻¹' range (j i k).hom.left.base)
    (hcover : ∀ x : (X 0).obj.left, ∃ i, x ∈ range (j i 0).hom.left.base)
    (hterm : ∀ i, ∃ N, (W i N).IsSmooth) :
    ∃ N : ℕ, (X N).IsSmooth := by
  apply exists_isSmooth_of_local_termination hp
  intro x
  obtain ⟨i, hi⟩ := hcover x
  obtain ⟨N, hN⟩ := hterm i
  exact ⟨range (j i 0).hom.left.base, (hj i 0).base_open.isOpen_range.mem_nhds hi, N,
    preimage_subset_regular_of_isSmooth p (j i) (hj i) (hr i) hN⟩

/-- The G11 conclusion from terminating window towers. -/
theorem hasSingularCentreResolution_of_window_towers [CompactSpace (X 0).obj.left]
    (hp : ∀ k, IsSingularCentreModification (p k)) {ι : Type*}
    {W : ι → ℕ → SourceReducedComplexSpace} (j : ∀ i k, W i k ⟶ X k)
    (hj : ∀ i k, LocallyRingedSpace.IsOpenImmersion (j i k).hom.left)
    (hr : ∀ i k, range (j i (k + 1)).hom.left.base =
      (p k).hom.left.base ⁻¹' range (j i k).hom.left.base)
    (hcover : ∀ x : (X 0).obj.left, ∃ i, x ∈ range (j i 0).hom.left.base)
    (hterm : ∀ i, ∃ N, (W i N).IsSmooth) :
    HasSingularCentreResolution (X 0) := by
  obtain ⟨N, hN⟩ := exists_isSmooth_of_window_towers p hp j hj hr hcover hterm
  exact ⟨X N, towerComp p N, isSingularCentreModification_towerComp hp N, hN⟩

end Tower

end

end Hironaka.Analytic.Unibranch.HironakaG11WindowTowers
