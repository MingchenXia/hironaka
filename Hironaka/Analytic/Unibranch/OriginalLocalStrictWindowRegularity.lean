import Hironaka.Analytic.Unibranch.OriginalLocalStrictWindowRestriction
import Hironaka.Analytic.Unibranch.HironakaG10ChowStrictTransformCalculus
import Hironaka.Resolution.HironakaG11IntrinsicRegularOpenImmersion

/-!
# Actual original regular inverses on the same literal strict refinements

An actual native open restriction transports a full prescribed inverse. For
the literal restricted strict tower, its square and exact endpoint range
are DERIVED by the preceding module, never supplied as comparison inputs.
Density then proves the SAME actual refined projection is a resolution.

Blueprint FIRST: `original-local-strict-window-regularity.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.OriginalLocalStrictWindowRegularity

noncomputable section

open Hironaka Hironaka.BlowupSequences
  Hironaka SourceReducedComplexSpace
  HironakaIntrinsicComplexAnalyticRegularLocus HironakaG11IntrinsicRegularOpenImmersion
  HironakaResolutionSpace HironakaResolutionSpaceComplex BlowupTowers
  OriginalLocalCanonicalStrictResolution OriginalLocalStrictWindowRestriction

private theorem pullback_snd_range {L A Y : LocallyRingedSpace}
    (g : L ⟶ Y) (a : A ⟶ Y) [LocallyRingedSpace.IsOpenImmersion g] :
    range (pullback.snd g a).base = a.base ⁻¹' range g.base := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨(pullback.fst g a).base z, ?_⟩
    exact congrArg (fun F => F.base z) (pullback.condition (f := g) (g := a))
  · rintro ⟨l, hl⟩
    let F := LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forget CommRingCat
    let E := (TopCat.pullbackConeIsLimit g.base a.base).conePointUniqueUpToIso
      (isLimitOfHasPullbackOfPreservesLimit F g a)
    let z : (pullback g a : LocallyRingedSpace) := E.hom ⟨⟨l, y⟩, hl⟩
    refine ⟨z, ?_⟩
    change ((E.hom ≫ F.map (pullback.snd g a)) ⟨⟨l, y⟩, hl⟩) = y
    erw [IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.right]
    rfl

/-- Actual full native open restrictions transport a prescribed inverse.
The actual strict-window consumer below proves its square/range internally. -/
theorem isIsoOver_of_open_square {Y V A B : SourceReducedComplexSpace}
    (p : Y ⟶ V) (q : A ⟶ B) (a : A ⟶ Y) (b : B ⟶ V)
    (ha : LocallyRingedSpace.IsOpenImmersion a.hom.left)
    (hb : LocallyRingedSpace.IsOpenImmersion b.hom.left)
    (hsq : q ≫ b = a ≫ p)
    (hrange : range a.hom.left.base = p.hom.left.base ⁻¹' range b.hom.left.base)
    (G : Set V.obj.left) (hp : IsIsoOver p G) :
    IsIsoOver q (b.hom.left.base ⁻¹' G) := by
  obtain ⟨L, g, hg, hgr, hgp, hgpr⟩ := hp
  let : LocallyRingedSpace.IsOpenImmersion g := hg
  let : LocallyRingedSpace.IsOpenImmersion a.hom.left := ha
  let : LocallyRingedSpace.IsOpenImmersion b.hom.left := hb
  let : LocallyRingedSpace.IsOpenImmersion (g ≫ p.hom.left) := hgp
  let u := pullback.snd g a.hom.left
  let v := pullback.fst g a.hom.left
  have hu : LocallyRingedSpace.IsOpenImmersion u := by dsimp only [u]; infer_instance
  have hv : LocallyRingedSpace.IsOpenImmersion v := by dsimp only [v]; infer_instance
  have hs : q.hom.left ≫ b.hom.left = a.hom.left ≫ p.hom.left :=
    congrArg (fun F => F.hom.left) hsq
  have hcomm : (u ≫ q.hom.left) ≫ b.hom.left = v ≫ (g ≫ p.hom.left) := by
    rw [Category.assoc, hs, ← Category.assoc, ← pullback.condition, Category.assoc]
  have hcomp : LocallyRingedSpace.IsOpenImmersion ((u ≫ q.hom.left) ≫ b.hom.left) := by
    rw [hcomm]
    exact @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ v hv _ hgp
  let : LocallyRingedSpace.IsOpenImmersion ((u ≫ q.hom.left) ≫ b.hom.left) := hcomp
  have huq : LocallyRingedSpace.IsOpenImmersion (u ≫ q.hom.left) :=
    HironakaG10ChowStrictTransformCalculus.isOpenImmersion_of_comp _ b.hom.left
  have hur : range u.base = q.hom.left.base ⁻¹' (b.hom.left.base ⁻¹' G) := by
    rw [pullback_snd_range, hgr]
    ext y
    exact iff_of_eq (congrArg (fun F => F.base y ∈ G) hs).symm
  refine ⟨pullback g a.hom.left, u, hu, hur, huq, ?_⟩
  apply subset_antisymm
  · rintro _ ⟨z, rfl⟩
    have hz : u.base z ∈ range u.base := ⟨z, rfl⟩
    rw [hur] at hz
    exact hz
  · intro z hz
    have hbg : b.hom.left.base z ∈ range (g ≫ p.hom.left).base := by
      rw [hgpr]
      exact hz
    obtain ⟨l, hl⟩ := hbg
    have hga : g.base l ∈ range a.hom.left.base := by
      rw [hrange]
      exact ⟨z, hl.symm⟩
    obtain ⟨w, hw⟩ := hga
    have hqw : q.hom.left.base w = z := by
      apply hb.base_open.injective
      have hpw := congrArg (fun F => F.base w) hs
      exact hpw.trans ((congrArg p.hom.left.base hw).trans hl)
    have hwu : w ∈ range u.base := by
      rw [pullback_snd_range]
      exact ⟨l, hw.symm⟩
    obtain ⟨t, ht⟩ := hwu
    exact ⟨t, (congrArg q.hom.left.base ht).trans hqw⟩

variable {X : SourceReducedComplexSpace} (e : LocalEmbedding X) (U : Opens e.ambient)
  {D : CMfd.{0} e.dim} (T : BlowupTower (CMfd.of (n := e.dim) U) D)
  {Ef : List (Set D)}
  (h : IsStrictTransformResolution e.dim (windowCarrier e U) T.proj Ef)

/-- The full original-Reg inverse for the SAME actual refined projection.
No refined inverse, square, range or history comparison is an input. -/
theorem projection_isIsoOver_originalRegularLocus (P : Opens U) :
    IsIsoOver (projection e U T h P)
      ((baseInclusion e U P ≫ windowMorphism e U).hom.left.base ⁻¹'
        intrinsicRegularLocus X.obj) := by
  exact isIsoOver_of_open_square
    (resolutionMorphism (windowCarrier_analytic e U) h) (projection e U T h P)
    (strictInclusion e U T h P) (baseInclusion e U P)
    (strictInclusion_isOpenImmersion e U T h P) (baseInclusion_isOpenImmersion e U P)
    (projection_square e U T h P) (strictInclusion_range e U T h P)
    ((windowMorphism e U).hom.left.base ⁻¹' intrinsicRegularLocus X.obj)
    (resolutionMorphism_isIsoOver_originalRegularLocus e U h)

/-- Density is inherited through the actual endpoint OPEN inclusion and the
proved full original square, for this SAME refined projection. -/
theorem dense_preimage_originalRegularLocus (P : Opens U) :
    Dense ((projection e U T h P).hom.left.base ⁻¹'
      ((baseInclusion e U P ≫ windowMorphism e U).hom.left.base ⁻¹'
        intrinsicRegularLocus X.obj)) := by
  have hd : Dense ((resolutionMorphism (windowCarrier_analytic e U) h).hom.left.base ⁻¹'
      ((windowMorphism e U).hom.left.base ⁻¹' intrinsicRegularLocus X.obj)) := by
    rw [windowMorphism_regular_preimage]
    exact dense_preimage_regular h
  have heq : (strictInclusion e U T h P).hom.left.base ⁻¹'
      ((resolutionMorphism (windowCarrier_analytic e U) h).hom.left.base ⁻¹'
        ((windowMorphism e U).hom.left.base ⁻¹' intrinsicRegularLocus X.obj)) =
      (projection e U T h P).hom.left.base ⁻¹'
        ((baseInclusion e U P ≫ windowMorphism e U).hom.left.base ⁻¹'
          intrinsicRegularLocus X.obj) := by
    ext z
    exact iff_of_eq (congrArg (fun F => F.hom.left.base z ∈ intrinsicRegularLocus X.obj)
      (projection_original_square e U T h P)).symm
  rw [← heq]
  exact hd.preimage (strictInclusion_isOpenImmersion e U T h P).base_open.isOpenMap

/-- The SAME actual literal restricted strict-space map is an ORIGINAL
resolution; compactness and a new terminal-history choice are unnecessary. -/
theorem projection_isResolution (P : Opens U) : IsResolution (projection e U T h P) := by
  have hj : LocallyRingedSpace.IsOpenImmersion
      (baseInclusion e U P ≫ windowMorphism e U).hom.left :=
    @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ _
      (baseInclusion_isOpenImmersion e U P) _ (windowMorphism_isOpenImmersion e U)
  have hReg : (baseInclusion e U P ≫ windowMorphism e U).hom.left.base ⁻¹'
      intrinsicRegularLocus X.obj = intrinsicRegularLocus (baseSpace e U P).obj :=
    preimage_intrinsicRegularLocus _ hj (baseInclusion e U P ≫ windowMorphism e U).hom.w
  have hd : Dense ((projection e U T h P).hom.left.base ⁻¹'
      intrinsicRegularLocus (baseSpace e U P).obj) := by
    rw [← hReg]
    exact dense_preimage_originalRegularLocus e U T h P
  have hi : IsIsoOver (projection e U T h P) (intrinsicRegularLocus (baseSpace e U P).obj) := by
    rw [← hReg]
    exact projection_isIsoOver_originalRegularLocus e U T h P
  refine ⟨strictSpace_isSmooth e U T h P, projection_isProperMap e U T h P,
    intrinsicSingularLocus (baseSpace e U P).obj,
    OriginalIntrinsicSingularLocus.isAnalyticSubset_intrinsicSingularLocus _,
    OriginalIntrinsicSingularLocus.interior_intrinsicSingularLocus_eq_empty _, ?_, ?_⟩
  · apply interior_eq_empty_iff_dense_compl.mpr
    simpa only [intrinsicSingularLocus, preimage_compl, compl_compl] using hd
  · simpa only [intrinsicSingularLocus, compl_compl] using hi

end
end Hironaka.Analytic.Unibranch.OriginalLocalStrictWindowRegularity
