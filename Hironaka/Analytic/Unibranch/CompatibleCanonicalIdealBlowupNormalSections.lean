import Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupSquareCharts
import Hironaka.Resolution.HironakaIntrinsicReducedCentreOpenSections

/-! Prescribed SAME normal sections on ONE actual canonical target open.
BP FIRST. The whole native B-image ideal, not its radical, is transported
through genuine open-immersion stalk isomorphisms. No arbitrary Cartier
generator replaces the normal-coordinate list. Pivot-open images, Qsat,
whole graph kernels and raw-fibre comparisons remain separate obligations. -/
set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupNormalSections
noncomputable section
open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences Hironaka
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaActualAnalyticSubspace
  HironakaActualAnalyticSubspaceMaps HironakaNativePulledIdealSheaf
  HironakaSingularModuleSheafStalk
  HironakaNativePulledIdealComposition HironakaIntrinsicReducedCentreOpenSections
  HironakaFiniteSectionProductGraph ProductComplexManifold BlowupStrictSubmanifold
  SourceReducedComplexSpace EmbeddedGeometricBlowup EmbeddedBlowupGlobalUniversalLocal
  OriginalFiniteIdealGraphChart CompatibleCanonicalIdealBlowupSquareCharts
open scoped ProductComplexManifold

section ActualSections
variable {n m : ℕ} {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [ChartedSpace (ComplexModel m) N] [IsComplexManifold m N]

private def globalFunctionSection (f : M → ℂ)
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) ∞ f) :
    actualComplexSection (n := n) (⊤ : Opens M) :=
  ⟨fun z => f z.val,hf.comp contMDiff_subtype_val⟩

private theorem globalFunctionSection_germ (f : M → ℂ)
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) ∞ f) (x : M) :
    (actualComplexStructureSheaf (n := n) M).presheaf.germ ⊤ x (by trivial)
      (globalFunctionSection f hf) =
    actualOriginalFunctionGerm x f (Eventually.of_forall fun _ =>
      hf.contMDiffAt.mdifferentiableAt (by simp)) := by
  apply (actualOriginalFunctionGerm_eq_section ⊤ x (by trivial)
    (globalFunctionSection f hf) f _ ?_).symm
  exact Eventually.of_forall fun z => sectionExtension_apply ⊤ _ z (by trivial)

private theorem native_global_function_germ {f : M → N}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
    (g : N → ℂ) (hg : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ℂ) ∞ g) (x : M) :
    (ChartedSpace.locallyRingedSpaceMap f hf).stalkMap x
      (actualOriginalFunctionGerm (f x) g (Eventually.of_forall fun _ =>
        hg.contMDiffAt.mdifferentiableAt (by simp))) =
      actualOriginalFunctionGerm x (g ∘ f) (Eventually.of_forall fun _ =>
        (hg.comp hf).contMDiffAt.mdifferentiableAt (by simp)) := by
  let H := ChartedSpace.locallyRingedSpaceMap f hf
  rw [←globalFunctionSection_germ g hg (f x)]
  have he := LocallyRingedSpace.stalkMap_germ_apply H ⊤ x (by trivial)
    (globalFunctionSection g hg)
  apply he.trans
  rw [←globalFunctionSection_germ (g ∘ f) (hg.comp hf) x]
  apply actual_section_germ_eq_of_extension_eventuallyEq
  exact Eventually.of_forall fun z => by
    rw [sectionExtension_apply _ _ z (by trivial),sectionExtension_apply _ _ z (by trivial)]
    rfl

private theorem normalSmooth {r : ℕ} (i : Fin r) :
    ContMDiff 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ℂ) ∞
      (fun q : M × ComplexModel r => q.2 i) :=
  (EuclideanSpace.proj i : ComplexModel r →L[ℂ] ℂ).contMDiff.comp
    ProductComplexManifold.contMDiff_snd

/-- Actual ambient coordinate germ; it is defined at EVERY actual point. -/
def prescribedNormalGerm {r : ℕ} (q : M × ComplexModel r) (i : Fin r) :
    actualComplexStructureStalk (n := n+r) q :=
  actualOriginalFunctionGerm q (fun z : M × ComplexModel r => z.2 i)
    (Eventually.of_forall fun _ => (normalSmooth (n := n) (M := M) i).contMDiffAt.mdifferentiableAt (by simp))

private theorem whole_zero_plane_normals {r : ℕ} (q : M × ComplexModel r) :
    actualWholeSheafStalkIdeal (vanishingIdeal (n := n+r)
      {z : M × ComplexModel r | z.2=0}) q =
      Ideal.span (range fun i : Fin r => prescribedNormalGerm q i) :=
  whole_product_zero_plane_ideal q

end ActualSections

section NativeFiniteDescent
variable {A T Z : LocallyRingedSpace.{0}}
  (j : A ⟶ Z) [LocallyRingedSpace.IsOpenImmersion j] (p : Z ⟶ T)
  (B : SheafOfModules.{0} (forgetRing T.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing T.toSheafedSpace.sheaf))

private def imageTop : Opens Z.toTopCat :=
  (LocallyRingedSpace.IsOpenImmersion.opensFunctor j).obj ⊤

private def descendedTopSection {r : ℕ}
    (σ : Fin r → (A.presheaf.obj (op ⊤)).carrier) (i : Fin r) :
    (Z.presheaf.obj (op (imageTop j))).carrier :=
  LocallyRingedSpace.IsOpenImmersion.invApp j ⊤ (σ i)

private theorem descendedTopSection_germ {r : ℕ}
    (σ : Fin r → (A.presheaf.obj (op ⊤)).carrier) (i : Fin r) (z : A) :
    j.stalkMap z (Z.presheaf.germ (imageTop j) (j.base z) ⟨z,by trivial,rfl⟩
      (descendedTopSection j σ i)) = A.presheaf.germ ⊤ z (by trivial) (σ i) :=
  openImmersion_invApp_germ j ⊤ (σ i) z (by trivial)

private theorem descendedTopSection_span {r : ℕ}
    (σ : Fin r → (A.presheaf.obj (op ⊤)).carrier)
    (hspan : ∀ z : A, Ideal.map (j.stalkMap z).hom
      (nativePulledIdealStalkIdeal p B b (j.base z)) =
        Ideal.span (range fun i : Fin r => A.presheaf.germ ⊤ z (by trivial) (σ i)))
    (z : Z) (hz : z∈imageTop j) :
    nativePulledIdealStalkIdeal p B b z =
      Ideal.span (range fun i : Fin r => Z.presheaf.germ (imageTop j) z hz
        (descendedTopSection j σ i)) := by
  obtain ⟨w,_hw,rfl⟩ := hz
  let e := (asIso (j.stalkMap w)).commRingCatIsoToRingEquiv
  have hm := Ideal.map_span (j.stalkMap w).hom
    (range fun i : Fin r => Z.presheaf.germ (imageTop j) (j.base w) ⟨w,by trivial,rfl⟩
      (descendedTopSection j σ i))
  rw [←Set.range_comp] at hm
  have he := (hspan w).trans ((congrArg Ideal.span (congrArg Set.range (funext fun i =>
    (descendedTopSection_germ j σ i w).symm))).trans hm.symm)
  exact e.idealComapOrderIso.symm.injective he

private def descendedIdealSections {r : ℕ}
    (σ : Fin r → (A.presheaf.obj (op ⊤)).carrier)
    (hspan : ∀ z : A, Ideal.map (j.stalkMap z).hom
      (nativePulledIdealStalkIdeal p B b (j.base z)) =
        Ideal.span (range fun i : Fin r => A.presheaf.germ ⊤ z (by trivial) (σ i))) :
    Fin r → nativePulledIdealSectionIdeal p B b (imageTop j) := fun i =>
  ⟨descendedTopSection j σ i,fun z hz => by
    rw [descendedTopSection_span j p B b σ hspan z hz]
    exact Ideal.subset_span ⟨i,rfl⟩⟩

end NativeFiniteDescent

private def pullTopSection {A Z : LocallyRingedSpace.{0}} (H : A ⟶ Z)
    (s : (Z.presheaf.obj (op ⊤)).carrier) : (A.presheaf.obj (op ⊤)).carrier :=
  A.presheaf.map (homOfLE (show (⊤ : Opens A.toTopCat) ≤ (Opens.map H.base).obj ⊤ from
    fun _ _ => by trivial)).op (H.c.app (op ⊤) s)

private theorem pullTopSection_germ {A Z : LocallyRingedSpace.{0}} (H : A ⟶ Z)
    (s : (Z.presheaf.obj (op ⊤)).carrier) (z : A) :
    A.presheaf.germ ⊤ z (by trivial) (pullTopSection H s) =
      H.stalkMap z (Z.presheaf.germ ⊤ (H.base z) (by trivial) s) := by
  unfold pullTopSection
  exact (A.presheaf.germ_res_apply
    (homOfLE (show (⊤ : Opens A.toTopCat) ≤ (Opens.map H.base).obj ⊤ from fun _ _ => by trivial))
    z (by trivial) (H.c.app (op ⊤) s)).trans
      (LocallyRingedSpace.stalkMap_germ_apply H ⊤ z (by trivial) s).symm

section ActualGeometricNormals
variable {n r : ℕ} {P E : Type} [TopologicalSpace P] [TopologicalSpace E]
  [ChartedSpace (ComplexModel n) P] [IsComplexManifold n P]
  [ChartedSpace (ComplexModel (n+r)) E] [IsComplexManifold (n+r) E]
  {W : Set (P × ComplexModel r)} {π : E → P × ComplexModel r}
  (hπ : IsBlowupAlong (n+r) {q : P × ComplexModel r | q.2=0} π)
  (hW : IsComplexAnalyticSubset (n := n+r) W)

/-- Literal original normal germ on the actual ambient blowup. -/
def projectionNormalGerm (z : E) (i : Fin r) :
    actualComplexStructureStalk (n := n+r) z :=
  actualOriginalFunctionGerm z (fun w => (π w).2 i)
    (Eventually.of_forall fun _ => ((normalSmooth (n := n) (M := P) i).comp
      hπ.contMDiff).contMDiffAt.mdifferentiableAt (by simp))

private def geometricAmbientProjection :
    (geometricSource hπ hW).obj.left ⟶ ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel (n+r))
      (P × ComplexModel r) :=
  geometricProjection hπ hW.isClosed ≫ actualSubspaceInclusion (n := n+r) W

private def geometricNormalSections (i : Fin r) :
    ((geometricSource hπ hW).obj.left.presheaf.obj (op ⊤)).carrier :=
  pullTopSection (geometricAmbientProjection hπ hW)
    (globalFunctionSection (fun q : P × ComplexModel r => q.2 i) (normalSmooth i))

private theorem geometricNormalSections_germ (z : (geometricSource hπ hW).obj.left)
    (i : Fin r) :
    (geometricSource hπ hW).obj.left.presheaf.germ ⊤ z (by trivial)
      (geometricNormalSections hπ hW i) =
      (geometricAmbientProjection hπ hW).stalkMap z
        (prescribedNormalGerm (π z.val) i) := by
  exact (pullTopSection_germ _ _ z).trans (congrArg
    (fun a => (geometricAmbientProjection hπ hW).stalkMap z a)
      (globalFunctionSection_germ _ (normalSmooth i) (π z.val)))

/-- FULL ambient inclusion square identifies every whole normal germ. -/
private theorem geometricNormalSections_original_germ
    (z : (geometricSource hπ hW).obj.left) (i : Fin r) :
    (geometricSource hπ hW).obj.left.presheaf.germ ⊤ z (by trivial)
      (geometricNormalSections hπ hW i) =
      (actualSubspaceInclusion (n := n+r) (geoStrictTransform π {q | q.2=0} W)).stalkMap z
        (projectionNormalGerm hπ z.val i) := by
  rw [geometricNormalSections_germ]
  let inc := actualSubspaceInclusion (n := n+r) (geoStrictTransform π {q | q.2=0} W)
  let L := ChartedSpace.locallyRingedSpaceMap π hπ.contMDiff
  have hs : inc ≫ L=geometricAmbientProjection hπ hW := geometricProjection_inclusion hπ hW.isClosed
  have he := congrArg (fun H : (geometricSource hπ hW).obj.left ⟶
      ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel (n+r)) (P × ComplexModel r) =>
    H.stalkMap z (prescribedNormalGerm (H.base z) i)) hs
  have hc := ConcreteCategory.congr_hom (LocallyRingedSpace.stalkMap_comp (f := inc) (g := L) z)
    (prescribedNormalGerm (π z.val) i)
  have hn := native_global_function_germ hπ.contMDiff
    (fun q : P × ComplexModel r => q.2 i) (normalSmooth i) z.val
  exact he.symm.trans (hc.trans (congrArg (fun a => inc.stalkMap z a) hn))

end ActualGeometricNormals

section TargetWholeNormals
variable {Y : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing Y.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing Y.obj.left.toSheafedSpace.sheaf)) [B.IsFiniteType]
  {y : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left}
  (t : CanonicalTargetGraph B b y)

private theorem target_whole_ideal
    (z : (geometricSource t.blowup t.analytic).obj.left) :
    Ideal.map (t.comparison.hom.left.stalkMap z).hom
      (nativePulledIdealStalkIdeal (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left
        B b (t.comparison.hom.left.base z)) =
      Ideal.map ((geometricAmbientProjection t.blowup t.analytic).stalkMap z).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := t.embedding.dim+t.rank)
          {q : t.domain × ComplexModel t.rank | q.2=0}) (t.projection z.val)) := by
  let p := geometricProjection t.blowup t.analytic.isClosed
  let J := chartGraphMap t.embedding t.domain t.functions t.holomorphic
  let LT := t.comparison.hom.left
  let pY := (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left
  have hs : LT ≫ pY=p ≫ J := congrArg (fun H => H.hom.left) t.comparison_projection
  have hwhole := (t.wholeIdeal (p.base z)).symm
  have hc := geometricProjection_wholeCentreIdeal t.blowup t.analytic.isClosed z
  exact (nativePulledIdealStalkIdeal_comp LT pY B b z).symm.trans
    ((congrArg (fun H => nativePulledIdealStalkIdeal H B b z) hs).trans
      ((nativePulledIdealStalkIdeal_comp p J B b z).trans
        ((congrArg (Ideal.map (p.stalkMap z).hom) hwhole).trans hc.symm)))

private theorem target_normal_span
    (z : (geometricSource t.blowup t.analytic).obj.left) :
    Ideal.map (t.comparison.hom.left.stalkMap z).hom
      (nativePulledIdealStalkIdeal (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left
        B b (t.comparison.hom.left.base z)) =
      Ideal.span (range fun i : Fin t.rank =>
        (geometricSource t.blowup t.analytic).obj.left.presheaf.germ ⊤ z (by trivial)
          (geometricNormalSections t.blowup t.analytic i)) := by
  have hzero := congrArg (Ideal.map ((geometricAmbientProjection t.blowup t.analytic).stalkMap z).hom)
    (whole_zero_plane_normals (t.projection z.val))
  have hm := Ideal.map_span ((geometricAmbientProjection t.blowup t.analytic).stalkMap z).hom
    (range fun i : Fin t.rank => prescribedNormalGerm (t.projection z.val) i)
  rw [←Set.range_comp] at hm
  exact (target_whole_ideal B b t z).trans (hzero.trans (hm.trans
    (congrArg Ideal.span (congrArg Set.range (funext fun i =>
      (geometricNormalSections_germ t.blowup t.analytic z i).symm)))))

local instance : LocallyRingedSpace.IsOpenImmersion t.comparison.hom.left := t.comparison_open

private def targetOpen := imageTop t.comparison.hom.left

private def targetSections : Fin t.rank → nativePulledIdealSectionIdeal
    (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left B b (targetOpen B b t) :=
  descendedIdealSections t.comparison.hom.left
    (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left B b
    (geometricNormalSections t.blowup t.analytic) (target_normal_span B b t)

private theorem targetOpen_mem (z : (geometricSource t.blowup t.analytic).obj.left) :
    t.comparison.hom.left.base z∈targetOpen B b t := ⟨z,by trivial,rfl⟩

private theorem targetSections_span (z : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left)
    (hz : z∈targetOpen B b t) :
    nativePulledIdealStalkIdeal (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left B b z =
      Ideal.span (range fun i : Fin t.rank =>
        (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left.presheaf.germ
          (targetOpen B b t) z hz (targetSections B b t i).val) :=
  descendedTopSection_span t.comparison.hom.left
    (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left B b
    (geometricNormalSections t.blowup t.analytic) (target_normal_span B b t) z hz

private theorem targetSections_germ (z : (geometricSource t.blowup t.analytic).obj.left) (i : Fin t.rank) :
    t.comparison.hom.left.stalkMap z
      ((OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left.presheaf.germ
        (targetOpen B b t) (t.comparison.hom.left.base z) (targetOpen_mem B b t z)
        (targetSections B b t i).val) =
      (actualSubspaceInclusion (n := t.embedding.dim+t.rank)
        (geoStrictTransform t.projection {q | q.2=0} _)).stalkMap z
          (projectionNormalGerm t.blowup z.val i) :=
  (descendedTopSection_germ t.comparison.hom.left (geometricNormalSections t.blowup t.analytic) i z).trans
    (geometricNormalSections_original_germ t.blowup t.analytic z i)

end TargetWholeNormals

private theorem native_section_germ_congr {A Z : LocallyRingedSpace.{0}}
    (f g : A ⟶ Z) (h : f=g) (U : Opens Z.toTopCat)
    (s : (Z.presheaf.obj (op U)).carrier) (z : A) (hf : f.base z∈U) (hg : g.base z∈U) :
    f.stalkMap z (Z.presheaf.germ U (f.base z) hf s) =
      g.stalkMap z (Z.presheaf.germ U (g.base z) hg s) := by
  subst g
  rfl

private theorem original_germ_congr {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (x : M) (f g : M → ℂ) (hf : HolomorphicAt n f x) (hg : HolomorphicAt n g x)
    (he : f=ᶠ[𝓝 x]g) : actualOriginalFunctionGerm x f hf=actualOriginalFunctionGerm x g hg := by
  apply (actualStalkChartEquiv (n := n) x).injective
  rw [actualOriginalFunctionGerm_chart,actualOriginalFunctionGerm_chart]
  exact chartTranslatedGerm_congr_original x f g hf hg he

section SourceWholeNormals
variable {X Y : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing Y.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing Y.obj.left.toSheafedSpace.sheaf)) [B.IsFiniteType]
  (F : X ⟶ Y)

local instance : (nativePulledIdealModule F.hom.left B b).IsFiniteType :=
  HironakaNativePulledIdealFiniteType.nativePulledIdealModule_isFiniteType F.hom.left B b

-- Native whole-image composition, repeated only as a private consumer (zero engine credit).
private theorem source_whole_ideal
    (z : (OriginalFiniteIdealGeometricBlowup.sourceObject
      (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).obj.left) :
    nativePulledIdealStalkIdeal (OriginalFiniteIdealGeometricBlowup.projectionMorphism
        (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).hom.left
        (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b) z =
      Ideal.map (((OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left).stalkMap z).hom
        (nativePulledIdealStalkIdeal (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left B b
          ((OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left.base z)) := by
  let pX := (OriginalFiniteIdealGeometricBlowup.projectionMorphism
    (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).hom.left
  let pY := (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left
  let Fp := (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left
  have hSquare : Fp ≫ pY=pX ≫ F.hom.left :=
    congrArg (fun v => v.hom.left) (OriginalFiniteIdealBlowupSquare.inducedMorphism_square B b F)
  have hWhole : nativePulledIdealStalkIdeal (pX ≫ F.hom.left) B b z=
      nativePulledIdealStalkIdeal (Fp ≫ pY) B b z :=
    congrArg (fun v => nativePulledIdealStalkIdeal v B b z) hSquare.symm
  exact (stalkIdeal_comp F.hom.left pX B b z).trans
    (hWhole.trans (nativePulledIdealStalkIdeal_comp Fp pY B b z))

private theorem source_normal_span {r : ℕ}
    (U : Opens (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left.toTopCat)
    (s : Fin r → nativePulledIdealSectionIdeal
      (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left B b U)
    (hspan : ∀ z hz,nativePulledIdealStalkIdeal
      (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left B b z =
        Ideal.span (range fun i : Fin r => (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left.presheaf.germ
          U z hz (s i).val))
    (z : (OriginalFiniteIdealGeometricBlowup.sourceObject
      (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).obj.left)
    (hz : (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left.base z∈U) :
    nativePulledIdealStalkIdeal (OriginalFiniteIdealGeometricBlowup.projectionMorphism
      (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).hom.left
        (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b) z =
      Ideal.span (range fun i : Fin r => (OriginalFiniteIdealGeometricBlowup.sourceObject
        (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).obj.left.presheaf.germ
          ((Opens.map (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left.base).obj U)
          z hz (canonicalPulledIdealSection B b F U (s i)).val) := by
  let Fp := (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left
  have he := congrArg (Ideal.map (Fp.stalkMap z).hom) (hspan (Fp.base z) hz)
  have hm := Ideal.map_span (Fp.stalkMap z).hom (range fun i : Fin r =>
    (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left.presheaf.germ U (Fp.base z) hz (s i).val)
  rw [←Set.range_comp] at hm
  exact (source_whole_ideal B b F z).trans (he.trans (hm.trans
    (congrArg Ideal.span (congrArg Set.range (funext fun i =>
      LocallyRingedSpace.stalkMap_germ_apply Fp U z hz (s i).val)))))

variable (x : X.obj.left) {y : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left}
  (t : CanonicalTargetGraph B b y) (c : CanonicalCompatibleSourceGraph B b F x t)
  (g : CanonicalSquareGeometry B b F x t c)

private def geometricMap := geometricNormalMorphism c.baseMap t.functions
    _ _ c.landing c.analytic t.analytic g.projection g.blowup t.projection t.blowup
      g.ambientLift g.lift_holomorphic g.lift_projection

private theorem geometricMap_normal_germ
    (z : (geometricSource g.blowup c.analytic).obj.left) (i : Fin t.rank) :
    (geometricMap B b F x t c g).hom.left.stalkMap z
      ((actualSubspaceInclusion (n := t.embedding.dim+t.rank)
        (geoStrictTransform t.projection {q | q.2=0} _)).stalkMap
          ((geometricMap B b F x t c g).hom.left.base z)
        (projectionNormalGerm t.blowup (g.ambientLift z.val) i)) =
      (actualSubspaceInclusion (n := c.embedding.dim+t.rank)
        (geoStrictTransform g.projection {q | q.2=0} _)).stalkMap z
        (projectionNormalGerm g.blowup z.val i) := by
  let H := (geometricMap B b F x t c g).hom.left
  let incS := actualSubspaceInclusion (n := c.embedding.dim+t.rank)
    (geoStrictTransform g.projection {q | q.2=0}
      (productGraph ((Subtype.val : c.subdomain → c.domain) ⁻¹'
        ((Subtype.val : c.domain → c.embedding.ambient) ⁻¹' c.embedding.carrier)) (t.functions ∘ c.baseMap)))
  let incT := actualSubspaceInclusion (n := t.embedding.dim+t.rank)
    (geoStrictTransform t.projection {q | q.2=0}
      (productGraph ((Subtype.val : t.domain → t.embedding.ambient) ⁻¹' t.embedding.carrier) t.functions))
  let L := ChartedSpace.locallyRingedSpaceMap g.ambientLift g.lift_holomorphic
  have hlanding : ∀ w∈geoStrictTransform g.projection {q | q.2=0}
      (productGraph ((Subtype.val : c.subdomain → c.domain) ⁻¹'
        ((Subtype.val : c.domain → c.embedding.ambient) ⁻¹' c.embedding.carrier)) (t.functions ∘ c.baseMap)),
      g.ambientLift w∈geoStrictTransform t.projection {q | q.2=0}
        (productGraph ((Subtype.val : t.domain → t.embedding.ambient) ⁻¹' t.embedding.carrier) t.functions) :=
    fun w hw => (H.base ⟨w,hw⟩).property
  have hinc : incS ≫ L=H ≫ incT := actualSubspaceMap_inclusion g.lift_holomorphic hlanding
  have he := congrArg (fun K : (geometricSource g.blowup c.analytic).obj.left ⟶
      ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel (t.embedding.dim+t.rank)) t.lift =>
    K.stalkMap z (projectionNormalGerm t.blowup (K.base z) i)) hinc
  have hfun : ((fun w : t.lift => (t.projection w).2 i) ∘ g.ambientLift)=
      (fun w : g.lift => (g.projection w).2 i) := by
    funext w
    exact congrArg (fun q => q.2 i) (congrFun g.lift_projection w)
  have hn := native_global_function_germ g.lift_holomorphic
    (fun w : t.lift => (t.projection w).2 i) ((normalSmooth i).comp t.blowup.contMDiff) z.val
  have hn' : L.stalkMap z.val (projectionNormalGerm t.blowup (g.ambientLift z.val) i)=
      projectionNormalGerm g.blowup z.val i := hn.trans
    (original_germ_congr z.val _ _ _ _ (Eventually.of_forall (congrFun hfun)))
  have hS := ConcreteCategory.congr_hom (LocallyRingedSpace.stalkMap_comp incS L z)
    (projectionNormalGerm t.blowup (g.ambientLift z.val) i)
  have hT := ConcreteCategory.congr_hom (LocallyRingedSpace.stalkMap_comp H incT z)
    (projectionNormalGerm t.blowup (g.ambientLift z.val) i)
  exact hT.symm.trans (he.symm.trans (hS.trans (congrArg (fun a => incS.stalkMap z a) hn')))

private theorem source_geometric_mem (z : (geometricSource g.blowup c.analytic).obj.left) :
    (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left.base
      (g.comparison.hom.left.base z)∈targetOpen B b t := by
  have hs := congrArg (fun H => H.hom.left.base z) g.full_canonical_square
  exact hs.symm ▸ targetOpen_mem B b t ((geometricMap B b F x t c g).hom.left.base z)

private theorem sourceSections_germ (z : (geometricSource g.blowup c.analytic).obj.left) (i : Fin t.rank) :
    g.comparison.hom.left.stalkMap z
      ((OriginalFiniteIdealGeometricBlowup.sourceObject (nativePulledIdealModule F.hom.left B b)
        (nativePulledIdealInclusion F.hom.left B b)).obj.left.presheaf.germ
        ((Opens.map (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left.base).obj (targetOpen B b t))
        (g.comparison.hom.left.base z) (source_geometric_mem B b F x t c g z)
        (canonicalPulledIdealSection B b F (targetOpen B b t) (targetSections B b t i)).val) =
      (actualSubspaceInclusion (n := c.embedding.dim+t.rank)
        (geoStrictTransform g.projection {q | q.2=0} _)).stalkMap z
        (projectionNormalGerm g.blowup z.val i) := by
  let LS := g.comparison.hom.left
  let LT := t.comparison.hom.left
  let H := (geometricMap B b F x t c g).hom.left
  let Fp := (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left
  let U := targetOpen B b t
  let s := (targetSections B b t i).val
  have hs : LS ≫ Fp=H ≫ LT := congrArg (fun H => H.hom.left) g.full_canonical_square
  have hmS := source_geometric_mem B b F x t c g z
  have hmT := targetOpen_mem B b t (H.base z)
  have hPull := (LocallyRingedSpace.stalkMap_germ_apply Fp U (LS.base z) hmS s).symm
  have hCompS := ConcreteCategory.congr_hom (LocallyRingedSpace.stalkMap_comp LS Fp z)
    ((OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left.presheaf.germ U
      (Fp.base (LS.base z)) hmS s)
  have hCompT := ConcreteCategory.congr_hom (LocallyRingedSpace.stalkMap_comp H LT z)
    ((OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left.presheaf.germ U
      (LT.base (H.base z)) hmT s)
  exact (congrArg (fun a => LS.stalkMap z a) hPull).trans
    (hCompS.symm.trans ((native_section_germ_congr (LS ≫ Fp) (H ≫ LT) hs U s z hmS hmT).trans
      (hCompT.trans ((congrArg (fun a => H.stalkMap z a)
        (targetSections_germ B b t (H.base z) i)).trans (geometricMap_normal_germ B b F x t c g z i)))))

end SourceWholeNormals

section OrdinaryOutput
variable {X Y : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing Y.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing Y.obj.left.toSheafedSpace.sheaf)) [B.IsFiniteType]
  (F : X ⟶ Y) (x : X.obj.left)
  {y : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left}

local instance : (nativePulledIdealModule F.hom.left B b).IsFiniteType :=
  HironakaNativePulledIdealFiniteType.nativePulledIdealModule_isFiniteType F.hom.left B b

/-- ONE actual target open and the prescribed finite sections, with their
ENTIRE native target span and original normal-germ dictionary. OUTPUT only. -/
structure CanonicalTargetNormalSectionData (t : CanonicalTargetGraph B b y) where
  targetOpen : Opens (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left.toTopCat
  targetOpen_range : (targetOpen : Set (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left.toTopCat) =
    range t.comparison.hom.left.base
  target_mem : y∈targetOpen
  sections : Fin t.rank → nativePulledIdealSectionIdeal
    (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left B b targetOpen
  target_geometric_mem : ∀ z : (geometricSource t.blowup t.analytic).obj.left,
    t.comparison.hom.left.base z∈targetOpen
  target_span : ∀ (z : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left) (hz : z∈targetOpen),
    nativePulledIdealStalkIdeal (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left B b z =
      Ideal.span (range fun i : Fin t.rank =>
        (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left.presheaf.germ targetOpen z hz (sections i).val)
  target_normal : ∀ (z : (geometricSource t.blowup t.analytic).obj.left) (i : Fin t.rank),
    t.comparison.hom.left.stalkMap z
      ((OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left.presheaf.germ targetOpen
        (t.comparison.hom.left.base z) (target_geometric_mem z) (sections i).val) =
      (actualSubspaceInclusion (n := t.embedding.dim+t.rank)
        (geoStrictTransform t.projection {q | q.2=0} _)).stalkMap z
          (projectionNormalGerm t.blowup z.val i)
  target_scalar : t.comparison.hom.left ≫ (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.hom =
    (geometricSource t.blowup t.analytic).obj.hom

/-- Literal native pulled sections and ENTIRE source spans on all of F'⁻¹U.
The target family is fixed before ALL source points and normal indices. -/
structure CanonicalPulledNormalSpanData (t : CanonicalTargetGraph B b y)
    (d : CanonicalTargetNormalSectionData B b t) where
  pulled_germ : ∀ (z : (OriginalFiniteIdealGeometricBlowup.sourceObject
      (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).obj.left)
      (hz : (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left.base z∈d.targetOpen)
      (i : Fin t.rank),
    (OriginalFiniteIdealGeometricBlowup.sourceObject (nativePulledIdealModule F.hom.left B b)
      (nativePulledIdealInclusion F.hom.left B b)).obj.left.presheaf.germ
      ((Opens.map (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left.base).obj d.targetOpen)
      z hz (canonicalPulledIdealSection B b F d.targetOpen (d.sections i)).val =
      (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left.stalkMap z
        ((OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left.presheaf.germ d.targetOpen
          ((OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left.base z) hz (d.sections i).val)
  source_span : ∀ (z : (OriginalFiniteIdealGeometricBlowup.sourceObject
      (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).obj.left)
      (hz : (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left.base z∈d.targetOpen),
    nativePulledIdealStalkIdeal (OriginalFiniteIdealGeometricBlowup.projectionMorphism
      (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).hom.left
        (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b) z =
      Ideal.span (range fun i : Fin t.rank => (OriginalFiniteIdealGeometricBlowup.sourceObject
        (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).obj.left.presheaf.germ
          ((Opens.map (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left.base).obj d.targetOpen)
          z hz (canonicalPulledIdealSection B b F d.targetOpen (d.sections i)).val)
  induced_scalar : (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left ≫
      (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.hom =
    (OriginalFiniteIdealGeometricBlowup.sourceObject (nativePulledIdealModule F.hom.left B b)
      (nativePulledIdealInclusion F.hom.left B b)).obj.hom

/-- Full original SAME-index normal transport on the actual geometric source,
which may be EMPTY. All maps are the actual original native morphisms. -/
structure CanonicalGeometricNormalTransportData (t : CanonicalTargetGraph B b y)
    (c : CanonicalCompatibleSourceGraph B b F x t)
    (g : CanonicalSquareGeometry B b F x t c)
    (d : CanonicalTargetNormalSectionData B b t) where
  source_geometric_mem : ∀ z : (geometricSource g.blowup c.analytic).obj.left,
    (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left.base
      (g.comparison.hom.left.base z)∈d.targetOpen
  source_normal : ∀ (z : (geometricSource g.blowup c.analytic).obj.left) (i : Fin t.rank),
    g.comparison.hom.left.stalkMap z
      ((OriginalFiniteIdealGeometricBlowup.sourceObject (nativePulledIdealModule F.hom.left B b)
        (nativePulledIdealInclusion F.hom.left B b)).obj.left.presheaf.germ
        ((Opens.map (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left.base).obj d.targetOpen)
        (g.comparison.hom.left.base z) (source_geometric_mem z)
        (canonicalPulledIdealSection B b F d.targetOpen (d.sections i)).val) =
      (actualSubspaceInclusion (n := c.embedding.dim+t.rank)
        (geoStrictTransform g.projection {q | q.2=0} _)).stalkMap z
        (projectionNormalGerm g.blowup z.val i)
  source_scalar : g.comparison.hom.left ≫ (OriginalFiniteIdealGeometricBlowup.sourceObject
    (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).obj.hom =
      (geometricSource g.blowup c.analytic).obj.hom

/-- Internally constructed OUTPUT, never a caller certificate. The smaller
records keep native dependent carrier inference bounded at default settings;
they retain every ENTIRE ideal/span and FULL original germ/scalar assertion. -/
structure CanonicalNormalSectionData (t : CanonicalTargetGraph B b y)
    (c : CanonicalCompatibleSourceGraph B b F x t)
    (g : CanonicalSquareGeometry B b F x t c) where
  target : CanonicalTargetNormalSectionData B b t
  pulled : CanonicalPulledNormalSpanData B b F t target
  geometric : CanonicalGeometricNormalTransportData B b F x t c g target

private def constructedTargetSections (t : CanonicalTargetGraph B b y) :
    CanonicalTargetNormalSectionData B b t := by
  refine {
    targetOpen := targetOpen B b t
    targetOpen_range := ?_
    target_mem := Eq.mp (congrArg
      (fun z : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left => z∈targetOpen B b t)
      t.point_over) (targetOpen_mem B b t t.point)
    sections := targetSections B b t
    target_geometric_mem := targetOpen_mem B b t
    target_span := targetSections_span B b t
    target_normal := targetSections_germ B b t
    target_scalar := Over.w t.comparison.hom }
  ext z
  constructor
  · rintro ⟨w,_hw,rfl⟩
    exact ⟨w,rfl⟩
  · rintro ⟨w,rfl⟩
    exact targetOpen_mem B b t w

private theorem constructedPulledSections (t : CanonicalTargetGraph B b y)
    (d : CanonicalTargetNormalSectionData B b t) : CanonicalPulledNormalSpanData B b F t d where
  pulled_germ := by
    intro z hz i
    exact (LocallyRingedSpace.stalkMap_germ_apply
      (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left
      d.targetOpen z hz (d.sections i).val).symm
  source_span := source_normal_span B b F d.targetOpen d.sections d.target_span
  induced_scalar := Over.w (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom

private theorem constructedGeometricSections (t : CanonicalTargetGraph B b y)
    (c : CanonicalCompatibleSourceGraph B b F x t)
    (g : CanonicalSquareGeometry B b F x t c) :
    CanonicalGeometricNormalTransportData B b F x t c g (constructedTargetSections B b t) where
  source_geometric_mem := source_geometric_mem B b F x t c g
  source_normal := sourceSections_germ B b F x t c g
  source_scalar := Over.w g.comparison.hom

/-- ONLY ordinary original BFT/b/F/x and the GIVEN actual target point/raw
pair. Geometry, ONE target open, the SAME normal labels, ENTIRE target/source
spans, and FULL native original germ/scalar laws are constructed internally.
No source strict point over the raw pair, pivot-chart image, Qsat, Cartier,
future whole graph kernel, lift or generator-equality certificate is input. -/
theorem exists_same_pulled_canonical_normal_sections
    (y : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left)
    (hxy : F.hom.left.base x=(OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.base y) :
    ∃ (t : CanonicalTargetGraph B b y) (c : CanonicalCompatibleSourceGraph B b F x t)
      (g : CanonicalSquareGeometry B b F x t c),
      Nonempty (CanonicalNormalSectionData B b F x t c g) := by
  obtain ⟨t,c,⟨g⟩⟩ := exists_same_canonical_geometric_square B b F x y hxy
  exact ⟨t,c,g,⟨{
    target := constructedTargetSections B b t
    pulled := constructedPulledSections B b F t (constructedTargetSections B b t)
    geometric := constructedGeometricSections B b F x t c g }⟩⟩

end OrdinaryOutput

end
end Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupNormalSections
