import Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupGlobalUniversalLocal
import Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupOriginalObject

/-!
# Full original universal lifting for the same native whole target ideal

The source A is arbitrary ORIGINAL, with no global second countability.
Standard native singleton locally-free data apply to EXACT original B,b.
Derived local source lifts/dense good loci and the full native cover gluer
produce the unique ENTIRE original lift through the SAME actual projection.
No reduced-centre ideal or incoming source lift is supplied. The explicit
local whole-ideal dictionaries are retained for the ordinary chart consumer.
Blueprint: `embedded-ideal-blowup-global-universal.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace Topology CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupGlobalUniversal

open Hironaka Hironaka.BlowupSequences
  Hironaka HironakaActualAnalyticSubspace
  HironakaReducedComplexAnalyticSpaces HironakaIntrinsicMorphismGluing
  HironakaIntrinsicMorphismGluingAnalytic HironakaSingularSubspaceBlowupLift
  HironakaSingularSubspaceBlowupCartierUniversalGlobal HironakaNativePulledIdealSheaf
  HironakaSingularModuleSheafStalk SourceReducedComplexSpace
  EmbeddedIdealBlowupGlobalUniversalLocal EmbeddedIdealBlowupNonunitLocus

noncomputable section

variable {X : SourceReducedComplexSpace} {ι : Type} {n : ι → ℕ}
  {M Y : ι → Type} [∀ i, TopologicalSpace (M i)] [∀ i, TopologicalSpace (Y i)]
  [∀ i, ChartedSpace (ComplexModel (n i)) (M i)] [∀ i, IsComplexManifold (n i) (M i)]
  [∀ i, ChartedSpace (ComplexModel (n i)) (Y i)] [∀ i, IsComplexManifold (n i) (Y i)]
  {C W : ∀ i, Set (M i)} {π : ∀ i, Y i → M i}
  (hW : ∀ i, IsComplexAnalyticSubset (n := n i) (W i))
  (hπ : ∀ i, IsBlowupAlong (n i) (C i) (π i))
  (J : ∀ i, ofClosedAnalytic (W i) (hW i) ⟶ X)
  [hJopen : ∀ i, LocallyRingedSpace.IsOpenImmersion (J i).hom.left]
  (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf))
  (hd : ∀ i, W i ⊆ closure (W i \ C i))
  (hJ : ∀ i (y : W i),
    Ideal.map ((actualSubspaceInclusion (n := n i) (W i)).stalkMap y).hom
      (HironakaSmoothCentreRealDomainActualSheafStalk.actualWholeSheafStalkIdeal
        (HolomorphicIdealSheaves.vanishingIdeal (n := n i) (C i)) y.val) =
          nativePulledIdealStalkIdeal (J i).hom.left B b y)
  (hcover : ∀ x : X.obj.left, ∃ (i : ι) (w : W i), (J i).hom.left.base w = x)

include hJ in
private theorem actual_local_lift_ext (i : ι) {T : LocallyRingedSpace}
    (σT : T ⟶ complexPoint) (hT : hasAnalyticCharts (Over.mk σT))
    (F : T ⟶ X.obj.left) (hF : F ≫ X.obj.hom = σT)
    (hDense : Dense {x : T | F.base x ∉ (nonunitLocus B b)})
    (L₁ L₂ : T ⟶ EmbeddedIdealBlowupObjectGluing.localObject hW hπ i)
    (hL₁ : L₁ ≫ EmbeddedIdealBlowupObjectGluing.localProjection hW hπ J i = F)
    (hL₂ : L₂ ≫ EmbeddedIdealBlowupObjectGluing.localProjection hW hπ J i = F) : L₁ = L₂ := by
  let p := strictTransformProjection (hπ i) (hW i).isClosed
  let G := L₁ ≫ p
  let : LocallyRingedSpace.IsOpenImmersion (J i).hom.left := (hJopen i)
  have hp : L₁ ≫ p = L₂ ≫ p := by
    apply (cancel_mono (J i).hom.left).mp
    have hproj : EmbeddedIdealBlowupObjectGluing.localProjection hW hπ J i =
        p ≫ (J i).hom.left := rfl
    simpa only [hproj, Category.assoc] using hL₁.trans hL₂.symm
  have hset : {x : T | (G.base x).val ∉ C i} = {x : T | F.base x ∉ (nonunitLocus B b)} := by
    ext x
    have hx : (J i).hom.left.base (G.base x) = F.base x := congrArg (fun H => H.base x) hL₁
    exact not_congr (((chart_mem_nonunitLocus B b hW hπ J hJ) i (G.base x)).trans (iff_of_eq (congrArg (fun y => y ∈ (nonunitLocus B b)) hx)))
  have hDG : Dense {x : T | (G.base x).val ∉ C i} := by rw [hset]; exact hDense
  have hbase := base_eq_of_dense_projection_eq (hπ i) (hW i).isClosed G hDG L₁ L₂ rfl hp.symm
  have hpoint (L : T ⟶ EmbeddedIdealBlowupObjectGluing.localObject hW hπ i)
      (hL : L ≫ EmbeddedIdealBlowupObjectGluing.localProjection hW hπ J i = F) :
      L ≫ subspacePointMap (n := (n i)) (strictTransform (n i) (π i) (W i)) = σT := by
    calc
      _ = L ≫ (EmbeddedIdealBlowupObjectGluing.localProjection hW hπ J i ≫ X.obj.hom) :=
        congrArg (fun t => L ≫ t) (EmbeddedIdealBlowupObjectGluing.localProjection_point hW hπ J i).symm
      _ = (L ≫ EmbeddedIdealBlowupObjectGluing.localProjection hW hπ J i) ≫ X.obj.hom :=
        (Category.assoc _ _ _).symm
      _ = F ≫ X.obj.hom := congrArg (fun t => t ≫ X.obj.hom) hL
      _ = _ := hF
  exact morphism_eq_of_base_eq σT hT L₁ L₂ (hpoint L₁ hL₁) (hpoint L₂ hL₂) hbase

private theorem local_maps_compatible (A : SourceReducedComplexSpace) (F : A ⟶ X)
    (i j : ι) {P Q : LocallyRingedSpace} (a : P ⟶ A.obj.left) (c : Q ⟶ A.obj.left)
    [LocallyRingedSpace.IsOpenImmersion a] [LocallyRingedSpace.IsOpenImmersion c]
    (hQ : hasAnalyticCharts (Over.mk (c ≫ A.obj.hom)))
    (hDense : Dense {x : Q | F.hom.left.base (c.base x) ∉ (nonunitLocus B b)})
    (K : P ⟶ EmbeddedIdealBlowupObjectGluing.localObject hW hπ i)
    (L : Q ⟶ EmbeddedIdealBlowupObjectGluing.localObject hW hπ j)
    (hK : K ≫ EmbeddedIdealBlowupObjectGluing.localProjection hW hπ J i = a ≫ F.hom.left)
    (hL : L ≫ EmbeddedIdealBlowupObjectGluing.localProjection hW hπ J j = c ≫ F.hom.left) :
    pullback.fst a c ≫ (K ≫ EmbeddedIdealBlowupObjectGluing.inclusion hW hπ J B b hd hJ i) =
      pullback.snd a c ≫ (L ≫ EmbeddedIdealBlowupObjectGluing.inclusion hW hπ J B b hd hJ j) := by
  let H := pullback a c
  let u := pullback.fst a c ≫ K
  let v := pullback.snd a c ≫ L
  let s := pullback.snd a c ≫ c
  let F₀ := s ≫ F.hom.left
  have hu : u ≫ EmbeddedIdealBlowupObjectGluing.localProjection hW hπ J i = F₀ := by
    calc
      _ = pullback.fst a c ≫ (a ≫ F.hom.left) := by rw [Category.assoc, hK]
      _ = (pullback.snd a c ≫ c) ≫ F.hom.left := by rw [← Category.assoc, pullback.condition]
      _ = _ := rfl
  have hv : v ≫ EmbeddedIdealBlowupObjectGluing.localProjection hW hπ J j = F₀ := by
    rw [Category.assoc, hL]
    exact (Category.assoc _ _ _).symm
  have hr : range u.base ⊆ range (EmbeddedIdealBlowupObjectGluing.overlapInclusion hW hπ J i j).base := by
    rintro _ ⟨x, rfl⟩
    have hp : (EmbeddedIdealBlowupObjectGluing.localProjection hW hπ J i).base (u.base x) =
        (EmbeddedIdealBlowupObjectGluing.localProjection hW hπ J j).base (v.base x) :=
      congrArg (fun H => H.base x) (hu.trans hv.symm)
    have hm : (EmbeddedIdealBlowupObjectGluing.localProjection hW hπ J i).base (u.base x) ∈
        range (J j).hom.left.base := hp.symm ▸
      ⟨(strictTransformProjection (hπ j) (hW j).isClosed).base (v.base x), rfl⟩
    exact ⟨⟨u.base x, hm⟩, rfl⟩
  let R := LocallyRingedSpace.IsOpenImmersion.lift
    (EmbeddedIdealBlowupObjectGluing.overlapInclusion hW hπ J i j) u hr
  have hR : R ≫ EmbeddedIdealBlowupObjectGluing.overlapInclusion hW hπ J i j = u :=
    LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ hr
  let M := R ≫ EmbeddedIdealBlowupObjectGluing.transition hW hπ J B b hd hJ i j ≫
    EmbeddedIdealBlowupObjectGluing.overlapInclusion hW hπ J j i
  have hM : M ≫ EmbeddedIdealBlowupObjectGluing.localProjection hW hπ J j = F₀ := by
    calc
      _ = R ≫ (EmbeddedIdealBlowupObjectGluing.transition hW hπ J B b hd hJ i j ≫
          EmbeddedIdealBlowupObjectGluing.overlapInclusion hW hπ J j i ≫
            EmbeddedIdealBlowupObjectGluing.localProjection hW hπ J j) := by simp only [M, Category.assoc]
      _ = R ≫ (EmbeddedIdealBlowupObjectGluing.overlapInclusion hW hπ J i j ≫
          EmbeddedIdealBlowupObjectGluing.localProjection hW hπ J i) :=
        congrArg (fun t => R ≫ t) (EmbeddedIdealBlowupObjectGluing.transition_over hW hπ J B b hd hJ i j)
      _ = u ≫ EmbeddedIdealBlowupObjectGluing.localProjection hW hπ J i := by rw [← Category.assoc, hR]
      _ = _ := hu
  let σH := s ≫ A.obj.hom
  have hH : hasAnalyticCharts (Over.mk σH) :=
    hasAnalyticCharts_of_openImmersion _ _ hQ (pullback.snd a c) (Category.assoc _ _ _).symm
  have hF₀ : F₀ ≫ X.obj.hom = σH := by rw [Category.assoc, Over.w F.hom]
  have hD : Dense {x : H | F₀.base x ∉ (nonunitLocus B b)} := hDense.preimage
    (inferInstance : LocallyRingedSpace.IsOpenImmersion (pullback.snd a c)).base_open.isOpenMap
  have hMv : M = v := actual_local_lift_ext hW hπ J B b hJ j σH hH F₀ hF₀ hD M v hM hv
  calc
    _ = u ≫ EmbeddedIdealBlowupObjectGluing.inclusion hW hπ J B b hd hJ i := (Category.assoc _ _ _).symm
    _ = R ≫ (EmbeddedIdealBlowupObjectGluing.overlapInclusion hW hπ J i j ≫
        EmbeddedIdealBlowupObjectGluing.inclusion hW hπ J B b hd hJ i) := by rw [← Category.assoc, hR]
    _ = R ≫ (EmbeddedIdealBlowupObjectGluing.transition hW hπ J B b hd hJ i j ≫
        EmbeddedIdealBlowupObjectGluing.overlapInclusion hW hπ J j i ≫
          EmbeddedIdealBlowupObjectGluing.inclusion hW hπ J B b hd hJ j) :=
      congrArg (fun t => R ≫ t)
        ((EmbeddedIdealBlowupObjectGluing.glueData hW hπ J B b hd hJ).toGlueData.glue_condition i j).symm
    _ = M ≫ EmbeddedIdealBlowupObjectGluing.inclusion hW hπ J B b hd hJ j := by simp only [M, Category.assoc]
    _ = v ≫ EmbeddedIdealBlowupObjectGluing.inclusion hW hπ J B b hd hJ j :=
      congrArg (fun t => t ≫ EmbeddedIdealBlowupObjectGluing.inclusion hW hπ J B b hd hJ j) hMv
    _ = _ := Category.assoc _ _ _

/-- Native locally-free singleton generator data on the SAME original
WHOLE native ideal pullback produce a UNIQUE FULL ORIGINAL lift through the SAME
actual original glued projection. No global source SC or incoming source-lift
or density certificate is input; arbitrary pulled-source multiplicities remain. -/
theorem exists_unique_lift_of_locallyFreeData (A : SourceReducedComplexSpace) (F : A ⟶ X)
    (q : (nativePulledIdealModule F.hom.left B b).LocalGeneratorsData)
    [q.IsLocallyFreeData] [∀ t, Unique (q.generators t).I] :
    ∃! L : A ⟶ EmbeddedIdealBlowupOriginalObject.sourceObject hW hπ J B b hd hJ hcover,
      L ≫ EmbeddedIdealBlowupOriginalObject.projectionMorphism hW hπ J B b hd hJ hcover = F := by
  classical
  have hlocal := EmbeddedIdealBlowupGlobalUniversalLocal.exists_local_source_lift hW J hcover hπ B b hJ A F q
  choose idx P j K hj hx hP hfac hdLocal using hlocal
  let : ∀ x, LocallyRingedSpace.IsOpenImmersion (j x) := hj
  have hc : ∀ x : A.obj.left, ∃ (a : A.obj.left) (u : P a), (j a).base u = x := by
    intro x
    obtain ⟨u, hu⟩ := hx x
    exact ⟨x, u, hu⟩
  let S := EmbeddedIdealBlowupOriginalObject.sourceObject hW hπ J B b hd hJ hcover
  let p := EmbeddedIdealBlowupObjectGluing.projection hW hπ J B b hd hJ
  let f (a : A.obj.left) : P a ⟶ S.obj.left :=
    K a ≫ EmbeddedIdealBlowupObjectGluing.inclusion hW hπ J B b hd hJ (idx a)
  have hf (a : A.obj.left) : f a ≫ p = j a ≫ F.hom.left := by
    calc
      _ = K a ≫ EmbeddedIdealBlowupObjectGluing.localProjection hW hπ J (idx a) := by
        rw [Category.assoc, EmbeddedIdealBlowupObjectGluing.inclusion_projection]
      _ = _ := hfac a
  have hcompat : ∀ a c, pullback.fst (j a) (j c) ≫ f a = pullback.snd (j a) (j c) ≫ f c := by
    intro a c
    exact local_maps_compatible hW hπ J B b hd hJ A F (idx a) (idx c)
      (j a) (j c) (hP c) (hdLocal c) (K a) (K c) (hfac a) (hfac c)
  have hpoint (a : A.obj.left) : f a ≫ S.obj.hom = j a ≫ A.obj.hom := by
    change f a ≫ (p ≫ X.obj.hom) = _
    rw [← Category.assoc, hf a, Category.assoc, Over.w F.hom]
  obtain ⟨L, hL, _⟩ := exists_unique_over P j hc A.obj.hom S.obj.hom f hcompat hpoint
  have hLp : L.left ≫ p = F.hom.left := by
    apply HironakaIntrinsicMorphismGluing.hom_ext P j hc
    intro a
    rw [← Category.assoc, hL a, hf a]
  refine ⟨ObjectProperty.homMk L, ?_, ?_⟩
  · apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact hLp
  · intro L' hL'p
    have hL'raw : L'.hom.left ≫ p = F.hom.left :=
      congrArg (fun H => H.hom.left) hL'p
    have heq (a : A.obj.left) : j a ≫ L'.hom.left = j a ≫ L.left := by
      let M := j a ≫ L'.hom.left
      let v := EmbeddedIdealBlowupObjectGluing.inclusion hW hπ J B b hd hJ (idx a)
      have hMp : M ≫ p = j a ≫ F.hom.left := by rw [Category.assoc, hL'raw]
      have hr : range M.base ⊆ range v.base := by
        rintro _ ⟨u, rfl⟩
        have hp : p.base (M.base u) =
            (EmbeddedIdealBlowupObjectGluing.localProjection hW hπ J (idx a)).base ((K a).base u) :=
          congrArg (fun H => H.base u) (hMp.trans (hfac a).symm)
        have hm : p.base (M.base u) ∈ range (J (idx a)).hom.left.base := hp.symm ▸
          ⟨(strictTransformProjection (hπ (idx a)) (hW (idx a)).isClosed).base ((K a).base u), rfl⟩
        exact (Set.ext_iff.mp
          (EmbeddedIdealBlowupObjectGluing.preimage_chart_range hW hπ J B b hd hJ (idx a)) (M.base u)).mp hm
      let K' := LocallyRingedSpace.IsOpenImmersion.lift v M hr
      have hK'v : K' ≫ v = M := LocallyRingedSpace.IsOpenImmersion.lift_fac v M hr
      have hK'p : K' ≫ EmbeddedIdealBlowupObjectGluing.localProjection hW hπ J (idx a) =
          j a ≫ F.hom.left := by
        calc
          _ = K' ≫ (v ≫ p) := congrArg (fun t => K' ≫ t)
            (EmbeddedIdealBlowupObjectGluing.inclusion_projection hW hπ J B b hd hJ (idx a)).symm
          _ = (K' ≫ v) ≫ p := (Category.assoc _ _ _).symm
          _ = M ≫ p := congrArg (fun t => t ≫ p) hK'v
          _ = _ := hMp
      have hFpoint : (j a ≫ F.hom.left) ≫ X.obj.hom = j a ≫ A.obj.hom := by
        rw [Category.assoc, Over.w F.hom]
      have hKK : K' = K a := actual_local_lift_ext hW hπ J B b hJ (idx a)
        (j a ≫ A.obj.hom) (hP a) (j a ≫ F.hom.left) hFpoint (hdLocal a) K' (K a) hK'p (hfac a)
      calc
        _ = K' ≫ v := hK'v.symm
        _ = K a ≫ v := congrArg (fun t => t ≫ v) hKK
        _ = f a := rfl
        _ = _ := (hL a).symm
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact HironakaIntrinsicMorphismGluing.hom_ext P j hc L'.hom.left L.left heq

end

end Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupGlobalUniversal
