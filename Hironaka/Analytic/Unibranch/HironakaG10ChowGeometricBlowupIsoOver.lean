import Hironaka.Analytic.Unibranch.OriginalFiniteIdealGeometricBlowupImage
import Hironaka.Analytic.Unibranch.HironakaG10ChowStrictTransformCalculus

/-!
# The geometric blowup of any finite-type ideal is an isomorphism over the unit locus

Route step N1 of `work/hironaka-resume-20261111/G10C/GLOBAL-FLATTENING-ROUTE.md`: the native
geometric blowup `OriginalFiniteIdealGeometricBlowup.sourceObject B b` of an ARBITRARY
finite-type ideal `b : B ⟶ 𝒪_X` (no density hypothesis; this is the strict-transform side of a
blowup step) restricts to an isomorphism over the unit locus of the ideal.  The proof transcribes
the dense-case proof (`EmbeddedIdealBlowupOriginalBimeromorphic.projection_isIsoOver_compl_nonunitLocus`)
to the geometric gluing: the local geometric projections are isomorphisms off the centres
(`EmbeddedGeometricBlowup.geometricProjectionMorphism_isIsoOver_compl_centre`), the chart images are
saturated, and the projection hits the whole unit locus (its image is the closure of the unit locus,
`OriginalFiniteIdealGeometricBlowupImage.projection_range`).

Main declarations:

* `Model.projection_isIsoOver_compl_nonunitLocus` — for the glued geometric models;
* **`geometricProjection_isIsoOver`** — `IsIsoOver (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b)
  (nonunitLocus B b)ᶜ`;
* `geometricProjection_isOpenImmersionOn` — the projection is an open immersion on the preimage of
  the unit locus;
* `geometricProjection_injOn` — it is injective there.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace Topology CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG10ChowGeometricBlowupIsoOver

open Hironaka Hironaka.BlowupSequences
  Hironaka HironakaActualAnalyticSubspace
  HironakaSingularModuleSheafStalk HironakaNativePulledIdealSheaf SourceReducedComplexSpace
  EmbeddedGeometricBlowup EmbeddedIdealBlowupNonunitLocus HironakaG10ChowStrictTransformCalculus
  HironakaG10ChowFlatteningReduction

noncomputable section

/-- A morphism that is injective and an open immersion on the members of an open-immersion cover
of its source is an open immersion. -/
theorem isOpenImmersion_of_cover {A B : LocallyRingedSpace} {κ : Type}
    (V : κ → LocallyRingedSpace) (r : ∀ i, V i ⟶ A)
    [∀ i, LocallyRingedSpace.IsOpenImmersion (r i)]
    (hcover : ∀ x : A, ∃ (i : κ) (u : V i), (r i).base u = x)
    (f : A ⟶ B) (hinj : Function.Injective f.base)
    [∀ i, LocallyRingedSpace.IsOpenImmersion (r i ≫ f)] :
    LocallyRingedSpace.IsOpenImmersion f := by
  have hOpen : IsOpenMap f.base := by
    intro S hS
    have heq : f.base '' S = ⋃ i, (r i ≫ f).base '' ((r i).base ⁻¹' S) := by
      ext b
      constructor
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨i, u, rfl⟩ := hcover x
        exact mem_iUnion.mpr ⟨i, u, hx, rfl⟩
      · intro hb
        obtain ⟨i, u, hu, hub⟩ := mem_iUnion.mp hb
        exact ⟨(r i).base u, hu, hub⟩
    rw [heq]
    exact isOpen_iUnion fun i =>
      (inferInstance : LocallyRingedSpace.IsOpenImmersion (r i ≫ f)).base_open.isOpenMap _
        (hS.preimage (r i).base.hom.continuous)
  have hEmbedding : IsOpenEmbedding f.base :=
    IsOpenEmbedding.of_continuous_injective_isOpenMap f.base.hom.continuous hinj hOpen
  let : ∀ x, IsIso (f.stalkMap x) := by
    intro x
    obtain ⟨i, u, rfl⟩ := hcover x
    have hcomp : IsIso ((r i ≫ f).stalkMap u) := inferInstance
    rw [LocallyRingedSpace.stalkMap_comp] at hcomp
    exact @IsIso.of_isIso_comp_right _ _ _ _ _
      (f.stalkMap ((r i).base u)) ((r i).stalkMap u) (inferInstance) hcomp
  exact LocallyRingedSpace.IsOpenImmersion.of_stalk_iso f hEmbedding

variable {X : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf))

namespace Model

variable {ι : Type} {n : ι → ℕ} {M Y : ι → Type}
  [∀ i, TopologicalSpace (M i)] [∀ i, TopologicalSpace (Y i)]
  [∀ i, ChartedSpace (ComplexModel (n i)) (M i)] [∀ i, IsComplexManifold (n i) (M i)]
  [∀ i, ChartedSpace (ComplexModel (n i)) (Y i)] [∀ i, IsComplexManifold (n i) (Y i)]
  {C W : ∀ i, Set (M i)} {π : ∀ i, Y i → M i}
  (hW : ∀ i, IsComplexAnalyticSubset (n := n i) (W i))
  (hπ : ∀ i, IsBlowupAlong (n i) (C i) (π i))
  (J : ∀ i, ofClosedAnalytic (W i) (hW i) ⟶ X)
  [hJopen : ∀ i, LocallyRingedSpace.IsOpenImmersion (J i).hom.left]
  (hJ : ∀ i (y : W i),
    Ideal.map ((actualSubspaceInclusion (n := n i) (W i)).stalkMap y).hom
      (HironakaSmoothCentreRealDomainActualSheafStalk.actualWholeSheafStalkIdeal
        (HolomorphicIdealSheaves.vanishingIdeal (n := n i) (C i)) y.val) =
      nativePulledIdealStalkIdeal (J i).hom.left B b y)
  (hcover : ∀ x : X.obj.left, ∃ (i : ι) (w : W i), (J i).hom.left.base w = x)

/-- **The glued geometric projection is an isomorphism over the unit locus.** -/
theorem projection_isIsoOver_compl_nonunitLocus :
    IsIsoOver (EmbeddedGeometricIdealOriginalObject.projectionMorphism hW hπ J B b hJ hcover)
      (nonunitLocus B b)ᶜ := by
  classical
  let T := EmbeddedGeometricIdealObjectGluing.glued hW hπ J B b hJ
  let p : T ⟶ X.obj.left := EmbeddedGeometricIdealObjectGluing.projection hW hπ J B b hJ
  let O : Opens T := ⟨p.base ⁻¹' (nonunitLocus B b)ᶜ,
    (nonunitLocus_isClosed B b hW hπ J hJ hcover).isOpen_compl.preimage p.base.hom.continuous⟩
  let A := T.restrict O.isOpenEmbedding
  let j : A ⟶ T := T.ofRestrict O.isOpenEmbedding
  let hj : LocallyRingedSpace.IsOpenImmersion j := by
    dsimp only [j, A]
    infer_instance
  let f : A ⟶ X.obj.left := j ≫ p
  have hlocal (i : ι) :
      ∃ (V : LocallyRingedSpace)
        (k : V ⟶ EmbeddedGeometricIdealObjectGluing.localObject hW hπ i),
        LocallyRingedSpace.IsOpenImmersion k ∧
        range k.base = (geometricProjection (hπ i) (hW i).isClosed).base ⁻¹'
          ((Subtype.val : (W i) → (M i)) ⁻¹' C i)ᶜ ∧
        LocallyRingedSpace.IsOpenImmersion
          (k ≫ geometricProjection (hπ i) (hW i).isClosed) ∧
        range (k ≫ geometricProjection (hπ i) (hW i).isClosed).base =
          ((Subtype.val : (W i) → (M i)) ⁻¹' C i)ᶜ :=
    geometricProjectionMorphism_isIsoOver_compl_centre (hπ i) (hW i)
  choose V k hk hkr hkp hpr using hlocal
  let : ∀ i, LocallyRingedSpace.IsOpenImmersion (k i) := hk
  let : ∀ i, LocallyRingedSpace.IsOpenImmersion
      (k i ≫ geometricProjection (hπ i) (hW i).isClosed) := hkp
  let : ∀ i, LocallyRingedSpace.IsOpenImmersion (J i).hom.left := fun i => (hJopen i)
  let l : ∀ i, V i ⟶ T := fun i =>
    k i ≫ EmbeddedGeometricIdealObjectGluing.inclusion hW hπ J B b hJ i
  let : ∀ i, LocallyRingedSpace.IsOpenImmersion (l i) := by
    intro i
    dsimp only [l]
    infer_instance
  have hlp (i : ι) : l i ≫ p =
      (k i ≫ geometricProjection (hπ i) (hW i).isClosed) ≫ (J i).hom.left := by
    change (k i ≫ EmbeddedGeometricIdealObjectGluing.inclusion hW hπ J B b hJ i) ≫
      EmbeddedGeometricIdealObjectGluing.projection hW hπ J B b hJ = _
    rw [Category.assoc, EmbeddedGeometricIdealObjectGluing.inclusion_projection]
    rfl
  have hOff (i : ι) : range (l i).base ⊆ range j.base := by
    rintro _ ⟨u, rfl⟩
    have hku : (k i).base u ∈ range (k i).base := ⟨u, rfl⟩
    rw [hkr i] at hku
    have hpv : p.base ((l i).base u) =
        (J i).hom.left.base ((geometricProjection (hπ i) (hW i).isClosed).base ((k i).base u)) :=
      congrArg (fun H => H.base u) (hlp i)
    have hu : p.base ((l i).base u) ∉ (nonunitLocus B b) := by
      rw [hpv]
      exact (not_congr ((chart_mem_nonunitLocus B b hW hπ J hJ) i
        ((geometricProjection (hπ i) (hW i).isClosed).base ((k i).base u)))).mp hku
    exact ⟨⟨(l i).base u, hu⟩, rfl⟩
  let r : ∀ i, V i ⟶ A := fun i =>
    @LocallyRingedSpace.IsOpenImmersion.lift A (V i) T j (l i) hj (hOff i)
  have hr (i : ι) : r i ≫ j = l i :=
    @LocallyRingedSpace.IsOpenImmersion.lift_fac A (V i) T j (l i) hj (hOff i)
  let : ∀ i, LocallyRingedSpace.IsOpenImmersion (r i) := by
    intro i
    let : IsIso (pullback.snd j (l i)) :=
      @LocallyRingedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset
        A (V i) T j (l i) hj (hOff i)
    dsimp only [r, LocallyRingedSpace.IsOpenImmersion.lift]
    infer_instance
  have hrf (i : ι) : r i ≫ f =
      (k i ≫ geometricProjection (hπ i) (hW i).isClosed) ≫ (J i).hom.left := by
    change r i ≫ (j ≫ p) = _
    rw [← Category.assoc, hr i]
    exact hlp i
  let : ∀ i, LocallyRingedSpace.IsOpenImmersion (r i ≫ f) := by
    intro i
    rw [hrf i]
    exact @LocallyRingedSpace.IsOpenImmersion.comp _ _ _
      (k i ≫ geometricProjection (hπ i) (hW i).isClosed) (hkp i)
      (J i).hom.left (hJopen i)
  have hsat (i : ι) : f.base ⁻¹' range (J i).hom.left.base = range (r i).base := by
    ext a
    constructor
    · intro ha
      have haT : j.base a ∈
          range (EmbeddedGeometricIdealObjectGluing.inclusion hW hπ J B b hJ i).base := by
        rw [← EmbeddedGeometricIdealObjectGluing.preimage_chart_range]
        exact ha
      obtain ⟨y, hy⟩ := haT
      have hpv : (J i).hom.left.base ((geometricProjection (hπ i) (hW i).isClosed).base y) =
          p.base (j.base a) := by
        have hproj := congrArg (fun H => H.base y)
          (EmbeddedGeometricIdealObjectGluing.inclusion_projection hW hπ J B b hJ i)
        calc
          _ = p.base ((EmbeddedGeometricIdealObjectGluing.inclusion hW hπ J B b hJ i).base y) :=
            hproj.symm
          _ = _ := congrArg p.base hy
      have hyoff : y ∈ (geometricProjection (hπ i) (hW i).isClosed).base ⁻¹'
          ((Subtype.val : (W i) → (M i)) ⁻¹' C i)ᶜ := by
        apply (not_congr ((chart_mem_nonunitLocus B b hW hπ J hJ) i
          ((geometricProjection (hπ i) (hW i).isClosed).base y))).mpr
        rw [hpv]
        exact a.property
      have hyk : y ∈ range (k i).base := by rw [hkr i]; exact hyoff
      obtain ⟨u, hu⟩ := hyk
      refine ⟨u, ?_⟩
      apply hj.base_open.injective
      calc
        j.base ((r i).base u) = (l i).base u := congrArg (fun H => H.base u) (hr i)
        _ = (EmbeddedGeometricIdealObjectGluing.inclusion hW hπ J B b hJ i).base y :=
          congrArg (EmbeddedGeometricIdealObjectGluing.inclusion hW hπ J B b hJ i).base hu
        _ = j.base a := hy
    · rintro ⟨u, rfl⟩
      have hpv := congrArg (fun H => H.base u) (hrf i)
      exact ⟨(geometricProjection (hπ i) (hW i).isClosed).base ((k i).base u), hpv.symm⟩
  have hrcover : ∀ a : A, ∃ (i : ι) (u : V i), (r i).base u = a := by
    intro a
    obtain ⟨i, w, hw⟩ := hcover (f.base a)
    have ha : a ∈ range (r i).base := by
      rw [← hsat i]
      exact ⟨w, hw⟩
    obtain ⟨u, hu⟩ := ha
    exact ⟨i, u, hu⟩
  have hinj : Function.Injective f.base := by
    intro a b hab
    obtain ⟨i, w, hw⟩ := hcover (f.base a)
    have ha : a ∈ range (r i).base := by rw [← hsat i]; exact ⟨w, hw⟩
    have hb : b ∈ range (r i).base := by rw [← hsat i]; exact ⟨w, hw.trans hab⟩
    obtain ⟨u, hu⟩ := ha
    obtain ⟨v, hv⟩ := hb
    have huv : u = v :=
      (inferInstance : LocallyRingedSpace.IsOpenImmersion (r i ≫ f)).base_open.injective
        ((congrArg f.base hu).trans (hab.trans (congrArg f.base hv).symm))
    exact hu.symm.trans ((congrArg (r i).base huv).trans hv)
  have hf : LocallyRingedSpace.IsOpenImmersion f := isOpenImmersion_of_cover V r hrcover f hinj
  have hjrange : range j.base = p.base ⁻¹' (nonunitLocus B b)ᶜ := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      exact a.property
    · intro hy
      exact ⟨⟨y, hy⟩, rfl⟩
  have hprange : range p.base = closure (OriginalFiniteIdealGeometricBlowupImage.unitLocus B b) :=
    OriginalFiniteIdealGeometricBlowupImage.Model.projection_range B b hW hπ J hJ hcover
  have hfrange : range f.base = (nonunitLocus B b)ᶜ := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact a.property
    · intro hx
      have hxU : x ∈ OriginalFiniteIdealGeometricBlowupImage.unitLocus B b := by
        change LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b x) = ⊤
        by_contra h
        exact hx h
      have hxr : x ∈ range p.base := by
        rw [hprange]
        exact subset_closure hxU
      obtain ⟨y, hy⟩ := hxr
      have hyO : p.base y ∉ (nonunitLocus B b) := by rw [hy]; exact hx
      exact ⟨⟨y, hyO⟩, hy⟩
  exact ⟨A, j, hj, hjrange, hf, hfrange⟩

end Model

variable [B.IsFiniteType]

/-- **The geometric blowup of a finite-type ideal is an isomorphism over its unit locus.** -/
theorem geometricProjection_isIsoOver :
    IsIsoOver (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b) (nonunitLocus B b)ᶜ := by
  unfold OriginalFiniteIdealGeometricBlowup.projectionMorphism
  exact Model.projection_isIsoOver_compl_nonunitLocus B b _ _ _ _ _

/-- The geometric blowup projection is an open immersion on the preimage of the unit locus. -/
theorem geometricProjection_isOpenImmersionOn :
    IsOpenImmersionOn (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b)
      ((OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.base ⁻¹'
        (nonunitLocus B b)ᶜ) :=
  isOpenImmersionOn_of_isIsoOver (geometricProjection_isIsoOver B b)

/-- The geometric blowup projection is injective over the unit locus. -/
theorem geometricProjection_injOn :
    InjOn (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.base
      ((OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.base ⁻¹'
        (nonunitLocus B b)ᶜ) :=
  IsOpenImmersionOn.injOn (geometricProjection_isOpenImmersionOn B b)

end

end Hironaka.Analytic.Unibranch.HironakaG10ChowGeometricBlowupIsoOver
