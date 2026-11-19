import Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupOriginalObject
import Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupNonunitLocus

/-!
# Same whole-ideal projection is proper bimeromorphic in the original category

The exceptional target subset is DERIVED as the nonunit locus of the SAME
native b-stalk image. Its trace, original analyticity and thinness are proved
without centre containment or replacing the whole ideal by a reduced ideal.
Native local off-centre geometry and the SAME saturation/projection squares
produce the full original isomorphism on its complement.
Blueprint: `embedded-ideal-blowup-original-bimeromorphic.tex`.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace Topology CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupOriginalBimeromorphic

open Hironaka Hironaka.BlowupSequences
  Hironaka HironakaActualAnalyticSubspace
  HironakaSingularSubspaceBlowupLift HironakaSingularModuleSheafStalk
  HironakaNativePulledIdealSheaf SourceReducedComplexSpace EmbeddedBlowup
  EmbeddedIdealBlowupOriginalObject EmbeddedIdealBlowupNonunitLocus

noncomputable section

private theorem isOpenImmersion_of_cover {A B : LocallyRingedSpace} {κ : Type}
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

/-- Actual local strict-transform density and the SAME full projection
square prove thinness of the literal global preimage on the SAME source. -/
theorem preimage_nonunitLocus_interior_eq_empty :
    interior ((projectionMorphism hW hπ J B b hd hJ hcover).hom.left.base ⁻¹' (nonunitLocus B b)) = ∅ := by
  rw [interior_eq_empty_iff_dense_compl, dense_iff_closure_eq, eq_univ_iff_forall]
  intro x
  obtain ⟨i, y, rfl⟩ := EmbeddedIdealBlowupObjectGluing.inclusion_jointly_surjective hW hπ J B b hd hJ x
  have hy : y ∈ closure ((strictTransformProjection (hπ i) (hW i).isClosed).base ⁻¹'
      {u : (W i) | u.val ∉ C i}) :=
    dense_preimage_compl_centre (hπ i) (hW i).isClosed (hd i) y
  apply closure_mono (s := (EmbeddedIdealBlowupObjectGluing.inclusion hW hπ J B b hd hJ i).base ''
      ((strictTransformProjection (hπ i) (hW i).isClosed).base ⁻¹'
        {u : (W i) | u.val ∉ C i})) ?_
    (mem_closure_image
      (EmbeddedIdealBlowupObjectGluing.inclusion hW hπ J B b hd hJ i).base.hom.continuous.continuousAt hy)
  rintro _ ⟨u, hu, rfl⟩
  change (EmbeddedIdealBlowupObjectGluing.projection hW hπ J B b hd hJ).base
    ((EmbeddedIdealBlowupObjectGluing.inclusion hW hπ J B b hd hJ i).base u) ∉ (nonunitLocus B b)
  have hp := congrArg (fun H => H.base u)
    (EmbeddedIdealBlowupObjectGluing.inclusion_projection hW hπ J B b hd hJ i)
  change (EmbeddedIdealBlowupObjectGluing.inclusion hW hπ J B b hd hJ i ≫
    EmbeddedIdealBlowupObjectGluing.projection hW hπ J B b hd hJ).base u ∉ (nonunitLocus B b)
  rw [hp]
  exact (not_congr ((chart_mem_nonunitLocus B b hW hπ J hJ) i ((strictTransformProjection (hπ i) (hW i).isClosed).base u))).mp hu

/-- The SAME actual full projection is an isomorphism off the SAME centre;
all local off-centre maps and global stalk isomorphisms are derived. -/
theorem projection_isIsoOver_compl_nonunitLocus :
    IsIsoOver (projectionMorphism hW hπ J B b hd hJ hcover) (nonunitLocus B b)ᶜ := by
  classical
  let T := EmbeddedIdealBlowupObjectGluing.glued hW hπ J B b hd hJ
  let p : T ⟶ X.obj.left := EmbeddedIdealBlowupObjectGluing.projection hW hπ J B b hd hJ
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
        (k : V ⟶ EmbeddedIdealBlowupObjectGluing.localObject hW hπ i),
        LocallyRingedSpace.IsOpenImmersion k ∧
        range k.base = (strictTransformProjection (hπ i) (hW i).isClosed).base ⁻¹'
          ((Subtype.val : (W i) → (M i)) ⁻¹' C i)ᶜ ∧
        LocallyRingedSpace.IsOpenImmersion
          (k ≫ strictTransformProjection (hπ i) (hW i).isClosed) ∧
        range (k ≫ strictTransformProjection (hπ i) (hW i).isClosed).base =
          ((Subtype.val : (W i) → (M i)) ⁻¹' C i)ᶜ :=
    strictTransformMorphism_isIsoOver_compl_centre (hπ i) (hW i)
  choose V k hk hkr hkp hpr using hlocal
  let : ∀ i, LocallyRingedSpace.IsOpenImmersion (k i) := hk
  let : ∀ i, LocallyRingedSpace.IsOpenImmersion
      (k i ≫ strictTransformProjection (hπ i) (hW i).isClosed) := hkp
  let : ∀ i, LocallyRingedSpace.IsOpenImmersion (J i).hom.left := fun i => (hJopen i)
  let l : ∀ i, V i ⟶ T := fun i =>
    k i ≫ EmbeddedIdealBlowupObjectGluing.inclusion hW hπ J B b hd hJ i
  let : ∀ i, LocallyRingedSpace.IsOpenImmersion (l i) := by
    intro i
    dsimp only [l]
    infer_instance
  have hlp (i : ι) : l i ≫ p =
      (k i ≫ strictTransformProjection (hπ i) (hW i).isClosed) ≫ (J i).hom.left := by
    change (k i ≫ EmbeddedIdealBlowupObjectGluing.inclusion hW hπ J B b hd hJ i) ≫
      EmbeddedIdealBlowupObjectGluing.projection hW hπ J B b hd hJ = _
    rw [Category.assoc, EmbeddedIdealBlowupObjectGluing.inclusion_projection]
    rfl
  have hOff (i : ι) : range (l i).base ⊆ range j.base := by
    rintro _ ⟨u, rfl⟩
    have hku : (k i).base u ∈ range (k i).base := ⟨u, rfl⟩
    rw [hkr i] at hku
    have hpv : p.base ((l i).base u) =
        (J i).hom.left.base ((strictTransformProjection (hπ i) (hW i).isClosed).base ((k i).base u)) :=
      congrArg (fun H => H.base u) (hlp i)
    have hu : p.base ((l i).base u) ∉ (nonunitLocus B b) := by
      rw [hpv]
      exact (not_congr ((chart_mem_nonunitLocus B b hW hπ J hJ) i
        ((strictTransformProjection (hπ i) (hW i).isClosed).base ((k i).base u)))).mp hku
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
      (k i ≫ strictTransformProjection (hπ i) (hW i).isClosed) ≫ (J i).hom.left := by
    change r i ≫ (j ≫ p) = _
    rw [← Category.assoc, hr i]
    exact hlp i
  let : ∀ i, LocallyRingedSpace.IsOpenImmersion (r i ≫ f) := by
    intro i
    rw [hrf i]
    exact @LocallyRingedSpace.IsOpenImmersion.comp _ _ _
      (k i ≫ strictTransformProjection (hπ i) (hW i).isClosed) (hkp i)
      (J i).hom.left (hJopen i)
  have hsat (i : ι) : f.base ⁻¹' range (J i).hom.left.base = range (r i).base := by
    ext a
    constructor
    · intro ha
      have haT : j.base a ∈ range (EmbeddedIdealBlowupObjectGluing.inclusion hW hπ J B b hd hJ i).base := by
        rw [← EmbeddedIdealBlowupObjectGluing.preimage_chart_range]
        exact ha
      obtain ⟨y, hy⟩ := haT
      have hpv : (J i).hom.left.base ((strictTransformProjection (hπ i) (hW i).isClosed).base y) =
          p.base (j.base a) := by
        have hproj := congrArg (fun H => H.base y)
          (EmbeddedIdealBlowupObjectGluing.inclusion_projection hW hπ J B b hd hJ i)
        calc
          _ = p.base ((EmbeddedIdealBlowupObjectGluing.inclusion hW hπ J B b hd hJ i).base y) := hproj.symm
          _ = _ := congrArg p.base hy
      have hyoff : y ∈ (strictTransformProjection (hπ i) (hW i).isClosed).base ⁻¹'
          ((Subtype.val : (W i) → (M i)) ⁻¹' C i)ᶜ := by
        apply (not_congr ((chart_mem_nonunitLocus B b hW hπ J hJ) i ((strictTransformProjection (hπ i) (hW i).isClosed).base y))).mpr
        rw [hpv]
        exact a.property
      have hyk : y ∈ range (k i).base := by rw [hkr i]; exact hyoff
      obtain ⟨u, hu⟩ := hyk
      refine ⟨u, ?_⟩
      apply hj.base_open.injective
      calc
        j.base ((r i).base u) = (l i).base u := congrArg (fun H => H.base u) (hr i)
        _ = (EmbeddedIdealBlowupObjectGluing.inclusion hW hπ J B b hd hJ i).base y :=
          congrArg (EmbeddedIdealBlowupObjectGluing.inclusion hW hπ J B b hd hJ i).base hu
        _ = j.base a := hy
    · rintro ⟨u, rfl⟩
      have hpv := congrArg (fun H => H.base u) (hrf i)
      exact ⟨(strictTransformProjection (hπ i) (hW i).isClosed).base ((k i).base u), hpv.symm⟩
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
  have hfrange : range f.base = (nonunitLocus B b)ᶜ := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact a.property
    · intro hx
      obtain ⟨y, hy⟩ := EmbeddedIdealBlowupObjectGluing.projection_surjective hW hπ J B b hd hJ hcover x
      have hyO : p.base y ∉ (nonunitLocus B b) := by rw [hy]; exact hx
      exact ⟨⟨y, hyO⟩, hy⟩
  exact ⟨A, j, hj, hjrange, hf, hfrange⟩

/-- The existing ORIGINAL proper-bimeromorphic predicate, on the SAME full p. -/
theorem projection_isProperBimeromorphic :
    IsProperBimeromorphic (projectionMorphism hW hπ J B b hd hJ hcover) := by
  exact ⟨projection_isProperMap hW hπ J B b hd hJ hcover, nonunitLocus B b,
    nonunitLocus_isAnalyticSubset B b hW hπ J hJ hcover,
    nonunitLocus_interior_eq_empty B b hW hπ J hJ hcover hd,
    preimage_nonunitLocus_interior_eq_empty hW hπ J B b hd hJ hcover,
    projection_isIsoOver_compl_nonunitLocus hW hπ J B b hd hJ hcover⟩

end

end Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupOriginalBimeromorphic
