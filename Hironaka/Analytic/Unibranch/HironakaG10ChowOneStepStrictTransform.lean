import Hironaka.Analytic.Unibranch.HironakaG10ChowGeometricBlowupIsoOver
import Hironaka.Analytic.Unibranch.OriginalFiniteIdealBlowupSquare
import Hironaka.Analytic.Unibranch.OriginalFiniteIdealBlowupUniversal
import Hironaka.Resolution.HironakaNativePulledIdealStalk

/-!
# The strict transform under one native ideal blowup (global flattening, route §3.2)

Let `f : Y ⟶ X` be a proper morphism of reduced complex spaces and `b : B ⟶ 𝒪_X` a finite-type
ideal with dense unit locus.  The blowup step of a flattening round is the native blowup
`σ : X' = Bl_B X ⟶ X` (`OriginalFiniteIdealBlowup`), with exceptional set
`E = σ⁻¹(nonunit locus of B)`.  Its strict transform is the GEOMETRIC blowup
`q : Y' = Bl_{f*B} Y ⟶ Y` of the pulled-back ideal (`OriginalFiniteIdealGeometricBlowup`; its image
is the closure of the unit locus, so components of `Y` inside `f⁻¹ V(B)` are discarded), with
`p : Y' ⟶ X'` given by the universal property of `σ` (the pulled ideal of `B` along `q ≫ f` is
invertible, `OriginalFiniteIdealBlowupSquare.composite_ideal_exists_locallyFreeData`).

Proved here: the unit locus of the pulled ideal is the preimage of the unit locus
(`mem_pulledUnitLocus_iff`); `σ` is a tower step, `E` is closed with empty interior and `σ` is an
open immersion off `E`; of the six fields of `IsStrictTransform f σ E p q`, five: `comm`, `proper`,
`covers`, `dense`, `openImmersionOn`, and `pair_injective` over the unit locus
(`strict_pairInjective_of_mem`).  The full `pair_injective` (points of the exceptional fibres) is
chart-level (route step N2) and enters `isStrictTransform_of_pairInjective` and
`isFlatteningData_of_pairInjective` as an explicit hypothesis on the constructed maps.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10ChowOneStepStrictTransform

open Hironaka HironakaSingularModuleSheafStalk HironakaNativePulledIdealSheaf
  HironakaNativePulledIdealFiniteType HironakaNativePulledIdealStalk SourceReducedComplexSpace
  EmbeddedIdealBlowupNonunitLocus HironakaG10ChowTowerDomination HironakaG10ChowFlatteningReduction
  HironakaG10ChowStrictTransformCalculus HironakaG10ChowGeometricBlowupIsoOver

noncomputable section

/-! ### Unit loci of pulled-back ideals -/

theorem local_map_ideal_eq_top_iff {R S : Type} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (φ : R →+* S) [IsLocalHom φ] (I : Ideal R) :
    Ideal.map φ I = ⊤ ↔ I = ⊤ := by
  constructor
  · intro h
    by_contra hI
    have hlt : Ideal.map φ I < ⊤ :=
      (Ideal.map_mono (IsLocalRing.le_maximalIdeal hI)).trans_lt
        (IsLocalRing.map_maximalIdeal_lt_top φ)
    exact hlt.ne h
  · rintro rfl
    exact Ideal.map_top φ

variable {X Y : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf))

/-- **The unit locus of a pulled-back ideal is the preimage of the unit locus.** -/
theorem mem_pulledUnitLocus_iff (f : Y ⟶ X) (y : Y.obj.left) :
    y ∉ nonunitLocus (nativePulledIdealModule f.hom.left B b)
        (nativePulledIdealInclusion f.hom.left B b) ↔
      f.hom.left.base y ∉ nonunitLocus B b := by
  have hY : IsLocalRing (Y.obj.left.presheaf.stalk y).carrier := Y.obj.left.isLocalRing y
  have hX : IsLocalRing (X.obj.left.presheaf.stalk (f.hom.left.base y)).carrier :=
    X.obj.left.isLocalRing (f.hom.left.base y)
  have hrange := nativePulledIdealStalkInclusion_range f.hom.left B b y
  change ¬ (LinearMap.range (stalkInclusionLinearMap Y.obj.left.toSheafedSpace.sheaf
      (nativePulledIdealModule f.hom.left B b) (nativePulledIdealInclusion f.hom.left B b) y)
        ≠ ⊤) ↔
    ¬ (LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b
      (f.hom.left.base y)) ≠ ⊤)
  rw [not_not, not_not]
  change LinearMap.range (nativePulledIdealStalkInclusion f.hom.left B b y) = ⊤ ↔ _
  rw [hrange]
  exact local_map_ideal_eq_top_iff (f.hom.left.stalkMap y).hom _

/-! ### The blowup step -/

section Step

variable [B.IsFiniteType]
  (hDense : Dense {x : X.obj.left |
    LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b x) = ⊤})

/-- The blowup step `σ : Bl_B X ⟶ X`. -/
abbrev stepProj : OriginalFiniteIdealBlowup.sourceObject B b hDense ⟶ X :=
  OriginalFiniteIdealBlowup.projectionMorphism B b hDense

/-- The exceptional set `E = σ⁻¹(nonunit locus)` of the blowup step. -/
abbrev stepExcep : Set (OriginalFiniteIdealBlowup.sourceObject B b hDense).obj.left :=
  (stepProj B b hDense).hom.left.base ⁻¹' nonunitLocus B b

/-- The dense blowup is an isomorphism over the unit locus. -/
theorem stepProj_isIsoOver : IsIsoOver (stepProj B b hDense) (nonunitLocus B b)ᶜ := by
  unfold stepProj OriginalFiniteIdealBlowup.projectionMorphism
  exact EmbeddedIdealBlowupOriginalBimeromorphic.projection_isIsoOver_compl_nonunitLocus
    _ _ _ B b _ _ _

/-- The exceptional set has empty interior. -/
theorem interior_stepExcep : interior (stepExcep B b hDense) = ∅ := by
  unfold stepExcep stepProj OriginalFiniteIdealBlowup.projectionMorphism
  exact EmbeddedIdealBlowupOriginalBimeromorphic.preimage_nonunitLocus_interior_eq_empty
    _ _ _ B b _ _ _

include hDense in
/-- The nonunit locus of an ideal with a dense unit locus is closed (it is the complement of the
open image of the isomorphism locus of its blowup). -/
theorem isClosed_nonunitLocus : IsClosed (nonunitLocus B b) := by
  obtain ⟨V, j, -, -, hjσ, hr⟩ := stepProj_isIsoOver B b hDense
  rw [← isOpen_compl_iff, ← hr]
  exact hjσ.base_open.isOpen_range

theorem isClosed_stepExcep : IsClosed (stepExcep B b hDense) :=
  (isClosed_nonunitLocus B b hDense).preimage (stepProj B b hDense).hom.left.base.hom.continuous

theorem stepProj_isOpenImmersionOn :
    IsOpenImmersionOn (stepProj B b hDense) (stepExcep B b hDense)ᶜ :=
  isOpenImmersionOn_of_isIsoOver (stepProj_isIsoOver B b hDense)

/-- The blowup step is a one-step tower. -/
theorem stepProj_isNativeBlowupTower :
    IsNativeBlowupTower X (OriginalFiniteIdealBlowup.sourceObject B b hDense)
      (stepProj B b hDense) := by
  have h := IsNativeBlowupTower.step (𝟙 X) B b hDense IsNativeBlowupTower.refl
  rwa [Category.comp_id] at h

/-! ### The strict transform -/

variable (f : Y ⟶ X)

local instance pulled_isFiniteType : (nativePulledIdealModule f.hom.left B b).IsFiniteType :=
  nativePulledIdealModule_isFiniteType f.hom.left B b

/-- The strict transform `Y' = Bl_{f*B} Y` (geometric blowup of the pulled ideal). -/
abbrev strictSource : SourceReducedComplexSpace :=
  OriginalFiniteIdealGeometricBlowup.sourceObject (nativePulledIdealModule f.hom.left B b)
    (nativePulledIdealInclusion f.hom.left B b)

/-- Its projection `q : Y' ⟶ Y`. -/
abbrev strictQ : strictSource B b f ⟶ Y :=
  OriginalFiniteIdealGeometricBlowup.projectionMorphism (nativePulledIdealModule f.hom.left B b)
    (nativePulledIdealInclusion f.hom.left B b)

theorem exists_unique_strictP :
    ∃! L : strictSource B b f ⟶ OriginalFiniteIdealBlowup.sourceObject B b hDense,
      L ≫ stepProj B b hDense = strictQ B b f ≫ f := by
  obtain ⟨q, hq, huniq⟩ := OriginalFiniteIdealBlowupSquare.composite_ideal_exists_locallyFreeData B b f
  let : q.IsLocallyFreeData := hq
  let : ∀ i, Unique (q.generators i).I := fun i => Classical.choice (huniq i)
  exact OriginalFiniteIdealBlowupUniversal.exists_unique_lift_of_locallyFreeData B b hDense
    (strictSource B b f) (strictQ B b f ≫ f) q

/-- The map `p : Y' ⟶ X'` of the strict transform. -/
def strictP : strictSource B b f ⟶ OriginalFiniteIdealBlowup.sourceObject B b hDense :=
  Classical.choose (exists_unique_strictP B b hDense f)

theorem strictP_comp : strictP B b hDense f ≫ stepProj B b hDense = strictQ B b f ≫ f :=
  (Classical.choose_spec (exists_unique_strictP B b hDense f)).1

theorem strictP_comp_apply (y : (strictSource B b f).obj.left) :
    (stepProj B b hDense).hom.left.base ((strictP B b hDense f).hom.left.base y) =
      f.hom.left.base ((strictQ B b f).hom.left.base y) :=
  congrArg (fun H : strictSource B b f ⟶ X => H.hom.left.base y) (strictP_comp B b hDense f)

theorem strictP_isProperMap (hf : IsProperMap f.hom.left.base) :
    IsProperMap (strictP B b hDense f).hom.left.base := by
  let : T2Space (OriginalFiniteIdealBlowup.sourceObject B b hDense).obj.left.toPresheafedSpace :=
    (OriginalFiniteIdealBlowup.sourceObject B b hDense).property.1
  have hcomp : IsProperMap ((strictP B b hDense f ≫ stepProj B b hDense).hom.left.base) := by
    rw [strictP_comp B b hDense f]
    exact hf.comp (OriginalFiniteIdealGeometricBlowup.projection_isProperMap _ _)
  exact isProperMap_of_comp_of_t2 (strictP B b hDense f).hom.left.base.hom.continuous
    (stepProj B b hDense).hom.left.base.hom.continuous hcomp

/-- `p⁻¹(Eᶜ)` is the preimage under `q` of the unit locus of the pulled ideal. -/
theorem strictP_preimage_compl_excep :
    (strictP B b hDense f).hom.left.base ⁻¹' (stepExcep B b hDense)ᶜ =
      (strictQ B b f).hom.left.base ⁻¹' (nonunitLocus (nativePulledIdealModule f.hom.left B b)
        (nativePulledIdealInclusion f.hom.left B b))ᶜ := by
  ext y
  change (stepProj B b hDense).hom.left.base ((strictP B b hDense f).hom.left.base y) ∉
      nonunitLocus B b ↔ _
  rw [strictP_comp_apply B b hDense f y]
  exact (mem_pulledUnitLocus_iff B b f _).symm

theorem strict_dense :
    Dense ((strictP B b hDense f).hom.left.base ⁻¹' (stepExcep B b hDense)ᶜ) := by
  rw [strictP_preimage_compl_excep B b hDense f]
  have hset : (nonunitLocus (nativePulledIdealModule f.hom.left B b)
      (nativePulledIdealInclusion f.hom.left B b))ᶜ =
      OriginalFiniteIdealGeometricBlowupImage.unitLocus (nativePulledIdealModule f.hom.left B b)
        (nativePulledIdealInclusion f.hom.left B b) := by
    ext y
    change ¬ (_ ≠ ⊤) ↔ _ = ⊤
    exact not_not
  rw [hset]
  unfold strictQ OriginalFiniteIdealGeometricBlowup.projectionMorphism
  exact OriginalFiniteIdealGeometricBlowupImage.Model.source_unit_preimage_dense _ _ _ _ _ _ _

theorem strict_openImmersionOn :
    IsOpenImmersionOn (strictQ B b f)
      ((strictP B b hDense f).hom.left.base ⁻¹' (stepExcep B b hDense)ᶜ) := by
  rw [strictP_preimage_compl_excep B b hDense f]
  exact geometricProjection_isOpenImmersionOn _ _

theorem strict_covers (y : Y.obj.left) (x' : (OriginalFiniteIdealBlowup.sourceObject B b hDense).obj.left)
    (hx' : x' ∉ stepExcep B b hDense)
    (hyx : f.hom.left.base y = (stepProj B b hDense).hom.left.base x') :
    ∃ y' : (strictSource B b f).obj.left,
      (strictP B b hDense f).hom.left.base y' = x' ∧ (strictQ B b f).hom.left.base y' = y := by
  have hfy : f.hom.left.base y ∉ nonunitLocus B b := by
    rw [hyx]
    exact hx'
  have hyU : y ∉ nonunitLocus (nativePulledIdealModule f.hom.left B b)
      (nativePulledIdealInclusion f.hom.left B b) := (mem_pulledUnitLocus_iff B b f y).mpr hfy
  have hyR : y ∈ range (strictQ B b f).hom.left.base := by
    rw [OriginalFiniteIdealGeometricBlowupImage.projection_range]
    apply subset_closure
    change LinearMap.range _ = ⊤
    by_contra h
    exact hyU h
  obtain ⟨y', rfl⟩ := hyR
  refine ⟨y', ?_, rfl⟩
  have hinj := IsOpenImmersionOn.injOn (stepProj_isOpenImmersionOn B b hDense)
  apply hinj
  · change (stepProj B b hDense).hom.left.base ((strictP B b hDense f).hom.left.base y') ∉
      nonunitLocus B b
    rw [strictP_comp_apply B b hDense f y']
    exact hfy
  · exact hx'
  · rw [strictP_comp_apply B b hDense f y']
    exact hyx

/-- Pair-injectivity over the unit locus: two points of `Y'` with the same image in `Y`, lying over
the unit locus, coincide. -/
theorem strict_pairInjective_of_mem (a c : (strictSource B b f).obj.left)
    (ha : a ∈ (strictP B b hDense f).hom.left.base ⁻¹' (stepExcep B b hDense)ᶜ)
    (hc : c ∈ (strictP B b hDense f).hom.left.base ⁻¹' (stepExcep B b hDense)ᶜ)
    (hq : (strictQ B b f).hom.left.base a = (strictQ B b f).hom.left.base c) : a = c :=
  IsOpenImmersionOn.injOn (strict_openImmersionOn B b hDense f) ha hc hq

/-- **The one-step strict transform**, given pair-injectivity of `(p, q)` (route step N2). -/
theorem isStrictTransform_of_pairInjective (hf : IsProperMap f.hom.left.base)
    (hpair : ∀ a c : (strictSource B b f).obj.left,
      (strictP B b hDense f).hom.left.base a = (strictP B b hDense f).hom.left.base c →
        (strictQ B b f).hom.left.base a = (strictQ B b f).hom.left.base c → a = c) :
    IsStrictTransform f (stepProj B b hDense) (stepExcep B b hDense) (strictP B b hDense f)
      (strictQ B b f) where
  comm := (strictP_comp B b hDense f).symm
  proper := strictP_isProperMap B b hDense f hf
  pair_injective := hpair
  covers := strict_covers B b hDense f
  dense := strict_dense B b hDense f
  openImmersionOn := strict_openImmersionOn B b hDense f

/-- **One blowup step with its strict transform is flattening data**, given pair-injectivity. -/
theorem isFlatteningData_of_pairInjective (hf : IsProperMap f.hom.left.base)
    (hpair : ∀ a c : (strictSource B b f).obj.left,
      (strictP B b hDense f).hom.left.base a = (strictP B b hDense f).hom.left.base c →
        (strictQ B b f).hom.left.base a = (strictQ B b f).hom.left.base c → a = c) :
    IsFlatteningData f (stepProj B b hDense) (stepExcep B b hDense) (strictP B b hDense f)
      (strictQ B b f) where
  tower := stepProj_isNativeBlowupTower B b hDense
  closed := isClosed_stepExcep B b hDense
  thin := interior_stepExcep B b hDense
  openImmersion := stepProj_isOpenImmersionOn B b hDense
  strict := isStrictTransform_of_pairInjective B b hDense f hf hpair

end Step

end

end Hironaka.Analytic.Unibranch.HironakaG10ChowOneStepStrictTransform
