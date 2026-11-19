import Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupObjectGluing
import Hironaka.Analytic.Unibranch.EmbeddedBlowupGlobalUniversalLocal
import Hironaka.Resolution.HironakaSingularSubspaceBlowupCartierUniversalProjectionSheaf
import Hironaka.Resolution.HironakaSingularRankOneLocalGenerators
import Hironaka.Resolution.HironakaIntrinsicReducedCentreOpenSections
import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Standard native invertibility for the same global whole ideal

Actual original OI inverse section maps lift the local genuine Cartier
sections to SAME raw global source. Whole local ideal dictionaries and full
projection squares retain the SAME original B,b and all multiplicities.
Actual stalk ring isomorphisms give one regular generator on each entire
source open; native rank-one adapter internally constructs standard q.
No reduced-target ideal, centre containment, input q, or global SC is used.
Blueprint: `embedded-ideal-blowup-global-cartier.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace Topology CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupGlobalCartier

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences Hironaka
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaActualAnalyticSubspace
  HironakaNativePulledIdealSheaf HironakaNativePulledIdealStalk
  HironakaSingularModuleSheafStalk HironakaSingularRankOneLocalGenerators
  HironakaSingularSubspaceBlowupLift
  HironakaSingularSubspaceBlowupCartierUniversalIdealStalk
  HironakaSingularSubspaceBlowupCartierUniversalProjectionSheaf
  HironakaSingularSubspaceBlowupCartierUniversalStalkTransport
  HironakaIntrinsicReducedCentreOpenSections SourceReducedComplexSpace
  EmbeddedIdealBlowupObjectGluing EmbeddedBlowupGlobalUniversalLocal

noncomputable section

private instance originalOverHasWeakSheafify (A : LocallyRingedSpace.{0}) (U : Opens A.toTopCat) :
    HasWeakSheafify ((Opens.grothendieckTopology A.toTopCat).over U) AddCommGrpCat.{0} :=
  CategoryTheory.sheafToPresheaf_isRightAdjoint
    ((Opens.grothendieckTopology A.toTopCat).over U) AddCommGrpCat.{0}

private theorem span_regular_of_map {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (I : Ideal R) (r : R)
    (hspan : Ideal.map e.toRingHom I = Ideal.span {e r}) (hreg : IsRegular (e r)) :
    I = Ideal.span {r} ∧ IsRegular r := by
  constructor
  · apply e.idealComapOrderIso.symm.injective
    change Ideal.map e I = Ideal.map e (Ideal.span {r})
    rw [Ideal.map_span, Set.image_singleton]
    exact hspan
  · have h := isRegular_map_ringEquiv e.symm hreg
    simpa only [e.symm_apply_apply] using h

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

/-- The FULL actual source chart square transports ENTIRE global J_p to
precisely SAME original local canonical H_i^# I_Ci, with no ideal certificate. -/
theorem projection_ideal_map_local (i : ι)
    (y : strictTransform (n i) (π i) (W i)) :
    Ideal.map ((inclusion hW hπ J B b hd hJ i).stalkMap y).hom
      (nativePulledIdealStalkIdeal (projection hW hπ J B b hd hJ)
        B
        b
          ((inclusion hW hπ J B b hd hJ i).base y)) =
      Ideal.map ((strictTransformProjection (hπ i) (hW i).isClosed ≫
        actualSubspaceInclusion (n := (n i)) (W i)).stalkMap y).hom
          (actualWholeSheafStalkIdeal (vanishingIdeal (n := (n i)) (C i)) (π i y.val)) := by
  let k := inclusion hW hπ J B b hd hJ i
  let p := projection hW hπ J B b hd hJ
  let p₀ := strictTransformProjection (hπ i) (hW i).isClosed
  let j := (J i).hom.left
  have hsquare : k ≫ p = p₀ ≫ j := inclusion_projection hW hπ J B b hd hJ i
  have hchart := (hJ i (p₀.base y)).symm
  have hcanonical :
      Ideal.map (p₀.stalkMap y).hom
        (Ideal.map ((actualSubspaceInclusion (n := (n i)) (W i)).stalkMap (p₀.base y)).hom
          (actualWholeSheafStalkIdeal (vanishingIdeal (n := (n i)) (C i)) (p₀.base y).val)) =
      Ideal.map ((p₀ ≫ actualSubspaceInclusion (n := (n i)) (W i)).stalkMap y).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := (n i)) (C i)) (π i y.val)) :=
    ((actualPulledCentreStalkInclusion_range
      (p₀ ≫ actualSubspaceInclusion (n := (n i)) (W i)) (C i) y).symm.trans
      (actualPulledCentreStalkInclusion_range_subspace p₀ (C i) y)).symm
  change Ideal.map (k.stalkMap y).hom (nativePulledIdealStalkIdeal p B b (k.base y)) = _
  exact (nativePulledIdealStalkIdeal_comp k p B b y).symm.trans
    ((congrArg (fun F : localObject hW hπ i ⟶ X.obj.left =>
      nativePulledIdealStalkIdeal F B b y) hsquare).trans
      ((nativePulledIdealStalkIdeal_comp p₀ j B b y).trans
        ((congrArg (Ideal.map (p₀.stalkMap y).hom) hchart).trans hcanonical)))

/-- Actual global canonical ideal sections, ONE per open, are regular and
generate ENTIRE J_p at EVERY nearby original point, derived from geometry. -/
theorem exists_local_projection_ideal_generator (x : glued hW hπ J B b hd hJ) :
    ∃ (U : Opens (glued hW hπ J B b hd hJ).toTopCat) (_hxU : x ∈ U)
      (s : nativePulledIdealSectionIdeal (projection hW hπ J B b hd hJ)
        B
        b U),
      ∀ (y : glued hW hπ J B b hd hJ) (hy : y ∈ U),
        nativePulledIdealStalkIdeal (projection hW hπ J B b hd hJ)
          B
          b y =
            Ideal.span {(glued hW hπ J B b hd hJ).presheaf.germ U y hy s.val} ∧
        IsRegular ((glued hW hπ J B b hd hJ).presheaf.germ U y hy s.val) := by
  obtain ⟨i, x₀, rfl⟩ := inclusion_jointly_surjective hW hπ J B b hd hJ x
  obtain ⟨V, hxV, s, hs⟩ := exists_local_projection_ideal_sheaf_generator
    (hπ i) (hW i).isClosed (hd i) x₀
  let G := glued hW hπ J B b hd hJ
  let k := inclusion hW hπ J B b hd hJ i
  let p := projection hW hπ J B b hd hJ
  let U := (LocallyRingedSpace.IsOpenImmersion.opensFunctor k).obj V
  let t : (G.presheaf.obj (op U)).carrier := LocallyRingedSpace.IsOpenImmersion.invApp k V s.val
  have hgen : ∀ (y : G) (hy : y ∈ U),
      nativePulledIdealStalkIdeal p B b y = Ideal.span {G.presheaf.germ U y hy t} ∧
        IsRegular (G.presheaf.germ U y hy t) := by
    rintro y ⟨z, hz, rfl⟩
    let e := (asIso (k.stalkMap z)).commRingCatIsoToRingEquiv
    let gamma := G.presheaf.germ U (k.base z) ⟨z, hz, rfl⟩ t
    let alpha := (localObject hW hπ i).presheaf.germ V z hz s.val
    have hg : e gamma = alpha := openImmersion_invApp_germ k V s.val z hz
    have hspan : Ideal.map e.toRingHom (nativePulledIdealStalkIdeal p B b (k.base z)) =
        Ideal.span {e gamma} :=
      (projection_ideal_map_local hW hπ J B b hd hJ i z).trans
        ((hs z hz).1.trans (congrArg (fun r => Ideal.span {r}) hg.symm))
    have hreg : IsRegular (e gamma) := hg.symm ▸ (hs z hz).2
    exact span_regular_of_map e _ gamma hspan hreg
  have ht : t ∈ nativePulledIdealSectionIdeal p B b U := by
    intro y hy
    rw [(hgen y hy).1]
    exact Ideal.subset_span (Set.mem_singleton _)
  exact ⟨U, ⟨x₀, hxV, rfl⟩, ⟨t, ht⟩, hgen⟩

/-- STANDARD native q on SAME ACTUAL GLOBAL projection ideal, all data
internally derived; no global SC/local generator/free-rank certificate input. -/
theorem projection_ideal_exists_locallyFreeData :
    ∃ q : (nativePulledIdealModule (projection hW hπ J B b hd hJ)
      B
      b).LocalGeneratorsData.{0},
      q.IsLocallyFreeData ∧ ∀ i, Nonempty (Unique (q.generators i).I) := by
  classical
  let G := glued hW hπ J B b hd hJ
  let p := projection hW hπ J B b hd hJ
  choose U hxU s hs using exists_local_projection_ideal_generator hW hπ J B b hd hJ
  exact exists_locallyFreeData_of_regular_sections G.toSheafedSpace.sheaf
    (nativePulledIdealInclusion p B b) (fun _ => Subtype.val_injective)
    U (fun x => ⟨x, hxU x⟩) s (fun i y hy => (hs i y hy).2)
    (fun i y hy => (nativePulledIdealStalkInclusion_range p B b y).trans (hs i y hy).1)

/-- The EXISTING native locally-free class holds for SAME actual global ideal module. -/
theorem projection_ideal_isLocallyFree :
    (nativePulledIdealModule (projection hW hπ J B b hd hJ)
      B
      b).IsLocallyFree := by
  obtain ⟨q, hq, _hunique⟩ := projection_ideal_exists_locallyFreeData hW hπ J B b hd hJ
  let : q.IsLocallyFreeData := hq
  exact q.isLocallyFree

/-- Standard native invertibility of ENTIRE actual global J_p at every original stalk. -/
theorem projection_ideal_moduleInvertible (x : glued hW hπ J B b hd hJ) :
    Module.Invertible ((glued hW hπ J B b hd hJ).presheaf.stalk x).carrier
      (nativePulledIdealStalkIdeal (projection hW hπ J B b hd hJ)
        B
        b x) := by
  classical
  obtain ⟨q, hq, hunique⟩ := projection_ideal_exists_locallyFreeData hW hπ J B b hd hJ
  let : q.IsLocallyFreeData := hq
  let : ∀ i, Unique (q.generators i).I := fun i => Classical.choice (hunique i)
  exact moduleInvertible_nativePulledIdeal_of_locallyFreeData
    (projection hW hπ J B b hd hJ)
    B
    b q x

end

end Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupGlobalCartier
