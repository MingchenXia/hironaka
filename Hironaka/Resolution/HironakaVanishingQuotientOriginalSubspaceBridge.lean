import Hironaka.Resolution.HironakaNonreducedQuotientNeighborhoodLifting
import Hironaka.Resolution.HironakaActualAnalyticSubspaceMaps
import Mathlib.Geometry.RingedSpace.OpenImmersion

/-! Actual ring-sheaf comparison between the independent native factories.
BP FIRST: hironaka-vanishing-quotient-original-subspace-bridge.tex.
The actual full comparison is derived from ordinary analytic-subset data.
No quotient factory or reduced-model dictionary is re-proved here. -/
set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaVanishingQuotientOriginalSubspaceBridge
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaSmoothCentreRealDomainActualIdealPresheaf
  HironakaSmoothCentreRealDomainActualCentreRingSheaf
  HironakaSmoothCentreRealDomainActualCentrePowerStalk
  HironakaSmoothCentreRealDomainActualRemainderQuotientStalk
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaNonreducedAnalyticQuotientModel HironakaNonreducedAnalyticQuotientMorphism
  HironakaNonreducedQuotientNeighborhoodLifting HironakaHolomorphicJetRankLoci
  HironakaReducedComplexAnalyticSpaces

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private theorem support_eq (T : Set M) (hT : IsComplexAnalyticSubset (n := n) T) :
    (vanishingIdeal (n := n) T).zeroLocus = T :=
  BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hT.isClosed

private theorem mem_support (T : Set M) (hT : IsComplexAnalyticSubset (n := n) T)
    (x : T) : x.val ∈ (vanishingIdeal (n := n) T).zeroLocus := by
  rw [support_eq T hT]
  exact x.property

private def bridgeBase (T : Set M) (hT : IsComplexAnalyticSubset (n := n) T) :
    TopCat.of T ⟶ TopCat.of (vanishingIdeal (n := n) T).zeroLocus :=
  TopCat.ofHom ⟨fun x => ⟨x.val,mem_support T hT x⟩,
    continuous_subtype_val.subtype_mk _⟩

/-- The actual raw quotient rings are identified through the held EXACT
section-ideal specialization. Naturality is checked on every numerator. -/
private def rawToCentre (T : Set M) :
    quotientPresheaf (vanishingIdeal (n := n) T) ⟶ actualCentreRingPresheaf (n := n) T where
  app U := (quotientSectionEquiv (vanishingIdeal (n := n) T) (unop U)).toCommRingCatIso.hom
  naturality U V i := by
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    ext s
    rfl

private theorem rawToCentre_ambient (T : Set M) :
    quotientAmbientPresheafMap (vanishingIdeal (n := n) T) ≫ rawToCentre T =
      actualCentreAmbientRingMap (n := n) T := by
  ext U s
  rfl

/-- Existing OLD sheaf and adjunction units, composed with the actual raw
quotient comparison. This is a morphism of whole presheaves. -/
private def rawToOldModel (T : Set M) :
    quotientPresheaf (vanishingIdeal (n := n) T) ⟶
      (TopCat.Presheaf.pushforward CommRingCat (actualSubspaceTopInclusion T)).obj
        (actualSubspaceSheaf (n := n) T).presheaf :=
  rawToCentre T ≫ actualCentreRingSheafUnit (n := n) T ≫
    (TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat
      (actualSubspaceTopInclusion T)).unit.app (actualCentreRingSheaf (n := n) T).presheaf ≫
    (TopCat.Presheaf.pushforward CommRingCat (actualSubspaceTopInclusion T)).map
      (actualSubspaceSheafUnit (n := n) T)

private theorem rawToOldModel_ambient (T : Set M) :
    quotientAmbientPresheafMap (vanishingIdeal (n := n) T) ≫ rawToOldModel T =
      (actualSubspaceInclusion (n := n) T).toHom.c := by
  unfold rawToOldModel
  rw [←Category.assoc,rawToCentre_ambient]
  rfl

/-- The actual inverse-image adjunction constructs the comparison BEFORE
sheafification, over the internally derived actual support map. -/
private def modelPresheafMap (T : Set M) (hT : IsComplexAnalyticSubset (n := n) T) :
    quotientModelPresheaf (vanishingIdeal (n := n) T) ⟶
      (TopCat.Presheaf.pushforward CommRingCat (bridgeBase T hT)).obj
        (actualSubspaceSheaf (n := n) T).presheaf :=
  ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat
    (actualSubspaceTopInclusion (vanishingIdeal (n := n) T).zeroLocus)).homEquiv
      (quotientPresheaf (vanishingIdeal (n := n) T))
      ((TopCat.Presheaf.pushforward CommRingCat (bridgeBase T hT)).obj
        (actualSubspaceSheaf (n := n) T).presheaf)).symm (rawToOldModel T)

/-- The native sheafification universal property compares the full ring
sheaves, not just their supports or isolated stalk rings. -/
private def modelSheafMap (T : Set M) (hT : IsComplexAnalyticSubset (n := n) T) :
    (quotientModelSheaf (vanishingIdeal (n := n) T)).presheaf ⟶
      (TopCat.Presheaf.pushforward CommRingCat (bridgeBase T hT)).obj
        (actualSubspaceSheaf (n := n) T).presheaf :=
  sheafifyLift (Opens.grothendieckTopology (TopCat.of (vanishingIdeal (n := n) T).zeroLocus))
    (modelPresheafMap T hT)
    ((TopCat.Sheaf.pushforward CommRingCat (bridgeBase T hT)).obj
      (actualSubspaceSheaf (n := n) T)).property

private theorem modelSheafMap_unit (T : Set M) (hT : IsComplexAnalyticSubset (n := n) T) :
    quotientModelUnit (vanishingIdeal (n := n) T) ≫ modelSheafMap T hT = modelPresheafMap T hT :=
  toSheafify_sheafifyLift _ _ _

private def quotientToModel (T : Set M) :
    quotientPresheaf (vanishingIdeal (n := n) T) ⟶
      (TopCat.Presheaf.pushforward CommRingCat
        (actualSubspaceTopInclusion (vanishingIdeal (n := n) T).zeroLocus)).obj
          (quotientModelSheaf (vanishingIdeal (n := n) T)).presheaf :=
  (TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat
    (actualSubspaceTopInclusion (vanishingIdeal (n := n) T).zeroLocus)).unit.app
      (quotientPresheaf (vanishingIdeal (n := n) T)) ≫
    (TopCat.Presheaf.pushforward CommRingCat
      (actualSubspaceTopInclusion (vanishingIdeal (n := n) T).zeroLocus)).map
        (quotientModelUnit (vanishingIdeal (n := n) T))

private theorem quotientToModel_comparison (T : Set M)
    (hT : IsComplexAnalyticSubset (n := n) T) :
    quotientToModel T ≫
      (TopCat.Presheaf.pushforward CommRingCat
        (actualSubspaceTopInclusion (vanishingIdeal (n := n) T).zeroLocus)).map
          (modelSheafMap T hT) = rawToOldModel T := by
  let G := TopCat.Presheaf.pushforward CommRingCat
    (actualSubspaceTopInclusion (vanishingIdeal (n := n) T).zeroLocus)
  let η : quotientPresheaf (vanishingIdeal (n := n) T) ⟶
      G.obj (quotientModelPresheaf (vanishingIdeal (n := n) T)) :=
    (TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat
      (actualSubspaceTopInclusion (vanishingIdeal (n := n) T).zeroLocus)).unit.app
        (quotientPresheaf (vanishingIdeal (n := n) T))
  have h := ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat
    (actualSubspaceTopInclusion (vanishingIdeal (n := n) T).zeroLocus)).homEquiv
      (quotientPresheaf (vanishingIdeal (n := n) T))
      ((TopCat.Presheaf.pushforward CommRingCat (bridgeBase T hT)).obj
        (actualSubspaceSheaf (n := n) T).presheaf)).apply_symm_apply (rawToOldModel T)
  rw [Adjunction.homEquiv_unit] at h
  have hAdj : η ≫ G.map (modelPresheafMap T hT) = rawToOldModel T := h
  change (η ≫ G.map (quotientModelUnit (vanishingIdeal (n := n) T))) ≫
    G.map (modelSheafMap T hT) = _
  have hMap : G.map (quotientModelUnit (vanishingIdeal (n := n) T)) ≫
      G.map (modelSheafMap T hT) = G.map (modelPresheafMap T hT) :=
    (G.map_comp _ _).symm.trans (congrArg G.map (modelSheafMap_unit T hT))
  exact (Category.assoc _ _ _).trans ((congrArg (η ≫ ·) hMap).trans hAdj)

private def ringedBridge (T : Set M) (hT : IsComplexAnalyticSubset (n := n) T) :
    (actualSubspaceLocallyRingedSpace (n := n) T).toPresheafedSpace ⟶
      (quotientLocallyRingedSpace (vanishingIdeal (n := n) T)
        (CartanIrreducible.cartanCoherence T hT)).toPresheafedSpace where
  base := bridgeBase T hT
  c := modelSheafMap T hT

private theorem ringedBridge_inclusion (T : Set M) (hT : IsComplexAnalyticSubset (n := n) T) :
    ringedBridge T hT ≫
      (quotientInclusion (vanishingIdeal (n := n) T) (CartanIrreducible.cartanCoherence T hT)).toHom =
        (actualSubspaceInclusion (n := n) T).toHom := by
  refine PresheafedSpace.hext _ _ rfl ?_
  apply heq_of_eq
  change (quotientAmbientPresheafMap (vanishingIdeal (n := n) T) ≫ quotientToModel T) ≫
    (TopCat.Presheaf.pushforward CommRingCat
      (actualSubspaceTopInclusion (vanishingIdeal (n := n) T).zeroLocus)).map
        (modelSheafMap T hT) = _
  rw [Category.assoc,quotientToModel_comparison]
  exact rawToOldModel_ambient T

private theorem ringedBridge_base_apply (T : Set M)
    (hT : IsComplexAnalyticSubset (n := n) T) (x : T) :
    (ringedBridge T hT).base x = bridgeBase T hT x := rfl

private theorem quotientInclusion_base_apply (T : Set M)
    (hT : IsComplexAnalyticSubset (n := n) T)
    (x : (vanishingIdeal (n := n) T).zeroLocus) :
    (quotientInclusion (vanishingIdeal (n := n) T)
      (CartanIrreducible.cartanCoherence T hT)).base x = x.val := rfl

private theorem bridgeBase_val (T : Set M)
    (hT : IsComplexAnalyticSubset (n := n) T) (x : T) : (bridgeBase T hT x).val = x.val := rfl

private theorem actualSubspaceInclusion_base_apply (T : Set M) (x : T) :
    (actualSubspaceInclusion (n := n) T).base x = x.val := rfl

private theorem ringedBridge_stalk_square (T : Set M)
    (hT : IsComplexAnalyticSubset (n := n) T) (x : T) :
    (quotientInclusion (vanishingIdeal (n := n) T)
      (CartanIrreducible.cartanCoherence T hT)).toHom.stalkMap (bridgeBase T hT x) ≫
        (ringedBridge T hT).stalkMap x = (actualSubspaceInclusion (n := n) T).toHom.stalkMap x := by
  have h := PresheafedSpace.stalkMap.congr_hom
    (ringedBridge T hT ≫
      (quotientInclusion (vanishingIdeal (n := n) T) (CartanIrreducible.cartanCoherence T hT)).toHom)
    (actualSubspaceInclusion (n := n) T).toHom (ringedBridge_inclusion T hT) x
  simp only [PresheafedSpace.stalkMap.comp,PresheafedSpace.comp_base,TopCat.comp_app] at h
  change (quotientInclusion (vanishingIdeal (n := n) T)
      (CartanIrreducible.cartanCoherence T hT)).toHom.stalkMap (bridgeBase T hT x) ≫
        (ringedBridge T hT).stalkMap x =
      (𝟙 ((ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel n) M).presheaf.stalk x.val)) ≫
        (actualSubspaceInclusion (n := n) T).toHom.stalkMap x at h
  exact h.trans (Category.id_comp _)

private def bridgeStalkEquiv (T : Set M) (hT : IsComplexAnalyticSubset (n := n) T) (x : T) :
    ((quotientLocallyRingedSpace (vanishingIdeal (n := n) T)
      (CartanIrreducible.cartanCoherence T hT)).presheaf.stalk (bridgeBase T hT x)).carrier ≃+*
        ((actualSubspaceLocallyRingedSpace (n := n) T).presheaf.stalk x).carrier :=
  (quotientStalkWholeEquiv (vanishingIdeal (n := n) T)
    (CartanIrreducible.cartanCoherence T hT) (bridgeBase T hT x)).trans
      (actualSubspaceStalkWholeEquiv (n := n) T x).symm

private theorem bridgeStalkEquiv_apply (T : Set M)
    (hT : IsComplexAnalyticSubset (n := n) T) (x : T)
    (r : ((quotientLocallyRingedSpace (vanishingIdeal (n := n) T)
      (CartanIrreducible.cartanCoherence T hT)).presheaf.stalk (bridgeBase T hT x)).carrier) :
    bridgeStalkEquiv T hT x r = (ringedBridge T hT).stalkMap x r := by
  obtain ⟨a,rfl⟩ := quotientInclusion_surjective_stalk (vanishingIdeal (n := n) T)
    (CartanIrreducible.cartanCoherence T hT) (bridgeBase T hT x) r
  have h := ConcreteCategory.congr_hom (ringedBridge_stalk_square T hT x) a
  have hmap : (ringedBridge T hT).stalkMap x
      ((quotientInclusion (vanishingIdeal (n := n) T)
        (CartanIrreducible.cartanCoherence T hT)).stalkMap (bridgeBase T hT x) a) =
      (actualSubspaceInclusion (n := n) T).stalkMap x a := h
  apply (actualSubspaceStalkWholeEquiv (n := n) T x).injective
  change actualSubspaceStalkWholeEquiv (n := n) T x
    ((actualSubspaceStalkWholeEquiv (n := n) T x).symm
      (quotientStalkWholeEquiv (vanishingIdeal (n := n) T)
        (CartanIrreducible.cartanCoherence T hT) (bridgeBase T hT x)
          ((quotientInclusion (vanishingIdeal (n := n) T)
            (CartanIrreducible.cartanCoherence T hT)).stalkMap (bridgeBase T hT x) a))) = _
  exact (RingEquiv.apply_symm_apply _ _).trans
    ((quotientInclusion_stalk (vanishingIdeal (n := n) T)
      (CartanIrreducible.cartanCoherence T hT) (bridgeBase T hT x) a).trans
        ((actualSubspaceInclusion_stalk T x a).symm.trans
          (congrArg (actualSubspaceStalkWholeEquiv (n := n) T x) hmap.symm)))

private theorem bridge_stalk_local (T : Set M)
    (hT : IsComplexAnalyticSubset (n := n) T) (x : T) :
    IsLocalHom ((ringedBridge T hT).stalkMap x).hom := by
  refine ⟨fun r hr => ?_⟩
  have he : IsUnit (bridgeStalkEquiv T hT x r) := (bridgeStalkEquiv_apply T hT x r).symm ▸ hr
  have h := (bridgeStalkEquiv T hT x).symm.toRingHom.isUnit_map he
  change IsUnit ((bridgeStalkEquiv T hT x).symm (bridgeStalkEquiv T hT x r)) at h
  exact (congrArg IsUnit ((bridgeStalkEquiv T hT x).symm_apply_apply r)).mp h

private def oldToQuotientMap (T : Set M) (hT : IsComplexAnalyticSubset (n := n) T) :
    actualSubspaceLocallyRingedSpace (n := n) T ⟶
      quotientLocallyRingedSpace (vanishingIdeal (n := n) T)
        (CartanIrreducible.cartanCoherence T hT) where
  toHom := ringedBridge T hT
  prop := bridge_stalk_local T hT

private theorem oldToQuotient_stalk_iso (T : Set M)
    (hT : IsComplexAnalyticSubset (n := n) T) (x : T) :
    IsIso ((oldToQuotientMap T hT).stalkMap x) := by
  have he : (oldToQuotientMap T hT).stalkMap x =
      (bridgeStalkEquiv T hT x).toCommRingCatIso.hom := by
    apply CommRingCat.hom_ext
    ext r
    exact (bridgeStalkEquiv_apply T hT x r).symm
  rw [he]
  exact (bridgeStalkEquiv T hT x).toCommRingCatIso.isIso_hom

private theorem oldToQuotient_base_open (T : Set M)
    (hT : IsComplexAnalyticSubset (n := n) T) :
    Topology.IsOpenEmbedding (oldToQuotientMap T hT).base :=
  (Homeomorph.setCongr (support_eq T hT).symm).isOpenEmbedding

private theorem oldToQuotient_base_epi (T : Set M)
    (hT : IsComplexAnalyticSubset (n := n) T) : Epi (oldToQuotientMap T hT).base := by
  apply (TopCat.epi_iff_surjective _).mpr
  exact (Homeomorph.setCongr (support_eq T hT).symm).surjective

private theorem oldToQuotient_isIso (T : Set M)
    (hT : IsComplexAnalyticSubset (n := n) T) : IsIso (oldToQuotientMap T hT) := by
  let : ∀x : T,IsIso ((oldToQuotientMap T hT).stalkMap x) := oldToQuotient_stalk_iso T hT
  let : LocallyRingedSpace.IsOpenImmersion (oldToQuotientMap T hT) :=
    LocallyRingedSpace.IsOpenImmersion.of_stalk_iso _ (oldToQuotient_base_open T hT)
  let : Epi (oldToQuotientMap T hT).base := oldToQuotient_base_epi T hT
  exact LocallyRingedSpace.IsOpenImmersion.to_iso (oldToQuotientMap T hT)

/-- The two independent actual structure sheaves are canonically identified
over the SAME original ambient manifold, from ordinary analyticity alone. -/
def vanishingQuotientOriginalSubspaceIso (T : Set M)
    (hT : IsComplexAnalyticSubset (n := n) T) :
    quotientLocallyRingedSpace (vanishingIdeal (n := n) T)
      (CartanIrreducible.cartanCoherence T hT) ≅ actualSubspaceLocallyRingedSpace (n := n) T := by
  letI : IsIso (oldToQuotientMap T hT) := oldToQuotient_isIso T hT
  exact (asIso (oldToQuotientMap T hT)).symm

/-- The comparison from the original subspace retains the FULL ambient
structure-sheaf morphism, not just its underlying support map. -/
theorem bridge_inv_inclusion (T : Set M) (hT : IsComplexAnalyticSubset (n := n) T) :
    (vanishingQuotientOriginalSubspaceIso T hT).inv ≫
      quotientInclusion (vanishingIdeal (n := n) T) (CartanIrreducible.cartanCoherence T hT) =
        actualSubspaceInclusion (n := n) T := by
  apply LocallyRingedSpace.Hom.ext'
  exact ringedBridge_inclusion T hT

/-- The inverse full native comparison has the SAME full ambient triangle. -/
theorem bridge_hom_inclusion (T : Set M) (hT : IsComplexAnalyticSubset (n := n) T) :
    (vanishingQuotientOriginalSubspaceIso T hT).hom ≫ actualSubspaceInclusion (n := n) T =
      quotientInclusion (vanishingIdeal (n := n) T) (CartanIrreducible.cartanCoherence T hT) := by
  have h := congrArg ((vanishingQuotientOriginalSubspaceIso T hT).hom ≫ ·)
    (bridge_inv_inclusion T hT)
  simpa only [Iso.hom_inv_id_assoc] using h.symm

/-- Genuine complex scalar compatibility in the Q-to-original direction. -/
theorem bridge_hom_point (T : Set M) (hT : IsComplexAnalyticSubset (n := n) T) :
    (vanishingQuotientOriginalSubspaceIso T hT).hom ≫ subspacePointMap (n := n) T =
      quotientPointMap (vanishingIdeal (n := n) T) (CartanIrreducible.cartanCoherence T hT) := by
  have h := congrArg (· ≫ ambientPointMap n M) (bridge_hom_inclusion T hT)
  simpa only [subspacePointMap,quotientPointMap,Category.assoc] using h

/-- Genuine complex scalar compatibility in the original-to-Q direction. -/
theorem bridge_inv_point (T : Set M) (hT : IsComplexAnalyticSubset (n := n) T) :
    (vanishingQuotientOriginalSubspaceIso T hT).inv ≫
      quotientPointMap (vanishingIdeal (n := n) T) (CartanIrreducible.cartanCoherence T hT) =
        subspacePointMap (n := n) T := by
  have h := congrArg (· ≫ ambientPointMap n M) (bridge_inv_inclusion T hT)
  simpa only [subspacePointMap,quotientPointMap,Category.assoc] using h

private theorem bridge_stalk_whole (T : Set M)
    (hT : IsComplexAnalyticSubset (n := n) T) (x : T)
    (r : ((quotientLocallyRingedSpace (vanishingIdeal (n := n) T)
      (CartanIrreducible.cartanCoherence T hT)).presheaf.stalk
        ((vanishingQuotientOriginalSubspaceIso T hT).inv.base x)).carrier) :
    actualSubspaceStalkWholeEquiv (n := n) T x
      ((vanishingQuotientOriginalSubspaceIso T hT).inv.stalkMap x r) =
        quotientStalkWholeEquiv (vanishingIdeal (n := n) T)
          (CartanIrreducible.cartanCoherence T hT)
            ((vanishingQuotientOriginalSubspaceIso T hT).inv.base x) r := by
  have h := congrArg (actualSubspaceStalkWholeEquiv (n := n) T x)
    (bridgeStalkEquiv_apply T hT x r).symm
  exact h.trans ((actualSubspaceStalkWholeEquiv (n := n) T x).apply_symm_apply _)

/-- EVERY original ambient stalk numerator retains its SAME WHOLE ideal
quotient class under the independently constructed stalk identifications. -/
theorem bridge_inv_whole_stalk_mk (T : Set M)
    (hT : IsComplexAnalyticSubset (n := n) T) (x : T)
    (r : actualComplexStructureStalk (n := n) x.val) :
    actualSubspaceStalkWholeEquiv (n := n) T x
      ((vanishingQuotientOriginalSubspaceIso T hT).inv.stalkMap x
        ((quotientStalkWholeEquiv (vanishingIdeal (n := n) T)
          (CartanIrreducible.cartanCoherence T hT)
            ((vanishingQuotientOriginalSubspaceIso T hT).inv.base x)).symm
              (Ideal.Quotient.mk (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) T) x.val) r))) =
      Ideal.Quotient.mk (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) T) x.val) r :=
  (bridge_stalk_whole T hT x _).trans (RingEquiv.apply_symm_apply _ _)

/-- EVERY genuine preferred-chart holomorphic germ numerator is retained,
modulo the SAME entire chart ideal, not merely its radical or residue field. -/
theorem bridge_inv_stalk_mk (T : Set M)
    (hT : IsComplexAnalyticSubset (n := n) T) (x : T) (g : HolGerm (ComplexModel n)) :
    actualSubspaceStalkChartEquiv (n := n) T x
      ((vanishingQuotientOriginalSubspaceIso T hT).inv.stalkMap x
        ((quotientStalkChartEquiv (vanishingIdeal (n := n) T)
          (CartanIrreducible.cartanCoherence T hT)
            ((vanishingQuotientOriginalSubspaceIso T hT).inv.base x)).symm
              (Ideal.Quotient.mk (wholeChartStalkIdeal (vanishingIdeal (n := n) T)
                x.val x.val (mem_chart_source (ComplexModel n) x.val)) g))) =
      Ideal.Quotient.mk (wholeChartStalkIdeal (vanishingIdeal (n := n) T)
        x.val x.val (mem_chart_source (ComplexModel n) x.val)) g := by
  let e := Ideal.quotientEquiv _ _ (actualStalkChartEquiv (n := n) x.val)
    (map_actualWholeSheafStalkIdeal (vanishingIdeal (n := n) T) x.val).symm
  let r := (quotientStalkChartEquiv (vanishingIdeal (n := n) T)
    (CartanIrreducible.cartanCoherence T hT)
      ((vanishingQuotientOriginalSubspaceIso T hT).inv.base x)).symm
        (Ideal.Quotient.mk (wholeChartStalkIdeal (vanishingIdeal (n := n) T)
          x.val x.val (mem_chart_source (ComplexModel n) x.val)) g)
  have hChart : actualSubspaceStalkChartEquiv (n := n) T x
      ((vanishingQuotientOriginalSubspaceIso T hT).inv.stalkMap x r) =
        quotientStalkChartEquiv (vanishingIdeal (n := n) T)
          (CartanIrreducible.cartanCoherence T hT)
            ((vanishingQuotientOriginalSubspaceIso T hT).inv.base x) r :=
    congrArg e (bridge_stalk_whole T hT x r)
  exact hChart.trans (RingEquiv.apply_symm_apply _ _)

/-- Full native comparison over the actual ambient space is unique. -/
theorem bridge_unique (T : Set M) (hT : IsComplexAnalyticSubset (n := n) T)
    (e : quotientLocallyRingedSpace (vanishingIdeal (n := n) T)
      (CartanIrreducible.cartanCoherence T hT) ≅ actualSubspaceLocallyRingedSpace (n := n) T)
    (he : e.hom ≫ actualSubspaceInclusion (n := n) T =
      quotientInclusion (vanishingIdeal (n := n) T) (CartanIrreducible.cartanCoherence T hT)) :
    e = vanishingQuotientOriginalSubspaceIso T hT := by
  apply Iso.ext
  apply (cancel_mono (actualSubspaceInclusion (n := n) T)).mp
  exact he.trans (bridge_hom_inclusion T hT).symm

end
end Hironaka.HironakaVanishingQuotientOriginalSubspaceBridge
