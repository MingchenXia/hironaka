/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothCentreRealDomainActualCentreRingSheafStalk
import Hironaka.Resolution.HironakaHilbertSamuelTangentValue
import Mathlib.Geometry.Manifold.Sheaf.LocallyRingedSpace

/-!
# Actual locally ringed models of embedded analytic subspaces

The actual ambient whole vanishing-ideal quotient sheaf is pulled back to
its genuine topological subspace and sheafified. Its actual colimit stalks
are identified with the entire original ambient quotient stalks, and the
original preferred-chart quotient rings. Locality is proved internally at
every point of the subspace. No smoothness of the subspace or resolution
certificate is assumed. For analytic subsets this is a genuine embedded
analytic-space model; abstract atlas comparisons and gluing remain separate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualAnalyticSubspace
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaSmoothCentreRealDomainActualIdealPresheaf
  HironakaSmoothCentreRealDomainActualCentreRingSheaf
  HironakaSmoothCentreRealDomainActualCentreRingSheafStalk
  HironakaHolomorphicJetChartInvariance HironakaHolomorphicJetRankLoci
  HironakaHilbertSamuelTangentValue
variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The actual continuous inclusion of the genuine topological subspace. -/
@[implicit_reducible]
def actualSubspaceTopInclusion (C : Set M) : TopCat.of C ⟶ TopCat.of M :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The inverse image of the independently constructed whole ambient quotient sheaf. -/
def actualSubspacePresheaf (C : Set M) : (TopCat.of C).Presheaf CommRingCat :=
  (TopCat.Presheaf.pullback CommRingCat (actualSubspaceTopInclusion C)).obj
    (actualCentreRingSheaf (n := n) C).presheaf

/-- The actual ring sheaf on the subspace, with no smoothness assumption on it. -/
def actualSubspaceSheaf (C : Set M) : (TopCat.of C).Sheaf CommRingCat :=
  (presheafToSheaf (Opens.grothendieckTopology (TopCat.of C)) CommRingCat).obj
    (actualSubspacePresheaf (n := n) C)

/-- The true sheafification unit of the actual inverse-image presheaf. -/
def actualSubspaceSheafUnit (C : Set M) :
    actualSubspacePresheaf (n := n) C ⟶ (actualSubspaceSheaf (n := n) C).presheaf :=
  toSheafify (Opens.grothendieckTopology (TopCat.of C)) (actualSubspacePresheaf (n := n) C)

/-- The actual sheafification unit is an internally proved stalk isomorphism. -/
def actualSubspaceUnitStalkIso (C : Set M) (x : C) :
    (actualSubspacePresheaf (n := n) C).stalk x ≅
      (actualSubspaceSheaf (n := n) C).presheaf.stalk x := by
  let f := (TopCat.Presheaf.stalkFunctor (X := TopCat.of C) CommRingCat x).map
    (actualSubspaceSheafUnit (n := n) C)
  have hf : IsIso f := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
    (X := TopCat.of C) x CommRingCat (actualSubspacePresheaf (n := n) C)
  exact @asIso _ _ _ _ f hf

/-- The actual subspace stalk is the whole original ambient quotient stalk. -/
def actualSubspaceStalkWholeEquiv (C : Set M) (x : C) :
    ((actualSubspaceSheaf (n := n) C).presheaf.stalk x).carrier ≃+*
      actualComplexStructureStalk (n := n) x.val ⧸
        actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) x.val :=
  (actualSubspaceUnitStalkIso (n := n) C x).symm.commRingCatIsoToRingEquiv.trans
    ((TopCat.Presheaf.stalkPullbackIso CommRingCat (actualSubspaceTopInclusion C)
      (actualCentreRingSheaf (n := n) C).presheaf x).symm.commRingCatIsoToRingEquiv.trans
      (actualCentreRingSheafStalkWholeEquiv (n := n) C x.val))

/-- The same actual subspace stalk is the whole original preferred-chart quotient ring. -/
def actualSubspaceStalkChartEquiv (C : Set M) (x : C) :
    ((actualSubspaceSheaf (n := n) C).presheaf.stalk x).carrier ≃+*
      HolGerm (ComplexModel n) ⧸ wholeChartStalkIdeal (vanishingIdeal (n := n) C)
        x.val x.val (mem_chart_source (ComplexModel n) x.val) :=
  (actualSubspaceStalkWholeEquiv (n := n) C x).trans
    (Ideal.quotientEquiv _ _ (actualStalkChartEquiv (n := n) x.val)
      (map_actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) x.val).symm)

/-- At every actual point the whole original chart quotient is a genuine local ring. -/
theorem actualSubspaceChartQuotient_isLocalRing (C : Set M) (x : C) :
    IsLocalRing (HolGerm (ComplexModel n) ⧸ wholeChartStalkIdeal (vanishingIdeal (n := n) C)
      x.val x.val (mem_chart_source (ComplexModel n) x.val)) := by
  let I := wholeChartStalkIdeal (vanishingIdeal (n := n) C)
    x.val x.val (mem_chart_source (ComplexModel n) x.val)
  have hI : I ≠ ⊤ := whole_vanishing_stalk_ne_top (n := n) x.property
  let : Nontrivial (HolGerm (ComplexModel n) ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

/-- Locality of each literal subspace stalk is a theorem, not an atlas certificate. -/
theorem actualSubspaceStalk_isLocalRing (C : Set M) (x : C) :
    IsLocalRing ((actualSubspaceSheaf (n := n) C).presheaf.stalk x).carrier := by
  let := actualSubspaceChartQuotient_isLocalRing (n := n) C x
  exact (actualSubspaceStalkChartEquiv (n := n) C x).symm.isLocalRing

/-- The actual singular subspace, equipped with its constructed whole quotient structure sheaf. -/
@[implicit_reducible]
def actualSubspaceLocallyRingedSpace (C : Set M) : LocallyRingedSpace where
  carrier := TopCat.of C
  presheaf := (actualSubspaceSheaf (n := n) C).presheaf
  IsSheaf := (actualSubspaceSheaf (n := n) C).property
  isLocalRing := actualSubspaceStalk_isLocalRing (n := n) C

/-- The genuine ringed-space inclusion is built from the quotient and both actual adjunction units. -/
@[implicit_reducible]
def actualSubspaceInclusionRingedHom (C : Set M) :
    (actualSubspaceLocallyRingedSpace (n := n) C).toPresheafedSpace ⟶
      (ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) M).toPresheafedSpace where
  base := actualSubspaceTopInclusion C
  c := (actualCentreAmbientRingSheafMap (n := n) C).hom ≫
    (TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat
      (actualSubspaceTopInclusion C)).unit.app (actualCentreRingSheaf (n := n) C).presheaf ≫
    (TopCat.Presheaf.pushforward CommRingCat (actualSubspaceTopInclusion C)).map
      (actualSubspaceSheafUnit (n := n) C)


/-- The actual global ringed inclusion retains every whole original quotient numerator. -/
theorem actualSubspaceInclusionRingedHom_stalk (C : Set M) (x : C)
    (r : actualComplexStructureStalk (n := n) x.val) :
    actualSubspaceStalkWholeEquiv (n := n) C x
      ((actualSubspaceInclusionRingedHom (n := n) C).stalkMap x r) =
      Ideal.Quotient.mk (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) x.val) r := by
  let Q := (actualCentreRingSheaf (n := n) C).presheaf
  let P := actualSubspacePresheaf (n := n) C
  let S := (actualSubspaceSheaf (n := n) C).presheaf
  let i := actualSubspaceTopInclusion C
  let u := actualSubspaceSheafUnit (n := n) C
  let E : Q.stalk x.val ≅ P.stalk x :=
    TopCat.Presheaf.stalkPullbackIso CommRingCat i Q x
  have hfactor : (actualSubspaceInclusionRingedHom (n := n) C).stalkMap x r =
      (actualSubspaceUnitStalkIso (n := n) C x).hom
        (E.hom (actualCentreAmbientRingSheafStalkHom (n := n) C x.val r)) := by
    obtain ⟨U,hx,s,rfl⟩ := (actualComplexStructureSheaf (n := n) M).presheaf.exists_germ_eq r
    have hA : actualCentreAmbientRingSheafStalkHom (n := n) C x.val
        ((actualComplexStructureSheaf (n := n) M).presheaf.germ U x.val hx s) =
        Q.germ U x.val hx ((actualCentreAmbientRingSheafMap (n := n) C).hom.app (op U) s) :=
      TopCat.Presheaf.stalkFunctor_map_germ_apply U x.val hx
        (actualCentreAmbientRingSheafMap (n := n) C).hom s
    have hP := ConcreteCategory.congr_hom
      (TopCat.Presheaf.germ_stalkPullbackHom CommRingCat i Q x U hx)
      ((actualCentreAmbientRingSheafMap (n := n) C).hom.app (op U) s)
    simp only [ConcreteCategory.comp_apply] at hP
    have hS := TopCat.Presheaf.stalkFunctor_map_germ_apply
      ((Opens.map i).obj U) x hx u
      (((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat i).unit.app Q).app (op U)
        ((actualCentreAmbientRingSheafMap (n := n) C).hom.app (op U) s))
    have hP' : E.hom
        (Q.germ U x.val hx ((actualCentreAmbientRingSheafMap (n := n) C).hom.app (op U) s)) =
        P.germ ((Opens.map i).obj U) x hx
          (((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat i).unit.app Q).app (op U)
            ((actualCentreAmbientRingSheafMap (n := n) C).hom.app (op U) s)) := hP
    calc
      _ = S.germ ((Opens.map i).obj U) x hx
          (u.app (op ((Opens.map i).obj U))
            (((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat i).unit.app Q).app (op U)
              ((actualCentreAmbientRingSheafMap (n := n) C).hom.app (op U) s))) :=
        PresheafedSpace.stalkMap_germ_apply (actualSubspaceInclusionRingedHom (n := n) C) U x hx s
      _ = (TopCat.Presheaf.stalkFunctor CommRingCat x).map u
          (P.germ ((Opens.map i).obj U) x hx
            (((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat i).unit.app Q).app (op U)
              ((actualCentreAmbientRingSheafMap (n := n) C).hom.app (op U) s))) := hS.symm
      _ = (TopCat.Presheaf.stalkFunctor CommRingCat x).map u
          (E.hom (Q.germ U x.val hx ((actualCentreAmbientRingSheafMap (n := n) C).hom.app (op U) s))) :=
        congrArg (fun a => (TopCat.Presheaf.stalkFunctor CommRingCat x).map u a) hP'.symm
      _ = _ := congrArg
        (fun a => (TopCat.Presheaf.stalkFunctor CommRingCat x).map u (E.hom a)) hA.symm
  change actualCentreRingSheafStalkWholeEquiv (n := n) C x.val
    (E.inv ((actualSubspaceUnitStalkIso (n := n) C x).inv
      ((actualSubspaceInclusionRingedHom (n := n) C).stalkMap x r))) = _
  rw [hfactor,CategoryTheory.Iso.hom_inv_id_apply,CategoryTheory.Iso.hom_inv_id_apply,
    actualCentreRingSheafStalkWholeEquiv_ambientHom]

/-- Every actual quotient stalk element has a genuine original ambient preimage. -/
theorem actualSubspaceInclusionRingedHom_stalk_surjective (C : Set M) (x : C) :
    Function.Surjective ((actualSubspaceInclusionRingedHom (n := n) C).stalkMap x) := by
  intro q
  obtain ⟨r,hr⟩ := Ideal.Quotient.mk_surjective (actualSubspaceStalkWholeEquiv (n := n) C x q)
  refine ⟨r,(actualSubspaceStalkWholeEquiv (n := n) C x).injective ?_⟩
  rw [actualSubspaceInclusionRingedHom_stalk,hr]

/-- The genuine topological inclusion and the actual quotient sheaf morphism form a local morphism. -/
@[implicit_reducible]
def actualSubspaceInclusion (C : Set M) :
    actualSubspaceLocallyRingedSpace (n := n) C ⟶
      ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) M where
  toHom := actualSubspaceInclusionRingedHom (n := n) C
  prop x := IsLocalHom.of_surjective _ (actualSubspaceInclusionRingedHom_stalk_surjective C x)

/-- The genuine locally ringed inclusion induces precisely the whole original quotient map. -/
theorem actualSubspaceInclusion_stalk (C : Set M) (x : C)
    (r : actualComplexStructureStalk (n := n) x.val) :
    actualSubspaceStalkWholeEquiv (n := n) C x
      ((actualSubspaceInclusion (n := n) C).stalkMap x r) =
      Ideal.Quotient.mk (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) x.val) r :=
  actualSubspaceInclusionRingedHom_stalk C x r

/-- The inclusion stalk kernel is the entire actual original vanishing ideal. -/
theorem actualSubspaceInclusion_stalk_kernel (C : Set M) (x : C) :
    RingHom.ker ((actualSubspaceInclusion (n := n) C).stalkMap x).hom =
      actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) x.val := by
  ext r
  change actualComplexStructureStalk (n := n) x.val at r
  change ((actualSubspaceInclusion (n := n) C).stalkMap x) r = 0 ↔ _
  constructor
  · intro h
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact (actualSubspaceInclusion_stalk C x r).symm.trans
      ((congrArg (actualSubspaceStalkWholeEquiv (n := n) C x) h).trans
        (actualSubspaceStalkWholeEquiv (n := n) C x).map_zero)
  · intro h
    apply (actualSubspaceStalkWholeEquiv (n := n) C x).injective
    rw [actualSubspaceInclusion_stalk,map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr h

/-- Closed original subsets give genuine closed topological embeddings, including singular ones. -/
theorem actualSubspaceInclusion_isClosedEmbedding (C : Set M) (hC : IsClosed C) :
    Topology.IsClosedEmbedding (actualSubspaceInclusion (n := n) C).base :=
  hC.isClosedEmbedding_subtypeVal


/-- The actual whole section ideal is exactly pointwise vanishing on the genuine subspace. -/
theorem actualSectionIdeal_vanishing_iff (C : Set M) (U : Opens M)
    (s : actualComplexSection (n := n) U) :
    s ∈ actualSectionIdeal (vanishingIdeal (n := n) C) U ↔
      ∀ (y : M) (hy : y ∈ U), y ∈ C → s ⟨y,hy⟩ = 0 := by
  constructor
  · intro hs y hy hyC
    have hj := Ideal.mem_map_of_mem (actualStalkChartEquiv (n := n) y).toRingHom (hs y hy)
    rw [map_actualWholeSheafStalkIdeal] at hj
    have hz := (HolGerm.mem_maximalIdeal_iff _).mp
      (whole_vanishing_stalk_le_maximalIdeal (n := n) hyC hj)
    change HolGerm.eval (actualStalkChartEquiv (n := n) y
      ((actualComplexStructureSheaf (n := n) M).presheaf.germ U y hy s)) = 0 at hz
    rw [actualStalkChartEquiv_germ] at hz
    have hvalue : sectionExtension U s y = 0 := by
      simpa [sectionChartRingHom,chartTranslatedGerm,translatedGerm,HolGerm.eval_mk,
        (chartAt (ComplexModel n) y).left_inv (mem_chart_source (ComplexModel n) y)] using hz
    exact (sectionExtension_apply U s y hy).symm.trans hvalue
  · intro hs y hy
    let f := sectionExtension U s
    have hf : HolomorphicAt n f y := sectionExtension_holomorphicAt U s y hy
    have hm : (vanishingIdeal (n := n) C).mem y f := by
      refine ⟨hf,?_⟩
      filter_upwards [U.isOpen.mem_nhds hy] with z hz hzC
      exact (sectionExtension_apply U s z hz).trans (hs z hz hzC)
    have hmem : actualOriginalFunctionGerm y f hf ∈
        actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y :=
      Ideal.subset_span ⟨f,hf,hm,rfl⟩
    rwa [actualOriginalFunctionGerm_eq_section U y hy s f hf Filter.EventuallyEq.rfl] at hmem

private theorem actualSectionIdeal_vanishing_isRadical (C : Set M) (U : Opens M) :
    (actualSectionIdeal (vanishingIdeal (n := n) C) U).IsRadical := by
  rintro s ⟨k,hk⟩
  apply (actualSectionIdeal_vanishing_iff C U s).mpr
  intro y hy hyC
  have hz := (actualSectionIdeal_vanishing_iff C U (s^k)).mp hk y hy hyC
  change (s ⟨y,hy⟩)^k = 0 at hz
  exact eq_zero_of_pow_eq_zero hz

/-- Whole original vanishing stalks are genuinely radical, without coherence or smoothness. -/
theorem actualWholeVanishingStalkIdeal_isRadical (C : Set M) (y : M) :
    (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y).IsRadical := by
  let F := (actualComplexStructureSheaf (n := n) M).presheaf
  rintro r ⟨k,hk⟩
  obtain ⟨U,hyU,s,rfl⟩ := F.exists_germ_eq r
  have hpow : F.germ U y hyU (s^k) ∈
      actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y := by
    change (F.germ U y hyU).hom (s^k) ∈ _
    rw [map_pow]
    exact hk
  have himg : F.germ U y hyU (s^k) ∈ actualIdealSectionGermImage (vanishingIdeal (n := n) C) y := by
    rw [actualCentreIdealSectionGermImage_eq_whole C y]
    exact hpow
  obtain ⟨V,hyV,t,ht⟩ := himg
  obtain ⟨W,hyW,iU,iV,heq⟩ := F.germ_eq y hyU hyV (s^k) t.val ht.symm
  have hpowW : (F.map iU.op s)^k ∈ actualSectionIdeal (vanishingIdeal (n := n) C) W := by
    change ((F.map iU.op).hom s)^k ∈ _
    rw [← map_pow,heq]
    exact actualSectionIdeal_restrict (vanishingIdeal (n := n) C) W V (leOfHom iV) t.val t.property
  have hroot := actualSectionIdeal_vanishing_isRadical (n := n) C W ⟨k,hpowW⟩
  have hg := hroot y hyW
  rwa [F.germ_res_apply iU y hyW s] at hg

/-- The actual whole original vanishing quotient ring is reduced at every ambient point. -/
theorem actualWholeVanishingStalkQuotient_isReduced (C : Set M) (y : M) :
    IsReduced (actualComplexStructureStalk (n := n) y ⧸
      actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y) := by
  refine ⟨?_⟩
  rintro q ⟨k,hk⟩
  obtain ⟨r,rfl⟩ := Ideal.Quotient.mk_surjective q
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply actualWholeVanishingStalkIdeal_isRadical C y
  refine ⟨k,Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
  simpa only [map_pow] using hk

/-- The constructed genuine analytic-subspace stalks are reduced local rings, proved internally. -/
theorem actualSubspaceStalk_isReduced (C : Set M) (x : C) :
    IsReduced ((actualSubspaceSheaf (n := n) C).presheaf.stalk x).carrier := by
  let := actualWholeVanishingStalkQuotient_isReduced (n := n) C x.val
  exact isReduced_of_injective (actualSubspaceStalkWholeEquiv (n := n) C x)
    (actualSubspaceStalkWholeEquiv (n := n) C x).injective

end
end Hironaka.HironakaActualAnalyticSubspace
