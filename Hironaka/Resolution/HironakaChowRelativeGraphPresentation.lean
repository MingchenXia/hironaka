import Hironaka.Resolution.HironakaActualHolomorphicGraphIdeal
import Hironaka.Resolution.HironakaActualJointBaseFibre
import Hironaka.Resolution.HironakaActualAnalyticSubspaceIntrinsicLifting

/-! Actual base-first relative graph quotients for ANY whole source ideal,
and original native stalk presentations from ordinary intrinsic morphisms.
Existing whole graph kernel and native stalk/lift maps are reused.
BP FIRST: hironaka-g10-relative-graph-presentation.tex. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaChowRelativeGraphPresentation
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaRelativeNormalIdeal HironakaActualCentreJointJets
  HironakaHolomorphicJetChartInvariance HironakaActualJointBaseFibre
  HironakaHolomorphicJetRankLoci HironakaHolomorphicJetMonomialSpan
  HironakaActualHolomorphicGraphIdeal
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceOpenRestriction
  HironakaActualAnalyticSubspaceIntrinsicLifting
  HironakaActualWholeStalkHolomorphicPullback
  HironakaReducedComplexAnalyticSpaces

private def swapLinear (d t : ℕ) : ComplexModel (d+t) ≃L[ℂ] ComplexModel (t+d) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (finAddFlip : Fin (d+t) ≃ Fin (t+d))).toContinuousLinearEquiv

private theorem swapLinear_source (d t : ℕ) (w : ComplexModel (d+t)) (i : Fin t) :
    swapLinear d t w (i.castAdd d) = w (i.natAdd d) := by
  change w ((finAddFlip : Fin (d+t) ≃ Fin (t+d)).symm (i.castAdd d)) = _
  rw [(finAddFlip : Fin (d+t) ≃ Fin (t+d)).symm_apply_eq.mpr
    (finAddFlip_apply_natAdd i d).symm]

private theorem swapLinear_base (d t : ℕ) (w : ComplexModel (d+t)) (i : Fin d) :
    swapLinear d t w (i.natAdd t) = w (i.castAdd t) := by
  change w ((finAddFlip : Fin (d+t) ≃ Fin (t+d)).symm (i.natAdd t)) = _
  rw [(finAddFlip : Fin (d+t) ≃ Fin (t+d)).symm_apply_eq.mpr
    (finAddFlip_apply_castAdd i t).symm]

private def swapGerm (d t : ℕ) :
    HolGerm (ComplexModel (t+d)) ≃ₐ[ℂ] HolGerm (ComplexModel (d+t)) where
  toRingEquiv := HolGerm.comapEquiv (swapLinear d t)
  commutes' _ := rfl

variable (d t : ℕ) (F : ComplexModel t → ComplexModel d)
  (hF : ∀ᶠ z in nhds (0 : ComplexModel t), DifferentiableAt ℂ F z) (hF0 : F 0 = 0)

/-- Actual substitution g(u,z) ↦ g(F(z),z), with ORIGINAL base coordinates first. -/
def relativeGraphTrace : HolGerm (ComplexModel (d+t)) →ₐ[ℂ] HolGerm (ComplexModel t) :=
  (graphTrace F hF hF0).comp (swapGerm d t).symm.toAlgHom

/-- The whole source-coordinate pullback, in the SAME base-first ring. -/
def relativeSourcePullback : HolGerm (ComplexModel t) →ₐ[ℂ] HolGerm (ComplexModel (d+t)) :=
  (swapGerm d t).toAlgHom.comp (tangentPullback t d)

/-- The genuine finite graph equations, transported by actual block interchange. -/
def relativeGraphEquations : Ideal (HolGerm (ComplexModel (d+t))) :=
  Ideal.map (swapGerm d t).toRingHom (graphRelations F hF)

/-- The same source-coordinate map is the existing native normal pullback. -/
theorem relativeSourcePullback_eq_normalPullback (g : HolGerm (ComplexModel t)) :
    relativeSourcePullback d t g = jointNormalPullback d t g := by
  induction g using HolGerm.induction_on with
  | h f hf =>
    change HolGerm.comapEquiv (swapLinear d t) (tangentPullback t d (HolGerm.mk f hf)) = _
    unfold tangentPullback jointNormalPullback
    rw [compAlgHom_mk,HolGerm.comapEquiv_mk,compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    apply Eventually.of_forall
    intro w
    apply congrArg f
    ext i
    exact swapLinear_source d t w i

/-- The transported graph equations are the literal ORIGINAL base-first functions u_i-F_i(z). -/
theorem relativeGraphEquation_eq (i : Fin d) :
    swapGerm d t (graphRelation F hF i) = coordinateGerm (i.castAdd t) -
      jointNormalPullback d t (compAlgHom F hF hF0 (coordinateGerm i)) := by
  change HolGerm.comapEquiv (swapLinear d t) (graphRelation F hF i) = _
  unfold graphRelation coordinateGerm jointNormalPullback
  rw [HolGerm.comapEquiv_mk,compAlgHom_mk,compAlgHom_mk,← HolGerm.mk_sub]
  apply HolGerm.mk_eq_mk_iff.mpr
  apply Eventually.of_forall
  intro w
  change swapLinear d t w (i.natAdd t) - F (tangentProjection t d (swapLinear d t w)) i =
    w (i.castAdd t) - F (actualJointNormalProjection d t w) i
  rw [swapLinear_base]
  have hp : tangentProjection t d (swapLinear d t w) = actualJointNormalProjection d t w := by
    ext j
    exact swapLinear_source d t w j
  rw [hp]

/-- Exact finite span of the whole original base-first graph equations. -/
theorem relativeGraphEquations_eq_span :
    relativeGraphEquations d t F hF = Ideal.span (range fun i : Fin d =>
      coordinateGerm (i.castAdd t) - jointNormalPullback d t (compAlgHom F hF hF0 (coordinateGerm i))) := by
  unfold relativeGraphEquations graphRelations
  rw [Ideal.map_span,← Set.range_comp]
  congr 2
  funext i
  exact relativeGraphEquation_eq d t F hF hF0 i

/-- Actual graph substitution retracts the entire source-coordinate pullback. -/
theorem relativeGraphTrace_sourcePullback (g : HolGerm (ComplexModel t)) :
    relativeGraphTrace d t F hF hF0 (relativeSourcePullback d t g) = g := by
  change graphTrace F hF hF0 ((swapGerm d t).symm
    ((swapGerm d t) (tangentPullback t d g))) = g
  rw [AlgEquiv.symm_apply_apply,graphTrace_tangentPullback]

private theorem swapGerm_normalPullback (a : HolGerm (ComplexModel d)) :
    swapGerm d t (jointNormalPullback t d a) = tangentPullback d t a := by
  induction a using HolGerm.induction_on with
  | h f hf =>
    change HolGerm.comapEquiv (swapLinear d t) (jointNormalPullback t d (HolGerm.mk f hf)) = _
    unfold jointNormalPullback tangentPullback
    rw [compAlgHom_mk,HolGerm.comapEquiv_mk,compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    apply Eventually.of_forall
    intro w
    apply congrArg f
    ext i
    exact swapLinear_base d t w i

private theorem graphTrace_normalPullback (a : HolGerm (ComplexModel d)) :
    graphTrace F hF hF0 (jointNormalPullback t d a) = compAlgHom F hF hF0 a := by
  induction a using HolGerm.induction_on with
  | h f hf =>
    unfold graphTrace jointNormalPullback
    rw [compAlgHom_mk,compAlgHom_mk,compAlgHom_mk]
    exact HolGerm.mk_eq_mk_iff.mpr (Eventually.of_forall fun z =>
      congrArg f (normalProjection_graphSection F z))

/-- The actual base action restricts to the ORIGINAL composition map F*. -/
theorem relativeGraphTrace_basePullback (a : HolGerm (ComplexModel d)) :
    relativeGraphTrace d t F hF hF0 (tangentPullback d t a) = compAlgHom F hF hF0 a := by
  rw [← swapGerm_normalPullback d t a]
  change graphTrace F hF hF0 ((swapGerm d t).symm ((swapGerm d t) _)) = _
  rw [AlgEquiv.symm_apply_apply,graphTrace_normalPullback]

/-- The existing entire graph kernel is retained under genuine block interchange. -/
theorem ker_relativeGraphTrace :
    RingHom.ker (relativeGraphTrace d t F hF hF0).toRingHom =
      relativeGraphEquations d t F hF := by
  rw [relativeGraphEquations,← ker_graphTrace_eq_graphRelations F hF hF0]
  ext g
  constructor
  · intro hg
    have hm : (swapGerm d t).symm g ∈ RingHom.ker (graphTrace F hF hF0).toRingHom := hg
    have hi := Ideal.mem_map_of_mem (swapGerm d t).toRingHom hm
    change (swapGerm d t) ((swapGerm d t).symm g) ∈ _ at hi
    rwa [AlgEquiv.apply_symm_apply] at hi
  · intro hg
    obtain ⟨a,ha,he⟩ := (Ideal.mem_map_iff_of_surjective (swapGerm d t).toRingHom
      (swapGerm d t).surjective).mp hg
    subst g
    change graphTrace F hF hF0 ((swapGerm d t).symm ((swapGerm d t) a)) = 0
    rwa [AlgEquiv.symm_apply_apply]

/-- The ORIGINAL source ideal is extended whole, retaining every nonradical equation. -/
def relativeGraphIdeal (J : Ideal (HolGerm (ComplexModel t))) :
    Ideal (HolGerm (ComplexModel (d+t))) :=
  Ideal.map (relativeSourcePullback d t).toRingHom J ⊔ relativeGraphEquations d t F hF

/-- The explicitly generated graph ideal is the exact WHOLE substitution preimage. -/
theorem relativeGraphIdeal_eq_comap (J : Ideal (HolGerm (ComplexModel t))) :
    relativeGraphIdeal d t F hF J = Ideal.comap (relativeGraphTrace d t F hF hF0).toRingHom J := by
  rw [relativeGraphIdeal,← ker_relativeGraphTrace d t F hF hF0]
  apply le_antisymm
  · apply sup_le
    · apply Ideal.map_le_iff_le_comap.mpr
      intro g hg
      change relativeGraphTrace d t F hF hF0 (relativeSourcePullback d t g) ∈ J
      rwa [relativeGraphTrace_sourcePullback]
    · intro g hg
      change relativeGraphTrace d t F hF hF0 g ∈ J
      change relativeGraphTrace d t F hF hF0 g = 0 at hg
      rw [hg]
      exact J.zero_mem
  · intro g hg
    have hs := Ideal.mem_map_of_mem (relativeSourcePullback d t).toRingHom hg
    have hk : g-relativeSourcePullback d t (relativeGraphTrace d t F hF hF0 g) ∈
        RingHom.ker (relativeGraphTrace d t F hF hF0).toRingHom := by
      change relativeGraphTrace d t F hF hF0 _ = 0
      rw [map_sub,relativeGraphTrace_sourcePullback,sub_self]
    have ha := Ideal.add_mem _ (Ideal.mem_sup_left hs) (Ideal.mem_sup_right hk)
    convert ha using 1
    change g = relativeSourcePullback d t (relativeGraphTrace d t F hF hF0 g) +
      (g-relativeSourcePullback d t (relativeGraphTrace d t F hF hF0 g))
    ring

private def quotientMap (J : Ideal (HolGerm (ComplexModel t))) :
    HolGerm (ComplexModel (d+t)) →ₐ[ℂ] HolGerm (ComplexModel t) ⧸ J :=
  (Ideal.Quotient.mkₐ ℂ J).comp (relativeGraphTrace d t F hF hF0)

private theorem quotientMap_surjective (J : Ideal (HolGerm (ComplexModel t))) :
    Function.Surjective (quotientMap d t F hF hF0 J) := by
  intro a
  obtain ⟨g,rfl⟩ := Ideal.Quotient.mk_surjective a
  exact ⟨relativeSourcePullback d t g,congrArg (Ideal.Quotient.mk J)
    (relativeGraphTrace_sourcePullback d t F hF hF0 g)⟩

private theorem quotientMap_kernel (J : Ideal (HolGerm (ComplexModel t))) :
    RingHom.ker (quotientMap d t F hF hF0 J).toRingHom = relativeGraphIdeal d t F hF J := by
  rw [relativeGraphIdeal_eq_comap d t F hF hF0]
  ext g
  exact Ideal.Quotient.eq_zero_iff_mem

/-- The native WHOLE graph quotient equivalence; J is ANY original ideal. -/
def relativeGraphQuotientEquiv (J : Ideal (HolGerm (ComplexModel t))) :
    (HolGerm (ComplexModel (d+t)) ⧸ relativeGraphIdeal d t F hF J) ≃+*
      (HolGerm (ComplexModel t) ⧸ J) :=
  (Ideal.quotEquivOfEq (quotientMap_kernel d t F hF hF0 J).symm).trans
    (RingHom.quotientKerEquivOfSurjective (quotientMap_surjective d t F hF hF0 J))

/-- Every ORIGINAL graph numerator maps to its literal WHOLE substitution class. -/
theorem relativeGraphQuotientEquiv_mk (J : Ideal (HolGerm (ComplexModel t)))
    (g : HolGerm (ComplexModel (d+t))) :
    relativeGraphQuotientEquiv d t F hF hF0 J (Ideal.Quotient.mk _ g) =
      Ideal.Quotient.mk J (relativeGraphTrace d t F hF hF0 g) := by
  rfl

local instance : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) := tangentAlgebra d t
/-- SAME equivalence with the actual tangent base action and original F-composition action. -/
def relativeGraphQuotientAlgEquiv (J : Ideal (HolGerm (ComplexModel t))) :
    letI : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel t)) :=
      (compAlgHom F hF hF0).toRingHom.toAlgebra
    (HolGerm (ComplexModel (d+t)) ⧸ relativeGraphIdeal d t F hF J) ≃ₐ[HolGerm (ComplexModel d)]
      (HolGerm (ComplexModel t) ⧸ J) := by
  letI : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel t)) :=
    (compAlgHom F hF hF0).toRingHom.toAlgebra
  exact { relativeGraphQuotientEquiv d t F hF hF0 J with
    commutes' a := by
      change relativeGraphQuotientEquiv d t F hF hF0 J
        (Ideal.Quotient.mk _ (tangentPullback d t a)) = Ideal.Quotient.mk J (compAlgHom F hF hF0 a)
      rw [relativeGraphQuotientEquiv_mk,relativeGraphTrace_basePullback] }

section Native
variable {m n : ℕ} {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (ComplexModel m) M] [IsComplexManifold m M]
  [ChartedSpace (ComplexModel n) N] [IsComplexManifold n N]
  {f : M → N} (hf : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
  (C : Set M) (x : C)

/-- ORIGINAL base germ action, manufactured from the actual full native stalk maps. -/
def nativeBasePullback : HolGerm (ComplexModel n) →+*
    ((actualSubspaceSheaf (n := m) C).presheaf.stalk x).carrier :=
  ((actualSubspaceInclusion (n := m) C).stalkMap x).hom.comp
    (((ChartedSpace.locallyRingedSpaceMap f hf).stalkMap x.val).hom.comp
      (actualStalkChartEquiv (n := n) (f x.val)).symm.toRingHom)

private abbrev sourceChartIdeal : Ideal (HolGerm (ComplexModel m)) :=
  wholeChartStalkIdeal (vanishingIdeal (n := m) C) x.val x.val (mem_chart_source _ x.val)

/-- The actual translated original map and whole source chart ideal determine the relative ideal. -/
def nativeRelativeGraphIdeal : Ideal (HolGerm (ComplexModel (n+m))) :=
  relativeGraphIdeal n m (actualTranslatedMap f x.val)
    (actualTranslatedMap_holomorphic hf x.val) (sourceChartIdeal C x)

/-- Full original quotient-to-stalk equivalence derived from the actual geometric map. -/
def nativeRelativeGraphEquiv :
    (HolGerm (ComplexModel (n+m)) ⧸ nativeRelativeGraphIdeal hf C x) ≃+*
      ((actualSubspaceSheaf (n := m) C).presheaf.stalk x).carrier :=
  (relativeGraphQuotientEquiv n m (actualTranslatedMap f x.val)
    (actualTranslatedMap_holomorphic hf x.val) (actualTranslatedMap_zero f x.val)
      (sourceChartIdeal C x)).trans (actualSubspaceStalkChartEquiv (n := m) C x).symm

/-- Literal native whole-stalk representative formula for EVERY original joint germ. -/
theorem nativeRelativeGraphEquiv_mk (g : HolGerm (ComplexModel (n+m))) :
    nativeRelativeGraphEquiv hf C x (Ideal.Quotient.mk _ g) =
      (actualSubspaceStalkChartEquiv (n := m) C x).symm
        (Ideal.Quotient.mk _ (relativeGraphTrace n m (actualTranslatedMap f x.val)
          (actualTranslatedMap_holomorphic hf x.val) (actualTranslatedMap_zero f x.val) g)) := by
  rfl

/-- Original base scalars are EXACTLY the native whole-stalk pullback, not a transported action. -/
theorem nativeRelativeGraphEquiv_base (a : HolGerm (ComplexModel n)) :
    nativeRelativeGraphEquiv hf C x (Ideal.Quotient.mk _ (tangentPullback n m a)) =
      nativeBasePullback hf C x a := by
  rw [nativeRelativeGraphEquiv_mk,relativeGraphTrace_basePullback]
  apply (actualSubspaceStalkChartEquiv (n := m) C x).injective
  rw [RingEquiv.apply_symm_apply]
  change Ideal.Quotient.mk _ (actualHolomorphicGermPullback hf x.val a) =
    actualSubspaceStalkChartEquiv (n := m) C x
      ((actualSubspaceInclusion (n := m) C).stalkMap x
        ((ChartedSpace.locallyRingedSpaceMap f hf).stalkMap x.val
          ((actualStalkChartEquiv (n := n) (f x.val)).symm a)))
  change _ = (Ideal.quotientEquiv _ _ (actualStalkChartEquiv (n := m) x.val)
    (map_actualWholeSheafStalkIdeal (vanishingIdeal (n := m) C) x.val).symm)
      (actualSubspaceStalkWholeEquiv (n := m) C x _)
  rw [actualSubspaceInclusion_stalk]
  change _ = Ideal.Quotient.mk _ (actualStalkChartEquiv (n := m) x.val _)
  rw [actualNativeStalk_chart_pullback,RingEquiv.apply_symm_apply]

/-- The SAME native whole-stalk equivalence as an algebra equivalence for the actual original base action. -/
def nativeRelativeGraphAlgEquiv :
    letI : Algebra (HolGerm (ComplexModel n)) (HolGerm (ComplexModel (n+m))) := tangentAlgebra n m
    letI : Algebra (HolGerm (ComplexModel n))
      ((actualSubspaceSheaf (n := m) C).presheaf.stalk x).carrier :=
        (nativeBasePullback hf C x).toAlgebra
    (HolGerm (ComplexModel (n+m)) ⧸ nativeRelativeGraphIdeal hf C x) ≃ₐ[HolGerm (ComplexModel n)]
      ((actualSubspaceSheaf (n := m) C).presheaf.stalk x).carrier := by
  letI : Algebra (HolGerm (ComplexModel n)) (HolGerm (ComplexModel (n+m))) := tangentAlgebra n m
  letI : Algebra (HolGerm (ComplexModel n))
      ((actualSubspaceSheaf (n := m) C).presheaf.stalk x).carrier :=
    (nativeBasePullback hf C x).toAlgebra
  exact { nativeRelativeGraphEquiv hf C x with
    commutes' a := nativeRelativeGraphEquiv_base hf C x a }

end Native

/-- An ORDINARY intrinsic model morphism internally supplies the full lift and actual relative stalk presentation. -/
theorem exists_intrinsic_relative_graph_presentation
    {m n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel m) M] [IsComplexManifold m M]
    {C : Set M} {V : Opens (ComplexModel n)} {D : Set V}
    (G : actualSubspaceLocallyRingedSpace (n := m) C ⟶ actualSubspaceLocallyRingedSpace (n := n) D)
    (hG : G ≫ subspacePointMap (n := n) D = subspacePointMap (n := m) C) (x : C) :
    ∃ (O : Opens M) (hx : x.val ∈ O) (f : O → V)
      (hf : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
      (hCD : ∀ y ∈ (Subtype.val : O → M) ⁻¹' C, f y ∈ D),
      actualSubspaceMap hf hCD = actualOpenSubspaceMap (n := m) C O ≫ G ∧
      actualSubspaceInclusion (n := m) ((Subtype.val : O → M) ⁻¹' C) ≫
          ChartedSpace.locallyRingedSpaceMap f hf =
        (actualOpenSubspaceMap (n := m) C O ≫ G) ≫ actualSubspaceInclusion (n := n) D ∧
      let xO : (Subtype.val : O → M) ⁻¹' C := ⟨⟨x.val,hx⟩,x.property⟩
      (∀ g : HolGerm (ComplexModel (n+m)),
        nativeRelativeGraphEquiv hf _ xO (Ideal.Quotient.mk _ g) =
          (actualSubspaceStalkChartEquiv (n := m) _ xO).symm
            (Ideal.Quotient.mk _ (relativeGraphTrace n m (actualTranslatedMap f xO.val)
              (actualTranslatedMap_holomorphic hf xO.val) (actualTranslatedMap_zero f xO.val) g))) ∧
      ∀ a : HolGerm (ComplexModel n),
        nativeRelativeGraphEquiv hf _ xO (Ideal.Quotient.mk _ (tangentPullback n m a)) =
          nativeBasePullback hf _ xO a := by
  obtain ⟨O,hx,f,hf,hCD,hLift⟩ := exists_actualSubspaceMap_local_holomorphic_lift G hG x
  refine ⟨O,hx,f,hf,hCD,hLift,?_,fun g => nativeRelativeGraphEquiv_mk hf _ _ g,
    fun a => nativeRelativeGraphEquiv_base hf _ _ a⟩
  rw [actualSubspaceMap_inclusion hf hCD,hLift]

end
end Hironaka.HironakaChowRelativeGraphPresentation
