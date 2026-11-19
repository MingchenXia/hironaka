import Hironaka.Resolution.HironakaNonreducedAnalyticQuotientMorphism
import Hironaka.Resolution.HironakaNonreducedQuotientGermLifting

/-! Neighborhood analytic representatives of genuine full complex-compatible
nonreduced quotient LRS morphisms. No incoming ambient lift or reduced
point-value faithfulness is used.
BP FIRST: hironaka-nonreduced-quotient-neighborhood-lifting.tex. -/
set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaNonreducedQuotientNeighborhoodLifting
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaSmoothCentreRealDomainActualIdealPresheaf
  HironakaActualAnalyticSubspaceMaps HironakaActualAnalyticSubspaceOpenRestriction
  HironakaActualAnalyticSubspaceResidue HironakaReducedComplexAnalyticSpaces
  HironakaActualWholeStalkHolomorphicPullback HironakaActualBiholomorphicWholeStalkHS
  HironakaActualOpenIntrinsicHS HironakaHolomorphicJetChartInvariance
  HironakaHolomorphicJetRankLoci HironakaHolomorphicJetMonomialSpan
  HironakaNonreducedAnalyticQuotientModel HironakaNonreducedAnalyticQuotientMorphism
  HironakaNonreducedQuotientGermLifting RelativePrincipalizationSpan
  InvertibleIdealQuotient GermIdealPullbackCalculus

variable {n m : ℕ} {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [ChartedSpace (ComplexModel m) N] [IsComplexManifold m N]

/-- The actual structural map, through the original inclusion and original complex point. -/
def quotientPointMap (C : GermIdeal n M) (hC : C.IsCoherent) :
    quotientLocallyRingedSpace C hC ⟶ complexPoint := quotientInclusion C hC ≫ ambientPointMap n M

private theorem quotientChart_inclusion (C : GermIdeal n M) (hC : C.IsCoherent)
    (x : C.zeroLocus) (r : actualComplexStructureStalk (n := n) x.val) :
    quotientStalkChartEquiv C hC x ((quotientInclusion C hC).stalkMap x r) =
      Ideal.Quotient.mk (wholeChartStalkIdeal C x.val x.val (mem_chart_source _ _))
        (actualStalkChartEquiv (n := n) x.val r) := by
  simp only [quotientStalkChartEquiv,RingEquiv.trans_apply,quotientInclusion_stalk]
  rfl

/-- Original constants in the ENTIRE native quotient stalk. -/
def quotientStalkConst (C : GermIdeal n M) (hC : C.IsCoherent) (x : C.zeroLocus) :
    ℂ →+* ((quotientLocallyRingedSpace C hC).presheaf.stalk x).carrier :=
  (quotientStalkChartEquiv C hC x).symm.toRingHom.comp
    ((Ideal.Quotient.mk (wholeChartStalkIdeal C x.val x.val (mem_chart_source _ _))).comp HolGerm.constHom)

private def chartQuotientEval (C : GermIdeal n M) (x : C.zeroLocus) :
    (HolGerm (ComplexModel n) ⧸ wholeChartStalkIdeal C x.val x.val (mem_chart_source _ _)) →+* ℂ :=
  Ideal.Quotient.lift _ HolGerm.eval (fun r hr =>
    (HolGerm.mem_maximalIdeal_iff r).mp (chartIdeal_le_maximalIdeal C x hr))

/-- Genuine residue evaluation; nilpotents are retained in its SOURCE. -/
def quotientStalkEval (C : GermIdeal n M) (hC : C.IsCoherent) (x : C.zeroLocus) :
    ((quotientLocallyRingedSpace C hC).presheaf.stalk x).carrier →+* ℂ :=
  (chartQuotientEval C x).comp (quotientStalkChartEquiv C hC x).toRingHom

theorem quotientStalkEval_const (C : GermIdeal n M) (hC : C.IsCoherent) (x : C.zeroLocus) (c : ℂ) :
    quotientStalkEval C hC x (quotientStalkConst C hC x c) = c := by
  simp [quotientStalkEval,quotientStalkConst,chartQuotientEval]

private theorem quotientStalkEval_surjective (C : GermIdeal n M) (hC : C.IsCoherent) (x : C.zeroLocus) :
    Function.Surjective (quotientStalkEval C hC x) :=
  fun c => ⟨quotientStalkConst C hC x c,quotientStalkEval_const C hC x c⟩

private theorem quotientStalkEval_ker (C : GermIdeal n M) (hC : C.IsCoherent) (x : C.zeroLocus) :
    RingHom.ker (quotientStalkEval C hC x) =
      IsLocalRing.maximalIdeal ((quotientLocallyRingedSpace C hC).presheaf.stalk x).carrier :=
  IsLocalRing.ker_eq_maximalIdeal _ (quotientStalkEval_surjective C hC x)

/-- Canonical complex algebra action, independently identified with the actual structural map below. -/
@[instance_reducible]
def quotientStalkAlgebra (C : GermIdeal n M) (hC : C.IsCoherent) (x : C.zeroLocus) :
    Algebra ℂ ((quotientLocallyRingedSpace C hC).presheaf.stalk x).carrier :=
  (quotientStalkConst C hC x).toAlgebra
attribute [local instance] quotientStalkAlgebra

private theorem quotientStalk_noetherian (C : GermIdeal n M) (hC : C.IsCoherent) (x : C.zeroLocus) :
    IsNoetherianRing ((quotientLocallyRingedSpace C hC).presheaf.stalk x).carrier := by
  let : IsNoetherianRing (HolGerm (ComplexModel n)) := isNoetherianRing_holGerm_euclidean n
  let : IsNoetherianRing (HolGerm (ComplexModel n) ⧸
      wholeChartStalkIdeal C x.val x.val (mem_chart_source _ _)) := inferInstance
  exact isNoetherianRing_of_ringEquiv _ (quotientStalkChartEquiv C hC x).symm

private theorem quotientInclusion_stalk_const (C : GermIdeal n M) (hC : C.IsCoherent)
    (x : C.zeroLocus) (c : ℂ) :
    (quotientInclusion C hC).stalkMap x
      ((actualStalkChartEquiv (n := n) x.val).symm (HolGerm.constHom c)) =
        quotientStalkConst C hC x c := by
  apply (quotientStalkChartEquiv C hC x).injective
  rw [quotientChart_inclusion]
  change Ideal.Quotient.mk _
      (actualStalkChartEquiv (n := n) x.val ((actualStalkChartEquiv (n := n) x.val).symm (HolGerm.constHom c))) =
    quotientStalkChartEquiv C hC x ((quotientStalkChartEquiv C hC x).symm (Ideal.Quotient.mk _ (HolGerm.constHom c)))
  rw [RingEquiv.apply_symm_apply,RingEquiv.apply_symm_apply]

private theorem point_germ_pullback (x : M) (r : HolGerm (ComplexModel 0)) :
    actualHolomorphicGermPullback (n := 0) (m := n)
      (f := fun _ : M => (0 : ComplexModel 0)) contMDiff_const x r = HolGerm.constHom (HolGerm.eval r) := by
  induction r using HolGerm.induction_on with
  | h f hf =>
    unfold actualHolomorphicGermPullback
    rw [compAlgHom_mk,HolGerm.constHom_apply,HolGerm.eval_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun z => congrArg f (Subsingleton.elim _ _)

private theorem ambientPointMap_stalk_const (x : M) (c : ℂ) :
    (ambientPointMap n M).stalkMap x (actualComplexPointStalkEquiv.symm c) =
      (actualStalkChartEquiv (n := n) x).symm (HolGerm.constHom c) := by
  apply (actualStalkChartEquiv (n := n) x).injective
  change actualStalkChartEquiv (n := n) x
    ((ChartedSpace.locallyRingedSpaceMap (fun _ : M => (0 : ComplexModel 0)) contMDiff_const).stalkMap x
      (actualComplexPointStalkEquiv.symm c)) = _
  rw [actualNativeStalk_chart_pullback,point_germ_pullback,RingEquiv.apply_symm_apply]
  have hc : HolGerm.eval (actualStalkChartEquiv (n := 0) (0 : ComplexModel 0)
      (actualComplexPointStalkEquiv.symm c)) = c := actualComplexPointStalkEquiv.apply_symm_apply c
  rw [hc]

/-- The original structural morphism gives EXACTLY the native complex constant action. -/
theorem quotientPointMap_stalk_const (C : GermIdeal n M) (hC : C.IsCoherent)
    (x : C.zeroLocus) (c : ℂ) :
    (quotientPointMap C hC).stalkMap x (actualComplexPointStalkEquiv.symm c) = quotientStalkConst C hC x c := by
  change (quotientInclusion C hC ≫ ambientPointMap n M).stalkMap x _ = _
  rw [LocallyRingedSpace.stalkMap_comp]
  change (quotientInclusion C hC).stalkMap x
    ((ambientPointMap n M).stalkMap x.val (actualComplexPointStalkEquiv.symm c)) = _
  rw [ambientPointMap_stalk_const]
  exact quotientInclusion_stalk_const C hC x c

private theorem quotientPointMap_base (C : GermIdeal n M) (hC : C.IsCoherent) (x : C.zeroLocus) :
    (quotientPointMap C hC).base x = (0 : ComplexModel 0) := rfl

private theorem pointComposite_stalk_apply (C : GermIdeal n M) (hC : C.IsCoherent)
    (A : GermIdeal m N) (hA : A.IsCoherent)
    (F : quotientLocallyRingedSpace C hC ⟶ quotientLocallyRingedSpace A hA)
    (x : C.zeroLocus) (r : actualComplexStructureStalk (n := 0) (0 : ComplexModel 0)) :
    (F ≫ quotientPointMap A hA).stalkMap x r =
      F.stalkMap x ((quotientPointMap A hA).stalkMap (F.base x) r) :=
  ConcreteCategory.congr_hom (LocallyRingedSpace.stalkMap_comp F (quotientPointMap A hA) x) r

private theorem pointCompatible_stalk_apply (C : GermIdeal n M) (hC : C.IsCoherent)
    (A : GermIdeal m N) (hA : A.IsCoherent)
    (F : quotientLocallyRingedSpace C hC ⟶ quotientLocallyRingedSpace A hA)
    (hpoint : F ≫ quotientPointMap A hA = quotientPointMap C hC)
    (x : C.zeroLocus) (r : actualComplexStructureStalk (n := 0) (0 : ComplexModel 0)) :
    (F ≫ quotientPointMap A hA).stalkMap x r = (quotientPointMap C hC).stalkMap x r := by
  have h := LocallyRingedSpace.stalkMap_congr_hom (F ≫ quotientPointMap A hA) (quotientPointMap C hC) hpoint x
  have hs : (F ≫ quotientPointMap A hA).stalkMap x =
      complexPoint.presheaf.stalkSpecializes (specializes_refl ((quotientPointMap C hC).base x)) ≫
        (quotientPointMap C hC).stalkMap x := h
  rw [TopCat.Presheaf.stalkSpecializes_refl,Category.id_comp] at hs
  exact ConcreteCategory.congr_hom hs r

theorem quotientMap_const_of_point_compatible (C : GermIdeal n M) (hC : C.IsCoherent)
    (A : GermIdeal m N) (hA : A.IsCoherent)
    (F : quotientLocallyRingedSpace C hC ⟶ quotientLocallyRingedSpace A hA)
    (hpoint : F ≫ quotientPointMap A hA = quotientPointMap C hC)
    (x : C.zeroLocus) (c : ℂ) :
    F.stalkMap x (quotientStalkConst A hA (F.base x) c) = quotientStalkConst C hC x c := by
  exact (congrArg (F.stalkMap x) (quotientPointMap_stalk_const A hA (F.base x) c).symm).trans
    ((pointComposite_stalk_apply C hC A hA F x (actualComplexPointStalkEquiv.symm c)).symm.trans
      ((pointCompatible_stalk_apply C hC A hA F hpoint x (actualComplexPointStalkEquiv.symm c)).trans
        (quotientPointMap_stalk_const C hC x c)))

/-- Locality and the FULL scalar square preserve residue values, without residue faithfulness. -/
theorem quotientMap_eval_of_point_compatible (C : GermIdeal n M) (hC : C.IsCoherent)
    (A : GermIdeal m N) (hA : A.IsCoherent)
    (F : quotientLocallyRingedSpace C hC ⟶ quotientLocallyRingedSpace A hA)
    (hpoint : F ≫ quotientPointMap A hA = quotientPointMap C hC) (x : C.zeroLocus)
    (a : ((quotientLocallyRingedSpace A hA).presheaf.stalk (F.base x)).carrier) :
    quotientStalkEval C hC x (F.stalkMap x a) = quotientStalkEval A hA (F.base x) a := by
  let c := quotientStalkEval A hA (F.base x) a
  have hz : a-quotientStalkConst A hA (F.base x) c ∈
      IsLocalRing.maximalIdeal ((quotientLocallyRingedSpace A hA).presheaf.stalk (F.base x)).carrier := by
    rw [←quotientStalkEval_ker,RingHom.mem_ker,map_sub,quotientStalkEval_const]
    exact sub_self c
  have hm := map_nonunit (F.stalkMap x).hom _ hz
  change (F.stalkMap x).hom _ ∈
    IsLocalRing.maximalIdeal ((quotientLocallyRingedSpace C hC).presheaf.stalk x).carrier at hm
  rw [←quotientStalkEval_ker,RingHom.mem_ker,map_sub,map_sub] at hm
  have hc := quotientMap_const_of_point_compatible C hC A hA F hpoint x c
  exact (sub_eq_zero.mp hm).trans
    ((congrArg (quotientStalkEval C hC x) hc).trans (quotientStalkEval_const C hC x c))

/-- The stalk algebra homomorphism is OUTPUT from the full genuine structural square. -/
def quotientStalkAlgHom (C : GermIdeal n M) (hC : C.IsCoherent)
    (A : GermIdeal m N) (hA : A.IsCoherent)
    (F : quotientLocallyRingedSpace C hC ⟶ quotientLocallyRingedSpace A hA)
    (hpoint : F ≫ quotientPointMap A hA = quotientPointMap C hC) (x : C.zeroLocus) :
    ((quotientLocallyRingedSpace A hA).presheaf.stalk (F.base x)).carrier →ₐ[ℂ]
      ((quotientLocallyRingedSpace C hC).presheaf.stalk x).carrier :=
  { (F.stalkMap x).hom with commutes' c := quotientMap_const_of_point_compatible C hC A hA F hpoint x c }

/-- The SAME independent whole chart equivalence preserves the genuine complex action. -/
def quotientStalkChartAlgEquiv (C : GermIdeal n M) (hC : C.IsCoherent) (x : C.zeroLocus) :
    ((quotientLocallyRingedSpace C hC).presheaf.stalk x).carrier ≃ₐ[ℂ]
      (HolGerm (ComplexModel n) ⧸ wholeChartStalkIdeal C x.val x.val (mem_chart_source _ _)) :=
  { quotientStalkChartEquiv C hC x with commutes' _c := (quotientStalkChartEquiv C hC x).apply_symm_apply _ }

/-- An ordinary full complex-compatible map gives the actual chart quotient algebra hom on GENERAL manifolds. -/
def quotientChartStalkAlgHom (C : GermIdeal n M) (hC : C.IsCoherent)
    (A : GermIdeal m N) (hA : A.IsCoherent)
    (F : quotientLocallyRingedSpace C hC ⟶ quotientLocallyRingedSpace A hA)
    (hpoint : F ≫ quotientPointMap A hA = quotientPointMap C hC) (x : C.zeroLocus) :
    (HolGerm (ComplexModel m) ⧸ wholeChartStalkIdeal A (F.base x).val (F.base x).val (mem_chart_source _ _)) →ₐ[ℂ]
      (HolGerm (ComplexModel n) ⧸ wholeChartStalkIdeal C x.val x.val (mem_chart_source _ _)) :=
  (quotientStalkChartAlgEquiv C hC x).toAlgHom.comp
    ((quotientStalkAlgHom C hC A hA F hpoint x).comp
      (quotientStalkChartAlgEquiv A hA (F.base x)).symm.toAlgHom)

instance quotientChartStalkAlgHom_isLocalHom (C : GermIdeal n M) (hC : C.IsCoherent)
    (A : GermIdeal m N) (hA : A.IsCoherent)
    (F : quotientLocallyRingedSpace C hC ⟶ quotientLocallyRingedSpace A hA)
    (hpoint : F ≫ quotientPointMap A hA = quotientPointMap C hC) (x : C.zeroLocus) :
    IsLocalHom (quotientChartStalkAlgHom C hC A hA F hpoint x).toRingHom := by
  let : IsLocalRing (HolGerm (ComplexModel m) ⧸
      wholeChartStalkIdeal A (F.base x).val (F.base x).val (mem_chart_source _ _)) := chartQuotient_isLocalRing A (F.base x)
  let : IsLocalRing (HolGerm (ComplexModel n) ⧸
      wholeChartStalkIdeal C x.val x.val (mem_chart_source _ _)) := chartQuotient_isLocalRing C x
  let : IsLocalHom (quotientStalkChartEquiv C hC x).toRingHom :=
    ⟨fun r hr => by
      have h := (quotientStalkChartEquiv C hC x).symm.toRingHom.isUnit_map hr
      change IsUnit ((quotientStalkChartEquiv C hC x).symm (quotientStalkChartEquiv C hC x r)) at h
      rwa [RingEquiv.symm_apply_apply] at h⟩
  let : IsLocalHom (quotientStalkChartEquiv A hA (F.base x)).symm.toRingHom :=
    ⟨fun r hr => by
      have h := (quotientStalkChartEquiv A hA (F.base x)).toRingHom.isUnit_map hr
      change IsUnit (quotientStalkChartEquiv A hA (F.base x) ((quotientStalkChartEquiv A hA (F.base x)).symm r)) at h
      rwa [RingEquiv.apply_symm_apply] at h⟩
  let : IsLocalHom (F.stalkMap x).hom := F.prop x
  change IsLocalHom ((quotientStalkChartEquiv C hC x).toRingHom.comp
    ((F.stalkMap x).hom.comp (quotientStalkChartEquiv A hA (F.base x)).symm.toRingHom))
  infer_instance

/-- Coherence reflects WHOLE chart membership into actual ORIGINAL holomorphic membership. -/
theorem coherent_mem_iff_whole_chart (C : GermIdeal n M) (hC : C.IsCoherent)
    (x : M) (g : M → ℂ) (hg : HolomorphicAt n g x) :
    C.mem x g ↔ chartTranslatedGerm x x (mem_chart_source _ x) g hg ∈
      wholeChartStalkIdeal C x x (mem_chart_source _ x) := by
  obtain ⟨U,hU,hx,s,G,hG,hgen⟩ := hC x
  have hGhol (i : Fin s) : HolomorphicAt n (G i) x :=
    holomorphicAt_of_mdifferentiableOn hU (hG i) hx
  rw [wholeChartStalkIdeal_eq_actual_generator_span C x G hGhol (hgen x hx)]
  let H : Fin s → ComplexModel n → ℂ := fun i z => G i ((chartAt (ComplexModel n) x).symm z)
  have hH (i : Fin s) := CartanLocalReduction.holAt_comp_chart_symm (mem_chart_source _ x) (hGhol i)
  exact (hgen x hx g).trans
    ((ManifoldFiniteSpanChartTransport.isInSpanAt_comp_chartSymm_iff (mem_chart_source _ x) G g).trans
      (isInSpanAt_iff_translatedGerm_mem H _ hH
        (CartanLocalReduction.holAt_comp_chart_symm (mem_chart_source _ x) hg)))

/-- Equivalent reflection in the literal native ORIGINAL structure-sheaf stalk. -/
theorem coherent_mem_iff_actual_whole (C : GermIdeal n M) (hC : C.IsCoherent)
    (x : M) (g : M → ℂ) (hg : HolomorphicAt n g x) :
    C.mem x g ↔ actualOriginalFunctionGerm x g hg ∈ actualWholeSheafStalkIdeal C x := by
  constructor
  · intro h
    exact Ideal.subset_span ⟨g,hg,h,rfl⟩
  · intro h
    apply (coherent_mem_iff_whole_chart C hC x g hg).mpr
    have hm := Ideal.mem_map_of_mem (actualStalkChartEquiv (n := n) x).toRingHom h
    rw [map_actualWholeSheafStalkIdeal] at hm
    exact (actualOriginalFunctionGerm_chart x g hg) ▸ hm

theorem chartIdeal_eq_top_off_support (C : GermIdeal n M) (hC : C.IsCoherent)
    (x : M) (hx : x ∉ C.zeroLocus) : wholeChartStalkIdeal C x x (mem_chart_source _ x) = ⊤ := by
  have h : ∃ g : M → ℂ, C.mem x g ∧ g x ≠ 0 := by
    by_contra h
    push Not at h
    exact hx h
  obtain ⟨g,hg,hg0⟩ := h
  have hhol := GermIdeal.IsCoherent.holomorphicAt_mem hC hg
  have hu : IsUnit (chartTranslatedGerm x x (mem_chart_source _ x) g hhol) := by
    apply (HolGerm.isUnit_iff_eval_ne_zero _).mpr
    simpa [chartTranslatedGerm,translatedGerm,HolGerm.eval_mk,
      (chartAt (ComplexModel n) x).left_inv (mem_chart_source _ x)] using hg0
  exact (wholeChartStalkIdeal C x x (mem_chart_source _ x)).eq_top_of_isUnit_mem
    (Ideal.subset_span ⟨g,hhol,hg,rfl⟩) hu

/-- EVERY native nonreduced quotient section has one real ambient representative near the chosen point,
with equality at EVERY support germ on that SAME neighborhood. -/
theorem quotientSection_local_ambient (C : GermIdeal n M) (hC : C.IsCoherent)
    (W : Opens (TopCat.of C.zeroLocus))
    (s : ((quotientLocallyRingedSpace C hC).presheaf.obj (op W)).carrier)
    (x : C.zeroLocus) (hx : x ∈ W) :
    ∃ (O : Opens M) (_hxO : x.val ∈ O) (t : actualComplexSection (n := n) O)
      (hOW : ∀ y : C.zeroLocus, y.val ∈ O → y ∈ W),
      ∀ (y : C.zeroLocus) (hyO : y.val ∈ O),
        (quotientLocallyRingedSpace C hC).presheaf.germ W y (hOW y hyO) s =
          (quotientInclusion C hC).stalkMap y
            ((actualComplexStructureSheaf (n := n) M).presheaf.germ O y.val hyO t) := by
  let S := (quotientLocallyRingedSpace C hC).presheaf
  let B := (actualComplexStructureSheaf (n := n) M).presheaf
  let I := quotientInclusion C hC
  obtain ⟨r,hr⟩ := quotientInclusion_surjective_stalk C hC x (S.germ W x hx s)
  obtain ⟨O₀,hxO₀,t₀,ht₀⟩ := B.exists_germ_eq r
  let V := (Opens.map I.base).obj O₀
  let a := I.toHom.c.app (op O₀) t₀
  have hxa : S.germ V x hxO₀ a = S.germ W x hx s := by
    calc
      _ = I.stalkMap x (B.germ O₀ x.val hxO₀ t₀) :=
        (LocallyRingedSpace.stalkMap_germ_apply I O₀ x hxO₀ t₀).symm
      _ = I.stalkMap x r := congrArg (I.stalkMap x) ht₀
      _ = _ := hr
  obtain ⟨Q,hxQ,iV,iW,ha⟩ := S.germ_eq x hxO₀ hx a s hxa
  obtain ⟨T,hT,hTQ⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp Q.isOpen
  let O : Opens M := ⟨T,hT⟩ ⊓ O₀
  have hQ : ∀ y : C.zeroLocus, y.val ∈ O → y ∈ Q := by
    intro y hy
    exact (Set.ext_iff.mp hTQ y).mp hy.1
  have hOW : ∀ y : C.zeroLocus, y.val ∈ O → y ∈ W := fun y hy => (leOfHom iW) (hQ y hy)
  have hxO : x.val ∈ O := ⟨(Set.ext_iff.mp hTQ x).mpr hxQ,hxO₀⟩
  let t := B.map (homOfLE (show O ≤ O₀ from inf_le_right)).op t₀
  refine ⟨O,hxO,t,hOW,?_⟩
  intro y hy
  have hyQ := hQ y hy
  have he := congrArg (S.germ Q y hyQ) ha
  rw [S.germ_res_apply,S.germ_res_apply] at he
  calc
    _ = S.germ V y ((leOfHom iV) hyQ) a := he.symm
    _ = I.stalkMap y (B.germ O₀ y.val hy.2 t₀) :=
      (LocallyRingedSpace.stalkMap_germ_apply I O₀ y hy.2 t₀).symm
    _ = _ := congrArg (I.stalkMap y)
      (B.germ_res_apply (homOfLE (show O ≤ O₀ from inf_le_right)) y.val hy t₀).symm

private theorem quotientStalkEval_inclusion (C : GermIdeal n M) (hC : C.IsCoherent)
    (x : C.zeroLocus) (r : actualComplexStructureStalk (n := n) x.val) :
    quotientStalkEval C hC x ((quotientInclusion C hC).stalkMap x r) =
      HolGerm.eval (actualStalkChartEquiv (n := n) x.val r) :=
  congrArg (chartQuotientEval C x) (quotientChart_inclusion C hC x r)

private theorem quotientStalkEval_inclusion_germ (C : GermIdeal n M) (hC : C.IsCoherent)
    (O : Opens M) (t : actualComplexSection (n := n) O) (y : C.zeroLocus) (hy : y.val ∈ O) :
    quotientStalkEval C hC y ((quotientInclusion C hC).stalkMap y
      ((actualComplexStructureSheaf (n := n) M).presheaf.germ O y.val hy t)) = t ⟨y.val,hy⟩ := by
  rw [quotientStalkEval_inclusion,actualStalkChartEquiv_germ]
  simpa [sectionChartRingHom,chartTranslatedGerm,translatedGerm,HolGerm.eval_mk,
    (chartAt (ComplexModel n) y.val).left_inv (mem_chart_source _ y.val)] using sectionExtension_apply O t y.val hy

private theorem actualGerm_eval {f : M → N}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f) (x : M)
    (g : HolGerm (ComplexModel m)) : HolGerm.eval (actualHolomorphicGermPullback hf x g) = HolGerm.eval g := by
  induction g using HolGerm.induction_on with
  | h h hh =>
    unfold actualHolomorphicGermPullback
    rw [compAlgHom_mk]
    change h (actualTranslatedMap (n := m) (m := n) f x 0) = h 0
    rw [actualTranslatedMap_zero]

/-- Actual pointed local chart substitution is LOCAL before any ideal inclusion is known. -/
instance actualHolomorphicGermPullback_isLocalHom {f : M → N}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f) (x : M) :
    IsLocalHom (actualHolomorphicGermPullback hf x).toRingHom := by
  refine ⟨fun g hg => ?_⟩
  apply (HolGerm.isUnit_iff_eval_ne_zero g).mpr
  have h := (HolGerm.isUnit_iff_eval_ne_zero (actualHolomorphicGermPullback hf x g)).mp hg
  rwa [actualGerm_eval] at h

/-- Actual holomorphic quotient maps preserve the FULL genuine complex structural square. -/
theorem quotientMap_point {f : M → N}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
    (C : GermIdeal n M) (hC : C.IsCoherent) (A : GermIdeal m N) (hA : A.IsCoherent)
    (hCA : GermIdeal.Le (GermIdeal.pullback (m := n) f A) C) :
    quotientMap hf C hC A hA hCA ≫ quotientPointMap A hA = quotientPointMap C hC := by
  unfold quotientPointMap
  rw [←Category.assoc,←quotientMap_inclusion,Category.assoc]
  have h : ChartedSpace.locallyRingedSpaceMap f hf ≫ ambientPointMap m N = ambientPointMap n M := by
    change ChartedSpace.locallyRingedSpaceMap f hf ≫
      ChartedSpace.locallyRingedSpaceMap (fun _ : N => (0 : ComplexModel 0)) contMDiff_const =
        ChartedSpace.locallyRingedSpaceMap (fun _ : M => (0 : ComplexModel 0)) contMDiff_const
    rw [←ChartedSpace.locallyRingedSpace_comp]
    rfl
  rw [h]

/-- Literal whole original ideal on an actual open, chosen without any later map. -/
def quotientOpenIdeal (C : GermIdeal n M) (O : Opens M) : GermIdeal n O :=
  GermIdeal.pullback (m := n) (Subtype.val : O → M) C

theorem quotientOpenIdeal_coherent (C : GermIdeal n M) (hC : C.IsCoherent) (O : Opens M) :
    (quotientOpenIdeal C O).IsCoherent := isCoherent_pullback contMDiff_subtype_val hC

/-- Canonical native open map, constructed from the reflexive WHOLE pullback inclusion. -/
def quotientOpenMap (C : GermIdeal n M) (hC : C.IsCoherent) (O : Opens M) :
    quotientLocallyRingedSpace (quotientOpenIdeal C O) (quotientOpenIdeal_coherent C hC O) ⟶
      quotientLocallyRingedSpace C hC :=
  quotientMap contMDiff_subtype_val _ (quotientOpenIdeal_coherent C hC O) C hC (fun _ _ h => h)

theorem quotientOpenMap_point (C : GermIdeal n M) (hC : C.IsCoherent) (O : Opens M) :
    quotientOpenMap C hC O ≫ quotientPointMap C hC =
      quotientPointMap (quotientOpenIdeal C O) (quotientOpenIdeal_coherent C hC O) :=
  quotientMap_point contMDiff_subtype_val _ (quotientOpenIdeal_coherent C hC O) C hC (fun _ _ h => h)

private theorem open_support_iff (C : GermIdeal n M) (hC : C.IsCoherent) (O : Opens M) (y : O) :
    y ∈ (quotientOpenIdeal C O).zeroLocus ↔ y.val ∈ C.zeroLocus := by
  constructor
  · intro hy g hg
    exact hy (g ∘ Subtype.val) (GermIdeal.mem_pullback_iff.mpr (isInSpanAt_self ⟨g,hg,rfl⟩
      ((GermIdeal.IsCoherent.holomorphicAt_mem hC hg).comp_contMDiff
        (Eventually.of_forall fun _ => contMDiff_subtype_val.contMDiffAt))))
  · intro hy g hg
    obtain ⟨_,s,g,a,hg,_,he⟩ := hg
    rw [he.self_of_nhds]
    apply Finset.sum_eq_zero
    intro i _
    obtain ⟨v,hv,heq⟩ := hg i
    rw [heq,Function.comp_apply,hy v hv,mul_zero]

private theorem openMap_base_val (C : GermIdeal n M) (hC : C.IsCoherent) (O : Opens M)
    (y : (quotientOpenIdeal C O).zeroLocus) : ((quotientOpenMap C hC O).base y).val = y.val.val := rfl

def quotientCarrierOpen (C : GermIdeal n M) (hC : C.IsCoherent) (O : Opens M) :
    Opens (quotientLocallyRingedSpace C hC) := (Opens.map (quotientInclusion C hC).base).obj O

private def openSupportHomeomorph (C : GermIdeal n M) (hC : C.IsCoherent) (O : Opens M) :
    (quotientOpenIdeal C O).zeroLocus ≃ₜ quotientCarrierOpen C hC O where
  toFun y := ⟨(quotientOpenMap C hC O).base y,y.val.property⟩
  invFun x := ⟨⟨x.val.val,x.property⟩,(open_support_iff C hC O _).mpr x.val.property⟩
  left_inv y := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; apply Subtype.ext; rfl
  continuous_toFun := (quotientOpenMap C hC O).base.hom.continuous.subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    fun_prop

theorem quotientOpenMap_range (C : GermIdeal n M) (hC : C.IsCoherent) (O : Opens M) :
    Set.range (quotientOpenMap C hC O).base = {x : C.zeroLocus | x.val ∈ O} := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    exact y.val.property
  · intro hx
    refine ⟨⟨⟨x.val,hx⟩,(open_support_iff C hC O _).mpr x.property⟩,?_⟩
    apply Subtype.ext
    rfl

private theorem quotientOpenMap_base_open (C : GermIdeal n M) (hC : C.IsCoherent) (O : Opens M) :
    Topology.IsOpenEmbedding (quotientOpenMap C hC O).base := by
  change Topology.IsOpenEmbedding ((Subtype.val : quotientCarrierOpen C hC O → C.zeroLocus) ∘
    (openSupportHomeomorph C hC O))
  exact (quotientCarrierOpen C hC O).isOpen.isOpenEmbedding_subtypeVal.comp
    (openSupportHomeomorph C hC O).isOpenEmbedding

private theorem quotientMap_chart_mk {a c : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (ComplexModel a) X] [IsComplexManifold a X]
    [ChartedSpace (ComplexModel c) Y] [IsComplexManifold c Y]
    {f : X → Y} (hf : ContMDiff 𝓘(ℂ,ComplexModel a) 𝓘(ℂ,ComplexModel c) ∞ f)
    (A : GermIdeal a X) (hA : A.IsCoherent) (B : GermIdeal c Y) (hB : B.IsCoherent)
    (hAB : GermIdeal.Le (GermIdeal.pullback (m := a) f B) A) (x : A.zeroLocus)
    (r : HolGerm (ComplexModel c)) :
    quotientStalkChartEquiv A hA x ((quotientMap hf A hA B hB hAB).stalkMap x
      ((quotientStalkChartEquiv B hB (quotientTopMap hf A B hB hAB x)).symm
        (Ideal.Quotient.mk (wholeChartStalkIdeal B (f x.val) (f x.val) (mem_chart_source _ _)) r))) =
      Ideal.Quotient.mk (wholeChartStalkIdeal A x.val x.val (mem_chart_source _ x.val))
        (actualHolomorphicGermPullback hf x.val r) := by
  let s := (actualStalkChartEquiv (n := c) (f x.val)).symm r
  have hchart : (quotientStalkChartEquiv B hB (quotientTopMap hf A B hB hAB x)).symm
      (Ideal.Quotient.mk (wholeChartStalkIdeal B (f x.val) (f x.val) (mem_chart_source _ _)) r) =
        (quotientInclusion B hB).stalkMap (quotientTopMap hf A B hB hAB x) s := by
    apply (quotientStalkChartEquiv B hB (quotientTopMap hf A B hB hAB x)).injective
    rw [RingEquiv.apply_symm_apply,quotientChart_inclusion]
    dsimp only [s]
    change Ideal.Quotient.mk (wholeChartStalkIdeal B (f x.val) (f x.val) (mem_chart_source _ _)) r =
      Ideal.Quotient.mk (wholeChartStalkIdeal B (f x.val) (f x.val) (mem_chart_source _ _))
        (actualStalkChartEquiv (n := c) (f x.val) ((actualStalkChartEquiv (n := c) (f x.val)).symm r))
    rw [RingEquiv.apply_symm_apply]
  have hwhole : (quotientStalkWholeEquiv B hB (quotientTopMap hf A B hB hAB x)).symm
      (Ideal.Quotient.mk (actualWholeSheafStalkIdeal B (f x.val)) s) =
        (quotientInclusion B hB).stalkMap (quotientTopMap hf A B hB hAB x) s := by
    apply (quotientStalkWholeEquiv B hB (quotientTopMap hf A B hB hAB x)).injective
    rw [RingEquiv.apply_symm_apply,quotientInclusion_stalk]
    rfl
  rw [hchart]
  have h := quotientMap_stalk_mk hf A hA B hB hAB x s
  rw [hwhole] at h
  simp only [quotientStalkChartEquiv,RingEquiv.trans_apply]
  rw [h]
  change Ideal.Quotient.mk _ (actualStalkChartEquiv (n := a) x.val
      ((ChartedSpace.locallyRingedSpaceMap f hf).stalkMap x.val s)) = _
  rw [actualNativeStalk_chart_pullback]
  dsimp only [s]
  rw [RingEquiv.apply_symm_apply]

private theorem openChartIdeal_eq (C : GermIdeal n M) (hC : C.IsCoherent) (O : Opens M)
    (y : (quotientOpenIdeal C O).zeroLocus) :
    wholeChartStalkIdeal (quotientOpenIdeal C O) y.val y.val (mem_chart_source _ _) =
      wholeChartStalkIdeal C ((quotientOpenMap C hC O).base y).val
        ((quotientOpenMap C hC O).base y).val (mem_chart_source _ _) := by
  change wholeChartStalkIdeal (GermIdeal.pullback (m := n) (Subtype.val : O → M) C)
      y.val y.val (mem_chart_source _ _) = wholeChartStalkIdeal C y.val.val y.val.val (mem_chart_source _ _)
  exact wholeChartStalkIdeal_actual_open_pullback C hC O y.val

/-- Canonical native stalk equivalence of the actual open quotient map, before ANY later F. -/
def quotientOpenStalkEquiv (C : GermIdeal n M) (hC : C.IsCoherent) (O : Opens M)
    (y : (quotientOpenIdeal C O).zeroLocus) :
    ((quotientLocallyRingedSpace C hC).presheaf.stalk ((quotientOpenMap C hC O).base y)).carrier ≃+*
      ((quotientLocallyRingedSpace (quotientOpenIdeal C O) (quotientOpenIdeal_coherent C hC O)).presheaf.stalk y).carrier :=
  ((quotientStalkChartEquiv C hC ((quotientOpenMap C hC O).base y)).trans
    (Ideal.quotEquivOfEq (openChartIdeal_eq C hC O y).symm)).trans
      (quotientStalkChartEquiv (quotientOpenIdeal C O) (quotientOpenIdeal_coherent C hC O) y).symm

/-- The independent whole quotient equivalence IS the actual native open-map stalk map. -/
theorem quotientOpenStalkEquiv_apply (C : GermIdeal n M) (hC : C.IsCoherent) (O : Opens M)
    (y : (quotientOpenIdeal C O).zeroLocus)
    (r : ((quotientLocallyRingedSpace C hC).presheaf.stalk ((quotientOpenMap C hC O).base y)).carrier) :
    quotientOpenStalkEquiv C hC O y r = (quotientOpenMap C hC O).stalkMap y r := by
  let e := quotientStalkChartEquiv C hC ((quotientOpenMap C hC O).base y)
  obtain ⟨g,hg⟩ := Ideal.Quotient.mk_surjective (e r)
  have hr : r = e.symm (Ideal.Quotient.mk _ g) := by
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    exact hg.symm
  rw [hr]
  apply (quotientStalkChartEquiv (quotientOpenIdeal C O) (quotientOpenIdeal_coherent C hC O) y).injective
  have he : quotientStalkChartEquiv (quotientOpenIdeal C O) (quotientOpenIdeal_coherent C hC O) y
      (quotientOpenStalkEquiv C hC O y (e.symm (Ideal.Quotient.mk _ g))) =
      Ideal.Quotient.mk (wholeChartStalkIdeal (quotientOpenIdeal C O) y.val y.val (mem_chart_source _ _)) g := by
    simp only [quotientOpenStalkEquiv,RingEquiv.trans_apply,RingEquiv.apply_symm_apply,e]
    rfl
  have hm := quotientMap_chart_mk contMDiff_subtype_val (quotientOpenIdeal C O)
    (quotientOpenIdeal_coherent C hC O) C hC (fun _ _ h => h) y g
  have hid : actualHolomorphicGermPullback (f := (Subtype.val : O → M)) contMDiff_subtype_val y.val g = g :=
    congrArg (fun f : HolGerm (ComplexModel n) →ₐ[ℂ] HolGerm (ComplexModel n) => f g)
      (actualHolomorphicGermPullback_val O y.val)
  have hm' := hm.trans (congrArg (Ideal.Quotient.mk
    (wholeChartStalkIdeal (quotientOpenIdeal C O) y.val y.val (mem_chart_source _ _))) hid)
  exact he.trans hm'.symm

instance quotientOpenMap_stalk_isIso (C : GermIdeal n M) (hC : C.IsCoherent) (O : Opens M)
    (y : (quotientOpenIdeal C O).zeroLocus) : IsIso ((quotientOpenMap C hC O).stalkMap y) := by
  have he : (quotientOpenMap C hC O).stalkMap y = (quotientOpenStalkEquiv C hC O y).toCommRingCatIso.hom := by
    apply CommRingCat.hom_ext
    ext r
    exact (quotientOpenStalkEquiv_apply C hC O y r).symm
  rw [he]
  infer_instance

/-- Actual open immersion, derived from original support geometry and EVERY actual whole stalk map. -/
instance quotientOpenMap_isOpenImmersion (C : GermIdeal n M) (hC : C.IsCoherent) (O : Opens M) :
    LocallyRingedSpace.IsOpenImmersion (quotientOpenMap C hC O) :=
  LocallyRingedSpace.IsOpenImmersion.of_stalk_iso _ (quotientOpenMap_base_open C hC O)

def quotientOpenRestriction (C : GermIdeal n M) (hC : C.IsCoherent) (O : Opens M) : LocallyRingedSpace :=
  (quotientLocallyRingedSpace C hC).restrict (Opens.isOpenEmbedding (quotientCarrierOpen C hC O))

def quotientOpenInclusion (C : GermIdeal n M) (hC : C.IsCoherent) (O : Opens M) :
    quotientOpenRestriction C hC O ⟶ quotientLocallyRingedSpace C hC :=
  (quotientLocallyRingedSpace C hC).ofRestrict (Opens.isOpenEmbedding (quotientCarrierOpen C hC O))

instance quotientOpenInclusion_isOpenImmersion (C : GermIdeal n M) (hC : C.IsCoherent) (O : Opens M) :
    LocallyRingedSpace.IsOpenImmersion (quotientOpenInclusion C hC O) := by
  change LocallyRingedSpace.IsOpenImmersion
    ((quotientLocallyRingedSpace C hC).ofRestrict (Opens.isOpenEmbedding (quotientCarrierOpen C hC O)))
  infer_instance

private theorem openInclusion_range (C : GermIdeal n M) (hC : C.IsCoherent) (O : Opens M) :
    Set.range (quotientOpenInclusion C hC O).base = {x : C.zeroLocus | x.val ∈ O} := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    exact y.property
  · intro hx
    exact ⟨⟨x,hx⟩,rfl⟩

private def openToRestriction (C : GermIdeal n M) (hC : C.IsCoherent) (O : Opens M) :
    quotientLocallyRingedSpace (quotientOpenIdeal C O) (quotientOpenIdeal_coherent C hC O) ⟶
      quotientOpenRestriction C hC O :=
  LocallyRingedSpace.IsOpenImmersion.lift (quotientOpenInclusion C hC O) (quotientOpenMap C hC O)
    (by rw [openInclusion_range,quotientOpenMap_range])

private def restrictionToOpen (C : GermIdeal n M) (hC : C.IsCoherent) (O : Opens M) :
    quotientOpenRestriction C hC O ⟶
      quotientLocallyRingedSpace (quotientOpenIdeal C O) (quotientOpenIdeal_coherent C hC O) :=
  LocallyRingedSpace.IsOpenImmersion.lift (quotientOpenMap C hC O) (quotientOpenInclusion C hC O)
    (by rw [openInclusion_range,quotientOpenMap_range])

private theorem openToRestriction_inclusion (C : GermIdeal n M) (hC : C.IsCoherent) (O : Opens M) :
    openToRestriction C hC O ≫ quotientOpenInclusion C hC O = quotientOpenMap C hC O :=
  LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _

private theorem restrictionToOpen_inclusion (C : GermIdeal n M) (hC : C.IsCoherent) (O : Opens M) :
    restrictionToOpen C hC O ≫ quotientOpenMap C hC O = quotientOpenInclusion C hC O :=
  LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _

/-- Genuine native isomorphism to the LITERAL carrier-open restriction, with full inclusion equations. -/
def quotientOpenIso (C : GermIdeal n M) (hC : C.IsCoherent) (O : Opens M) :
    quotientLocallyRingedSpace (quotientOpenIdeal C O) (quotientOpenIdeal_coherent C hC O) ≅
      quotientOpenRestriction C hC O where
  hom := openToRestriction C hC O
  inv := restrictionToOpen C hC O
  hom_inv_id := by
    apply (cancel_mono (quotientOpenMap C hC O)).mp
    rw [Category.assoc,restrictionToOpen_inclusion,openToRestriction_inclusion,Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono (quotientOpenInclusion C hC O)).mp
    rw [Category.assoc,openToRestriction_inclusion,restrictionToOpen_inclusion,Category.id_comp]

theorem quotientOpenIso_hom_inclusion (C : GermIdeal n M) (hC : C.IsCoherent) (O : Opens M) :
    (quotientOpenIso C hC O).hom ≫ quotientOpenInclusion C hC O = quotientOpenMap C hC O :=
  openToRestriction_inclusion C hC O

theorem quotientOpenIso_inv_inclusion (C : GermIdeal n M) (hC : C.IsCoherent) (O : Opens M) :
    (quotientOpenIso C hC O).inv ≫ quotientOpenMap C hC O = quotientOpenInclusion C hC O :=
  restrictionToOpen_inclusion C hC O

/-- Entire native morphisms are determined by their base map and EVERY whole chart numerator.
The numerator domain is the same ambient germ ring even before transporting image points. -/
theorem quotientHom_ext_chart (C : GermIdeal n M) (hC : C.IsCoherent)
    (A : GermIdeal m N) (hA : A.IsCoherent)
    (F G : quotientLocallyRingedSpace C hC ⟶ quotientLocallyRingedSpace A hA)
    (hF : F ≫ quotientPointMap A hA = quotientPointMap C hC)
    (hG : G ≫ quotientPointMap A hA = quotientPointMap C hC)
    (hbase : F.base = G.base)
    (hraw : ∀ (x : C.zeroLocus) (r : HolGerm (ComplexModel m)),
      quotientChartStalkAlgHom C hC A hA F hF x (Ideal.Quotient.mk _ r) =
      quotientChartStalkAlgHom C hC A hA G hG x (Ideal.Quotient.mk _ r)) : F = G := by
  rcases F with ⟨⟨f,fc⟩,hf⟩
  rcases G with ⟨⟨g,gc⟩,hg⟩
  change f = g at hbase
  subst g
  let F : quotientLocallyRingedSpace C hC ⟶ quotientLocallyRingedSpace A hA := ⟨⟨f,fc⟩,hf⟩
  let G : quotientLocallyRingedSpace C hC ⟶ quotientLocallyRingedSpace A hA := ⟨⟨f,gc⟩,hg⟩
  have hs (x : C.zeroLocus) (a : ((quotientLocallyRingedSpace A hA).presheaf.stalk (f x)).carrier) :
      F.stalkMap x a = G.stalkMap x a := by
    apply (quotientStalkChartEquiv C hC x).injective
    let e := quotientStalkChartEquiv A hA (f x)
    obtain ⟨r,hr⟩ := Ideal.Quotient.mk_surjective (e a)
    have ha : a = e.symm (Ideal.Quotient.mk _ r) := by
      apply e.injective
      rw [RingEquiv.apply_symm_apply]
      exact hr.symm
    rw [ha]
    exact hraw x r
  suffices hc : fc = gc by cases hc; rfl
  apply NatTrans.ext
  funext U
  apply CommRingCat.hom_ext
  ext s
  apply TopCat.Presheaf.section_ext (quotientLocallyRingedSpace C hC).sheaf
  intro x hx
  let a := (quotientLocallyRingedSpace A hA).presheaf.germ U.unop (f x) hx s
  calc
    _ = F.stalkMap x a := (LocallyRingedSpace.stalkMap_germ_apply F U.unop x hx s).symm
    _ = G.stalkMap x a := hs x a
    _ = _ := LocallyRingedSpace.stalkMap_germ_apply G U.unop x hx s

/-- Original coordinate sections on the actual target open, with no entire extension. -/
def coordinateSection (V : Opens (ComplexModel m)) (i : Fin m) :
    actualComplexSection (n := m) (⊤ : Opens V) := by
  have h₀ : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ℂ) ∞
      (fun z : ComplexModel m => z i) := (EuclideanSpace.proj (𝕜 := ℂ) i).contMDiff
  have h₁ : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ℂ) ∞
      (fun z : V => z.val i) := h₀.comp contMDiff_subtype_val
  exact ⟨fun z => z.val.val i,h₁.comp contMDiff_subtype_val⟩

private theorem local_scalar_lift (C : GermIdeal n M) (hC : C.IsCoherent)
    (A : GermIdeal m N) (hA : A.IsCoherent)
    (F : quotientLocallyRingedSpace C hC ⟶ quotientLocallyRingedSpace A hA)
    (hF : F ≫ quotientPointMap A hA = quotientPointMap C hC)
    (a : actualComplexSection (n := m) (⊤ : Opens N)) (x : C.zeroLocus) :
    ∃ (O : Opens M) (_hxO : x.val ∈ O) (t : actualComplexSection (n := n) O),
      (∀ (y : C.zeroLocus) (hy : y.val ∈ O),
        F.stalkMap y ((quotientInclusion A hA).stalkMap (F.base y)
          ((actualComplexStructureSheaf (n := m) N).presheaf.germ ⊤ (F.base y).val (by trivial) a)) =
        (quotientInclusion C hC).stalkMap y
          ((actualComplexStructureSheaf (n := n) M).presheaf.germ O y.val hy t)) ∧
      (∀ (y : C.zeroLocus) (hy : y.val ∈ O), t ⟨y.val,hy⟩ = a ⟨(F.base y).val,by trivial⟩) := by
  let K := F ≫ quotientInclusion A hA
  let W := (Opens.map K.base).obj (⊤ : Opens N)
  let s := K.c.app (op (⊤ : Opens N)) a
  obtain ⟨O,hxO,t,hOW,ht⟩ := quotientSection_local_ambient C hC W s x (by trivial)
  have hstalk (y : C.zeroLocus) (hy : y.val ∈ O) :
      F.stalkMap y ((quotientInclusion A hA).stalkMap (F.base y)
        ((actualComplexStructureSheaf (n := m) N).presheaf.germ ⊤ (F.base y).val (by trivial) a)) =
      (quotientInclusion C hC).stalkMap y
        ((actualComplexStructureSheaf (n := n) M).presheaf.germ O y.val hy t) := by
    let r := (actualComplexStructureSheaf (n := m) N).presheaf.germ ⊤ (F.base y).val (by trivial) a
    calc
      _ = K.stalkMap y r :=
        (ConcreteCategory.congr_hom (LocallyRingedSpace.stalkMap_comp F (quotientInclusion A hA) y) r).symm
      _ = (quotientLocallyRingedSpace C hC).presheaf.germ W y (hOW y hy) s :=
        LocallyRingedSpace.stalkMap_germ_apply K ⊤ y (by trivial) a
      _ = _ := ht y hy
  refine ⟨O,hxO,t,hstalk,?_⟩
  intro y hy
  calc
    _ = quotientStalkEval C hC y ((quotientInclusion C hC).stalkMap y
        ((actualComplexStructureSheaf (n := n) M).presheaf.germ O y.val hy t)) :=
      (quotientStalkEval_inclusion_germ C hC O t y hy).symm
    _ = quotientStalkEval C hC y (F.stalkMap y ((quotientInclusion A hA).stalkMap (F.base y)
        ((actualComplexStructureSheaf (n := m) N).presheaf.germ ⊤ (F.base y).val (by trivial) a))) :=
      congrArg (quotientStalkEval C hC y) (hstalk y hy).symm
    _ = quotientStalkEval A hA (F.base y) ((quotientInclusion A hA).stalkMap (F.base y)
        ((actualComplexStructureSheaf (n := m) N).presheaf.germ ⊤ (F.base y).val (by trivial) a)) :=
      quotientMap_eval_of_point_compatible C hC A hA F hF y _
    _ = _ := quotientStalkEval_inclusion_germ A hA ⊤ a (F.base y) (by trivial)

private theorem native_function {f : M → N}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
    (x : M) (g : N → ℂ) (hg : HolomorphicAt m g (f x)) :
    (ChartedSpace.locallyRingedSpaceMap f hf).stalkMap x (actualOriginalFunctionGerm (f x) g hg) =
      actualOriginalFunctionGerm x (g ∘ f)
        (hg.comp_contMDiff (Eventually.of_forall fun _ => hf.contMDiffAt)) := by
  apply (actualStalkChartEquiv (n := n) x).injective
  rw [actualNativeStalk_chart_pullback,actualOriginalFunctionGerm_chart,
    actualHolomorphicGermPullback_original_function,actualOriginalFunctionGerm_chart]

private theorem quotientMap_stalk_inclusion {f : M → N}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
    (C : GermIdeal n M) (hC : C.IsCoherent) (A : GermIdeal m N) (hA : A.IsCoherent)
    (hCA : GermIdeal.Le (GermIdeal.pullback (m := n) f A) C) (x : C.zeroLocus)
    (r : actualComplexStructureStalk (n := m) (f x.val)) :
    (quotientMap hf C hC A hA hCA).stalkMap x
      ((quotientInclusion A hA).stalkMap (quotientTopMap hf C A hA hCA x) r) =
    (quotientInclusion C hC).stalkMap x ((ChartedSpace.locallyRingedSpaceMap f hf).stalkMap x.val r) := by
  have hr : (quotientInclusion A hA).stalkMap (quotientTopMap hf C A hA hCA x) r =
      (quotientStalkChartEquiv A hA (quotientTopMap hf C A hA hCA x)).symm
        (Ideal.Quotient.mk _ (actualStalkChartEquiv (n := m) (f x.val) r)) := by
    apply (quotientStalkChartEquiv A hA (quotientTopMap hf C A hA hCA x)).injective
    rw [quotientChart_inclusion,RingEquiv.apply_symm_apply]
    rfl
  rw [hr]
  apply (quotientStalkChartEquiv C hC x).injective
  calc
    _ = Ideal.Quotient.mk _ (actualHolomorphicGermPullback hf x.val
        (actualStalkChartEquiv (n := m) (f x.val) r)) :=
      quotientMap_chart_mk hf C hC A hA hCA x (actualStalkChartEquiv (n := m) (f x.val) r)
    _ = _ := by rw [quotientChart_inclusion,actualNativeStalk_chart_pullback]

private theorem coordinate_function_holomorphic (V : Opens (ComplexModel m)) (i : Fin m) (p : V) :
    HolomorphicAt m (fun z : V => z.val i) p := by
  have h : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ℂ) ∞ (fun z : V => z.val i) :=
    (EuclideanSpace.proj (𝕜 := ℂ) i).contMDiff.comp contMDiff_subtype_val
  exact Eventually.of_forall fun _ => h.contMDiffAt.mdifferentiableAt (by simp)

private theorem coordinate_germ_eq_section (V : Opens (ComplexModel m)) (i : Fin m) (p : V) :
    actualOriginalFunctionGerm p (fun z : V => z.val i) (coordinate_function_holomorphic V i p) =
      (actualComplexStructureSheaf (n := m) V).presheaf.germ ⊤ p (by trivial) (coordinateSection V i) := by
  apply actualOriginalFunctionGerm_eq_section
  exact Eventually.of_forall fun z => sectionExtension_apply ⊤ (coordinateSection V i) z (by trivial)

private theorem coordinate_section_chart (V : Opens (ComplexModel m)) (p : V) (i : Fin m) :
    actualStalkChartEquiv (n := m) p
      ((actualComplexStructureSheaf (n := m) V).presheaf.germ ⊤ p (by trivial) (coordinateSection V i)) =
        coordinateGerm i + HolGerm.constHom (p.val i) := by
  rw [←coordinate_germ_eq_section,actualOriginalFunctionGerm_chart]
  have hc : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ℂ) ∞ (fun z : ComplexModel m => z i) :=
    (EuclideanSpace.proj (𝕜 := ℂ) i).contMDiff
  have hg : HolomorphicAt m (fun z : ComplexModel m => z i) p.val :=
    Eventually.of_forall fun _ => hc.contMDiffAt.mdifferentiableAt (by simp)
  have h := actualHolomorphicGermPullback_original_function
    (f := (Subtype.val : V → ComplexModel m)) contMDiff_subtype_val p (fun z => z i) hg
  rw [actualHolomorphicGermPullback_val] at h
  change chartTranslatedGerm p.val p.val (mem_chart_source _ _) (fun z : ComplexModel m => z i) hg =
    chartTranslatedGerm p p (mem_chart_source _ _) (fun z : V => z.val i) _ at h
  rw [←h]
  unfold chartTranslatedGerm translatedGerm coordinateGerm
  rw [HolGerm.constHom_apply,←HolGerm.mk_add]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun z => by simp [chartAt_self_eq]

/-- The finite original coordinate SECTION lifts produce one actual holomorphic map,
retaining every nearby native coordinate-germ identity. -/
private theorem exists_coordinate_lift (C : GermIdeal n M) (hC : C.IsCoherent)
    {V : Opens (ComplexModel m)} (A : GermIdeal m V) (hA : A.IsCoherent)
    (F : quotientLocallyRingedSpace C hC ⟶ quotientLocallyRingedSpace A hA)
    (hF : F ≫ quotientPointMap A hA = quotientPointMap C hC) (x : C.zeroLocus) :
    ∃ (O : Opens M) (_hxO : x.val ∈ O) (f : O → V)
      (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f),
      (∀ y : (quotientOpenIdeal C O).zeroLocus,
        (F.base ((quotientOpenMap C hC O).base y)).val = f y.val) ∧
      (∀ (y : (quotientOpenIdeal C O).zeroLocus) (i : Fin m),
        (quotientOpenMap C hC O ≫ F).stalkMap y
          ((quotientInclusion A hA).stalkMap ((quotientOpenMap C hC O ≫ F).base y)
            ((actualComplexStructureSheaf (n := m) V).presheaf.germ ⊤
              ((quotientOpenMap C hC O ≫ F).base y).val (by trivial) (coordinateSection V i))) =
        (quotientInclusion (quotientOpenIdeal C O) (quotientOpenIdeal_coherent C hC O)).stalkMap y
          ((ChartedSpace.locallyRingedSpaceMap f hf).stalkMap y.val
            ((actualComplexStructureSheaf (n := m) V).presheaf.germ ⊤ (f y.val) (by trivial) (coordinateSection V i)))) := by
  classical
  choose O hxO t ht using fun i : Fin m => local_scalar_lift C hC A hA F hF (coordinateSection V i) x
  let O₀ : Opens M := ⨅ i : Fin m, O i
  have hO₀ : ∀ i : Fin m, O₀ ≤ O i := fun i => iInf_le O i
  have hxO₀ : x.val ∈ O₀ := by
    change x.val ∈ (O₀ : Set M)
    simp only [O₀,Opens.coe_iInf,Set.mem_iInter]
    exact hxO
  let g : M → ComplexModel m := fun z =>
    (EuclideanSpace.equiv (Fin m) ℂ).symm (fun i => sectionExtension (O i) (t i) z)
  have hg : ∀ z ∈ O₀, ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ g z := by
    intro z hz
    have hpi : ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,Fin m → ℂ) ∞
        (fun w => fun i : Fin m => sectionExtension (O i) (t i) w) z :=
      contMDiffAt_pi_space.mpr fun i => sectionExtension_contMDiffAt (O i) (t i) z (hO₀ i hz)
    exact (EuclideanSpace.equiv (Fin m) ℂ).symm.toContinuousLinearMap.contMDiffAt.comp z hpi
  have hgC : ∀ y : C.zeroLocus, y.val ∈ O₀ → g y.val = (F.base y).val.val := by
    intro y hy
    ext i
    change sectionExtension (O i) (t i) y.val = (F.base y).val.val i
    rw [sectionExtension_apply (O i) (t i) y.val (hO₀ i hy)]
    exact (ht i).2 y (hO₀ i hy)
  have hxV : g x.val ∈ V := by rw [hgC x hxO₀]; exact (F.base x).val.property
  have hnb : g ⁻¹' (V : Set (ComplexModel m)) ∈ nhds x.val :=
    (hg x.val hxO₀).continuousAt.preimage_mem_nhds (V.isOpen.mem_nhds hxV)
  obtain ⟨T,hTsub,hT,hxT⟩ := mem_nhds_iff.mp hnb
  let O' : Opens M := O₀ ⊓ ⟨T,hT⟩
  let f : O' → V := fun y => ⟨g y.val,hTsub y.property.2⟩
  have hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f := by
    apply (ContMDiff.subtypeVal_comp_iff V f).mp
    intro y
    exact contMDiffAt_subtype_iff.mpr (hg y.val y.property.1)
  refine ⟨O',⟨hxO₀,hxT⟩,f,hf,?_,?_⟩
  · intro y
    exact Subtype.ext (hgC ((quotientOpenMap C hC O').base y) y.val.property.1).symm
  · intro y i
    let z := (quotientOpenMap C hC O').base y
    have hzi : z.val ∈ O i := hO₀ i y.val.property.1
    let r := (actualComplexStructureSheaf (n := n) M).presheaf.germ (O i) z.val hzi (t i)
    have hs := (ht i).1 z hzi
    have hcomp := ConcreteCategory.congr_hom
      (LocallyRingedSpace.stalkMap_comp (quotientOpenMap C hC O') F y)
      ((quotientInclusion A hA).stalkMap (F.base z)
        ((actualComplexStructureSheaf (n := m) V).presheaf.germ ⊤ (F.base z).val (by trivial) (coordinateSection V i)))
    have hri : actualOriginalFunctionGerm z.val (sectionExtension (O i) (t i))
        (sectionExtension_holomorphicAt (O i) (t i) z.val hzi) = r :=
      actualOriginalFunctionGerm_eq_section (O i) z.val hzi (t i) _ _ (Eventually.of_forall fun _ => rfl)
    have hfun : (sectionExtension (O i) (t i)) ∘ (Subtype.val : O' → M) =
        (fun v : V => v.val i) ∘ f := by
      funext v
      rfl
    calc
      _ = (quotientOpenMap C hC O').stalkMap y ((quotientInclusion C hC).stalkMap z r) :=
        hcomp.trans (congrArg ((quotientOpenMap C hC O').stalkMap y) hs)
      _ = (quotientInclusion (quotientOpenIdeal C O') (quotientOpenIdeal_coherent C hC O')).stalkMap y
          ((ChartedSpace.locallyRingedSpaceMap (Subtype.val : O' → M) contMDiff_subtype_val).stalkMap y.val r) :=
        quotientMap_stalk_inclusion contMDiff_subtype_val (quotientOpenIdeal C O')
          (quotientOpenIdeal_coherent C hC O') C hC (fun _ _ h => h) y r
      _ = _ := by
        apply congrArg ((quotientInclusion (quotientOpenIdeal C O') (quotientOpenIdeal_coherent C hC O')).stalkMap y)
        have h₁ := native_function (f := (Subtype.val : O' → M)) contMDiff_subtype_val y.val
          (sectionExtension (O i) (t i)) (sectionExtension_holomorphicAt (O i) (t i) z.val hzi)
        have h₂ := native_function hf y.val (fun v : V => v.val i)
          (coordinate_function_holomorphic V i (f y.val))
        have hfval : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (Subtype.val : O' → M) :=
          contMDiff_subtype_val
        have hhol₁ : HolomorphicAt n ((sectionExtension (O i) (t i)) ∘ (Subtype.val : O' → M)) y.val :=
          (sectionExtension_holomorphicAt (O i) (t i) z.val hzi).comp_contMDiff
            (f := (Subtype.val : O' → M)) (y := y.val)
            (Eventually.of_forall fun _ => hfval.contMDiffAt)
        have hhol₂ : HolomorphicAt n ((fun v : V => v.val i) ∘ f) y.val :=
          (coordinate_function_holomorphic V i (f y.val)).comp_contMDiff
            (Eventually.of_forall fun _ => hf.contMDiffAt)
        have h₃ : actualOriginalFunctionGerm (n := n) y.val ((sectionExtension (O i) (t i)) ∘ (Subtype.val : O' → M)) hhol₁ =
            actualOriginalFunctionGerm (n := n) y.val ((fun v : V => v.val i) ∘ f) hhol₂ := by
          apply (actualStalkChartEquiv (n := n) y.val).injective
          rw [actualOriginalFunctionGerm_chart,actualOriginalFunctionGerm_chart]
          exact chartTranslatedGerm_congr_original y.val _ _ _ _ (Eventually.of_forall fun v => congrFun hfun v)
        exact (congrArg ((ChartedSpace.locallyRingedSpaceMap (Subtype.val : O' → M)
          contMDiff_subtype_val).stalkMap y.val) hri.symm).trans
            (h₁.trans (h₃.trans ((h₂.symm).trans
              (congrArg ((ChartedSpace.locallyRingedSpaceMap f hf).stalkMap y.val)
                (coordinate_germ_eq_section V i (f y.val))))))

private theorem chartHom_on_coordinate_section (C : GermIdeal n M) (hC : C.IsCoherent)
    {V : Opens (ComplexModel m)} (A : GermIdeal m V) (hA : A.IsCoherent)
    (F : quotientLocallyRingedSpace C hC ⟶ quotientLocallyRingedSpace A hA)
    (hF : F ≫ quotientPointMap A hA = quotientPointMap C hC) (x : C.zeroLocus) (i : Fin m) :
    quotientChartStalkAlgHom C hC A hA F hF x
      (Ideal.Quotient.mk _ (coordinateGerm i + HolGerm.constHom ((F.base x).val.val i))) =
    quotientStalkChartEquiv C hC x (F.stalkMap x
      ((quotientInclusion A hA).stalkMap (F.base x)
        ((actualComplexStructureSheaf (n := m) V).presheaf.germ ⊤ (F.base x).val (by trivial) (coordinateSection V i)))) := by
  have hr : (quotientInclusion A hA).stalkMap (F.base x)
      ((actualComplexStructureSheaf (n := m) V).presheaf.germ ⊤ (F.base x).val (by trivial) (coordinateSection V i)) =
      (quotientStalkChartEquiv A hA (F.base x)).symm
        (Ideal.Quotient.mk _ (coordinateGerm i + HolGerm.constHom ((F.base x).val.val i))) := by
    apply (quotientStalkChartEquiv A hA (F.base x)).injective
    rw [quotientChart_inclusion,coordinate_section_chart,RingEquiv.apply_symm_apply]
  exact (congrArg (fun r => quotientStalkChartEquiv C hC x (F.stalkMap x r)) hr).symm

/-- At EVERY nearby point, coordinate SECTION identities force ALL analytic numerator identities.
All hypotheses here are constructed by the finite section lift above in the public producer. -/
private theorem all_germs_of_coordinate_sections (C : GermIdeal n M) (hC : C.IsCoherent)
    {V : Opens (ComplexModel m)} (A : GermIdeal m V) (hA : A.IsCoherent)
    (G : quotientLocallyRingedSpace C hC ⟶ quotientLocallyRingedSpace A hA)
    (hG : G ≫ quotientPointMap A hA = quotientPointMap C hC)
    {f : M → V} (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
    (hp : ∀ y : C.zeroLocus, (G.base y).val = f y.val)
    (hc : ∀ (y : C.zeroLocus) (i : Fin m),
      G.stalkMap y ((quotientInclusion A hA).stalkMap (G.base y)
        ((actualComplexStructureSheaf (n := m) V).presheaf.germ ⊤ (G.base y).val (by trivial) (coordinateSection V i))) =
      (quotientInclusion C hC).stalkMap y ((ChartedSpace.locallyRingedSpaceMap f hf).stalkMap y.val
        ((actualComplexStructureSheaf (n := m) V).presheaf.germ ⊤ (f y.val) (by trivial) (coordinateSection V i)))) :
    ∀ (y : C.zeroLocus) (r : HolGerm (ComplexModel m)),
      quotientChartStalkAlgHom C hC A hA G hG y (Ideal.Quotient.mk _ r) =
        Ideal.Quotient.mk (wholeChartStalkIdeal C y.val y.val (mem_chart_source _ _))
          (actualHolomorphicGermPullback hf y.val r) := by
  intro y
  let IC := wholeChartStalkIdeal C y.val y.val (mem_chart_source _ _)
  let IA := wholeChartStalkIdeal A (G.base y).val (G.base y).val (mem_chart_source _ _)
  let T := HolGerm (ComplexModel n) ⧸ IC
  let : IsNoetherianRing (HolGerm (ComplexModel n)) := isNoetherianRing_holGerm_euclidean n
  let : IsNoetherianRing T := inferInstance
  let : IsLocalRing T := chartQuotient_isLocalRing C y
  let : IsLocalRing (HolGerm (ComplexModel m) ⧸ IA) := chartQuotient_isLocalRing A (G.base y)
  let : IsLocalHom (Ideal.Quotient.mk IC) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  let : IsLocalHom (Ideal.Quotient.mk IA) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  let a : HolGerm (ComplexModel m) →ₐ[ℂ] T :=
    (quotientChartStalkAlgHom C hC A hA G hG y).comp (Ideal.Quotient.mkₐ ℂ IA)
  let b : HolGerm (ComplexModel m) →ₐ[ℂ] T :=
    (Ideal.Quotient.mkₐ ℂ IC).comp (actualHolomorphicGermPullback hf y.val)
  let : IsLocalHom a.toRingHom := by
    change IsLocalHom ((quotientChartStalkAlgHom C hC A hA G hG y).toRingHom.comp (Ideal.Quotient.mk IA))
    infer_instance
  let : IsLocalHom b.toRingHom := by
    change IsLocalHom ((Ideal.Quotient.mk IC).comp (actualHolomorphicGermPullback hf y.val).toRingHom)
    infer_instance
  have hcoords (i : Fin m) : a (coordinateGerm i) = b (coordinateGerm i) := by
    have h₁ := chartHom_on_coordinate_section C hC A hA G hG y i
    have h₂ := congrArg (quotientStalkChartEquiv C hC y) (hc y i)
    have h₃ : quotientStalkChartEquiv C hC y
        ((quotientInclusion C hC).stalkMap y ((ChartedSpace.locallyRingedSpaceMap f hf).stalkMap y.val
          ((actualComplexStructureSheaf (n := m) V).presheaf.germ ⊤ (f y.val) (by trivial) (coordinateSection V i)))) =
        b (coordinateGerm i + HolGerm.constHom ((f y.val).val i)) := by
      rw [quotientChart_inclusion,actualNativeStalk_chart_pullback,coordinate_section_chart]
      rfl
    have he : a (coordinateGerm i + HolGerm.constHom ((G.base y).val.val i)) =
        b (coordinateGerm i + HolGerm.constHom ((f y.val).val i)) := h₁.trans (h₂.trans h₃)
    have hv : (G.base y).val.val i = (f y.val).val i := congrArg (fun p : V => p.val i) (hp y)
    rw [hv] at he
    change a (coordinateGerm i + algebraMap ℂ _ ((f y.val).val i)) =
      b (coordinateGerm i + algebraMap ℂ _ ((f y.val).val i)) at he
    simpa only [map_add,AlgHom.commutes,add_right_cancel_iff] using he
  have heq : a = b := local_algHom_ext_coordinates m a b hcoords
  intro r
  exact congrArg (fun k : HolGerm (ComplexModel m) →ₐ[ℂ] T => k r) heq

/-- The all-germ equation forces the WHOLE original ideal inclusion at ALL ambient points,
including the off-support unit stalks. No whole-ideal inclusion is an input to the public producer. -/
private theorem whole_containment_of_all_germs (C : GermIdeal n M) (hC : C.IsCoherent)
    {V : Opens (ComplexModel m)} (A : GermIdeal m V) (hA : A.IsCoherent)
    (G : quotientLocallyRingedSpace C hC ⟶ quotientLocallyRingedSpace A hA)
    (hG : G ≫ quotientPointMap A hA = quotientPointMap C hC)
    {f : M → V} (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
    (hp : ∀ y : C.zeroLocus, (G.base y).val = f y.val)
    (hall : ∀ (y : C.zeroLocus) (r : HolGerm (ComplexModel m)),
      quotientChartStalkAlgHom C hC A hA G hG y (Ideal.Quotient.mk _ r) =
        Ideal.Quotient.mk (wholeChartStalkIdeal C y.val y.val (mem_chart_source _ _))
          (actualHolomorphicGermPullback hf y.val r)) :
    GermIdeal.Le (GermIdeal.pullback (m := n) f A) C := by
  have hPB : (GermIdeal.pullback (m := n) f A).IsCoherent := isCoherent_pullback hf hA
  have hle (y : M) :
      Ideal.map (actualHolomorphicGermPullback hf y).toRingHom
        (wholeChartStalkIdeal A (f y) (f y) (mem_chart_source _ _)) ≤
          wholeChartStalkIdeal C y y (mem_chart_source _ _) := by
    by_cases hy : y ∈ C.zeroLocus
    · let x : C.zeroLocus := ⟨y,hy⟩
      apply Ideal.map_le_iff_le_comap.mpr
      intro r hr
      change actualHolomorphicGermPullback hf y r ∈ wholeChartStalkIdeal C y y (mem_chart_source _ _)
      have hid : wholeChartStalkIdeal A (G.base x).val (G.base x).val (mem_chart_source _ _) =
          wholeChartStalkIdeal A (f y) (f y) (mem_chart_source _ _) :=
        congrArg (fun p : V => wholeChartStalkIdeal A p p (mem_chart_source _ p)) (hp x)
      have hr' : r ∈ wholeChartStalkIdeal A (G.base x).val (G.base x).val (mem_chart_source _ _) := hid.symm ▸ hr
      have hz : quotientChartStalkAlgHom C hC A hA G hG x (Ideal.Quotient.mk _ r) = 0 := by
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr',map_zero]
      exact Ideal.Quotient.eq_zero_iff_mem.mp ((hall x r).symm.trans hz)
    · rw [chartIdeal_eq_top_off_support C hC y hy]
      exact le_top
  intro y g hg
  have hhol := GermIdeal.IsCoherent.holomorphicAt_mem hPB hg
  apply (coherent_mem_iff_whole_chart C hC y g hhol).mpr
  have hm := (coherent_mem_iff_whole_chart (GermIdeal.pullback (m := n) f A) hPB y g hhol).mp hg
  rw [←map_wholeChartStalkIdeal_actual_pullback hf A hA y] at hm
  exact hle y hm

/-- An arbitrary genuine complex-compatible native nonreduced quotient morphism has a
holomorphic representative on one actual ambient neighborhood, with the WHOLE ideal condition
and the FULL native LRS morphism equality derived internally. -/
theorem exists_local_holomorphic_lift (C : GermIdeal n M) (hC : C.IsCoherent)
    {V : Opens (ComplexModel m)} (A : GermIdeal m V) (hA : A.IsCoherent)
    (F : quotientLocallyRingedSpace C hC ⟶ quotientLocallyRingedSpace A hA)
    (hF : F ≫ quotientPointMap A hA = quotientPointMap C hC) (x : C.zeroLocus) :
    ∃ (O : Opens M) (_hxO : x.val ∈ O) (f : O → V)
      (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
      (hCA : GermIdeal.Le (GermIdeal.pullback (m := n) f A) (quotientOpenIdeal C O)),
      quotientMap hf (quotientOpenIdeal C O) (quotientOpenIdeal_coherent C hC O) A hA hCA =
        quotientOpenMap C hC O ≫ F := by
  obtain ⟨O,hxO,f,hf,hp,hcoords⟩ := exists_coordinate_lift C hC A hA F hF x
  let D := quotientOpenIdeal C O
  have hD : D.IsCoherent := quotientOpenIdeal_coherent C hC O
  let G := quotientOpenMap C hC O ≫ F
  have hG : G ≫ quotientPointMap A hA = quotientPointMap D hD := by
    dsimp only [G]
    rw [Category.assoc,hF]
    exact quotientOpenMap_point C hC O
  have hall := all_germs_of_coordinate_sections D hD A hA G hG hf hp hcoords
  have hCA := whole_containment_of_all_germs D hD A hA G hG hf hp hall
  refine ⟨O,hxO,f,hf,hCA,?_⟩
  let Q := quotientMap hf D hD A hA hCA
  have hQ : Q ≫ quotientPointMap A hA = quotientPointMap D hD := quotientMap_point hf D hD A hA hCA
  have hbase : Q.base = G.base := by
    ext y
    exact Subtype.ext (hp y).symm
  apply quotientHom_ext_chart D hD A hA Q G hQ hG hbase
  intro y r
  have hq := quotientMap_chart_mk hf D hD A hA hCA y r
  exact hq.trans (hall y r).symm

end
end Hironaka.HironakaNonreducedQuotientNeighborhoodLifting
