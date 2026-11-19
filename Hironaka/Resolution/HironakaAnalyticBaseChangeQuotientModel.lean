import Hironaka.Resolution.HironakaNonreducedAnalyticQuotientMorphism
import Hironaka.Resolution.HironakaActualAnalyticBaseChangeCoefficients
import Hironaka.Resolution.HironakaActualIntrinsicStableAmbientIso
import Hironaka.Resolution.HironakaActualProjectionIntrinsicHS

/-! Actual open-domain analytic base-change candidate, retaining whole nonradical ideals.
No fibre-product universal property is claimed.
BP FIRST: hironaka-analytic-basechange-quotient-model.tex. -/
set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaAnalyticBaseChangeQuotientModel
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaHolomorphicJetChartInvariance HironakaHolomorphicJetRankLoci
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaSmoothCentreRealDomainActualIdealPresheaf
  HironakaActualWholeStalkHolomorphicPullback HironakaActualBiholomorphicWholeStalkHS
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceOpenRestriction
  HironakaSingularSubspaceBlowupCartier HironakaNonreducedAnalyticQuotientModel
  HironakaNonreducedAnalyticQuotientMorphism HironakaActualAnalyticBaseChangeCoefficients
  HironakaRelativeNormalIdeal HironakaActualCentreJointJets HironakaActualJointBaseFibre
  HironakaActualIntrinsicStableAmbientIso HironakaActualOpenIntrinsicHS
  HironakaActualProjectionIntrinsicHS RelativePrincipalizationSpan InvertibleIdealQuotient
  RestrictedIdealExtension GermIdealPullbackCalculus

section WholeSum
variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private theorem chart_sum_mul (x : M) {s : ℕ} (a g : Fin s → M → ℂ)
    (ha : ∀ i, HolomorphicAt n (a i) x) (hg : ∀ i, HolomorphicAt n (g i) x) :
    chartTranslatedGerm x x (mem_chart_source _ x) (fun y => ∑ i, a i y*g i y)
        (HolomorphicAt.sum Finset.univ fun i _ => (ha i).mul (hg i)) =
      ∑ i, chartTranslatedGerm x x (mem_chart_source _ x) (a i) (ha i) *
        chartTranslatedGerm x x (mem_chart_source _ x) (g i) (hg i) := by
  simp only [chartTranslatedGerm,translatedGerm]
  rw [HolGerm.mk_sum Finset.univ]
  · exact Finset.sum_congr rfl fun i _ => HolGerm.mk_mul _ _ _ _
  · intro i
    exact translated_holomorphic _ (CartanLocalReduction.holAt_comp_chart_symm
      (mem_chart_source _ x) ((ha i).mul (hg i)))

/-- The WHOLE original sum, with both inclusions and no radical replacement. -/
theorem wholeChartStalkIdeal_sum (A B : GermIdeal n M) (hA : A.IsCoherent) (hB : B.IsCoherent) (x : M) :
    wholeChartStalkIdeal (sumIdeal A B) x x (mem_chart_source _ x) =
      wholeChartStalkIdeal A x x (mem_chart_source _ x) ⊔
        wholeChartStalkIdeal B x x (mem_chart_source _ x) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨f,hf,hmem,rfl⟩
    obtain ⟨_,s,g,a,hg,ha,he⟩ := hmem
    have hgHol (i : Fin s) : HolomorphicAt n (g i) x :=
      (hg i).elim (GermIdeal.IsCoherent.holomorphicAt_mem hA)
        (GermIdeal.IsCoherent.holomorphicAt_mem hB)
    rw [chartTranslatedGerm_congr_original x f (fun y => ∑ i, a i y*g i y) hf
      (HolomorphicAt.sum Finset.univ fun i _ => (ha i).mul (hgHol i)) he,chart_sum_mul x a g ha hgHol]
    apply Ideal.sum_mem
    intro i _
    apply Ideal.mul_mem_left
    rcases hg i with hi | hi
    · exact Submodule.mem_sup_left (Ideal.subset_span ⟨g i,hgHol i,hi,rfl⟩)
    · exact Submodule.mem_sup_right (Ideal.subset_span ⟨g i,hgHol i,hi,rfl⟩)
  · apply sup_le
    · apply Ideal.span_le.mpr
      rintro _ ⟨f,hf,hmem,rfl⟩
      exact Ideal.subset_span ⟨f,hf,le_sumIdeal_left hA x f hmem,rfl⟩
    · apply Ideal.span_le.mpr
      rintro _ ⟨f,hf,hmem,rfl⟩
      exact Ideal.subset_span ⟨f,hf,le_sumIdeal_right hB x f hmem,rfl⟩

/-- The SAME identity in the literal original structure-sheaf stalk ring. -/
theorem actualWholeSheafStalkIdeal_sum (A B : GermIdeal n M)
    (hA : A.IsCoherent) (hB : B.IsCoherent) (x : M) :
    actualWholeSheafStalkIdeal (sumIdeal A B) x =
      actualWholeSheafStalkIdeal A x ⊔ actualWholeSheafStalkIdeal B x := by
  apply (actualStalkChartEquiv (n := n) x).idealComapOrderIso.symm.injective
  change Ideal.map (actualStalkChartEquiv (n := n) x).toRingHom _ =
    Ideal.map (actualStalkChartEquiv (n := n) x).toRingHom _
  rw [Ideal.map_sup,map_actualWholeSheafStalkIdeal,map_actualWholeSheafStalkIdeal,
    map_actualWholeSheafStalkIdeal,wholeChartStalkIdeal_sum A B hA hB]

end WholeSum

private theorem nativeMap_congr {a c : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (ComplexModel a) X] [ChartedSpace (ComplexModel c) Y]
    {f g : X → Y} {hf : ContMDiff 𝓘(ℂ,ComplexModel a) 𝓘(ℂ,ComplexModel c) ∞ f}
    {hg : ContMDiff 𝓘(ℂ,ComplexModel a) 𝓘(ℂ,ComplexModel c) ∞ g} (he : f = g) :
    ChartedSpace.locallyRingedSpaceMap f hf = ChartedSpace.locallyRingedSpaceMap g hg := by
  subst g
  rfl

variable (d b t : ℕ)

/-- A real open cylinder, without extending any ideal or holomorphic map globally. -/
def cylinder (V : Opens (ComplexModel b)) : Opens (ComplexModel (b+t)) :=
  ⟨(tangentProjection b t) ⁻¹' V,V.isOpen.preimage (tangentProjection b t).continuous⟩

def cylinderProjection (V : Opens (ComplexModel b)) : cylinder b t V → V :=
  fun w => ⟨tangentProjection b t w.val,w.property⟩

theorem cylinderProjection_holomorphic (V : Opens (ComplexModel b)) :
    ContMDiff 𝓘(ℂ,ComplexModel (b+t)) 𝓘(ℂ,ComplexModel b) ∞ (cylinderProjection b t V) := by
  apply (ContMDiff.subtypeVal_comp_iff V _).mp
  exact (tangentProjection b t).contDiff.contMDiff.comp contMDiff_subtype_val

def jointOnCylinder (V : Opens (ComplexModel b)) (φ : V → ComplexModel d)
    (w : cylinder b t V) : ComplexModel (d+t) :=
  join (φ (cylinderProjection b t V w)) (actualJointNormalProjection b t w.val)

theorem jointOnCylinder_holomorphic (V : Opens (ComplexModel b)) (φ : V → ComplexModel d)
    (hφ : ContMDiff 𝓘(ℂ,ComplexModel b) 𝓘(ℂ,ComplexModel d) ∞ φ) :
    ContMDiff 𝓘(ℂ,ComplexModel (b+t)) 𝓘(ℂ,ComplexModel (d+t)) ∞ (jointOnCylinder d b t V φ) :=
  ((tangentInclusion d t).contDiff.contMDiff.comp
    (hφ.comp (cylinderProjection_holomorphic b t V))).add
      ((actualJointNormalInclusion d t).contDiff.contMDiff.comp
        ((actualJointNormalProjection b t).contDiff.contMDiff.comp contMDiff_subtype_val))

/-- The genuine joint open is a true open of the real cylinder; its image in coordinate space is open. -/
def jointOpen (U : Opens (ComplexModel (d+t))) (V : Opens (ComplexModel b)) (φ : V → ComplexModel d)
    (hφ : ContMDiff 𝓘(ℂ,ComplexModel b) 𝓘(ℂ,ComplexModel d) ∞ φ) : Opens (cylinder b t V) :=
  ⟨(jointOnCylinder d b t V φ) ⁻¹' U,
    U.isOpen.preimage (jointOnCylinder_holomorphic d b t V φ hφ).continuous⟩

theorem jointOpen_image_open (U : Opens (ComplexModel (d+t))) (V : Opens (ComplexModel b))
    (φ : V → ComplexModel d) (hφ : ContMDiff 𝓘(ℂ,ComplexModel b) 𝓘(ℂ,ComplexModel d) ∞ φ) :
    IsOpen ((Subtype.val : cylinder b t V → ComplexModel (b+t)) '' (jointOpen d b t U V φ hφ)) :=
  (cylinder b t V).isOpen.isOpenMap_subtype_val _ (jointOpen d b t U V φ hφ).isOpen

def sourceProjection (U : Opens (ComplexModel (d+t))) (V : Opens (ComplexModel b)) (φ : V → ComplexModel d)
    (hφ : ContMDiff 𝓘(ℂ,ComplexModel b) 𝓘(ℂ,ComplexModel d) ∞ φ) : jointOpen d b t U V φ hφ → U :=
  fun w => ⟨jointOnCylinder d b t V φ w.val,w.property⟩

def baseProjection (U : Opens (ComplexModel (d+t))) (V : Opens (ComplexModel b)) (φ : V → ComplexModel d)
    (hφ : ContMDiff 𝓘(ℂ,ComplexModel b) 𝓘(ℂ,ComplexModel d) ∞ φ) : jointOpen d b t U V φ hφ → V :=
  fun w => cylinderProjection b t V w.val

theorem sourceProjection_holomorphic (U : Opens (ComplexModel (d+t))) (V : Opens (ComplexModel b))
    (φ : V → ComplexModel d) (hφ : ContMDiff 𝓘(ℂ,ComplexModel b) 𝓘(ℂ,ComplexModel d) ∞ φ) :
    ContMDiff 𝓘(ℂ,ComplexModel (b+t)) 𝓘(ℂ,ComplexModel (d+t)) ∞ (sourceProjection d b t U V φ hφ) := by
  apply (ContMDiff.subtypeVal_comp_iff U _).mp
  exact (jointOnCylinder_holomorphic d b t V φ hφ).comp contMDiff_subtype_val

theorem baseProjection_holomorphic (U : Opens (ComplexModel (d+t))) (V : Opens (ComplexModel b))
    (φ : V → ComplexModel d) (hφ : ContMDiff 𝓘(ℂ,ComplexModel b) 𝓘(ℂ,ComplexModel d) ∞ φ) :
    ContMDiff 𝓘(ℂ,ComplexModel (b+t)) 𝓘(ℂ,ComplexModel b) ∞ (baseProjection d b t U V φ hφ) :=
  (cylinderProjection_holomorphic b t V).comp contMDiff_subtype_val

theorem projection_point_square (U : Opens (ComplexModel (d+t))) (V : Opens (ComplexModel b))
    (φ : V → ComplexModel d) (hφ : ContMDiff 𝓘(ℂ,ComplexModel b) 𝓘(ℂ,ComplexModel d) ∞ φ)
    (w : jointOpen d b t U V φ hφ) :
    tangentProjection d t (sourceProjection d b t U V φ hφ w).val =
      φ (baseProjection d b t U V φ hφ w) := first_join _ _

def jointIdeal {U : Opens (ComplexModel (d+t))} {V : Opens (ComplexModel b)}
    (φ : V → ComplexModel d) (hφ : ContMDiff 𝓘(ℂ,ComplexModel b) 𝓘(ℂ,ComplexModel d) ∞ φ)
    (A : GermIdeal (d+t) U) (q : GermIdeal b V) : GermIdeal (b+t) (jointOpen d b t U V φ hφ) :=
  sumIdeal (GermIdeal.pullback (sourceProjection d b t U V φ hφ) A)
    (GermIdeal.pullback (baseProjection d b t U V φ hφ) q)

theorem jointIdeal_coherent {U : Opens (ComplexModel (d+t))} {V : Opens (ComplexModel b)}
    (φ : V → ComplexModel d) (hφ : ContMDiff 𝓘(ℂ,ComplexModel b) 𝓘(ℂ,ComplexModel d) ∞ φ)
    (A : GermIdeal (d+t) U) (hA : A.IsCoherent) (q : GermIdeal b V) (hq : q.IsCoherent) :
    (jointIdeal d b t φ hφ A q).IsCoherent :=
  isCoherent_sumIdeal (isCoherent_pullback (sourceProjection_holomorphic d b t U V φ hφ) hA)
    (isCoherent_pullback (baseProjection_holomorphic d b t U V φ hφ) hq)

private theorem zeroLocus_pullback {a c : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (ComplexModel a) X] [IsComplexManifold a X]
    [ChartedSpace (ComplexModel c) Y] [IsComplexManifold c Y]
    {f : X → Y} (hf : ContMDiff 𝓘(ℂ,ComplexModel a) 𝓘(ℂ,ComplexModel c) ∞ f)
    (A : GermIdeal c Y) (hA : A.IsCoherent) :
    (GermIdeal.pullback (m := a) f A).zeroLocus = f ⁻¹' A.zeroLocus := by
  ext x
  constructor
  · intro hx g hg
    exact hx (g ∘ f) (GermIdeal.mem_pullback_iff.mpr (isInSpanAt_self ⟨g,hg,rfl⟩
      ((GermIdeal.IsCoherent.holomorphicAt_mem hA hg).comp_contMDiff
        (Eventually.of_forall fun _ => hf.contMDiffAt))))
  · intro hx g hg
    obtain ⟨_,s,g,a,hg,_,he⟩ := hg
    rw [he.self_of_nhds]
    apply Finset.sum_eq_zero
    intro i _
    obtain ⟨v,hv,heq⟩ := hg i
    rw [heq,Function.comp_apply,hx v hv,mul_zero]

private theorem zeroLocus_sum {a : ℕ} {X : Type} [TopologicalSpace X]
    [ChartedSpace (ComplexModel a) X] (A B : GermIdeal a X)
    (hA : A.IsCoherent) (hB : B.IsCoherent) :
    (sumIdeal A B).zeroLocus = A.zeroLocus ∩ B.zeroLocus := by
  ext x
  constructor
  · intro hx
    exact ⟨fun g hg => hx g (le_sumIdeal_left hA x g hg),
      fun g hg => hx g (le_sumIdeal_right hB x g hg)⟩
  · rintro ⟨hxA,hxB⟩ g hg
    obtain ⟨_,s,g,a,hg,_,he⟩ := hg
    rw [he.self_of_nhds]
    apply Finset.sum_eq_zero
    intro i _
    rcases hg i with hi | hi
    · rw [hxA _ hi,mul_zero]
    · rw [hxB _ hi,mul_zero]

theorem joint_support_iff {U : Opens (ComplexModel (d+t))} {V : Opens (ComplexModel b)}
    (φ : V → ComplexModel d) (hφ : ContMDiff 𝓘(ℂ,ComplexModel b) 𝓘(ℂ,ComplexModel d) ∞ φ)
    (A : GermIdeal (d+t) U) (hA : A.IsCoherent) (q : GermIdeal b V) (hq : q.IsCoherent)
    (w : jointOpen d b t U V φ hφ) :
    w ∈ (jointIdeal d b t φ hφ A q).zeroLocus ↔
      sourceProjection d b t U V φ hφ w ∈ A.zeroLocus ∧
        baseProjection d b t U V φ hφ w ∈ q.zeroLocus := by
  change w ∈ (sumIdeal _ _).zeroLocus ↔ _
  rw [zeroLocus_sum _ _ (isCoherent_pullback (sourceProjection_holomorphic d b t U V φ hφ) hA)
    (isCoherent_pullback (baseProjection_holomorphic d b t U V φ hφ) hq),
    zeroLocus_pullback (sourceProjection_holomorphic d b t U V φ hφ) A hA,
    zeroLocus_pullback (baseProjection_holomorphic d b t U V φ hφ) q hq]
  rfl

private def pairPoint {U : Opens (ComplexModel (d+t))} {V : Opens (ComplexModel b)}
    (φ : V → ComplexModel d) (hφ : ContMDiff 𝓘(ℂ,ComplexModel b) 𝓘(ℂ,ComplexModel d) ∞ φ)
    (x : U) (v : V) (h : tangentProjection d t x.val = φ v) : jointOpen d b t U V φ hφ :=
  ⟨⟨join v.val (actualJointNormalProjection d t x.val),by
      change tangentProjection b t (join v.val (actualJointNormalProjection d t x.val)) ∈ V
      simpa only [first_join] using v.property⟩,by
    change join (φ ⟨tangentProjection b t (join v.val (actualJointNormalProjection d t x.val)),_⟩)
      (actualJointNormalProjection b t (join v.val (actualJointNormalProjection d t x.val))) ∈ U
    have hv : (⟨tangentProjection b t (join v.val (actualJointNormalProjection d t x.val)),
        by simpa only [first_join] using v.property⟩ : V) = v :=
      Subtype.ext (first_join _ _)
    rw [hv,second_join,←h,join_projections]
    exact x.property⟩

private theorem pairPoint_source {U : Opens (ComplexModel (d+t))} {V : Opens (ComplexModel b)}
    (φ : V → ComplexModel d) (hφ : ContMDiff 𝓘(ℂ,ComplexModel b) 𝓘(ℂ,ComplexModel d) ∞ φ)
    (x : U) (v : V) (h : tangentProjection d t x.val = φ v) :
    sourceProjection d b t U V φ hφ (pairPoint d b t φ hφ x v h) = x := by
  apply Subtype.ext
  change join (φ ⟨tangentProjection b t (join v.val (actualJointNormalProjection d t x.val)),_⟩)
      (actualJointNormalProjection b t (join v.val (actualJointNormalProjection d t x.val))) = x.val
  have hv : (⟨tangentProjection b t (join v.val (actualJointNormalProjection d t x.val)),
      by simpa only [first_join] using v.property⟩ : V) = v :=
    Subtype.ext (first_join _ _)
  rw [hv,second_join,←h,join_projections]

private theorem pairPoint_base {U : Opens (ComplexModel (d+t))} {V : Opens (ComplexModel b)}
    (φ : V → ComplexModel d) (hφ : ContMDiff 𝓘(ℂ,ComplexModel b) 𝓘(ℂ,ComplexModel d) ∞ φ)
    (x : U) (v : V) (h : tangentProjection d t x.val = φ v) :
    baseProjection d b t U V φ hφ (pairPoint d b t φ hφ x v h) = v :=
  Subtype.ext (first_join _ _)

/-- Actual paired support, with the original source and target points and the actual base equation. -/
abbrev supportPairs {U : Opens (ComplexModel (d+t))} {V : Opens (ComplexModel b)}
    (φ : V → ComplexModel d) (A : GermIdeal (d+t) U) (q : GermIdeal b V) :=
  {p : A.zeroLocus × q.zeroLocus // tangentProjection d t p.1.val.val = φ p.2.val}

/-- Whole support homeomorphism, including empty/unit cases and the literal original coordinate inverse. -/
def supportPairHomeomorph {U : Opens (ComplexModel (d+t))} {V : Opens (ComplexModel b)}
    (φ : V → ComplexModel d) (hφ : ContMDiff 𝓘(ℂ,ComplexModel b) 𝓘(ℂ,ComplexModel d) ∞ φ)
    (A : GermIdeal (d+t) U) (hA : A.IsCoherent) (q : GermIdeal b V) (hq : q.IsCoherent) :
    (jointIdeal d b t φ hφ A q).zeroLocus ≃ₜ supportPairs d b t φ A q where
  toFun w := ⟨(⟨sourceProjection d b t U V φ hφ w.val,
      ((joint_support_iff d b t φ hφ A hA q hq w.val).mp w.property).1⟩,
    ⟨baseProjection d b t U V φ hφ w.val,
      ((joint_support_iff d b t φ hφ A hA q hq w.val).mp w.property).2⟩),
    projection_point_square d b t U V φ hφ w.val⟩
  invFun p := ⟨pairPoint d b t φ hφ p.val.1.val p.val.2.val p.property,
    (joint_support_iff d b t φ hφ A hA q hq _).mpr (by
      rw [pairPoint_source,pairPoint_base]
      exact ⟨p.val.1.property,p.val.2.property⟩)⟩
  left_inv w := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    change join (tangentProjection b t w.val.val.val)
      (actualJointNormalProjection d t (join _ (actualJointNormalProjection b t w.val.val.val))) = w.val.val.val
    rw [second_join,join_projections]
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact pairPoint_source d b t φ hφ p.val.1.val p.val.2.val p.property
    · apply Subtype.ext
      exact pairPoint_base d b t φ hφ p.val.1.val p.val.2.val p.property
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · exact ((sourceProjection_holomorphic d b t U V φ hφ).continuous.comp continuous_subtype_val).subtype_mk _
    · exact ((baseProjection_holomorphic d b t U V φ hφ).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    change Continuous (fun p : supportPairs d b t φ A q =>
      tangentInclusion b t p.val.2.val.val + actualJointNormalInclusion b t
        (actualJointNormalProjection d t p.val.1.val.val))
    fun_prop

def sourceQuotientProjection {U : Opens (ComplexModel (d+t))} {V : Opens (ComplexModel b)}
    (φ : V → ComplexModel d) (hφ : ContMDiff 𝓘(ℂ,ComplexModel b) 𝓘(ℂ,ComplexModel d) ∞ φ)
    (A : GermIdeal (d+t) U) (hA : A.IsCoherent) (q : GermIdeal b V) (hq : q.IsCoherent) :
    quotientLocallyRingedSpace (jointIdeal d b t φ hφ A q) (jointIdeal_coherent d b t φ hφ A hA q hq) ⟶
      quotientLocallyRingedSpace A hA :=
  quotientMap (sourceProjection_holomorphic d b t U V φ hφ) _ (jointIdeal_coherent d b t φ hφ A hA q hq)
    A hA (le_sumIdeal_left (isCoherent_pullback (sourceProjection_holomorphic d b t U V φ hφ) hA))

def baseQuotientProjection {U : Opens (ComplexModel (d+t))} {V : Opens (ComplexModel b)}
    (φ : V → ComplexModel d) (hφ : ContMDiff 𝓘(ℂ,ComplexModel b) 𝓘(ℂ,ComplexModel d) ∞ φ)
    (A : GermIdeal (d+t) U) (hA : A.IsCoherent) (q : GermIdeal b V) (hq : q.IsCoherent) :
    quotientLocallyRingedSpace (jointIdeal d b t φ hφ A q) (jointIdeal_coherent d b t φ hφ A hA q hq) ⟶
      quotientLocallyRingedSpace q hq :=
  quotientMap (baseProjection_holomorphic d b t U V φ hφ) _ (jointIdeal_coherent d b t φ hφ A hA q hq)
    q hq (le_sumIdeal_right (isCoherent_pullback (baseProjection_holomorphic d b t U V φ hφ) hq))

theorem projection_square {U : Opens (ComplexModel (d+t))} {V : Opens (ComplexModel b)}
    (φ : V → ComplexModel d) (hφ : ContMDiff 𝓘(ℂ,ComplexModel b) 𝓘(ℂ,ComplexModel d) ∞ φ)
    (A : GermIdeal (d+t) U) (hA : A.IsCoherent) (q : GermIdeal b V) (hq : q.IsCoherent) :
    sourceQuotientProjection d b t φ hφ A hA q hq ≫ quotientInclusion A hA ≫
      ChartedSpace.locallyRingedSpaceMap (fun x : U => tangentProjection d t x.val)
        ((tangentProjection d t).contDiff.contMDiff.comp contMDiff_subtype_val) =
    baseQuotientProjection d b t φ hφ A hA q hq ≫ quotientInclusion q hq ≫
      ChartedSpace.locallyRingedSpaceMap φ hφ := by
  let J := jointIdeal d b t φ hφ A q
  let hJ := jointIdeal_coherent d b t φ hφ A hA q hq
  have hs := quotientMap_inclusion (sourceProjection_holomorphic d b t U V φ hφ) J hJ A hA
    (le_sumIdeal_left (isCoherent_pullback (sourceProjection_holomorphic d b t U V φ hφ) hA))
  have hb := quotientMap_inclusion (baseProjection_holomorphic d b t U V φ hφ) J hJ q hq
    (le_sumIdeal_right (isCoherent_pullback (baseProjection_holomorphic d b t U V φ hφ) hq))
  change _ = sourceQuotientProjection d b t φ hφ A hA q hq ≫ quotientInclusion A hA at hs
  change _ = baseQuotientProjection d b t φ hφ A hA q hq ≫ quotientInclusion q hq at hb
  rw [←Category.assoc,←hs,Category.assoc,←ChartedSpace.locallyRingedSpace_comp,
    ←Category.assoc,←hb,Category.assoc,←ChartedSpace.locallyRingedSpace_comp]
  congr 1
  have hp : (fun x : U => tangentProjection d t x.val) ∘ sourceProjection d b t U V φ hφ =
      φ ∘ baseProjection d b t U V φ hφ := funext (projection_point_square d b t U V φ hφ)
  exact nativeMap_congr (a := b+t) (c := d) hp

section GermMaps
variable {U : Opens (ComplexModel (d+t))} {V : Opens (ComplexModel b)}
  (φ : V → ComplexModel d) (hφ : ContMDiff 𝓘(ℂ,ComplexModel b) 𝓘(ℂ,ComplexModel d) ∞ φ)

private def coordinateInclusion : jointOpen d b t U V φ hφ → ComplexModel (b+t) :=
  fun w => w.val.val

private theorem coordinateInclusion_holomorphic :
    ContMDiff 𝓘(ℂ,ComplexModel (b+t)) 𝓘(ℂ,ComplexModel (b+t)) ∞
      (coordinateInclusion d b t φ hφ (U := U)) :=
  contMDiff_subtype_val.comp contMDiff_subtype_val

private theorem coordinateTranslated_eventually (w : jointOpen d b t U V φ hφ) :
    actualTranslatedMap (coordinateInclusion d b t φ hφ) w =ᶠ[𝓝 (0 : ComplexModel (b+t))] id := by
  have hc := actualTranslatedMap_comp_eventually (n := b+t) (m := b+t) (k := b+t)
    (Subtype.val : cylinder b t V → ComplexModel (b+t))
    (g := (Subtype.val : jointOpen d b t U V φ hφ → cylinder b t V)) contMDiff_subtype_val w
  filter_upwards [hc,actualTranslatedMap_val_eventually (n := b+t) (cylinder b t V) w.val,
    actualTranslatedMap_val_eventually (n := b+t) (jointOpen d b t U V φ hφ) w] with z hz hcyl hopen
  change actualTranslatedMap (n := b+t) (m := b+t)
    ((Subtype.val : cylinder b t V → ComplexModel (b+t)) ∘
      (Subtype.val : jointOpen d b t U V φ hφ → cylinder b t V)) w z = z
  simpa only [Function.comp_apply,hopen,id_eq,hcyl] using hz

private theorem baseTranslated_eq (w : jointOpen d b t U V φ hφ) (z : ComplexModel (b+t)) :
    actualTranslatedMap (baseProjection d b t U V φ hφ) w z =
      tangentProjection b t (actualTranslatedMap (coordinateInclusion d b t φ hφ) w z) := by
  change tangentProjection b t
      (((chartAt (ComplexModel (b+t)) w).symm (z+(chartAt (ComplexModel (b+t)) w) w)).val.val) -
        tangentProjection b t w.val.val =
    tangentProjection b t
      ((((chartAt (ComplexModel (b+t)) w).symm (z+(chartAt (ComplexModel (b+t)) w) w)).val.val)-w.val.val)
  rw [map_sub]

private theorem jointTranslated_eq (w : jointOpen d b t U V φ hφ) (z : ComplexModel (b+t)) :
    actualTranslatedMap (n := d+t) (m := b+t) (sourceProjection d b t U V φ hφ) w z =
      join (actualTranslatedMap (n := d) (m := b+t) (φ ∘ baseProjection d b t U V φ hφ) w z)
        (actualJointNormalProjection b t (actualTranslatedMap (coordinateInclusion d b t φ hφ) w z)) := by
  change join (φ (baseProjection d b t U V φ hφ
      ((chartAt (ComplexModel (b+t)) w).symm (z+(chartAt (ComplexModel (b+t)) w) w))))
        (actualJointNormalProjection b t
          (((chartAt (ComplexModel (b+t)) w).symm (z+(chartAt (ComplexModel (b+t)) w) w)).val.val)) -
      join (φ (baseProjection d b t U V φ hφ w)) (actualJointNormalProjection b t w.val.val) =
    join (φ (baseProjection d b t U V φ hφ
        ((chartAt (ComplexModel (b+t)) w).symm (z+(chartAt (ComplexModel (b+t)) w) w))) -
      φ (baseProjection d b t U V φ hφ w))
      (actualJointNormalProjection b t
        ((((chartAt (ComplexModel (b+t)) w).symm (z+(chartAt (ComplexModel (b+t)) w) w)).val.val)-w.val.val))
  simp only [HironakaActualIntrinsicStableAmbientIso.join,map_sub]
  abel

/-- The real-open base projection has EXACTLY the original first-block germ map at every point. -/
theorem baseProjection_germ (w : jointOpen d b t U V φ hφ) :
    actualHolomorphicGermPullback (baseProjection_holomorphic d b t U V φ hφ) w = tangentPullback b t := by
  have he : actualTranslatedMap (baseProjection d b t U V φ hφ) w =ᶠ[𝓝 (0 : ComplexModel (b+t))]
      tangentProjection b t := (coordinateTranslated_eventually d b t φ hφ w).mono fun z hz => by
    rw [baseTranslated_eq,hz]
    rfl
  apply AlgHom.ext
  intro g
  induction g using HolGerm.induction_on with
  | h f hf =>
    unfold actualHolomorphicGermPullback tangentPullback
    rw [compAlgHom_mk,compAlgHom_mk]
    exact HolGerm.mk_eq_mk_iff.mpr (he.mono fun z hz => congrArg f hz)

/-- Exact joint substitution using the actual LOCAL chart representative of phi, never an entire extension. -/
theorem sourceProjection_germ (w : jointOpen d b t U V φ hφ) :
    actualHolomorphicGermPullback (sourceProjection_holomorphic d b t U V φ hφ) w =
      jointBasePullback d b t (actualTranslatedMap φ (baseProjection d b t U V φ hφ w))
        (actualTranslatedMap_holomorphic hφ _) (actualTranslatedMap_zero φ _) := by
  have hc := actualTranslatedMap_comp_eventually (n := d) (m := b) (k := b+t)
    φ (baseProjection_holomorphic d b t U V φ hφ) w
  have he : actualTranslatedMap (sourceProjection d b t U V φ hφ) w =ᶠ[𝓝 (0 : ComplexModel (b+t))]
      jointBaseMap d b t (actualTranslatedMap φ (baseProjection d b t U V φ hφ w)) := by
    filter_upwards [hc,coordinateTranslated_eventually d b t φ hφ w] with z hc hz
    rw [jointTranslated_eq,hc,Function.comp_apply,baseTranslated_eq,hz]
    rfl
  apply AlgHom.ext
  intro g
  induction g using HolGerm.induction_on with
  | h f hf =>
    unfold actualHolomorphicGermPullback jointBasePullback
    rw [compAlgHom_mk,compAlgHom_mk]
    exact HolGerm.mk_eq_mk_iff.mpr (he.mono fun z hz => congrArg f hz)

end GermMaps

section WholeJointStalk
variable {U : Opens (ComplexModel (d+t))} {V : Opens (ComplexModel b)}
  (φ : V → ComplexModel d) (hφ : ContMDiff 𝓘(ℂ,ComplexModel b) 𝓘(ℂ,ComplexModel d) ∞ φ)
  (A : GermIdeal (d+t) U) (hA : A.IsCoherent) (q : GermIdeal b V) (hq : q.IsCoherent)

/-- Whole analytic ideal at EVERY original point, with the actual local phi representative. -/
def jointChartIdeal (w : jointOpen d b t U V φ hφ) : Ideal (HolGerm (ComplexModel (b+t))) :=
  Ideal.map (jointBasePullback d b t (actualTranslatedMap (n := d) (m := b) φ
      (baseProjection d b t U V φ hφ w)) (actualTranslatedMap_holomorphic hφ _) (actualTranslatedMap_zero φ _)).toRingHom
    (wholeChartStalkIdeal A (sourceProjection d b t U V φ hφ w)
      (sourceProjection d b t U V φ hφ w) (mem_chart_source _ _)) ⊔
  Ideal.map (tangentPullback b t).toRingHom
    (wholeChartStalkIdeal q (baseProjection d b t U V φ hφ w)
      (baseProjection d b t U V φ hφ w) (mem_chart_source _ _))

include hA hq in
theorem whole_joint_chart (w : jointOpen d b t U V φ hφ) :
    wholeChartStalkIdeal (jointIdeal d b t φ hφ A q) w w (mem_chart_source _ w) =
      jointChartIdeal d b t φ hφ A q w := by
  unfold jointIdeal jointChartIdeal
  rw [wholeChartStalkIdeal_sum _ _
    (isCoherent_pullback (sourceProjection_holomorphic d b t U V φ hφ) hA)
    (isCoherent_pullback (baseProjection_holomorphic d b t U V φ hφ) hq),
    ←map_wholeChartStalkIdeal_actual_pullback (sourceProjection_holomorphic d b t U V φ hφ) A hA w,
    ←map_wholeChartStalkIdeal_actual_pullback (baseProjection_holomorphic d b t U V φ hφ) q hq w,
    sourceProjection_germ,baseProjection_germ]

private def jointStalkEquiv (x : (jointIdeal d b t φ hφ A q).zeroLocus) :
    ((quotientLocallyRingedSpace (jointIdeal d b t φ hφ A q)
      (jointIdeal_coherent d b t φ hφ A hA q hq)).presheaf.stalk x).carrier ≃+*
        (HolGerm (ComplexModel (b+t)) ⧸ jointChartIdeal d b t φ hφ A q x.val) :=
  (quotientStalkChartEquiv _ (jointIdeal_coherent d b t φ hφ A hA q hq) x).trans
    (Ideal.quotEquivOfEq (whole_joint_chart d b t φ hφ A hA q hq x.val))

private theorem jointStalkEquiv_inclusion (x : (jointIdeal d b t φ hφ A q).zeroLocus)
    (r : actualComplexStructureStalk (n := b+t) x.val) :
    jointStalkEquiv d b t φ hφ A hA q hq x
      ((quotientInclusion _ (jointIdeal_coherent d b t φ hφ A hA q hq)).stalkMap x r) =
        Ideal.Quotient.mk (jointChartIdeal d b t φ hφ A q x.val) (actualStalkChartEquiv (n := b+t) x.val r) := by
  let c := Ideal.quotientEquiv (actualWholeSheafStalkIdeal (jointIdeal d b t φ hφ A q) x.val)
    (wholeChartStalkIdeal (jointIdeal d b t φ hφ A q) x.val x.val (mem_chart_source _ _))
    (actualStalkChartEquiv (n := b+t) x.val)
    (map_actualWholeSheafStalkIdeal (jointIdeal d b t φ hφ A q) x.val).symm
  let e := Ideal.quotEquivOfEq (whole_joint_chart d b t φ hφ A hA q hq x.val)
  exact congrArg (fun z => e (c z))
    (quotientInclusion_stalk (jointIdeal d b t φ hφ A q)
      (jointIdeal_coherent d b t φ hφ A hA q hq) x r)

end WholeJointStalk
section QuotientChartRepresentatives
private theorem quotientChart_inclusion {a : ℕ} {X : Type} [TopologicalSpace X]
    [ChartedSpace (ComplexModel a) X] [IsComplexManifold a X]
    (A : GermIdeal a X) (hA : A.IsCoherent) (x : A.zeroLocus)
    (r : actualComplexStructureStalk (n := a) x.val) :
    quotientStalkChartEquiv A hA x ((quotientInclusion A hA).stalkMap x r) =
      Ideal.Quotient.mk (wholeChartStalkIdeal A x.val x.val (mem_chart_source _ x.val))
        (actualStalkChartEquiv (n := a) x.val r) := by
  simp only [quotientStalkChartEquiv,RingEquiv.trans_apply,quotientInclusion_stalk]
  rfl

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
end QuotientChartRepresentatives

section ProjectionRepresentatives
variable {U : Opens (ComplexModel (d+t))} {V : Opens (ComplexModel b)}
  (φ : V → ComplexModel d) (hφ : ContMDiff 𝓘(ℂ,ComplexModel b) 𝓘(ℂ,ComplexModel d) ∞ φ)
  (A : GermIdeal (d+t) U) (hA : A.IsCoherent) (q : GermIdeal b V) (hq : q.IsCoherent)

/-- EVERY base quotient numerator, in the actual independent whole chart-stalk equivalences. -/
theorem baseQuotientProjection_chart_mk (x : (jointIdeal d b t φ hφ A q).zeroLocus)
    (r : HolGerm (ComplexModel b)) :
    quotientStalkChartEquiv _ (jointIdeal_coherent d b t φ hφ A hA q hq) x
      ((baseQuotientProjection d b t φ hφ A hA q hq).stalkMap x
        ((quotientStalkChartEquiv q hq ((baseQuotientProjection d b t φ hφ A hA q hq).base x)).symm
          (Ideal.Quotient.mk (wholeChartStalkIdeal q
            ((baseQuotientProjection d b t φ hφ A hA q hq).base x).val
            ((baseQuotientProjection d b t φ hφ A hA q hq).base x).val (mem_chart_source _ _)) r))) =
      Ideal.Quotient.mk (wholeChartStalkIdeal (jointIdeal d b t φ hφ A q) x.val x.val (mem_chart_source _ _))
        (tangentPullback b t r) := by
  have h := quotientMap_chart_mk (baseProjection_holomorphic d b t U V φ hφ)
    (jointIdeal d b t φ hφ A q) (jointIdeal_coherent d b t φ hφ A hA q hq) q hq
    (le_sumIdeal_right (isCoherent_pullback (baseProjection_holomorphic d b t U V φ hφ) hq)) x r
  have hr := congrArg (fun e : HolGerm (ComplexModel b) →ₐ[ℂ] HolGerm (ComplexModel (b+t)) => e r)
    (baseProjection_germ d b t φ hφ x.val)
  exact h.trans (congrArg (Ideal.Quotient.mk
    (wholeChartStalkIdeal (jointIdeal d b t φ hφ A q) x.val x.val (mem_chart_source _ _))) hr)

/-- EVERY source quotient numerator retains the actual LOCAL joint phi pullback. -/
theorem sourceQuotientProjection_chart_mk (x : (jointIdeal d b t φ hφ A q).zeroLocus)
    (r : HolGerm (ComplexModel (d+t))) :
    quotientStalkChartEquiv _ (jointIdeal_coherent d b t φ hφ A hA q hq) x
      ((sourceQuotientProjection d b t φ hφ A hA q hq).stalkMap x
        ((quotientStalkChartEquiv A hA ((sourceQuotientProjection d b t φ hφ A hA q hq).base x)).symm
          (Ideal.Quotient.mk (wholeChartStalkIdeal A
            ((sourceQuotientProjection d b t φ hφ A hA q hq).base x).val
            ((sourceQuotientProjection d b t φ hφ A hA q hq).base x).val (mem_chart_source _ _)) r))) =
      Ideal.Quotient.mk (wholeChartStalkIdeal (jointIdeal d b t φ hφ A q) x.val x.val (mem_chart_source _ _))
        (jointBasePullback d b t (actualTranslatedMap (n := d) (m := b) φ
          (baseProjection d b t U V φ hφ x.val)) (actualTranslatedMap_holomorphic hφ _) (actualTranslatedMap_zero φ _) r) := by
  have h := quotientMap_chart_mk (sourceProjection_holomorphic d b t U V φ hφ)
    (jointIdeal d b t φ hφ A q) (jointIdeal_coherent d b t φ hφ A hA q hq) A hA
    (le_sumIdeal_left (isCoherent_pullback (sourceProjection_holomorphic d b t U V φ hφ) hA)) x r
  have hr := congrArg (fun e : HolGerm (ComplexModel (d+t)) →ₐ[ℂ] HolGerm (ComplexModel (b+t)) => e r)
    (sourceProjection_germ d b t φ hφ x.val)
  exact h.trans (congrArg (Ideal.Quotient.mk
    (wholeChartStalkIdeal (jointIdeal d b t φ hφ A q) x.val x.val (mem_chart_source _ _))) hr)
end ProjectionRepresentatives

section Origin
variable {U : Opens (ComplexModel (d+t))} {V : Opens (ComplexModel b)}
  (φ : V → ComplexModel d) (hφ : ContMDiff 𝓘(ℂ,ComplexModel b) 𝓘(ℂ,ComplexModel d) ∞ φ)
  (A : GermIdeal (d+t) U) (hA : A.IsCoherent) (q : GermIdeal b V) (hq : q.IsCoherent)
  (hU0 : (0 : ComplexModel (d+t)) ∈ U) (hV0 : (0 : ComplexModel b) ∈ V)
  (hφ0 : φ ⟨0,hV0⟩ = 0)
  (hA0 : (⟨0,hU0⟩ : U) ∈ A.zeroLocus) (hq0 : (⟨0,hV0⟩ : V) ∈ q.zeroLocus)

def originPoint : jointOpen d b t U V φ hφ :=
  pairPoint d b t φ hφ ⟨0,hU0⟩ ⟨0,hV0⟩ (by simpa only [map_zero] using hφ0.symm)

private theorem originPoint_source :
    sourceProjection d b t U V φ hφ (originPoint d b t φ hφ hU0 hV0 hφ0) = ⟨0,hU0⟩ :=
  pairPoint_source d b t φ hφ _ _ _

private theorem originPoint_base :
    baseProjection d b t U V φ hφ (originPoint d b t φ hφ hU0 hV0 hφ0) = ⟨0,hV0⟩ :=
  pairPoint_base d b t φ hφ _ _ _

theorem originPoint_coordinates : (originPoint d b t φ hφ hU0 hV0 hφ0).val.val = 0 := by
  change join (0 : ComplexModel b) (actualJointNormalProjection d t 0) = 0
  simp only [HironakaActualIntrinsicStableAmbientIso.join,map_zero,zero_add]

def originSupportPoint : (jointIdeal d b t φ hφ A q).zeroLocus :=
  ⟨originPoint d b t φ hφ hU0 hV0 hφ0,
    (joint_support_iff d b t φ hφ A hA q hq _).mpr (by
      rw [originPoint_source,originPoint_base]
      exact ⟨hA0,hq0⟩)⟩

def originIdeal : Ideal (HolGerm (ComplexModel (b+t))) :=
  Ideal.map (jointBasePullback d b t (actualTranslatedMap (n := d) (m := b) φ (⟨0,hV0⟩ : V))
      (actualTranslatedMap_holomorphic hφ _) (actualTranslatedMap_zero φ _)).toRingHom
    (wholeChartStalkIdeal A (⟨0,hU0⟩ : U) ⟨0,hU0⟩ (mem_chart_source _ _)) ⊔
  Ideal.map (tangentPullback b t).toRingHom
    (wholeChartStalkIdeal q (⟨0,hV0⟩ : V) ⟨0,hV0⟩ (mem_chart_source _ _))

private theorem jointChartIdeal_origin :
    jointChartIdeal d b t φ hφ A q (originPoint d b t φ hφ hU0 hV0 hφ0) =
      originIdeal d b t φ hφ A q hU0 hV0 := by
  simp only [jointChartIdeal,originIdeal,originPoint_source,originPoint_base]

/-- Actual support-origin stalk, used only when the original origins belong to their supports. -/
abbrev originStalk :=
  ((quotientLocallyRingedSpace (jointIdeal d b t φ hφ A q)
    (jointIdeal_coherent d b t φ hφ A hA q hq)).presheaf.stalk
      (originSupportPoint d b t φ hφ A hA q hq hU0 hV0 hφ0 hA0 hq0)).carrier

/-- The literal WHOLE original analytic quotient ring, retaining all nilpotents. -/
def originStalkEquiv : originStalk d b t φ hφ A hA q hq hU0 hV0 hφ0 hA0 hq0 ≃+*
    (HolGerm (ComplexModel (b+t)) ⧸ originIdeal d b t φ hφ A q hU0 hV0) :=
  (jointStalkEquiv d b t φ hφ A hA q hq
    (originSupportPoint d b t φ hφ A hA q hq hU0 hV0 hφ0 hA0 hq0)).trans
      (Ideal.quotEquivOfEq (jointChartIdeal_origin d b t φ hφ A q hU0 hV0 hφ0))

/-- EVERY original analytic ambient numerator has its exact whole quotient class. -/
theorem originStalkEquiv_inclusion
    (r : actualComplexStructureStalk (n := b+t) (originPoint d b t φ hφ hU0 hV0 hφ0)) :
    originStalkEquiv d b t φ hφ A hA q hq hU0 hV0 hφ0 hA0 hq0
      ((quotientInclusion _ (jointIdeal_coherent d b t φ hφ A hA q hq)).stalkMap
        (originSupportPoint d b t φ hφ A hA q hq hU0 hV0 hφ0 hA0 hq0) r) =
    Ideal.Quotient.mk (originIdeal d b t φ hφ A q hU0 hV0)
      (actualStalkChartEquiv (n := b+t) (originPoint d b t φ hφ hU0 hV0 hφ0) r) := by
  exact congrArg (Ideal.quotEquivOfEq (jointChartIdeal_origin d b t φ hφ A q hU0 hV0 hφ0))
    (jointStalkEquiv_inclusion d b t φ hφ A hA q hq
      (originSupportPoint d b t φ hφ A hA q hq hU0 hV0 hφ0 hA0 hq0) r)

private def baseOriginStalkEquiv :
    ((quotientLocallyRingedSpace q hq).presheaf.stalk
      ((baseQuotientProjection d b t φ hφ A hA q hq).base
        (originSupportPoint d b t φ hφ A hA q hq hU0 hV0 hφ0 hA0 hq0))).carrier ≃+*
      (HolGerm (ComplexModel b) ⧸
        wholeChartStalkIdeal q (⟨0,hV0⟩ : V) ⟨0,hV0⟩ (mem_chart_source _ _)) :=
  (quotientStalkChartEquiv q hq _).trans (Ideal.quotEquivOfEq (by
    change wholeChartStalkIdeal q
      (baseProjection d b t U V φ hφ (originPoint d b t φ hφ hU0 hV0 hφ0))
      (baseProjection d b t U V φ hφ (originPoint d b t φ hφ hU0 hV0 hφ0)) (mem_chart_source _ _) = _
    rw [originPoint_base]))

private def originNativeBaseHom :
    (HolGerm (ComplexModel b) ⧸ wholeChartStalkIdeal q (⟨0,hV0⟩ : V) ⟨0,hV0⟩ (mem_chart_source _ _)) →+*
      originStalk d b t φ hφ A hA q hq hU0 hV0 hφ0 hA0 hq0 :=
  ((baseQuotientProjection d b t φ hφ A hA q hq).stalkMap
    (originSupportPoint d b t φ hφ A hA q hq hU0 hV0 hφ0 hA0 hq0)).hom.comp
      (baseOriginStalkEquiv d b t φ hφ A hA q hq hU0 hV0 hφ0 hA0 hq0).symm.toRingHom

private def originBaseHom :
    (HolGerm (ComplexModel b) ⧸ wholeChartStalkIdeal q (⟨0,hV0⟩ : V) ⟨0,hV0⟩ (mem_chart_source _ _)) →+*
      (HolGerm (ComplexModel (b+t)) ⧸ originIdeal d b t φ hφ A q hU0 hV0) :=
  Ideal.quotientMap _ (tangentPullback b t).toRingHom
    (Ideal.le_comap_map.trans (Ideal.comap_mono le_sup_right))


private theorem baseOrigin_inverse_mk (r : HolGerm (ComplexModel b)) :
    (baseOriginStalkEquiv d b t φ hφ A hA q hq hU0 hV0 hφ0 hA0 hq0).symm
      (Ideal.Quotient.mk (wholeChartStalkIdeal q (⟨0,hV0⟩ : V) ⟨0,hV0⟩ (mem_chart_source _ _)) r) =
        (quotientStalkChartEquiv q hq ((baseQuotientProjection d b t φ hφ A hA q hq).base (originSupportPoint d b t φ hφ A hA q hq hU0 hV0 hφ0 hA0 hq0))).symm (Ideal.Quotient.mk (wholeChartStalkIdeal q ((baseQuotientProjection d b t φ hφ A hA q hq).base (originSupportPoint d b t φ hφ A hA q hq hU0 hV0 hφ0 hA0 hq0)).val ((baseQuotientProjection d b t φ hφ A hA q hq).base (originSupportPoint d b t φ hφ A hA q hq hU0 hV0 hφ0 hA0 hq0)).val (mem_chart_source _ _)) r) := by
  have he : (wholeChartStalkIdeal q ((baseQuotientProjection d b t φ hφ A hA q hq).base (originSupportPoint d b t φ hφ A hA q hq hU0 hV0 hφ0 hA0 hq0)).val ((baseQuotientProjection d b t φ hφ A hA q hq).base (originSupportPoint d b t φ hφ A hA q hq hU0 hV0 hφ0 hA0 hq0)).val (mem_chart_source _ _)) = (wholeChartStalkIdeal q (⟨0,hV0⟩ : V) ⟨0,hV0⟩ (mem_chart_source _ _)) := by
    change wholeChartStalkIdeal q
      (baseProjection d b t U V φ hφ (originPoint d b t φ hφ hU0 hV0 hφ0))
      (baseProjection d b t U V φ hφ (originPoint d b t φ hφ hU0 hV0 hφ0)) (mem_chart_source _ _) = _
    rw [originPoint_base]
  apply (baseOriginStalkEquiv d b t φ hφ A hA q hq hU0 hV0 hφ0 hA0 hq0).injective
  rw [RingEquiv.apply_symm_apply]
  change Ideal.Quotient.mk (wholeChartStalkIdeal q (⟨0,hV0⟩ : V) ⟨0,hV0⟩ (mem_chart_source _ _)) r = Ideal.quotEquivOfEq he
    (quotientStalkChartEquiv q hq ((baseQuotientProjection d b t φ hφ A hA q hq).base (originSupportPoint d b t φ hφ A hA q hq hU0 hV0 hφ0 hA0 hq0)) ((quotientStalkChartEquiv q hq ((baseQuotientProjection d b t φ hφ A hA q hq).base (originSupportPoint d b t φ hφ A hA q hq hU0 hV0 hφ0 hA0 hq0))).symm (Ideal.Quotient.mk (wholeChartStalkIdeal q ((baseQuotientProjection d b t φ hφ A hA q hq).base (originSupportPoint d b t φ hφ A hA q hq hU0 hV0 hφ0 hA0 hq0)).val ((baseQuotientProjection d b t φ hφ A hA q hq).base (originSupportPoint d b t φ hφ A hA q hq hU0 hV0 hφ0 hA0 hq0)).val (mem_chart_source _ _)) r)))
  rw [RingEquiv.apply_symm_apply]
  rfl

private theorem originNativeBaseHom_mk (r : HolGerm (ComplexModel b)) :
    originNativeBaseHom d b t φ hφ A hA q hq hU0 hV0 hφ0 hA0 hq0 (Ideal.Quotient.mk (wholeChartStalkIdeal q (⟨0,hV0⟩ : V) ⟨0,hV0⟩ (mem_chart_source _ _)) r) =
      (baseQuotientProjection d b t φ hφ A hA q hq).stalkMap (originSupportPoint d b t φ hφ A hA q hq hU0 hV0 hφ0 hA0 hq0)
        ((quotientStalkChartEquiv q hq ((baseQuotientProjection d b t φ hφ A hA q hq).base (originSupportPoint d b t φ hφ A hA q hq hU0 hV0 hφ0 hA0 hq0))).symm (Ideal.Quotient.mk (wholeChartStalkIdeal q ((baseQuotientProjection d b t φ hφ A hA q hq).base (originSupportPoint d b t φ hφ A hA q hq hU0 hV0 hφ0 hA0 hq0)).val ((baseQuotientProjection d b t φ hφ A hA q hq).base (originSupportPoint d b t φ hφ A hA q hq hU0 hV0 hφ0 hA0 hq0)).val (mem_chart_source _ _)) r)) := by
  change (baseQuotientProjection d b t φ hφ A hA q hq).stalkMap (originSupportPoint d b t φ hφ A hA q hq hU0 hV0 hφ0 hA0 hq0)
    ((baseOriginStalkEquiv d b t φ hφ A hA q hq hU0 hV0 hφ0 hA0 hq0).symm (Ideal.Quotient.mk (wholeChartStalkIdeal q (⟨0,hV0⟩ : V) ⟨0,hV0⟩ (mem_chart_source _ _)) r)) = _
  rw [baseOrigin_inverse_mk]

private theorem originBaseHom_mk (r : HolGerm (ComplexModel b)) :
    originBaseHom d b t φ hφ A q hU0 hV0 (Ideal.Quotient.mk (wholeChartStalkIdeal q (⟨0,hV0⟩ : V) ⟨0,hV0⟩ (mem_chart_source _ _)) r) =
      Ideal.Quotient.mk (originIdeal d b t φ hφ A q hU0 hV0) (tangentPullback b t r) := rfl

private theorem originStalkEquiv_apply
    (z : originStalk d b t φ hφ A hA q hq hU0 hV0 hφ0 hA0 hq0) :
    originStalkEquiv d b t φ hφ A hA q hq hU0 hV0 hφ0 hA0 hq0 z =
      Ideal.quotEquivOfEq (jointChartIdeal_origin d b t φ hφ A q hU0 hV0 hφ0)
        (Ideal.quotEquivOfEq (whole_joint_chart d b t φ hφ A hA q hq (originPoint d b t φ hφ hU0 hV0 hφ0))
          (quotientStalkChartEquiv _ (jointIdeal_coherent d b t φ hφ A hA q hq) (originSupportPoint d b t φ hφ A hA q hq hU0 hV0 hφ0 hA0 hq0) z)) := rfl

private theorem originStalkEquiv_base_mk (r : HolGerm (ComplexModel b)) :
    originStalkEquiv d b t φ hφ A hA q hq hU0 hV0 hφ0 hA0 hq0
      (originNativeBaseHom d b t φ hφ A hA q hq hU0 hV0 hφ0 hA0 hq0 (Ideal.Quotient.mk (wholeChartStalkIdeal q (⟨0,hV0⟩ : V) ⟨0,hV0⟩ (mem_chart_source _ _)) r)) =
        originBaseHom d b t φ hφ A q hU0 hV0 (Ideal.Quotient.mk (wholeChartStalkIdeal q (⟨0,hV0⟩ : V) ⟨0,hV0⟩ (mem_chart_source _ _)) r) := by
  rw [originNativeBaseHom_mk,originStalkEquiv_apply,originBaseHom_mk]
  let e1 := Ideal.quotEquivOfEq (jointChartIdeal_origin d b t φ hφ A q hU0 hV0 hφ0)
  let e2 := Ideal.quotEquivOfEq (whole_joint_chart d b t φ hφ A hA q hq (originPoint d b t φ hφ hU0 hV0 hφ0))
  have hm := congrArg (fun z => e1 (e2 z))
    (baseQuotientProjection_chart_mk d b t φ hφ A hA q hq
      (originSupportPoint d b t φ hφ A hA q hq hU0 hV0 hφ0 hA0 hq0) r)
  exact hm

private theorem originStalkEquiv_base (c : HolGerm (ComplexModel b) ⧸ (wholeChartStalkIdeal q (⟨0,hV0⟩ : V) ⟨0,hV0⟩ (mem_chart_source _ _))) :
    originStalkEquiv d b t φ hφ A hA q hq hU0 hV0 hφ0 hA0 hq0
      (originNativeBaseHom d b t φ hφ A hA q hq hU0 hV0 hφ0 hA0 hq0 c) =
        originBaseHom d b t φ hφ A q hU0 hV0 c := by
  obtain ⟨r,rfl⟩ := Ideal.Quotient.mk_surjective c
  exact originStalkEquiv_base_mk d b t φ hφ A hA q hq hU0 hV0 hφ0 hA0 hq0 r

/-- The actual B/q action comes from the CONSTRUCTED native base projection, with no scalar-action input. -/
def originStalkAlgEquiv :
    letI : Algebra
      (HolGerm (ComplexModel b) ⧸ wholeChartStalkIdeal q (⟨0,hV0⟩ : V) ⟨0,hV0⟩ (mem_chart_source _ _))
      (originStalk d b t φ hφ A hA q hq hU0 hV0 hφ0 hA0 hq0) :=
        (originNativeBaseHom d b t φ hφ A hA q hq hU0 hV0 hφ0 hA0 hq0).toAlgebra
    letI : Algebra
      (HolGerm (ComplexModel b) ⧸ wholeChartStalkIdeal q (⟨0,hV0⟩ : V) ⟨0,hV0⟩ (mem_chart_source _ _))
      (HolGerm (ComplexModel (b+t)) ⧸ originIdeal d b t φ hφ A q hU0 hV0) :=
        (originBaseHom d b t φ hφ A q hU0 hV0).toAlgebra
    originStalk d b t φ hφ A hA q hq hU0 hV0 hφ0 hA0 hq0 ≃ₐ[
      HolGerm (ComplexModel b) ⧸ wholeChartStalkIdeal q (⟨0,hV0⟩ : V) ⟨0,hV0⟩ (mem_chart_source _ _)]
        (HolGerm (ComplexModel (b+t)) ⧸ originIdeal d b t φ hφ A q hU0 hV0) := by
  letI := (originNativeBaseHom d b t φ hφ A hA q hq hU0 hV0 hφ0 hA0 hq0).toAlgebra
  letI := (originBaseHom d b t φ hφ A q hU0 hV0).toAlgebra
  exact { originStalkEquiv d b t φ hφ A hA q hq hU0 hV0 hφ0 hA0 hq0 with
    commutes' c := originStalkEquiv_base d b t φ hφ A hA q hq hU0 hV0 hφ0 hA0 hq0 c }
end Origin


end
end Hironaka.HironakaAnalyticBaseChangeQuotientModel
