import Hironaka.Resolution.HironakaAnalyticBaseChangeQuotientModel
import Hironaka.Resolution.HironakaNonreducedQuotientNeighborhoodLifting

/-! Local joint factorization of an ordinary full analytic-model cone.
All actual lifts, whole-ideal conditions and both full projection triangles
are outputs. Global descent/uniqueness/UP are separate consumers.
BP FIRST: hironaka-analytic-basechange-local-factorization.tex. -/
set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaAnalyticBaseChangeLocalFactorization
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaHolomorphicJetChartInvariance HironakaHolomorphicJetRankLoci
  HironakaHolomorphicJetMonomialSpan HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaSmoothCentreRealDomainActualIdealPresheaf
  HironakaActualWholeStalkHolomorphicPullback HironakaActualBiholomorphicWholeStalkHS
  HironakaActualAnalyticSubspaceMaps HironakaActualAnalyticSubspaceOpenRestriction
  HironakaActualOpenIntrinsicHS HironakaActualProjectionIntrinsicHS
  HironakaNonreducedAnalyticQuotientModel HironakaNonreducedAnalyticQuotientMorphism
  HironakaNonreducedQuotientGermLifting HironakaNonreducedQuotientNeighborhoodLifting
  HironakaAnalyticBaseChangeQuotientModel HironakaRelativeNormalIdeal
  HironakaActualCentreJointJets HironakaActualJointBaseFibre
  HironakaActualIntrinsicStableAmbientIso RelativePrincipalizationSpan
  InvertibleIdealQuotient RestrictedIdealExtension GermIdealPullbackCalculus

private theorem whole_mono {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {A B : GermIdeal n M} (hAB : GermIdeal.Le A B) (x : M) :
    wholeChartStalkIdeal A x x (mem_chart_source _ x) ≤ wholeChartStalkIdeal B x x (mem_chart_source _ x) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨g,hg,hm,rfl⟩
  exact Ideal.subset_span ⟨g,hg,hAB x g hm,rfl⟩

/-- Actual coherent WHOLE pullback composition for arbitrary model dimensions. -/
private theorem whole_pullback_comp {a c e : ℕ} {X Y Z : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [ChartedSpace (ComplexModel a) X] [IsComplexManifold a X]
    [ChartedSpace (ComplexModel c) Y] [IsComplexManifold c Y]
    [ChartedSpace (ComplexModel e) Z] [IsComplexManifold e Z]
    {f : Y → X} {g : Z → Y}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel c) 𝓘(ℂ,ComplexModel a) ∞ f)
    (hg : ContMDiff 𝓘(ℂ,ComplexModel e) 𝓘(ℂ,ComplexModel c) ∞ g)
    (A : GermIdeal a X) (hA : A.IsCoherent) :
    GermIdeal.pullback (m := e) (f ∘ g) A =
      GermIdeal.pullback (m := e) g (GermIdeal.pullback (m := c) f A) := by
  have hL := isCoherent_pullback (hf.comp hg) hA
  have hF := isCoherent_pullback hf hA
  have hR := isCoherent_pullback hg hF
  have hw (z : Z) :
      wholeChartStalkIdeal (GermIdeal.pullback (m := e) (f ∘ g) A) z z (mem_chart_source _ _) =
      wholeChartStalkIdeal (GermIdeal.pullback (m := e) g (GermIdeal.pullback (m := c) f A)) z z (mem_chart_source _ _) := by
    calc
      _ = Ideal.map (actualHolomorphicGermPullback (hf.comp hg) z).toRingHom
          (wholeChartStalkIdeal A (f (g z)) (f (g z)) (mem_chart_source _ _)) :=
        (map_wholeChartStalkIdeal_actual_pullback (hf.comp hg) A hA z).symm
      _ = Ideal.map (actualHolomorphicGermPullback hg z).toRingHom
          (Ideal.map (actualHolomorphicGermPullback hf (g z)).toRingHom
            (wholeChartStalkIdeal A (f (g z)) (f (g z)) (mem_chart_source _ _))) := by
        have hc := actualHolomorphicGermPullback_comp (f := f) (g := g) hf hg z
        rw [Ideal.map_map]
        apply congrArg (fun h : HolGerm (ComplexModel a) →+* HolGerm (ComplexModel e) =>
          Ideal.map h (wholeChartStalkIdeal A (f (g z)) (f (g z)) (mem_chart_source _ _)))
        apply RingHom.ext
        intro r
        exact congrArg (fun h : HolGerm (ComplexModel a) →ₐ[ℂ] HolGerm (ComplexModel e) => h r) hc
      _ = _ := by rw [map_wholeChartStalkIdeal_actual_pullback hf A hA,
        map_wholeChartStalkIdeal_actual_pullback hg _ hF]
  apply GermIdeal.ext
  funext z
  funext v
  apply propext
  constructor
  · intro hv
    have hhol := GermIdeal.IsCoherent.holomorphicAt_mem hL hv
    exact (coherent_mem_iff_whole_chart _ hR z v hhol).mpr
      ((hw z) ▸ (coherent_mem_iff_whole_chart _ hL z v hhol).mp hv)
  · intro hv
    have hhol := GermIdeal.IsCoherent.holomorphicAt_mem hR hv
    exact (coherent_mem_iff_whole_chart _ hL z v hhol).mpr
      ((hw z).symm ▸ (coherent_mem_iff_whole_chart _ hR z v hhol).mp hv)

variable {n m : ℕ} {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [ChartedSpace (ComplexModel m) N] [IsComplexManifold m N]

private def openInclusion (O P : Opens M) (hOP : O ≤ P) : O → P := fun x => ⟨x.val,hOP x.property⟩

omit [IsComplexManifold n M] in
private theorem openInclusion_holomorphic (O P : Opens M) (hOP : O ≤ P) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (openInclusion O P hOP) := by
  apply (ContMDiff.subtypeVal_comp_iff P _).mp
  exact contMDiff_subtype_val

private theorem openIdeal_refine (C : GermIdeal n M) (hC : C.IsCoherent)
    (O P : Opens M) (hOP : O ≤ P) :
    GermIdeal.pullback (m := n) (openInclusion O P hOP) (quotientOpenIdeal C P) = quotientOpenIdeal C O :=
  (whole_pullback_comp contMDiff_subtype_val (openInclusion_holomorphic O P hOP) C hC).symm

private def refinementMap (C : GermIdeal n M) (hC : C.IsCoherent)
    (O P : Opens M) (hOP : O ≤ P) :
    quotientLocallyRingedSpace (quotientOpenIdeal C O) (quotientOpenIdeal_coherent C hC O) ⟶
      quotientLocallyRingedSpace (quotientOpenIdeal C P) (quotientOpenIdeal_coherent C hC P) :=
  quotientMap (openInclusion_holomorphic O P hOP) _ (quotientOpenIdeal_coherent C hC O)
    _ (quotientOpenIdeal_coherent C hC P) (fun _x _g hg => (openIdeal_refine C hC O P hOP) ▸ hg)

private theorem refinementMap_to_open (C : GermIdeal n M) (hC : C.IsCoherent)
    (O P : Opens M) (hOP : O ≤ P) :
    refinementMap C hC O P hOP ≫ quotientOpenMap C hC P = quotientOpenMap C hC O := by
  apply (cancel_mono (quotientInclusion C hC)).mp
  have hr := quotientMap_inclusion (openInclusion_holomorphic O P hOP)
    (quotientOpenIdeal C O) (quotientOpenIdeal_coherent C hC O)
    (quotientOpenIdeal C P) (quotientOpenIdeal_coherent C hC P)
    (fun _x _g hg => (openIdeal_refine C hC O P hOP) ▸ hg)
  have hp := quotientMap_inclusion (f := (Subtype.val : P → M)) contMDiff_subtype_val
    (quotientOpenIdeal C P) (quotientOpenIdeal_coherent C hC P) C hC (fun _ _ h => h)
  have ho := quotientMap_inclusion (f := (Subtype.val : O → M)) contMDiff_subtype_val
    (quotientOpenIdeal C O) (quotientOpenIdeal_coherent C hC O) C hC (fun _ _ h => h)
  change quotientInclusion _ _ ≫ _ = refinementMap C hC O P hOP ≫ quotientInclusion _ _ at hr
  change quotientInclusion _ _ ≫ _ = quotientOpenMap C hC P ≫ quotientInclusion C hC at hp
  change quotientInclusion _ _ ≫ _ = quotientOpenMap C hC O ≫ quotientInclusion C hC at ho
  rw [Category.assoc,←hp,←Category.assoc,←hr,Category.assoc,←ChartedSpace.locallyRingedSpace_comp]
  exact ho

/-- Refinement of an internally chosen actual lift retains the literal open quotient square. -/
private theorem restrict_lift (C : GermIdeal n M) (hC : C.IsCoherent)
    (A : GermIdeal m N) (hA : A.IsCoherent)
    (F : quotientLocallyRingedSpace C hC ⟶ quotientLocallyRingedSpace A hA)
    (P : Opens M) (f : P → N)
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
    (hCA : GermIdeal.Le (GermIdeal.pullback (m := n) f A) (quotientOpenIdeal C P))
    (he : quotientMap hf _ (quotientOpenIdeal_coherent C hC P) A hA hCA = quotientOpenMap C hC P ≫ F)
    (O : Opens M) (hOP : O ≤ P) :
    ∃ hCA' : GermIdeal.Le (GermIdeal.pullback (m := n) (f ∘ openInclusion O P hOP) A) (quotientOpenIdeal C O),
      quotientMap (hf.comp (openInclusion_holomorphic O P hOP)) _ (quotientOpenIdeal_coherent C hC O) A hA hCA' =
        quotientOpenMap C hC O ≫ F := by
  have hCA' : GermIdeal.Le (GermIdeal.pullback (m := n) (f ∘ openInclusion O P hOP) A) (quotientOpenIdeal C O) := by
    rw [whole_pullback_comp hf (openInclusion_holomorphic O P hOP) A hA]
    intro x g hg
    exact (openIdeal_refine C hC O P hOP) ▸ (pullback_le_pullback (f := openInclusion O P hOP) hCA x g hg)
  refine ⟨hCA',?_⟩
  apply (cancel_mono (quotientInclusion A hA)).mp
  have hn := quotientMap_inclusion (hf.comp (openInclusion_holomorphic O P hOP))
    _ (quotientOpenIdeal_coherent C hC O) A hA hCA'
  rw [←hn]
  have hp := quotientMap_inclusion hf _ (quotientOpenIdeal_coherent C hC P) A hA hCA
  have hr := quotientMap_inclusion (openInclusion_holomorphic O P hOP)
    (quotientOpenIdeal C O) (quotientOpenIdeal_coherent C hC O)
    (quotientOpenIdeal C P) (quotientOpenIdeal_coherent C hC P)
    (fun _x _g hg => (openIdeal_refine C hC O P hOP) ▸ hg)
  change quotientInclusion _ _ ≫ _ = refinementMap C hC O P hOP ≫ quotientInclusion _ _ at hr
  calc
    _ = refinementMap C hC O P hOP ≫ quotientInclusion (quotientOpenIdeal C P) (quotientOpenIdeal_coherent C hC P) ≫
        ChartedSpace.locallyRingedSpaceMap f hf := by
      rw [←Category.assoc,←hr,Category.assoc,←ChartedSpace.locallyRingedSpace_comp]
    _ = refinementMap C hC O P hOP ≫ quotientMap hf _ (quotientOpenIdeal_coherent C hC P) A hA hCA ≫ quotientInclusion A hA := by rw [hp]
    _ = _ := by
      rw [he]
      simpa only [Category.assoc] using congrArg (fun k => k ≫ F ≫ quotientInclusion A hA)
        (refinementMap_to_open C hC O P hOP)

private theorem chart_inclusion (C : GermIdeal n M) (hC : C.IsCoherent)
    (x : C.zeroLocus) (r : actualComplexStructureStalk (n := n) x.val) :
    quotientStalkChartEquiv C hC x ((quotientInclusion C hC).stalkMap x r) =
      Ideal.Quotient.mk (wholeChartStalkIdeal C x.val x.val (mem_chart_source _ _))
        (actualStalkChartEquiv (n := n) x.val r) := by
  simp only [quotientStalkChartEquiv,RingEquiv.trans_apply,quotientInclusion_stalk]
  rfl

/-- Raw native chart conjugation is defined at a map's ACTUAL image point, so full map
equality gives raw ring-map equality by ordinary congruence, without a supplied transport. -/
private def ambientRaw (C : GermIdeal n M) (hC : C.IsCoherent)
    (F : quotientLocallyRingedSpace C hC ⟶ ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel m) N)
    (x : C.zeroLocus) :
    HolGerm (ComplexModel m) →+* (HolGerm (ComplexModel n) ⧸ wholeChartStalkIdeal C x.val x.val (mem_chart_source _ _)) :=
  (quotientStalkChartEquiv C hC x).toRingHom.comp
    ((F.stalkMap x).hom.comp (actualStalkChartEquiv (n := m) (show N from F.base x)).symm.toRingHom)

private theorem ambientRaw_actual (C : GermIdeal n M) (hC : C.IsCoherent)
    {f : M → N} (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
    (x : C.zeroLocus) (r : HolGerm (ComplexModel m)) :
    ambientRaw C hC (quotientInclusion C hC ≫ ChartedSpace.locallyRingedSpaceMap f hf) x r =
      Ideal.Quotient.mk _ (actualHolomorphicGermPullback hf x.val r) := by
  change quotientStalkChartEquiv C hC x ((quotientInclusion C hC ≫ ChartedSpace.locallyRingedSpaceMap f hf).stalkMap x
    ((actualStalkChartEquiv (n := m) (f x.val)).symm r)) = _
  rw [LocallyRingedSpace.stalkMap_comp]
  change quotientStalkChartEquiv C hC x ((quotientInclusion C hC).stalkMap x
    ((ChartedSpace.locallyRingedSpaceMap f hf).stalkMap x.val ((actualStalkChartEquiv (n := m) (f x.val)).symm r))) = _
  rw [chart_inclusion,actualNativeStalk_chart_pullback,RingEquiv.apply_symm_apply]

private theorem ambientRaw_ext (C : GermIdeal n M) (hC : C.IsCoherent)
    (F G : quotientLocallyRingedSpace C hC ⟶ ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel m) N)
    (hbase : F.base = G.base) (hraw : ∀ (x : C.zeroLocus) (r : HolGerm (ComplexModel m)),
      ambientRaw C hC F x r = ambientRaw C hC G x r) : F = G := by
  rcases F with ⟨⟨f,fc⟩,hf⟩
  rcases G with ⟨⟨g,gc⟩,hg⟩
  change f = g at hbase
  subst g
  let F : quotientLocallyRingedSpace C hC ⟶ ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel m) N := ⟨⟨f,fc⟩,hf⟩
  let G : quotientLocallyRingedSpace C hC ⟶ ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel m) N := ⟨⟨f,gc⟩,hg⟩
  have hs (x : C.zeroLocus) (a : actualComplexStructureStalk (n := m) (show N from f x)) : F.stalkMap x a = G.stalkMap x a := by
    apply (quotientStalkChartEquiv C hC x).injective
    have h := hraw x (actualStalkChartEquiv (n := m) (show N from f x) a)
    change quotientStalkChartEquiv C hC x (F.stalkMap x
        ((actualStalkChartEquiv (n := m) (show N from f x)).symm (actualStalkChartEquiv (n := m) (show N from f x) a))) =
      quotientStalkChartEquiv C hC x (G.stalkMap x
        ((actualStalkChartEquiv (n := m) (show N from f x)).symm (actualStalkChartEquiv (n := m) (show N from f x) a))) at h
    simpa only [RingEquiv.symm_apply_apply] using h
  suffices hc : fc = gc by cases hc; rfl
  apply NatTrans.ext
  funext U
  apply CommRingCat.hom_ext
  ext s
  apply TopCat.Presheaf.section_ext (quotientLocallyRingedSpace C hC).sheaf
  intro x hx
  let a := (actualComplexStructureSheaf (n := m) N).presheaf.germ U.unop (f x) hx s
  calc
    _ = F.stalkMap x a := (LocallyRingedSpace.stalkMap_germ_apply F U.unop x hx s).symm
    _ = G.stalkMap x a := hs x a
    _ = _ := LocallyRingedSpace.stalkMap_germ_apply G U.unop x hx s

private theorem germ_into_open {c : ℕ} {U : Opens (ComplexModel c)} {f : M → U}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel c) ∞ f) (x : M) :
    actualHolomorphicGermPullback hf x =
      actualHolomorphicGermPullback (contMDiff_subtype_val.comp hf) x := by
  have h := actualHolomorphicGermPullback_comp (f := (Subtype.val : U → ComplexModel c)) (g := f)
    contMDiff_subtype_val hf x
  rw [actualHolomorphicGermPullback_val] at h
  simpa only [AlgHom.comp_id] using h.symm

private theorem tangent_on_open_germ (d t : ℕ) (U : Opens (ComplexModel (d+t))) (p : U) :
    actualHolomorphicGermPullback
      ((tangentProjection d t).contDiff.contMDiff.comp (contMDiff_subtype_val :
        ContMDiff 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ComplexModel (d+t)) ∞ (Subtype.val : U → ComplexModel (d+t)))) p =
      tangentPullback d t := by
  have h := actualHolomorphicGermPullback_comp (f := tangentProjection d t)
    (g := (Subtype.val : U → ComplexModel (d+t)))
    (tangentProjection d t).contDiff.contMDiff contMDiff_subtype_val p
  rw [actualHolomorphicGermPullback_val,actualHolomorphicGermPullback_tangentProjection] at h
  simpa only [AlgHom.id_comp] using h

private theorem tangent_coordinate (d t : ℕ) (i : Fin d) :
    tangentPullback d t (coordinateGerm i) = coordinateGerm (i.castAdd t) := by
  unfold tangentPullback coordinateGerm
  rw [compAlgHom_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun _ => rfl

private theorem pullback_first_coordinate {d t : ℕ} {U : Opens (ComplexModel (d+t))}
    {f : M → U} (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel (d+t)) ∞ f)
    (x : M) (i : Fin d) :
    actualHolomorphicGermPullback
      (((tangentProjection d t).contDiff.contMDiff.comp contMDiff_subtype_val).comp hf) x (coordinateGerm i) =
      actualHolomorphicGermPullback hf x (coordinateGerm (i.castAdd t)) := by
  have h := actualHolomorphicGermPullback_comp
    (f := fun p : U => tangentProjection d t p.val) (g := f)
    ((tangentProjection d t).contDiff.contMDiff.comp contMDiff_subtype_val) hf x
  have he := congrArg (fun k : HolGerm (ComplexModel d) →ₐ[ℂ] HolGerm (ComplexModel n) => k (coordinateGerm i)) h
  simpa only [AlgHom.comp_apply,tangent_on_open_germ,tangent_coordinate] using he

private theorem coordinate_pullback_congr {c : ℕ} {U : Opens (ComplexModel c)} {f g : M → U}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel c) ∞ f)
    (hg : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel c) ∞ g)
    (i : Fin c) (hi : ∀ z : M, (f z).val i = (g z).val i) (x : M) :
    actualHolomorphicGermPullback hf x (coordinateGerm i) =
      actualHolomorphicGermPullback hg x (coordinateGerm i) := by
  rw [germ_into_open hf,germ_into_open hg]
  unfold actualHolomorphicGermPullback coordinateGerm
  rw [compAlgHom_mk,compAlgHom_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  apply Eventually.of_forall
  intro z
  change (f ((chartAt (ComplexModel n) x).symm (z+(chartAt (ComplexModel n) x) x))).val i - (f x).val i =
    (g ((chartAt (ComplexModel n) x).symm (z+(chartAt (ComplexModel n) x) x))).val i - (g x).val i
  rw [hi,hi]

/-- The FULL base morphism and literal original normal coordinates force all nearby
analytic germs modulo the WHOLE source ideal, by the accepted local Taylor/Krull theorem. -/
private theorem block_congruence (C : GermIdeal n M) (hC : C.IsCoherent)
    {d t : ℕ} {U : Opens (ComplexModel (d+t))} {f g : M → U}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel (d+t)) ∞ f)
    (hg : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel (d+t)) ∞ g)
    (hbase : quotientInclusion C hC ≫ ChartedSpace.locallyRingedSpaceMap
        ((fun p : U => tangentProjection d t p.val) ∘ f)
        (((tangentProjection d t).contDiff.contMDiff.comp contMDiff_subtype_val).comp hf) =
      quotientInclusion C hC ≫ ChartedSpace.locallyRingedSpaceMap
        ((fun p : U => tangentProjection d t p.val) ∘ g)
        (((tangentProjection d t).contDiff.contMDiff.comp contMDiff_subtype_val).comp hg))
    (hnormal : ∀ z : M, actualJointNormalProjection d t (f z).val = actualJointNormalProjection d t (g z).val) :
    (∀ x : C.zeroLocus, f x.val = g x.val) ∧
    (∀ (x : C.zeroLocus) (r : HolGerm (ComplexModel (d+t))),
      Ideal.Quotient.mk (wholeChartStalkIdeal C x.val x.val (mem_chart_source _ _))
        (actualHolomorphicGermPullback hf x.val r) =
      Ideal.Quotient.mk (wholeChartStalkIdeal C x.val x.val (mem_chart_source _ _))
        (actualHolomorphicGermPullback hg x.val r)) ∧
    quotientInclusion C hC ≫ ChartedSpace.locallyRingedSpaceMap f hf =
      quotientInclusion C hC ≫ ChartedSpace.locallyRingedSpaceMap g hg := by
  have hp (x : C.zeroLocus) : f x.val = g x.val := by
    have hb : tangentProjection d t (f x.val).val = tangentProjection d t (g x.val).val :=
      congrArg (fun k => k.base x) hbase
    apply Subtype.ext
    calc
      _ = join (tangentProjection d t (f x.val).val) (actualJointNormalProjection d t (f x.val).val) :=
        (join_projections _).symm
      _ = join (tangentProjection d t (g x.val).val) (actualJointNormalProjection d t (g x.val).val) := by
        rw [hb,hnormal]
      _ = _ := join_projections _
  have hall (x : C.zeroLocus) (r : HolGerm (ComplexModel (d+t))) :
      Ideal.Quotient.mk (wholeChartStalkIdeal C x.val x.val (mem_chart_source _ _))
        (actualHolomorphicGermPullback hf x.val r) =
      Ideal.Quotient.mk (wholeChartStalkIdeal C x.val x.val (mem_chart_source _ _))
        (actualHolomorphicGermPullback hg x.val r) := by
    let IC := wholeChartStalkIdeal C x.val x.val (mem_chart_source _ _)
    let T := HolGerm (ComplexModel n) ⧸ IC
    let : IsNoetherianRing (HolGerm (ComplexModel n)) := isNoetherianRing_holGerm_euclidean n
    let : IsNoetherianRing T := inferInstance
    let : IsLocalRing T := chartQuotient_isLocalRing C x
    let : IsLocalHom (Ideal.Quotient.mk IC) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    let a : HolGerm (ComplexModel (d+t)) →ₐ[ℂ] T :=
      (Ideal.Quotient.mkₐ ℂ IC).comp (actualHolomorphicGermPullback hf x.val)
    let b : HolGerm (ComplexModel (d+t)) →ₐ[ℂ] T :=
      (Ideal.Quotient.mkₐ ℂ IC).comp (actualHolomorphicGermPullback hg x.val)
    let : IsLocalHom a.toRingHom := by
      change IsLocalHom ((Ideal.Quotient.mk IC).comp (actualHolomorphicGermPullback hf x.val).toRingHom)
      infer_instance
    let : IsLocalHom b.toRingHom := by
      change IsLocalHom ((Ideal.Quotient.mk IC).comp (actualHolomorphicGermPullback hg x.val).toRingHom)
      infer_instance
    have hc (i : Fin (d+t)) : a (coordinateGerm i) = b (coordinateGerm i) := by
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · have hb := congrArg (fun k => ambientRaw C hC k x (coordinateGerm j)) hbase
        have hf' := ambientRaw_actual C hC
          (((tangentProjection d t).contDiff.contMDiff.comp contMDiff_subtype_val).comp hf) x (coordinateGerm j)
        have hg' := ambientRaw_actual C hC
          (((tangentProjection d t).contDiff.contMDiff.comp contMDiff_subtype_val).comp hg) x (coordinateGerm j)
        have h₀ := hf'.symm.trans (hb.trans hg')
        have h₁ := congrArg (Ideal.Quotient.mk IC) (pullback_first_coordinate hf x.val j)
        have h₂ := congrArg (Ideal.Quotient.mk IC) (pullback_first_coordinate hg x.val j)
        exact h₁.symm.trans (h₀.trans h₂)
      · have hi (z : M) : (f z).val (j.natAdd d) = (g z).val (j.natAdd d) :=
          congrArg (fun v : ComplexModel t => v j) (hnormal z)
        exact congrArg (Ideal.Quotient.mk IC) (coordinate_pullback_congr hf hg (j.natAdd d) hi x.val)
    have he : a = b := local_algHom_ext_coordinates (d+t) a b hc
    exact congrArg (fun k : HolGerm (ComplexModel (d+t)) →ₐ[ℂ] T => k r) he
  refine ⟨hp,hall,?_⟩
  apply ambientRaw_ext C hC
  · ext x
    exact hp x
  · intro x r
    exact (ambientRaw_actual C hC hf x r).trans ((hall x r).trans (ambientRaw_actual C hC hg x r).symm)

omit [IsComplexManifold n M] in
/-- Genuine real-open joint map, obtained by shrinking the original common domain.
The target is literally741's open OF the cylinder, not a replacement support or global domain. -/
private theorem joint_geometry {d b t : ℕ} (P : Opens M)
    (U : Opens (ComplexModel (d+t))) (V : Opens (ComplexModel b))
    (φ : V → ComplexModel d) (hφ : ContMDiff 𝓘(ℂ,ComplexModel b) 𝓘(ℂ,ComplexModel d) ∞ φ)
    (f : P → U) (g : P → V)
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel (d+t)) ∞ f)
    (hg : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel b) ∞ g)
    (x : P) (hx : tangentProjection d t (f x).val = φ (g x)) :
    ∃ (O : Opens M) (_hxO : x.val ∈ O) (hOP : O ≤ P)
      (H : O → jointOpen d b t U V φ hφ)
      (_hH : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel (b+t)) ∞ H),
      ((baseProjection d b t U V φ hφ) ∘ H = g ∘ openInclusion O P hOP) ∧
      (∀ y : O, actualJointNormalProjection d t ((sourceProjection d b t U V φ hφ) (H y)).val =
        actualJointNormalProjection d t (f (openInclusion O P hOP y)).val) := by
  let h₀ : P → cylinder b t V := fun y =>
    ⟨join (g y).val (actualJointNormalProjection d t (f y).val),by
      change tangentProjection b t (join (g y).val (actualJointNormalProjection d t (f y).val)) ∈ V
      simpa only [first_join] using (g y).property⟩
  have hh₀ : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel (b+t)) ∞ h₀ := by
    apply (ContMDiff.subtypeVal_comp_iff (cylinder b t V) _).mp
    exact ((tangentInclusion b t).contDiff.contMDiff.comp (contMDiff_subtype_val.comp hg)).add
      ((actualJointNormalInclusion b t).contDiff.contMDiff.comp
        ((actualJointNormalProjection d t).contDiff.contMDiff.comp (contMDiff_subtype_val.comp hf)))
  have hp (y : P) : cylinderProjection b t V (h₀ y) = g y := Subtype.ext (first_join _ _)
  let T : Opens P := ⟨(jointOnCylinder d b t V φ ∘ h₀) ⁻¹' U,
    U.isOpen.preimage ((jointOnCylinder_holomorphic d b t V φ hφ).comp hh₀).continuous⟩
  have hxT : x ∈ T := by
    change join (φ (cylinderProjection b t V (h₀ x)))
      (actualJointNormalProjection b t (h₀ x).val) ∈ U
    rw [hp]
    change join (φ (g x)) (actualJointNormalProjection b t
      (join (g x).val (actualJointNormalProjection d t (f x).val))) ∈ U
    rw [second_join,←hx,join_projections]
    exact (f x).property
  let O : Opens M := ⟨(Subtype.val : P → M) '' (T : Set P),P.isOpen.isOpenMap_subtype_val _ T.isOpen⟩
  have hOP : O ≤ P := by rintro z ⟨y,hy,rfl⟩; exact y.property
  have hrT (y : O) : openInclusion O P hOP y ∈ T := by
    obtain ⟨z,hz,hzy⟩ := y.property
    have he : openInclusion O P hOP y = z := Subtype.ext hzy.symm
    exact he.symm ▸ hz
  let H : O → jointOpen d b t U V φ hφ := fun y => ⟨h₀ (openInclusion O P hOP y),hrT y⟩
  have hH : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel (b+t)) ∞ H := by
    apply (ContMDiff.subtypeVal_comp_iff (jointOpen d b t U V φ hφ) _).mp
    exact hh₀.comp (openInclusion_holomorphic O P hOP)
  refine ⟨O,⟨x,hxT,rfl⟩,hOP,H,hH,?_,?_⟩
  · funext y
    exact hp (openInclusion O P hOP y)
  · intro y
    change actualJointNormalProjection d t (join (φ (cylinderProjection b t V (h₀ (openInclusion O P hOP y))))
      (actualJointNormalProjection b t (join (g (openInclusion O P hOP y)).val
        (actualJointNormalProjection d t (f (openInclusion O P hOP y)).val)))) = _
    rw [second_join,second_join]

private theorem whole_pullback_sum {f : M → N}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
    (A B : GermIdeal m N) (hA : A.IsCoherent) (hB : B.IsCoherent) :
    GermIdeal.pullback (m := n) f (sumIdeal A B) =
      sumIdeal (GermIdeal.pullback (m := n) f A) (GermIdeal.pullback (m := n) f B) := by
  have hL := isCoherent_pullback hf (isCoherent_sumIdeal hA hB)
  have hPA := isCoherent_pullback hf hA
  have hPB := isCoherent_pullback hf hB
  have hR := isCoherent_sumIdeal hPA hPB
  have hw (x : M) :
      wholeChartStalkIdeal (GermIdeal.pullback (m := n) f (sumIdeal A B)) x x (mem_chart_source _ _) =
      wholeChartStalkIdeal (sumIdeal (GermIdeal.pullback (m := n) f A) (GermIdeal.pullback (m := n) f B))
        x x (mem_chart_source _ _) := by
    rw [←map_wholeChartStalkIdeal_actual_pullback hf (sumIdeal A B) (isCoherent_sumIdeal hA hB),
      wholeChartStalkIdeal_sum A B hA hB,Ideal.map_sup,
      map_wholeChartStalkIdeal_actual_pullback hf A hA,map_wholeChartStalkIdeal_actual_pullback hf B hB,
      wholeChartStalkIdeal_sum _ _ hPA hPB]
  apply GermIdeal.ext
  funext x
  funext v
  apply propext
  constructor
  · intro hv
    have hh := GermIdeal.IsCoherent.holomorphicAt_mem hL hv
    exact (coherent_mem_iff_whole_chart _ hR x v hh).mpr
      ((hw x) ▸ (coherent_mem_iff_whole_chart _ hL x v hh).mp hv)
  · intro hv
    have hh := GermIdeal.IsCoherent.holomorphicAt_mem hR hv
    exact (coherent_mem_iff_whole_chart _ hL x v hh).mpr
      ((hw x).symm ▸ (coherent_mem_iff_whole_chart _ hR x v hh).mp hv)

private theorem pullback_le_of_germ_congruence (C : GermIdeal n M) (hC : C.IsCoherent)
    (A : GermIdeal m N) (hA : A.IsCoherent) {f g : M → N}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
    (hg : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ g)
    (hCA : GermIdeal.Le (GermIdeal.pullback (m := n) f A) C)
    (hp : ∀ x : C.zeroLocus, f x.val = g x.val)
    (hall : ∀ (x : C.zeroLocus) (r : HolGerm (ComplexModel m)),
      Ideal.Quotient.mk (wholeChartStalkIdeal C x.val x.val (mem_chart_source _ _))
        (actualHolomorphicGermPullback hf x.val r) =
      Ideal.Quotient.mk (wholeChartStalkIdeal C x.val x.val (mem_chart_source _ _))
        (actualHolomorphicGermPullback hg x.val r)) :
    GermIdeal.Le (GermIdeal.pullback (m := n) g A) C := by
  have hPB := isCoherent_pullback hg hA
  have hle (y : M) : Ideal.map (actualHolomorphicGermPullback hg y).toRingHom
      (wholeChartStalkIdeal A (g y) (g y) (mem_chart_source _ _)) ≤
      wholeChartStalkIdeal C y y (mem_chart_source _ _) := by
    by_cases hy : y ∈ C.zeroLocus
    · let x : C.zeroLocus := ⟨y,hy⟩
      have hfmap : Ideal.map (actualHolomorphicGermPullback hf y).toRingHom
          (wholeChartStalkIdeal A (f y) (f y) (mem_chart_source _ _)) ≤ wholeChartStalkIdeal C y y (mem_chart_source _ _) := by
        rw [map_wholeChartStalkIdeal_actual_pullback hf A hA y]
        exact whole_mono hCA y
      apply Ideal.map_le_iff_le_comap.mpr
      intro r hr
      change actualHolomorphicGermPullback hg y r ∈ wholeChartStalkIdeal C y y (mem_chart_source _ _)
      have hid : wholeChartStalkIdeal A (f y) (f y) (mem_chart_source _ _) =
          wholeChartStalkIdeal A (g y) (g y) (mem_chart_source _ _) :=
        congrArg (fun p : N => wholeChartStalkIdeal A p p (mem_chart_source _ p)) (hp x)
      have hm := hfmap (Ideal.mem_map_of_mem (actualHolomorphicGermPullback hf y).toRingHom (hid.symm ▸ hr))
      exact Ideal.Quotient.eq_zero_iff_mem.mp
        ((hall x r).symm.trans (Ideal.Quotient.eq_zero_iff_mem.mpr hm))
    · rw [chartIdeal_eq_top_off_support C hC y hy]
      exact le_top
  intro y v hv
  have hh := GermIdeal.IsCoherent.holomorphicAt_mem hPB hv
  apply (coherent_mem_iff_whole_chart C hC y v hh).mpr
  have hm := (coherent_mem_iff_whole_chart _ hPB y v hh).mp hv
  rw [←map_wholeChartStalkIdeal_actual_pullback hg A hA y] at hm
  exact hle y hm

omit [IsComplexManifold n M] [IsComplexManifold m N] in
private theorem native_congr {f g : M → N}
    {hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f}
    {hg : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ g} (he : f = g) :
    ChartedSpace.locallyRingedSpaceMap f hf = ChartedSpace.locallyRingedSpaceMap g hg := by
  subst g
  rfl

private theorem base_square_of_lifts (C : GermIdeal n M) (hC : C.IsCoherent)
    {d b t : ℕ} {U : Opens (ComplexModel (d+t))} {V : Opens (ComplexModel b)}
    (φ : V → ComplexModel d) (hφ : ContMDiff 𝓘(ℂ,ComplexModel b) 𝓘(ℂ,ComplexModel d) ∞ φ)
    (A : GermIdeal (d+t) U) (hA : A.IsCoherent) (q : GermIdeal b V) (hq : q.IsCoherent)
    (F : quotientLocallyRingedSpace C hC ⟶ quotientLocallyRingedSpace A hA)
    (G : quotientLocallyRingedSpace C hC ⟶ quotientLocallyRingedSpace q hq)
    (hFG : F ≫ quotientInclusion A hA ≫ ChartedSpace.locallyRingedSpaceMap
        (fun p : U => tangentProjection d t p.val) ((tangentProjection d t).contDiff.contMDiff.comp contMDiff_subtype_val) =
      G ≫ quotientInclusion q hq ≫ ChartedSpace.locallyRingedSpaceMap φ hφ)
    (O : Opens M) (f : O → U) (g : O → V)
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel (d+t)) ∞ f)
    (hg : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel b) ∞ g)
    (hCA : GermIdeal.Le (GermIdeal.pullback (m := n) f A) (quotientOpenIdeal C O))
    (hCq : GermIdeal.Le (GermIdeal.pullback (m := n) g q) (quotientOpenIdeal C O))
    (hF : quotientMap hf _ (quotientOpenIdeal_coherent C hC O) A hA hCA = quotientOpenMap C hC O ≫ F)
    (hG : quotientMap hg _ (quotientOpenIdeal_coherent C hC O) q hq hCq = quotientOpenMap C hC O ≫ G) :
    quotientInclusion (quotientOpenIdeal C O) (quotientOpenIdeal_coherent C hC O) ≫
        ChartedSpace.locallyRingedSpaceMap ((fun p : U => tangentProjection d t p.val) ∘ f)
          (((tangentProjection d t).contDiff.contMDiff.comp contMDiff_subtype_val).comp hf) =
    quotientInclusion (quotientOpenIdeal C O) (quotientOpenIdeal_coherent C hC O) ≫
        ChartedSpace.locallyRingedSpaceMap (φ ∘ g) (hφ.comp hg) := by
  have hs := quotientMap_inclusion hf _ (quotientOpenIdeal_coherent C hC O) A hA hCA
  have hb := quotientMap_inclusion hg _ (quotientOpenIdeal_coherent C hC O) q hq hCq
  have hc : ChartedSpace.locallyRingedSpaceMap
      ((fun p : U => tangentProjection d t p.val) ∘ f)
      (((tangentProjection d t).contDiff.contMDiff.comp contMDiff_subtype_val).comp hf) =
      ChartedSpace.locallyRingedSpaceMap f hf ≫
        ChartedSpace.locallyRingedSpaceMap (fun p : U => tangentProjection d t p.val)
          ((tangentProjection d t).contDiff.contMDiff.comp contMDiff_subtype_val) :=
    ChartedSpace.locallyRingedSpace_comp
      (IM := 𝓘(ℂ,ComplexModel n)) (IN := 𝓘(ℂ,ComplexModel (d+t))) (IP := 𝓘(ℂ,ComplexModel d))
      hf ((tangentProjection d t).contDiff.contMDiff.comp contMDiff_subtype_val)
  have hd := ChartedSpace.locallyRingedSpace_comp
    (IM := 𝓘(ℂ,ComplexModel n)) (IN := 𝓘(ℂ,ComplexModel b)) (IP := 𝓘(ℂ,ComplexModel d)) hg hφ
  calc
    _ = (quotientOpenMap C hC O ≫ F) ≫ quotientInclusion A hA ≫
        ChartedSpace.locallyRingedSpaceMap (fun p : U => tangentProjection d t p.val)
          ((tangentProjection d t).contDiff.contMDiff.comp contMDiff_subtype_val) := by
      rw [hc,←Category.assoc,hs,hF,Category.assoc]
    _ = (quotientOpenMap C hC O ≫ G) ≫ quotientInclusion q hq ≫ ChartedSpace.locallyRingedSpaceMap φ hφ := by
      simpa only [Category.assoc] using congrArg (fun k => quotientOpenMap C hC O ≫ k) hFG
    _ = _ := by rw [←hG,←Category.assoc,←hb,Category.assoc,←hd]

/-- Local actual analytic factorization of an ORDINARY full test cone.
The actual O/H, WHOLE pulled-ideal law, and BOTH FULL projection triangles are constructed. -/
theorem exists_local_joint_factor (d b t : ℕ)
    (U : Opens (ComplexModel (d+t))) (V : Opens (ComplexModel b))
    (φ : V → ComplexModel d) (hφ : ContMDiff 𝓘(ℂ,ComplexModel b) 𝓘(ℂ,ComplexModel d) ∞ φ)
    (A : GermIdeal (d+t) U) (hA : A.IsCoherent) (q : GermIdeal b V) (hq : q.IsCoherent)
    (C : GermIdeal n M) (hC : C.IsCoherent)
    (F : quotientLocallyRingedSpace C hC ⟶ quotientLocallyRingedSpace A hA)
    (G : quotientLocallyRingedSpace C hC ⟶ quotientLocallyRingedSpace q hq)
    (hF : F ≫ quotientPointMap A hA = quotientPointMap C hC)
    (hG : G ≫ quotientPointMap q hq = quotientPointMap C hC)
    (hFG : F ≫ quotientInclusion A hA ≫ ChartedSpace.locallyRingedSpaceMap
        (fun p : U => tangentProjection d t p.val) ((tangentProjection d t).contDiff.contMDiff.comp contMDiff_subtype_val) =
      G ≫ quotientInclusion q hq ≫ ChartedSpace.locallyRingedSpaceMap φ hφ)
    (x : C.zeroLocus) :
    ∃ (O : Opens M) (_hxO : x.val ∈ O) (H : O → jointOpen d b t U V φ hφ)
      (hH : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel (b+t)) ∞ H)
      (hCJ : GermIdeal.Le (GermIdeal.pullback (m := n) H (jointIdeal d b t φ hφ A q)) (quotientOpenIdeal C O)),
      (quotientMap hH _ (quotientOpenIdeal_coherent C hC O) _ (jointIdeal_coherent d b t φ hφ A hA q hq) hCJ ≫
        sourceQuotientProjection d b t φ hφ A hA q hq = quotientOpenMap C hC O ≫ F) ∧
      (quotientMap hH _ (quotientOpenIdeal_coherent C hC O) _ (jointIdeal_coherent d b t φ hφ A hA q hq) hCJ ≫
        baseQuotientProjection d b t φ hφ A hA q hq = quotientOpenMap C hC O ≫ G) := by
  obtain ⟨OF,hxF,fF,hfF,hCAF,heF⟩ := exists_local_holomorphic_lift C hC A hA F hF x
  obtain ⟨OG,hxG,gG,hgG,hCqG,heG⟩ := exists_local_holomorphic_lift C hC q hq G hG x
  let P : Opens M := OF ⊓ OG
  have hxP : x.val ∈ P := ⟨hxF,hxG⟩
  let fP := fF ∘ openInclusion P OF inf_le_left
  let gP := gG ∘ openInclusion P OG inf_le_right
  have hfP := hfF.comp (openInclusion_holomorphic P OF inf_le_left)
  have hgP := hgG.comp (openInclusion_holomorphic P OG inf_le_right)
  obtain ⟨hCAP,heFP⟩ := restrict_lift C hC A hA F OF fF hfF hCAF heF P inf_le_left
  obtain ⟨hCqP,heGP⟩ := restrict_lift C hC q hq G OG gG hgG hCqG heG P inf_le_right
  have hbaseP := base_square_of_lifts C hC φ hφ A hA q hq F G hFG P fP gP hfP hgP hCAP hCqP heFP heGP
  let xP : P := ⟨x.val,hxP⟩
  have hxrange : x ∈ Set.range (quotientOpenMap C hC P).base := by
    rw [quotientOpenMap_range]
    exact hxP
  obtain ⟨yP,hyP⟩ := hxrange
  have hyval : yP.val = xP := Subtype.ext (congrArg (fun y : C.zeroLocus => y.val) hyP)
  have hxbase : tangentProjection d t (fP xP).val = φ (gP xP) := by
    have h := congrArg (fun k => k.base yP) hbaseP
    change tangentProjection d t (fP yP.val).val = φ (gP yP.val) at h
    simpa only [hyval] using h
  obtain ⟨O,hxO,hOP,H,hH,hpH,hnH⟩ := joint_geometry P U V φ hφ fP gP hfP hgP xP hxbase
  let f := fP ∘ openInclusion O P hOP
  let g := gP ∘ openInclusion O P hOP
  have hf := hfP.comp (openInclusion_holomorphic O P hOP)
  have hg := hgP.comp (openInclusion_holomorphic O P hOP)
  obtain ⟨hCA,heFO⟩ := restrict_lift C hC A hA F P fP hfP hCAP heFP O hOP
  obtain ⟨hCq,heGO⟩ := restrict_lift C hC q hq G P gP hgP hCqP heGP O hOP
  let D := quotientOpenIdeal C O
  have hD : D.IsCoherent := quotientOpenIdeal_coherent C hC O
  let k := sourceProjection d b t U V φ hφ ∘ H
  have hk := (sourceProjection_holomorphic d b t U V φ hφ).comp hH
  have hbaseO := base_square_of_lifts C hC φ hφ A hA q hq F G hFG O f g hf hg hCA hCq heFO heGO
  have hπk : (fun p : U => tangentProjection d t p.val) ∘ k = φ ∘ g := by
    funext y
    exact (projection_point_square d b t U V φ hφ (H y)).trans (congrArg φ (congrFun hpH y))
  have hbasefk : quotientInclusion D hD ≫ ChartedSpace.locallyRingedSpaceMap
        ((fun p : U => tangentProjection d t p.val) ∘ f)
        (((tangentProjection d t).contDiff.contMDiff.comp contMDiff_subtype_val).comp hf) =
      quotientInclusion D hD ≫ ChartedSpace.locallyRingedSpaceMap
        ((fun p : U => tangentProjection d t p.val) ∘ k)
        (((tangentProjection d t).contDiff.contMDiff.comp contMDiff_subtype_val).comp hk) :=
    hbaseO.trans (congrArg (fun l => quotientInclusion D hD ≫ l) (native_congr hπk.symm))
  obtain ⟨hpk,hall,hfull⟩ := block_congruence D hD hf hk hbasefk (fun y => (hnH y).symm)
  have hCAk := pullback_le_of_germ_congruence D hD A hA hf hk hCA hpk hall
  have hCqH : GermIdeal.Le (GermIdeal.pullback (m := n) (baseProjection d b t U V φ hφ ∘ H) q) D := by
    rw [hpH]
    exact hCq
  let J := jointIdeal d b t φ hφ A q
  have hJ : J.IsCoherent := jointIdeal_coherent d b t φ hφ A hA q hq
  have hCJ : GermIdeal.Le (GermIdeal.pullback (m := n) H J) D := by
    dsimp only [J]
    rw [jointIdeal,whole_pullback_sum hH _ _
      (isCoherent_pullback (sourceProjection_holomorphic d b t U V φ hφ) hA)
      (isCoherent_pullback (baseProjection_holomorphic d b t U V φ hφ) hq),
      ←whole_pullback_comp (sourceProjection_holomorphic d b t U V φ hφ) hH A hA,
      ←whole_pullback_comp (baseProjection_holomorphic d b t U V φ hφ) hH q hq]
    intro y v hv
    change IsInSpanAt (n := n) (fun z =>
      (GermIdeal.pullback (m := n) (sourceProjection d b t U V φ hφ ∘ H) A).mem y z ∨
      (GermIdeal.pullback (m := n) (baseProjection d b t U V φ hφ ∘ H) q).mem y z) y v at hv
    apply HomogenizedIdeal.mem_of_isInSpanAt hD
    apply IsInSpanAt.mono (S := fun z =>
      (GermIdeal.pullback (m := n) (sourceProjection d b t U V φ hφ ∘ H) A).mem y z ∨
      (GermIdeal.pullback (m := n) (baseProjection d b t U V φ hφ ∘ H) q).mem y z) ?_ hv
    intro z hz
    exact Or.elim hz (hCAk y z) (hCqH y z)
  let L := quotientMap hH D hD J hJ hCJ
  let S := sourceQuotientProjection d b t φ hφ A hA q hq
  let Pq := baseQuotientProjection d b t φ hφ A hA q hq
  have hLS : quotientInclusion D hD ≫ ChartedSpace.locallyRingedSpaceMap H hH = L ≫ quotientInclusion J hJ :=
    quotientMap_inclusion hH D hD J hJ hCJ
  have hS : quotientInclusion J hJ ≫ ChartedSpace.locallyRingedSpaceMap (sourceProjection d b t U V φ hφ)
      (sourceProjection_holomorphic d b t U V φ hφ) = S ≫ quotientInclusion A hA :=
    quotientMap_inclusion (sourceProjection_holomorphic d b t U V φ hφ) J hJ A hA
      (le_sumIdeal_left (isCoherent_pullback (sourceProjection_holomorphic d b t U V φ hφ) hA))
  have hPq : quotientInclusion J hJ ≫ ChartedSpace.locallyRingedSpaceMap (baseProjection d b t U V φ hφ)
      (baseProjection_holomorphic d b t U V φ hφ) = Pq ≫ quotientInclusion q hq :=
    quotientMap_inclusion (baseProjection_holomorphic d b t U V φ hφ) J hJ q hq
      (le_sumIdeal_right (isCoherent_pullback (baseProjection_holomorphic d b t U V φ hφ) hq))
  refine ⟨O,hxO,H,hH,hCJ,?_,?_⟩
  · change L ≫ S = quotientOpenMap C hC O ≫ F
    apply (cancel_mono (quotientInclusion A hA)).mp
    calc
      _ = quotientInclusion D hD ≫ ChartedSpace.locallyRingedSpaceMap k hk := by
        rw [Category.assoc,←hS,←Category.assoc,←hLS,Category.assoc,←ChartedSpace.locallyRingedSpace_comp]
      _ = quotientInclusion D hD ≫ ChartedSpace.locallyRingedSpaceMap f hf := hfull.symm
      _ = _ := by rw [quotientMap_inclusion hf D hD A hA hCA,heFO]
  · change L ≫ Pq = quotientOpenMap C hC O ≫ G
    apply (cancel_mono (quotientInclusion q hq)).mp
    calc
      _ = quotientInclusion D hD ≫ ChartedSpace.locallyRingedSpaceMap
          (baseProjection d b t U V φ hφ ∘ H) ((baseProjection_holomorphic d b t U V φ hφ).comp hH) := by
        rw [Category.assoc,←hPq,←Category.assoc,←hLS,Category.assoc,←ChartedSpace.locallyRingedSpace_comp]
      _ = quotientInclusion D hD ≫ ChartedSpace.locallyRingedSpaceMap g hg :=
        congrArg (fun l => quotientInclusion D hD ≫ l) (native_congr hpH)
      _ = _ := by rw [quotientMap_inclusion hg D hD q hq hCq,heGO]

end
end Hironaka.HironakaAnalyticBaseChangeLocalFactorization
