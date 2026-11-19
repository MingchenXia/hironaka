import Hironaka.Resolution.HironakaChowRelativeGraphPresentation
import Hironaka.Resolution.HironakaAnalyticTestBaseChangeUniversality
import Mathlib.Geometry.RingedSpace.OpenImmersion

/-! Actual graph-coordinate elimination for the original raw analytic joint
model. Blueprint first: `hironaka-graph-basechange-elimination.tex`.
The real domains, whole nonradical ideals and original maps are retained.
Geometric P8 saturation and its canonical object identification are separate
consumers; no future chart or kernel certificate is an input here. -/
set_option autoImplicit false
noncomputable section

open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaGraphBaseChangeElimination

open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaRelativeNormalIdeal HironakaActualCentreJointJets
  HironakaActualIntrinsicStableAmbientIso HironakaActualJointBaseFibre
  HironakaChowRelativeGraphPresentation HironakaActualWholeStalkHolomorphicPullback
  HironakaHolomorphicJetChartInvariance HironakaHolomorphicJetRankLoci
  HironakaHolomorphicJetMonomialSpan HironakaActualOpenIntrinsicHS
  HironakaActualBiholomorphicWholeStalkHS HironakaActualProjectionIntrinsicHS
  HironakaActualAnalyticSubspaceMaps HironakaSmoothCentreRealDomainActualIdealPresheaf
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaActualAnalyticSubspaceOpenRestriction
  HironakaAnalyticBaseChangeQuotientModel HironakaNonreducedAnalyticQuotientModel
  HironakaNonreducedAnalyticQuotientMorphism HironakaNonreducedQuotientNeighborhoodLifting
  HironakaNonreducedQuotientGermLifting
  RestrictedIdealExtension GermIdealPullbackCalculus RelativePrincipalizationSpan InvertibleIdealQuotient

section NativeAux

/-! Consumed private whole-pullback and185 coordinate-congruence proofs from
accepted local-factor650. These are reused support for the actual new raw
inverse construction, with zero repeated engine credit. -/

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

private theorem aux_tangent_coordinate (d t : ℕ) (i : Fin d) :
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
  simpa only [AlgHom.comp_apply,tangent_on_open_germ,aux_tangent_coordinate] using he

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

end NativeAux

private theorem whole_sum_le {a : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel a) M] [IsComplexManifold a M]
    (A B C : GermIdeal a M) (hC : C.IsCoherent) (hAC : A.Le C) (hBC : B.Le C) :
    (sumIdeal A B).Le C := by
  intro x g hg
  change IsInSpanAt (n := a) (fun s => A.mem x s ∨ B.mem x s) x g at hg
  apply HomogenizedIdeal.mem_of_isInSpanAt hC
  exact IsInSpanAt.mono (fun s hs => hs.elim (hAC x s) (hBC x s)) hg

variable {d n : ℕ} (X : Opens (ComplexModel n)) (Y : Opens (ComplexModel d))

/-- The literal real open containing the original graph, in base-first order. -/
def graphOpen : Opens (ComplexModel (d+n)) :=
  ⟨(tangentProjection d n) ⁻¹' Y ∩ (actualJointNormalProjection d n) ⁻¹' X,
    (Y.isOpen.preimage (tangentProjection d n).continuous).inter
      (X.isOpen.preimage (actualJointNormalProjection d n).continuous)⟩

def graphSource : graphOpen X Y → X :=
  fun w => ⟨actualJointNormalProjection d n w.val,w.property.2⟩

def graphTarget : graphOpen X Y → Y :=
  fun w => ⟨tangentProjection d n w.val,w.property.1⟩

theorem graphSource_holomorphic :
    ContMDiff 𝓘(ℂ,ComplexModel (d+n)) 𝓘(ℂ,ComplexModel n) ∞ (graphSource X Y) := by
  apply (ContMDiff.subtypeVal_comp_iff X _).mp
  exact (actualJointNormalProjection d n).contDiff.contMDiff.comp contMDiff_subtype_val

theorem graphTarget_holomorphic :
    ContMDiff 𝓘(ℂ,ComplexModel (d+n)) 𝓘(ℂ,ComplexModel d) ∞ (graphTarget X Y) := by
  apply (ContMDiff.subtypeVal_comp_iff Y _).mp
  exact (tangentProjection d n).contDiff.contMDiff.comp contMDiff_subtype_val

variable (f : X → Y)
  (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel d) ∞ f)

/-- Original graph insertion; f is used only on its actual open X. -/
def graphMap (x : X) : graphOpen X Y :=
  ⟨join (f x).val x.val,by
    change tangentProjection d n (join (f x).val x.val) ∈ Y ∧
      actualJointNormalProjection d n (join (f x).val x.val) ∈ X
    simpa only [first_join,second_join] using And.intro (f x).property x.property⟩

include hf in
theorem graphMap_holomorphic :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel (d+n)) ∞ (graphMap X Y f) := by
  apply (ContMDiff.subtypeVal_comp_iff (graphOpen X Y) _).mp
  exact ((tangentInclusion d n).contDiff.contMDiff.comp
    (contMDiff_subtype_val.comp hf)).add
      ((actualJointNormalInclusion d n).contDiff.contMDiff.comp contMDiff_subtype_val)

theorem graphSource_graphMap (x : X) : graphSource X Y (graphMap X Y f x) = x := by
  apply Subtype.ext
  exact second_join _ _

theorem graphTarget_graphMap (x : X) : graphTarget X Y (graphMap X Y f x) = f x := by
  apply Subtype.ext
  exact first_join _ _

/-- The actual finite graph equations on the same real open. -/
def graphEquation (i : Fin d) (w : graphOpen X Y) : ℂ :=
  (graphTarget X Y w).val i - (f (graphSource X Y w)).val i

include hf in
theorem graphEquation_holomorphic (i : Fin d) :
    ContMDiff 𝓘(ℂ,ComplexModel (d+n)) 𝓘(ℂ,ℂ) ∞ (graphEquation X Y f i) :=
  ((EuclideanSpace.proj i).contDiff.contMDiff.comp
    (contMDiff_subtype_val.comp (graphTarget_holomorphic X Y))).sub
      ((EuclideanSpace.proj i).contDiff.contMDiff.comp
        (contMDiff_subtype_val.comp (hf.comp (graphSource_holomorphic X Y))))

def graphEquations : GermIdeal (d+n) (graphOpen X Y) where
  mem w g := IsInSpanAt (n := d+n) (· ∈ range (graphEquation X Y f)) w g

include hf in
theorem graphEquations_coherent : (graphEquations X Y f).IsCoherent := by
  intro w
  refine ⟨univ,isOpen_univ,mem_univ _,d,graphEquation X Y f,?_,?_⟩
  · intro i
    exact ((graphEquation_holomorphic X Y f hf i).mdifferentiable (by simp)).mdifferentiableOn
  · intro z _ g
    rfl

/-- Whole original source equations plus the actual finite graph equations. -/
def graphIdeal (I : GermIdeal n X) : GermIdeal (d+n) (graphOpen X Y) :=
  sumIdeal (GermIdeal.pullback (graphSource X Y) I) (graphEquations X Y f)

include hf in
theorem graphIdeal_coherent (I : GermIdeal n X) (hI : I.IsCoherent) :
    (graphIdeal X Y f I).IsCoherent :=
  isCoherent_sumIdeal (isCoherent_pullback (graphSource_holomorphic X Y) hI)
    (graphEquations_coherent X Y f hf)

private theorem graphSource_translated (w : graphOpen X Y) :
    actualTranslatedMap (graphSource X Y) w =ᶠ[𝓝 (0 : ComplexModel (d+n))]
      actualJointNormalProjection d n := by
  filter_upwards [actualTranslatedMap_val_eventually (graphOpen X Y) w] with z hz
  change actualJointNormalProjection d n
      (((chartAt (ComplexModel (d+n)) w).symm
        (z+(chartAt (ComplexModel (d+n)) w) w)).val) -
      actualJointNormalProjection d n w.val = _
  rw [← map_sub]
  exact congrArg (actualJointNormalProjection d n) hz

private theorem graphSource_germ (w : graphOpen X Y) :
    actualHolomorphicGermPullback (graphSource_holomorphic X Y) w = jointNormalPullback d n := by
  apply AlgHom.ext
  intro g
  induction g using HolGerm.induction_on with
  | h a ha =>
    unfold actualHolomorphicGermPullback jointNormalPullback
    rw [compAlgHom_mk,compAlgHom_mk]
    exact HolGerm.mk_eq_mk_iff.mpr
      ((graphSource_translated X Y w).mono fun z hz => congrArg a hz)

include hf in
private theorem graphEquation_holomorphicAt (i : Fin d) (w : graphOpen X Y) :
    HolomorphicAt (d+n) (graphEquation X Y f i) w :=
  Eventually.of_forall fun _ =>
    ((graphEquation_holomorphic X Y f hf i).mdifferentiable (by simp)).mdifferentiableAt

private theorem graphEquations_whole (w : graphOpen X Y) :
    wholeChartStalkIdeal (graphEquations X Y f) w w (mem_chart_source _ w) =
      Ideal.span (range fun i : Fin d => chartTranslatedGerm w w (mem_chart_source _ w)
        (graphEquation X Y f i) (graphEquation_holomorphicAt X Y f hf i w)) :=
  wholeChartStalkIdeal_eq_actual_generator_span (graphEquations X Y f) w
    (graphEquation X Y f) (fun i => graphEquation_holomorphicAt X Y f hf i w)
      (fun _ => Iff.rfl)

private theorem graphEquation_chart (x : X) (i : Fin d) :
    chartTranslatedGerm (graphMap X Y f x) (graphMap X Y f x)
        (mem_chart_source _ _) (graphEquation X Y f i)
        (graphEquation_holomorphicAt X Y f hf i _) =
      coordinateGerm (i.castAdd n) - jointNormalPullback d n
        (compAlgHom (actualTranslatedMap f x) (actualTranslatedMap_holomorphic hf x)
          (actualTranslatedMap_zero f x) (coordinateGerm i)) := by
  let p := graphMap X Y f x
  unfold chartTranslatedGerm translatedGerm coordinateGerm jointNormalPullback
  rw [compAlgHom_mk,compAlgHom_mk,← HolGerm.mk_sub]
  apply HolGerm.mk_eq_mk_iff.mpr
  have hc := actualTranslatedMap_comp_eventually (n := d) (m := n) (k := d+n)
    f (graphSource_holomorphic X Y) p
  filter_upwards [hc,graphSource_translated X Y p,
    actualTranslatedMap_val_eventually (graphOpen X Y) p] with z hc hs hv
  simp only [Function.comp_apply] at hc
  rw [hs] at hc
  have hx : graphSource X Y p = x := graphSource_graphMap X Y f x
  rw [hx] at hc
  let w := (chartAt (ComplexModel (d+n)) p).symm
    (z+(chartAt (ComplexModel (d+n)) p) p)
  have hcomp : (f (graphSource X Y w)).val - (f x).val =
      actualTranslatedMap f x (actualJointNormalProjection d n z) := by
    change (f (graphSource X Y w)).val - (f (graphSource X Y p)).val = _ at hc
    simpa only [hx] using hc
  have hval : w.val - p.val = z := hv
  have hp : p.val (i.castAdd n) = (f x).val i := by
    change (join (f x).val x.val) (i.castAdd n) = _
    simp [HironakaActualIntrinsicStableAmbientIso.join]
  have hv' : w.val (i.castAdd n) - (f x).val i = z (i.castAdd n) := by
    have h := congrArg (fun v : ComplexModel (d+n) => v (i.castAdd n)) hval
    change w.val (i.castAdd n) - p.val (i.castAdd n) = _ at h
    rwa [hp] at h
  have hc' : (f (graphSource X Y w)).val i - (f x).val i =
      actualTranslatedMap f x (actualJointNormalProjection d n z) i :=
    congrArg (fun v : ComplexModel d => v i) hcomp
  change w.val (i.castAdd n) - (f (graphSource X Y w)).val i =
    z (i.castAdd n) - actualTranslatedMap f x (actualJointNormalProjection d n z) i
  linear_combination hv' - hc'

/-- The actual finite original graph functions give the ENTIRE native chart
ideal, with the actual translated f and the whole source ideal. -/
theorem whole_graph_chart (I : GermIdeal n X) (hI : I.IsCoherent) (x : X) :
    wholeChartStalkIdeal (graphIdeal X Y f I) (graphMap X Y f x)
        (graphMap X Y f x) (mem_chart_source _ _) =
      relativeGraphIdeal d n (actualTranslatedMap f x)
        (actualTranslatedMap_holomorphic hf x)
        (wholeChartStalkIdeal I x x (mem_chart_source _ x)) := by
  have hpull : relativeSourcePullback d n = jointNormalPullback d n := by
    apply AlgHom.ext
    exact relativeSourcePullback_eq_normalPullback d n
  unfold graphIdeal
  rw [wholeChartStalkIdeal_sum _ _
      (isCoherent_pullback (graphSource_holomorphic X Y) hI)
      (graphEquations_coherent X Y f hf),
    ←map_wholeChartStalkIdeal_actual_pullback (graphSource_holomorphic X Y) I hI,
    graphSource_germ,graphSource_graphMap,relativeGraphIdeal,hpull,
    graphEquations_whole X Y f hf,
    relativeGraphEquations_eq_span d n (actualTranslatedMap f x)
      (actualTranslatedMap_holomorphic hf x) (actualTranslatedMap_zero f x)]
  apply congrArg (fun L : Ideal (HolGerm (ComplexModel (d+n))) =>
    Ideal.map (jointNormalPullback d n).toRingHom
      (wholeChartStalkIdeal I x x (mem_chart_source _ x)) ⊔ L)
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  exact graphEquation_chart X Y f hf x i

private theorem graphMap_translated (x : X) :
    actualTranslatedMap (n := d+n) (m := n) (graphMap X Y f) x =ᶠ[𝓝 (0 : ComplexModel n)]
      fun z => join (actualTranslatedMap (n := d) (m := n) f x z) z := by
  filter_upwards [actualTranslatedMap_val_eventually X x] with z hz
  let w := (chartAt (ComplexModel n) x).symm (z+(chartAt (ComplexModel n) x) x)
  change join (f w).val w.val - join (f x).val x.val =
    join ((f w).val-(f x).val) z
  have hv : w.val-x.val=z := hz
  rw [←hv]
  simp only [HironakaActualIntrinsicStableAmbientIso.join,map_sub]
  abel

private theorem graphMap_germ_normal (x : X) (g : HolGerm (ComplexModel n)) :
    actualHolomorphicGermPullback (graphMap_holomorphic X Y f hf) x
      (jointNormalPullback d n g) = g := by
  induction g using HolGerm.induction_on with
  | h a ha =>
    unfold actualHolomorphicGermPullback jointNormalPullback
    rw [compAlgHom_mk,compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact (graphMap_translated X Y f x).mono fun z hz => by
      change a (actualJointNormalProjection d n (actualTranslatedMap (graphMap X Y f) x z)) = a z
      rw [hz,second_join]

private theorem graphMap_germ_base (x : X) (g : HolGerm (ComplexModel d)) :
    actualHolomorphicGermPullback (graphMap_holomorphic X Y f hf) x
      (tangentPullback d n g) = actualHolomorphicGermPullback hf x g := by
  induction g using HolGerm.induction_on with
  | h a ha =>
    unfold actualHolomorphicGermPullback tangentPullback
    rw [compAlgHom_mk,compAlgHom_mk,compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact (graphMap_translated X Y f x).mono fun z hz => by
      change a (tangentProjection d n (actualTranslatedMap (graphMap X Y f) x z)) =
        a (actualTranslatedMap f x z)
      rw [hz,first_join]

private theorem tangent_coordinate (i : Fin d) :
    tangentPullback d n (coordinateGerm i) = coordinateGerm (i.castAdd n) := by
  unfold tangentPullback coordinateGerm
  rw [compAlgHom_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun _ => rfl

private theorem normal_coordinate (i : Fin n) :
    jointNormalPullback d n (coordinateGerm i) = coordinateGerm (i.natAdd d) := by
  unfold jointNormalPullback coordinateGerm
  rw [compAlgHom_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun _ => rfl

/-- The actual native graph map induces the EXISTING entire graph trace,
rather than an independently transported quotient action. -/
private theorem graphMap_germ (x : X) :
    actualHolomorphicGermPullback (graphMap_holomorphic X Y f hf) x =
      relativeGraphTrace d n (actualTranslatedMap f x)
        (actualTranslatedMap_holomorphic hf x) (actualTranslatedMap_zero f x) := by
  let F := actualTranslatedMap (n := d) (m := n) f x
  let hF := actualTranslatedMap_holomorphic hf x
  let hF0 := actualTranslatedMap_zero (n := d) (m := n) f x
  let T := relativeGraphTrace d n F hF hF0
  let : IsNoetherianRing (HolGerm (ComplexModel n)) := isNoetherianRing_holGerm_euclidean n
  have hT : Function.Surjective T := fun g =>
    ⟨relativeSourcePullback d n g,relativeGraphTrace_sourcePullback d n F hF hF0 g⟩
  let : IsLocalHom T.toRingHom := IsLocalHom.of_surjective _ hT
  apply local_algHom_ext_coordinates (d+n)
    (actualHolomorphicGermPullback (graphMap_holomorphic X Y f hf) x) T
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [←tangent_coordinate (n := n) j,
      graphMap_germ_base X Y f hf x (coordinateGerm j)]
    exact (relativeGraphTrace_basePullback d n F hF hF0 (coordinateGerm j)).symm
  · rw [←normal_coordinate (d := d) j,
      graphMap_germ_normal X Y f hf x (coordinateGerm j)]
    rw [←relativeSourcePullback_eq_normalPullback d n]
    exact (relativeGraphTrace_sourcePullback d n F hF hF0 (coordinateGerm j)).symm

include hf in
private theorem graphMap_ideal (I : GermIdeal n X) (hI : I.IsCoherent) :
    (GermIdeal.pullback (graphMap X Y f) (graphIdeal X Y f I)).Le I := by
  let A := graphIdeal X Y f I
  let hA := graphIdeal_coherent X Y f hf I hI
  let hP := isCoherent_pullback (graphMap_holomorphic X Y f hf) hA
  intro x g hg
  have hhol := GermIdeal.IsCoherent.holomorphicAt_mem hP hg
  apply (coherent_mem_iff_whole_chart I hI x g hhol).mpr
  have hm := (coherent_mem_iff_whole_chart _ hP x g hhol).mp hg
  have hw : wholeChartStalkIdeal
      (GermIdeal.pullback (graphMap X Y f) A) x x (mem_chart_source _ x) ≤
      wholeChartStalkIdeal I x x (mem_chart_source _ x) := by
    rw [←map_wholeChartStalkIdeal_actual_pullback
        (graphMap_holomorphic X Y f hf) A hA x]
    change Ideal.map
      (actualHolomorphicGermPullback (graphMap_holomorphic X Y f hf) x).toRingHom
      (wholeChartStalkIdeal (graphIdeal X Y f I) (graphMap X Y f x)
        (graphMap X Y f x) (mem_chart_source _ _)) ≤ _
    rw [whole_graph_chart X Y f hf I hI x,graphMap_germ X Y f hf x,
      relativeGraphIdeal_eq_comap d n (actualTranslatedMap f x)
        (actualTranslatedMap_holomorphic hf x) (actualTranslatedMap_zero f x)]
    exact Ideal.map_comap_le
  exact hw hm

/-- The native graph morphism is made by the original quotient factory,
after deriving whole ideal preservation from the actual graph calculation. -/
def graphQuotientMap (I : GermIdeal n X) (hI : I.IsCoherent) :
    quotientLocallyRingedSpace I hI ⟶
      quotientLocallyRingedSpace (graphIdeal X Y f I) (graphIdeal_coherent X Y f hf I hI) :=
  quotientMap (graphMap_holomorphic X Y f hf) I hI _
    (graphIdeal_coherent X Y f hf I hI) (graphMap_ideal X Y f hf I hI)

private theorem graphSource_support (I : GermIdeal n X) (hI : I.IsCoherent)
    (w : (graphIdeal X Y f I).zeroLocus) : graphSource X Y w.val ∈ I.zeroLocus := by
  intro g hg
  have hp : (GermIdeal.pullback (m := d+n) (graphSource X Y) I).mem w.val (g ∘ graphSource X Y) := by
    apply (RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff
      (n := n) (m := d+n) (f := graphSource X Y)).mpr
    exact InvertibleIdealQuotient.isInSpanAt_self
      ⟨g,hg,rfl⟩ ((GermIdeal.IsCoherent.holomorphicAt_mem hI hg).comp_contMDiff
        (Eventually.of_forall fun _ => (graphSource_holomorphic X Y).contMDiffAt))
  exact w.property (g ∘ graphSource X Y)
    (le_sumIdeal_left (isCoherent_pullback (graphSource_holomorphic X Y) hI) _ _ hp)

include hf in
private theorem graphTarget_support (I : GermIdeal n X)
    (w : (graphIdeal X Y f I).zeroLocus) :
    graphTarget X Y w.val = f (graphSource X Y w.val) := by
  apply Subtype.ext
  ext i
  have hm : (graphEquations X Y f).mem w.val (graphEquation X Y f i) :=
    CoherentIdealColon.isInSpanAt_range_self
      (fun j => graphEquation_holomorphicAt X Y f hf j w.val) i
  have hz := w.property (graphEquation X Y f i)
    (le_sumIdeal_right (graphEquations_coherent X Y f hf) _ _ hm)
  exact sub_eq_zero.mp hz

include hf in
private theorem graphMap_source_support (I : GermIdeal n X)
    (w : (graphIdeal X Y f I).zeroLocus) :
    graphMap X Y f (graphSource X Y w.val) = w.val := by
  apply Subtype.ext
  change join (f (graphSource X Y w.val)).val
    (actualJointNormalProjection d n w.val.val) = w.val.val
  rw [←graphTarget_support X Y f hf I w]
  exact join_projections w.val.val

private def graphSupportHomeomorph (I : GermIdeal n X) (hI : I.IsCoherent) :
    I.zeroLocus ≃ₜ (graphIdeal X Y f I).zeroLocus where
  toFun := quotientTopMap (graphMap_holomorphic X Y f hf) I _
    (graphIdeal_coherent X Y f hf I hI) (graphMap_ideal X Y f hf I hI)
  invFun w := ⟨graphSource X Y w.val,graphSource_support X Y f I hI w⟩
  left_inv x := by
    apply Subtype.ext
    exact graphSource_graphMap X Y f x.val
  right_inv w := by
    apply Subtype.ext
    exact graphMap_source_support X Y f hf I w
  continuous_toFun := Continuous.subtype_mk
    ((graphMap_holomorphic X Y f hf).continuous.comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk
    ((graphSource_holomorphic X Y).continuous.comp continuous_subtype_val) _

private theorem graphQuotientMap_chart_mk (I : GermIdeal n X) (hI : I.IsCoherent)
    (x : I.zeroLocus) (g : HolGerm (ComplexModel (d+n))) :
    quotientStalkChartEquiv I hI x ((graphQuotientMap X Y f hf I hI).stalkMap x
      ((quotientStalkChartEquiv (graphIdeal X Y f I) (graphIdeal_coherent X Y f hf I hI)
        ((graphQuotientMap X Y f hf I hI).base x)).symm
        (Ideal.Quotient.mk (wholeChartStalkIdeal (graphIdeal X Y f I)
          (graphMap X Y f x.val) (graphMap X Y f x.val) (mem_chart_source _ _)) g))) =
      Ideal.Quotient.mk (wholeChartStalkIdeal I x.val x.val (mem_chart_source _ _))
        (relativeGraphTrace d n (actualTranslatedMap f x.val)
          (actualTranslatedMap_holomorphic hf x.val) (actualTranslatedMap_zero f x.val) g) := by
  let A := graphIdeal X Y f I
  let hA := graphIdeal_coherent X Y f hf I hI
  let y : A.zeroLocus := quotientTopMap (graphMap_holomorphic X Y f hf) I A hA
    (graphMap_ideal X Y f hf I hI) x
  let s := (actualStalkChartEquiv (n := d+n) (graphMap X Y f x.val)).symm g
  change quotientStalkChartEquiv I hI x
    ((quotientMap (graphMap_holomorphic X Y f hf) I hI A hA
      (graphMap_ideal X Y f hf I hI)).stalkMap x
      ((quotientStalkChartEquiv A hA y).symm
        (Ideal.Quotient.mk (wholeChartStalkIdeal A (graphMap X Y f x.val)
          (graphMap X Y f x.val) (mem_chart_source _ _)) g))) = _
  have hchart : (quotientStalkChartEquiv A hA y).symm
      (Ideal.Quotient.mk (wholeChartStalkIdeal A (graphMap X Y f x.val)
        (graphMap X Y f x.val) (mem_chart_source _ _)) g) =
      (quotientInclusion A hA).stalkMap y s := by
    apply (quotientStalkChartEquiv A hA y).injective
    rw [RingEquiv.apply_symm_apply]
    simp only [quotientStalkChartEquiv,RingEquiv.trans_apply,quotientInclusion_stalk]
    change Ideal.Quotient.mk (wholeChartStalkIdeal A (graphMap X Y f x.val)
      (graphMap X Y f x.val) (mem_chart_source _ _)) g = Ideal.Quotient.mk _
      (actualStalkChartEquiv (n := d+n) (graphMap X Y f x.val) s)
    dsimp only [s]
    rw [RingEquiv.apply_symm_apply]
  have hwhole : (quotientStalkWholeEquiv A hA y).symm
      (Ideal.Quotient.mk (actualWholeSheafStalkIdeal A (graphMap X Y f x.val)) s) =
      (quotientInclusion A hA).stalkMap y s := by
    apply (quotientStalkWholeEquiv A hA y).injective
    rw [RingEquiv.apply_symm_apply,quotientInclusion_stalk]
    rfl
  rw [hchart]
  have hm := quotientMap_stalk_mk (graphMap_holomorphic X Y f hf) I hI A hA
    (graphMap_ideal X Y f hf I hI) x s
  rw [hwhole] at hm
  simp only [quotientStalkChartEquiv,RingEquiv.trans_apply]
  rw [hm]
  change Ideal.Quotient.mk _ (actualStalkChartEquiv (n := n) x.val
    ((ChartedSpace.locallyRingedSpaceMap (graphMap X Y f)
      (graphMap_holomorphic X Y f hf)).stalkMap x.val s)) = _
  rw [actualNativeStalk_chart_pullback]
  dsimp only [s]
  rw [RingEquiv.apply_symm_apply,graphMap_germ X Y f hf x.val]

private def graphStalkEquiv (I : GermIdeal n X) (hI : I.IsCoherent) (x : I.zeroLocus) :
    ((quotientLocallyRingedSpace (graphIdeal X Y f I) (graphIdeal_coherent X Y f hf I hI)).presheaf.stalk
      ((graphQuotientMap X Y f hf I hI).base x)).carrier ≃+*
      ((quotientLocallyRingedSpace I hI).presheaf.stalk x).carrier :=
  (((quotientStalkChartEquiv _ (graphIdeal_coherent X Y f hf I hI)
    ((graphQuotientMap X Y f hf I hI).base x)).trans
      (Ideal.quotEquivOfEq (whole_graph_chart X Y f hf I hI x.val))).trans
        (relativeGraphQuotientEquiv d n (actualTranslatedMap f x.val)
          (actualTranslatedMap_holomorphic hf x.val) (actualTranslatedMap_zero f x.val)
            (wholeChartStalkIdeal I x.val x.val (mem_chart_source _ _)))).trans
              (quotientStalkChartEquiv I hI x).symm

private theorem graphStalkEquiv_apply (I : GermIdeal n X) (hI : I.IsCoherent)
    (x : I.zeroLocus) (r : ((quotientLocallyRingedSpace (graphIdeal X Y f I)
      (graphIdeal_coherent X Y f hf I hI)).presheaf.stalk
        ((graphQuotientMap X Y f hf I hI).base x)).carrier) :
    graphStalkEquiv X Y f hf I hI x r = (graphQuotientMap X Y f hf I hI).stalkMap x r := by
  let e := quotientStalkChartEquiv (graphIdeal X Y f I)
    (graphIdeal_coherent X Y f hf I hI) ((graphQuotientMap X Y f hf I hI).base x)
  obtain ⟨g,hg⟩ := Ideal.Quotient.mk_surjective (e r)
  have hr : r = e.symm (Ideal.Quotient.mk _ g) := by
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    exact hg.symm
  rw [hr]
  apply (quotientStalkChartEquiv I hI x).injective
  have he : quotientStalkChartEquiv I hI x
      (graphStalkEquiv X Y f hf I hI x (e.symm (Ideal.Quotient.mk _ g))) =
      Ideal.Quotient.mk (wholeChartStalkIdeal I x.val x.val (mem_chart_source _ _))
        (relativeGraphTrace d n (actualTranslatedMap f x.val)
          (actualTranslatedMap_holomorphic hf x.val) (actualTranslatedMap_zero f x.val) g) := by
    simp only [graphStalkEquiv,RingEquiv.trans_apply,RingEquiv.apply_symm_apply,e]
    exact relativeGraphQuotientEquiv_mk d n (actualTranslatedMap f x.val)
      (actualTranslatedMap_holomorphic hf x.val) (actualTranslatedMap_zero f x.val) _ g
  exact he.trans (graphQuotientMap_chart_mk X Y f hf I hI x g).symm

/-- Actual graph elimination as a FULL native isomorphism. The whole graph
ideal, support inverse and all stalk isomorphisms are derived internally. -/
def graphQuotientIso (I : GermIdeal n X) (hI : I.IsCoherent) :
    quotientLocallyRingedSpace I hI ≅
      quotientLocallyRingedSpace (graphIdeal X Y f I) (graphIdeal_coherent X Y f hf I hI) := by
  let F := graphQuotientMap X Y f hf I hI
  let e := graphSupportHomeomorph X Y f hf I hI
  let : ∀ x : I.zeroLocus, IsIso (F.stalkMap x) := fun x => by
    have he : F.stalkMap x = (graphStalkEquiv X Y f hf I hI x).toCommRingCatIso.hom := by
      apply CommRingCat.hom_ext
      ext r
      exact (graphStalkEquiv_apply X Y f hf I hI x r).symm
    rw [he]
    infer_instance
  have hopen : Topology.IsOpenEmbedding F.base := e.isOpenEmbedding
  let : LocallyRingedSpace.IsOpenImmersion F := LocallyRingedSpace.IsOpenImmersion.of_stalk_iso F hopen
  let : Epi F.base := ConcreteCategory.epi_of_surjective _ e.surjective
  let : IsIso F := LocallyRingedSpace.IsOpenImmersion.to_iso F
  exact asIso F

/-- The FULL ambient square uses the literal original graph insertion. -/
theorem graphQuotientIso_ambient (I : GermIdeal n X) (hI : I.IsCoherent) :
    (graphQuotientIso X Y f hf I hI).hom ≫
      quotientInclusion (graphIdeal X Y f I) (graphIdeal_coherent X Y f hf I hI) =
    quotientInclusion I hI ≫ ChartedSpace.locallyRingedSpaceMap (graphMap X Y f)
      (graphMap_holomorphic X Y f hf) :=
  (quotientMap_inclusion (graphMap_holomorphic X Y f hf) I hI _
    (graphIdeal_coherent X Y f hf I hI) (graphMap_ideal X Y f hf I hI)).symm

private theorem nativeMap_congr {a c : ℕ} {M N : Type}
    [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (ComplexModel a) M] [ChartedSpace (ComplexModel c) N]
    {u v : M → N} {hu : ContMDiff 𝓘(ℂ,ComplexModel a) 𝓘(ℂ,ComplexModel c) ∞ u}
    {hv : ContMDiff 𝓘(ℂ,ComplexModel a) 𝓘(ℂ,ComplexModel c) ∞ v} (he : u = v) :
    ChartedSpace.locallyRingedSpaceMap u hu = ChartedSpace.locallyRingedSpaceMap v hv := by
  subst v
  rfl

/-- FULL comparison with the original source projection. -/
theorem graphQuotientIso_source (I : GermIdeal n X) (hI : I.IsCoherent) :
    (graphQuotientIso X Y f hf I hI).hom ≫
      quotientInclusion (graphIdeal X Y f I) (graphIdeal_coherent X Y f hf I hI) ≫
        ChartedSpace.locallyRingedSpaceMap (graphSource X Y) (graphSource_holomorphic X Y) =
      quotientInclusion I hI := by
  rw [←Category.assoc,graphQuotientIso_ambient,Category.assoc,
    ←ChartedSpace.locallyRingedSpace_comp]
  have he : graphSource X Y ∘ graphMap X Y f = id := funext (graphSource_graphMap X Y f)
  have hm := nativeMap_congr (a := n) (c := n) (hu :=
    (graphSource_holomorphic X Y).comp (graphMap_holomorphic X Y f hf))
      (hv := contMDiff_id) he
  rw [hm,ChartedSpace.locallyRingedSpace_id,Category.comp_id]

/-- FULL comparison with the original f and its actual base action. -/
theorem graphQuotientIso_base (I : GermIdeal n X) (hI : I.IsCoherent) :
    (graphQuotientIso X Y f hf I hI).hom ≫
      quotientInclusion (graphIdeal X Y f I) (graphIdeal_coherent X Y f hf I hI) ≫
        ChartedSpace.locallyRingedSpaceMap (graphTarget X Y) (graphTarget_holomorphic X Y) =
      quotientInclusion I hI ≫ ChartedSpace.locallyRingedSpaceMap f hf := by
  rw [←Category.assoc,graphQuotientIso_ambient,Category.assoc,
    ←ChartedSpace.locallyRingedSpace_comp]
  congr 1
  exact nativeMap_congr (funext (graphTarget_graphMap X Y f))

/-- ALL native graph-stalk numerator classes retain literal graph substitution. -/
theorem graphQuotientIso_stalk_mk (I : GermIdeal n X) (hI : I.IsCoherent)
    (x : I.zeroLocus) (g : HolGerm (ComplexModel (d+n))) :
    quotientStalkChartEquiv I hI x ((graphQuotientIso X Y f hf I hI).hom.stalkMap x
      ((quotientStalkChartEquiv (graphIdeal X Y f I) (graphIdeal_coherent X Y f hf I hI)
        ((graphQuotientIso X Y f hf I hI).hom.base x)).symm
        (Ideal.Quotient.mk (wholeChartStalkIdeal (graphIdeal X Y f I)
          (graphMap X Y f x.val) (graphMap X Y f x.val) (mem_chart_source _ _)) g))) =
      Ideal.Quotient.mk (wholeChartStalkIdeal I x.val x.val (mem_chart_source _ _))
        (relativeGraphTrace d n (actualTranslatedMap f x.val)
          (actualTranslatedMap_holomorphic hf x.val) (actualTranslatedMap_zero f x.val) g) :=
  graphQuotientMap_chart_mk X Y f hf I hI x g

private theorem graph_base_relation (I : GermIdeal n X) (hI : I.IsCoherent) :
    quotientInclusion (graphIdeal X Y f I) (graphIdeal_coherent X Y f hf I hI) ≫
        ChartedSpace.locallyRingedSpaceMap (graphTarget X Y) (graphTarget_holomorphic X Y) =
      quotientInclusion (graphIdeal X Y f I) (graphIdeal_coherent X Y f hf I hI) ≫
        ChartedSpace.locallyRingedSpaceMap (graphSource X Y) (graphSource_holomorphic X Y) ≫
          ChartedSpace.locallyRingedSpaceMap f hf := by
  apply (cancel_epi (graphQuotientIso X Y f hf I hI).hom).mp
  calc
    _ = quotientInclusion I hI ≫ ChartedSpace.locallyRingedSpaceMap f hf :=
      graphQuotientIso_base X Y f hf I hI
    _ = ((graphQuotientIso X Y f hf I hI).hom ≫
        quotientInclusion (graphIdeal X Y f I) (graphIdeal_coherent X Y f hf I hI) ≫
          ChartedSpace.locallyRingedSpaceMap (graphSource X Y) (graphSource_holomorphic X Y)) ≫
            ChartedSpace.locallyRingedSpaceMap f hf :=
      congrArg (fun k => k ≫ ChartedSpace.locallyRingedSpaceMap f hf)
        (graphQuotientIso_source X Y f hf I hI).symm
    _ = _ := by simp only [Category.assoc]

private theorem graphQuotientIso_inv_source (I : GermIdeal n X) (hI : I.IsCoherent) :
    (graphQuotientIso X Y f hf I hI).inv ≫ quotientInclusion I hI =
      quotientInclusion (graphIdeal X Y f I) (graphIdeal_coherent X Y f hf I hI) ≫
        ChartedSpace.locallyRingedSpaceMap (graphSource X Y) (graphSource_holomorphic X Y) := by
  calc
    _ = (graphQuotientIso X Y f hf I hI).inv ≫
        ((graphQuotientIso X Y f hf I hI).hom ≫
          quotientInclusion (graphIdeal X Y f I) (graphIdeal_coherent X Y f hf I hI) ≫
            ChartedSpace.locallyRingedSpaceMap (graphSource X Y) (graphSource_holomorphic X Y)) :=
      congrArg (fun k => (graphQuotientIso X Y f hf I hI).inv ≫ k)
        (graphQuotientIso_source X Y f hf I hI).symm
    _ = _ := by simp only [←Category.assoc,Iso.inv_hom_id,Category.id_comp]

section RawBaseChange

variable (r : ℕ) (V : Opens (ComplexModel (d+r)))

/-- The target chart uses its literal original base-coordinate projection. -/
def rawPhi (v : V) : ComplexModel d := tangentProjection d r v.val

theorem rawPhi_holomorphic :
    ContMDiff 𝓘(ℂ,ComplexModel (d+r)) 𝓘(ℂ,ComplexModel d) ∞ (rawPhi r V) :=
  (tangentProjection d r).contDiff.contMDiff.comp contMDiff_subtype_val

/-- LITERAL741 raw joint open, before any elimination. -/
def rawOpen : Opens (cylinder (d+r) n V) :=
  jointOpen d (d+r) n (graphOpen X Y) V (rawPhi r V) (rawPhi_holomorphic r V)

def ratioCylinder : Opens (ComplexModel (r+n)) :=
  ⟨(actualJointNormalProjection r n) ⁻¹' X,
    X.isOpen.preimage (actualJointNormalProjection r n).continuous⟩

def ratioCylinderSource : ratioCylinder X r → X :=
  fun z => ⟨actualJointNormalProjection r n z.val,z.property⟩

theorem ratioCylinderSource_holomorphic :
    ContMDiff 𝓘(ℂ,ComplexModel (r+n)) 𝓘(ℂ,ComplexModel n) ∞ (ratioCylinderSource X r) := by
  apply (ContMDiff.subtypeVal_comp_iff X _).mp
  exact (actualJointNormalProjection r n).contDiff.contMDiff.comp contMDiff_subtype_val

/-- The actual map (u,x)↦(f(x),u) only evaluates f on its true domain. -/
def ratioMap (z : ratioCylinder X r) : ComplexModel (d+r) :=
  join (f (ratioCylinderSource X r z)).val (tangentProjection r n z.val)

include hf in
theorem ratioMap_holomorphic :
    ContMDiff 𝓘(ℂ,ComplexModel (r+n)) 𝓘(ℂ,ComplexModel (d+r)) ∞ (ratioMap X Y f r) :=
  ((tangentInclusion d r).contDiff.contMDiff.comp
    (contMDiff_subtype_val.comp (hf.comp (ratioCylinderSource_holomorphic X r)))).add
      ((actualJointNormalInclusion d r).contDiff.contMDiff.comp
        ((tangentProjection r n).contDiff.contMDiff.comp contMDiff_subtype_val))

/-- Genuine inverse-image open of the original V, without an entire extension. -/
def ratioOpen : Opens (ratioCylinder X r) :=
  ⟨(ratioMap X Y f r) ⁻¹' V,V.isOpen.preimage (ratioMap_holomorphic X Y f hf r).continuous⟩

def ratioSource : ratioOpen X Y f hf r V → X :=
  fun z => ratioCylinderSource X r z.val

def ratioBase : ratioOpen X Y f hf r V → V :=
  fun z => ⟨ratioMap X Y f r z.val,z.property⟩

theorem ratioSource_holomorphic :
    ContMDiff 𝓘(ℂ,ComplexModel (r+n)) 𝓘(ℂ,ComplexModel n) ∞ (ratioSource X Y f hf r V) :=
  (ratioCylinderSource_holomorphic X r).comp contMDiff_subtype_val

theorem ratioBase_holomorphic :
    ContMDiff 𝓘(ℂ,ComplexModel (r+n)) 𝓘(ℂ,ComplexModel (d+r)) ∞ (ratioBase X Y f hf r V) := by
  apply (ContMDiff.subtypeVal_comp_iff V _).mp
  exact (ratioMap_holomorphic X Y f hf r).comp contMDiff_subtype_val

theorem ratioBase_first (z : ratioOpen X Y f hf r V) :
    rawPhi r V (ratioBase X Y f hf r V z) = (f (ratioSource X Y f hf r V z)).val :=
  first_join _ _

/-- The WHOLE eliminated source/ratio ideal, on its actual real open. -/
def ratioIdeal (I : GermIdeal n X) (q : GermIdeal (d+r) V) :
    GermIdeal (r+n) (ratioOpen X Y f hf r V) :=
  sumIdeal (GermIdeal.pullback (ratioSource X Y f hf r V) I)
    (GermIdeal.pullback (ratioBase X Y f hf r V) q)

theorem ratioIdeal_coherent (I : GermIdeal n X) (hI : I.IsCoherent)
    (q : GermIdeal (d+r) V) (hq : q.IsCoherent) :
    (ratioIdeal X Y f hf r V I q).IsCoherent :=
  isCoherent_sumIdeal (isCoherent_pullback (ratioSource_holomorphic X Y f hf r V) hI)
    (isCoherent_pullback (ratioBase_holomorphic X Y f hf r V) hq)

/-- The unchanged native raw ideal of741 for the internally constructed graph. -/
def rawIdeal (I : GermIdeal n X) (q : GermIdeal (d+r) V) :
    GermIdeal ((d+r)+n) (rawOpen X Y r V) :=
  jointIdeal d (d+r) n (rawPhi r V) (rawPhi_holomorphic r V) (graphIdeal X Y f I) q

include hf in
theorem rawIdeal_coherent (I : GermIdeal n X) (hI : I.IsCoherent)
    (q : GermIdeal (d+r) V) (hq : q.IsCoherent) :
    (rawIdeal X Y f r V I q).IsCoherent :=
  jointIdeal_coherent d (d+r) n (rawPhi r V) (rawPhi_holomorphic r V)
    (graphIdeal X Y f I) (graphIdeal_coherent X Y f hf I hI) q hq

/-- The ACTUAL graph insertion into the literal original raw joint open. -/
def rawGraphInsert (z : ratioOpen X Y f hf r V) : rawOpen X Y r V := by
  let v := ratioBase X Y f hf r V z
  let x := ratioSource X Y f hf r V z
  let w : cylinder (d+r) n V := ⟨join v.val x.val,by
    change tangentProjection (d+r) n (join v.val x.val) ∈ V
    rw [first_join]
    exact v.property⟩
  have hw : cylinderProjection (d+r) n V w = v := by
    apply Subtype.ext
    exact first_join _ _
  have hx : actualJointNormalProjection (d+r) n w.val = x.val := second_join _ _
  refine ⟨w,?_⟩
  change tangentProjection d n (join (rawPhi r V (cylinderProjection (d+r) n V w))
      (actualJointNormalProjection (d+r) n w.val)) ∈ Y ∧
    actualJointNormalProjection d n (join (rawPhi r V (cylinderProjection (d+r) n V w))
      (actualJointNormalProjection (d+r) n w.val)) ∈ X
  rw [first_join,second_join,hw,hx]
  change rawPhi r V (ratioBase X Y f hf r V z) ∈ Y ∧
    (ratioSource X Y f hf r V z).val ∈ X
  rw [ratioBase_first]
  exact ⟨(f x).property,x.property⟩

theorem rawGraphInsert_holomorphic :
    ContMDiff 𝓘(ℂ,ComplexModel (r+n)) 𝓘(ℂ,ComplexModel ((d+r)+n)) ∞
      (rawGraphInsert X Y f hf r V) := by
  apply (ContMDiff.subtypeVal_comp_iff (rawOpen X Y r V) _).mp
  apply (ContMDiff.subtypeVal_comp_iff (cylinder (d+r) n V) _).mp
  exact ((tangentInclusion (d+r) n).contDiff.contMDiff.comp
    (contMDiff_subtype_val.comp (ratioBase_holomorphic X Y f hf r V))).add
      ((actualJointNormalInclusion (d+r) n).contDiff.contMDiff.comp
        (contMDiff_subtype_val.comp (ratioSource_holomorphic X Y f hf r V)))

theorem rawGraphInsert_base (z : ratioOpen X Y f hf r V) :
    baseProjection d (d+r) n (graphOpen X Y) V (rawPhi r V) (rawPhi_holomorphic r V)
      (rawGraphInsert X Y f hf r V z) = ratioBase X Y f hf r V z := by
  apply Subtype.ext
  exact first_join _ _

theorem rawGraphInsert_normal (z : ratioOpen X Y f hf r V) :
    actualJointNormalProjection (d+r) n (rawGraphInsert X Y f hf r V z).val.val =
      (ratioSource X Y f hf r V z).val := second_join _ _

theorem rawGraphInsert_source (z : ratioOpen X Y f hf r V) :
    sourceProjection d (d+r) n (graphOpen X Y) V (rawPhi r V) (rawPhi_holomorphic r V)
      (rawGraphInsert X Y f hf r V z) = graphMap X Y f (ratioSource X Y f hf r V z) := by
  apply Subtype.ext
  change join (rawPhi r V (baseProjection d (d+r) n (graphOpen X Y) V
    (rawPhi r V) (rawPhi_holomorphic r V) (rawGraphInsert X Y f hf r V z)))
      (actualJointNormalProjection (d+r) n (rawGraphInsert X Y f hf r V z).val.val) = _
  rw [rawGraphInsert_base,rawGraphInsert_normal]
  change join (rawPhi r V (ratioBase X Y f hf r V z)) (ratioSource X Y f hf r V z).val =
    join (f (ratioSource X Y f hf r V z)).val (ratioSource X Y f hf r V z).val
  rw [ratioBase_first]

/-- Literal coordinate deletion exists on the entire raw ambient open;
its source coordinate already lies in X by the original raw domain. -/
def rawDelete (w : rawOpen X Y r V) : ratioCylinder X r := by
  let v := baseProjection d (d+r) n (graphOpen X Y) V (rawPhi r V)
    (rawPhi_holomorphic r V) w
  let x := graphSource X Y (sourceProjection d (d+r) n (graphOpen X Y) V
    (rawPhi r V) (rawPhi_holomorphic r V) w)
  refine ⟨join (actualJointNormalProjection d r v.val) x.val,?_⟩
  change actualJointNormalProjection r n
    (join (actualJointNormalProjection d r v.val) x.val) ∈ X
  rw [second_join]
  exact x.property

theorem rawDelete_holomorphic :
    ContMDiff 𝓘(ℂ,ComplexModel ((d+r)+n)) 𝓘(ℂ,ComplexModel (r+n)) ∞
      (rawDelete X Y r V) := by
  apply (ContMDiff.subtypeVal_comp_iff (ratioCylinder X r) _).mp
  exact ((tangentInclusion r n).contDiff.contMDiff.comp
    ((actualJointNormalProjection d r).contDiff.contMDiff.comp
      (contMDiff_subtype_val.comp
        (baseProjection_holomorphic d (d+r) n (graphOpen X Y) V
          (rawPhi r V) (rawPhi_holomorphic r V))))).add
    ((actualJointNormalInclusion r n).contDiff.contMDiff.comp
      (contMDiff_subtype_val.comp ((graphSource_holomorphic X Y).comp
        (sourceProjection_holomorphic d (d+r) n (graphOpen X Y) V
          (rawPhi r V) (rawPhi_holomorphic r V)))))

theorem rawDelete_source (w : rawOpen X Y r V) :
    ratioCylinderSource X r (rawDelete X Y r V w) =
      graphSource X Y (sourceProjection d (d+r) n (graphOpen X Y) V
        (rawPhi r V) (rawPhi_holomorphic r V) w) := by
  apply Subtype.ext
  exact second_join _ _

theorem rawDelete_baseNormal (w : rawOpen X Y r V) :
    tangentProjection r n (rawDelete X Y r V w).val =
      actualJointNormalProjection d r
        (baseProjection d (d+r) n (graphOpen X Y) V (rawPhi r V)
          (rawPhi_holomorphic r V) w).val := first_join _ _

theorem rawDelete_insert (z : ratioOpen X Y f hf r V) :
    rawDelete X Y r V (rawGraphInsert X Y f hf r V z) = z.val := by
  apply Subtype.ext
  change join (actualJointNormalProjection d r
    (baseProjection d (d+r) n (graphOpen X Y) V (rawPhi r V)
      (rawPhi_holomorphic r V) (rawGraphInsert X Y f hf r V z)).val)
    (graphSource X Y (sourceProjection d (d+r) n (graphOpen X Y) V (rawPhi r V)
      (rawPhi_holomorphic r V) (rawGraphInsert X Y f hf r V z))).val = z.val.val
  rw [rawGraphInsert_base,rawGraphInsert_source,graphSource_graphMap]
  change join (actualJointNormalProjection d r
      (join (f (ratioSource X Y f hf r V z)).val (tangentProjection r n z.val.val)))
    (actualJointNormalProjection r n z.val.val) = z.val.val
  rw [second_join]
  exact join_projections _

/-- Actual open where the deleted source/ratio point lands in the ORIGINAL V. -/
def rawInverseOpen : Opens (rawOpen X Y r V) :=
  ⟨(ratioMap X Y f r ∘ rawDelete X Y r V) ⁻¹' V,
    V.isOpen.preimage ((ratioMap_holomorphic X Y f hf r).continuous.comp
      (rawDelete_holomorphic X Y r V).continuous)⟩

def rawRetraction : rawInverseOpen X Y f hf r V → ratioOpen X Y f hf r V :=
  fun w => ⟨rawDelete X Y r V w.val,w.property⟩

theorem rawRetraction_holomorphic :
    ContMDiff 𝓘(ℂ,ComplexModel ((d+r)+n)) 𝓘(ℂ,ComplexModel (r+n)) ∞
      (rawRetraction X Y f hf r V) := by
  apply (ContMDiff.subtypeVal_comp_iff (ratioOpen X Y f hf r V) _).mp
  exact (rawDelete_holomorphic X Y r V).comp contMDiff_subtype_val

theorem rawInverseOpen_contains_insert (z : ratioOpen X Y f hf r V) :
    rawGraphInsert X Y f hf r V z ∈ rawInverseOpen X Y f hf r V := by
  change ratioMap X Y f r (rawDelete X Y r V (rawGraphInsert X Y f hf r V z)) ∈ V
  rw [rawDelete_insert]
  exact z.property

def rawInsertOnInverseOpen (z : ratioOpen X Y f hf r V) : rawInverseOpen X Y f hf r V :=
  ⟨rawGraphInsert X Y f hf r V z,rawInverseOpen_contains_insert X Y f hf r V z⟩

theorem rawInsertOnInverseOpen_holomorphic :
    ContMDiff 𝓘(ℂ,ComplexModel (r+n)) 𝓘(ℂ,ComplexModel ((d+r)+n)) ∞
      (rawInsertOnInverseOpen X Y f hf r V) := by
  apply (ContMDiff.subtypeVal_comp_iff (rawInverseOpen X Y f hf r V) _).mp
  exact rawGraphInsert_holomorphic X Y f hf r V

theorem rawRetraction_insert (z : ratioOpen X Y f hf r V) :
    rawRetraction X Y f hf r V (rawInsertOnInverseOpen X Y f hf r V z) = z := by
  apply Subtype.ext
  exact rawDelete_insert X Y f hf r V z

/-- EVERY raw support point lies in D; no strict-transform image is assumed. -/
theorem rawInverseOpen_contains_support (I : GermIdeal n X) (hI : I.IsCoherent)
    (q : GermIdeal (d+r) V) (hq : q.IsCoherent) (w : (rawIdeal X Y f r V I q).zeroLocus) :
    w.val ∈ rawInverseOpen X Y f hf r V := by
  have hs := ((joint_support_iff d (d+r) n (rawPhi r V) (rawPhi_holomorphic r V)
    (graphIdeal X Y f I) (graphIdeal_coherent X Y f hf I hI) q hq w.val).mp w.property).1
  let v := baseProjection d (d+r) n (graphOpen X Y) V (rawPhi r V)
    (rawPhi_holomorphic r V) w.val
  let a := sourceProjection d (d+r) n (graphOpen X Y) V (rawPhi r V)
    (rawPhi_holomorphic r V) w.val
  have hgraph := graphTarget_support X Y f hf I ⟨a,hs⟩
  have hy : (graphTarget X Y a).val = rawPhi r V v := first_join _ _
  have hb : ratioMap X Y f r (rawDelete X Y r V w.val) = v.val := by
    change join (f (ratioCylinderSource X r (rawDelete X Y r V w.val))).val
      (tangentProjection r n (rawDelete X Y r V w.val).val) = v.val
    rw [rawDelete_source,rawDelete_baseNormal]
    change join (f (graphSource X Y a)).val (actualJointNormalProjection d r v.val) = v.val
    rw [←hgraph,hy]
    exact join_projections _
  change ratioMap X Y f r (rawDelete X Y r V w.val) ∈ V
  rw [hb]
  exact v.property

private theorem rawInsert_ideal (I : GermIdeal n X) (hI : I.IsCoherent)
    (q : GermIdeal (d+r) V) (hq : q.IsCoherent) :
    (GermIdeal.pullback (rawGraphInsert X Y f hf r V) (rawIdeal X Y f r V I q)).Le
      (ratioIdeal X Y f hf r V I q) := by
  let A := graphIdeal X Y f I
  let hA := graphIdeal_coherent X Y f hf I hI
  let s : rawOpen X Y r V → graphOpen X Y :=
    sourceProjection d (d+r) n (graphOpen X Y) V (rawPhi r V) (rawPhi_holomorphic r V)
  let hs : ContMDiff 𝓘(ℂ,ComplexModel ((d+r)+n)) 𝓘(ℂ,ComplexModel (d+n)) ∞ s :=
    sourceProjection_holomorphic d (d+r) n (graphOpen X Y) V
    (rawPhi r V) (rawPhi_holomorphic r V)
  let p : rawOpen X Y r V → V :=
    baseProjection d (d+r) n (graphOpen X Y) V (rawPhi r V) (rawPhi_holomorphic r V)
  let hp : ContMDiff 𝓘(ℂ,ComplexModel ((d+r)+n)) 𝓘(ℂ,ComplexModel (d+r)) ∞ p :=
    baseProjection_holomorphic d (d+r) n (graphOpen X Y) V
    (rawPhi r V) (rawPhi_holomorphic r V)
  let i : ratioOpen X Y f hf r V → rawOpen X Y r V := rawGraphInsert X Y f hf r V
  let hi : ContMDiff 𝓘(ℂ,ComplexModel (r+n)) 𝓘(ℂ,ComplexModel ((d+r)+n)) ∞ i :=
    rawGraphInsert_holomorphic X Y f hf r V
  have hsi : s ∘ i = graphMap X Y f ∘ ratioSource X Y f hf r V :=
    funext (rawGraphInsert_source X Y f hf r V)
  have hpi : p ∘ i = ratioBase X Y f hf r V := funext (rawGraphInsert_base X Y f hf r V)
  change (GermIdeal.pullback i (sumIdeal (GermIdeal.pullback s A) (GermIdeal.pullback p q))).Le _
  rw [whole_pullback_sum hi _ _ (isCoherent_pullback hs hA) (isCoherent_pullback hp hq),
    ←whole_pullback_comp hs hi A hA,←whole_pullback_comp hp hi q hq,hsi,hpi,
    whole_pullback_comp (graphMap_holomorphic X Y f hf)
      (ratioSource_holomorphic X Y f hf r V) A hA]
  apply whole_sum_le _ _ _ (ratioIdeal_coherent X Y f hf r V I hI q hq)
  · intro x g hg
    apply le_sumIdeal_left (isCoherent_pullback (ratioSource_holomorphic X Y f hf r V) hI)
    exact pullback_le_pullback (graphMap_ideal X Y f hf I hI) x g hg
  · exact le_sumIdeal_right (isCoherent_pullback (ratioBase_holomorphic X Y f hf r V) hq)

/-- Genuine native graph-insertion map into the unchanged raw741 quotient. -/
def rawQuotientMap (I : GermIdeal n X) (hI : I.IsCoherent)
    (q : GermIdeal (d+r) V) (hq : q.IsCoherent) :
    quotientLocallyRingedSpace (ratioIdeal X Y f hf r V I q)
      (ratioIdeal_coherent X Y f hf r V I hI q hq) ⟶
    quotientLocallyRingedSpace (rawIdeal X Y f r V I q)
      (rawIdeal_coherent X Y f hf r V I hI q hq) :=
  quotientMap (rawGraphInsert_holomorphic X Y f hf r V)
    _ (ratioIdeal_coherent X Y f hf r V I hI q hq)
    _ (rawIdeal_coherent X Y f hf r V I hI q hq)
    (rawInsert_ideal X Y f hf r V I hI q hq)

/-- Before constructing any inverse, the actual quotient-open restriction
to D is already an isomorphism because D contains EVERY raw support point. -/
private def rawRestrictionIso (I : GermIdeal n X) (hI : I.IsCoherent)
    (q : GermIdeal (d+r) V) (hq : q.IsCoherent) :
    quotientLocallyRingedSpace
      (quotientOpenIdeal (rawIdeal X Y f r V I q) (rawInverseOpen X Y f hf r V))
      (quotientOpenIdeal_coherent _ (rawIdeal_coherent X Y f hf r V I hI q hq) _) ≅
    quotientLocallyRingedSpace (rawIdeal X Y f r V I q)
      (rawIdeal_coherent X Y f hf r V I hI q hq) := by
  let J := rawIdeal X Y f r V I q
  let hJ := rawIdeal_coherent X Y f hf r V I hI q hq
  let D := rawInverseOpen X Y f hf r V
  let j := quotientOpenMap J hJ D
  have hsurj : Function.Surjective j.base := by
    intro x
    change x ∈ Set.range (quotientOpenMap J hJ D).base
    rw [quotientOpenMap_range]
    exact rawInverseOpen_contains_support X Y f hf r V I hI q hq x
  let : Epi j.base := ConcreteCategory.epi_of_surjective _ hsurj
  let : IsIso j := LocallyRingedSpace.IsOpenImmersion.to_iso j
  exact asIso j

private def rawRestrictedSource : rawInverseOpen X Y f hf r V → graphOpen X Y :=
  fun w => sourceProjection d (d+r) n (graphOpen X Y) V (rawPhi r V)
    (rawPhi_holomorphic r V) w.val

private theorem rawRestrictedSource_holomorphic :
    ContMDiff 𝓘(ℂ,ComplexModel ((d+r)+n)) 𝓘(ℂ,ComplexModel (d+n)) ∞
      (rawRestrictedSource X Y f hf r V) := by
  let s : rawOpen X Y r V → graphOpen X Y := sourceProjection d (d+r) n
    (graphOpen X Y) V (rawPhi r V) (rawPhi_holomorphic r V)
  let hs : ContMDiff 𝓘(ℂ,ComplexModel ((d+r)+n)) 𝓘(ℂ,ComplexModel (d+n)) ∞ s :=
    sourceProjection_holomorphic d (d+r) n (graphOpen X Y) V (rawPhi r V) (rawPhi_holomorphic r V)
  exact hs.comp contMDiff_subtype_val

private def rawRestrictedBase : rawInverseOpen X Y f hf r V → V :=
  fun w => baseProjection d (d+r) n (graphOpen X Y) V (rawPhi r V)
    (rawPhi_holomorphic r V) w.val

private theorem rawRestrictedBase_holomorphic :
    ContMDiff 𝓘(ℂ,ComplexModel ((d+r)+n)) 𝓘(ℂ,ComplexModel (d+r)) ∞
      (rawRestrictedBase X Y f hf r V) := by
  let p : rawOpen X Y r V → V := baseProjection d (d+r) n
    (graphOpen X Y) V (rawPhi r V) (rawPhi_holomorphic r V)
  let hp : ContMDiff 𝓘(ℂ,ComplexModel ((d+r)+n)) 𝓘(ℂ,ComplexModel (d+r)) ∞ p :=
    baseProjection_holomorphic d (d+r) n (graphOpen X Y) V (rawPhi r V) (rawPhi_holomorphic r V)
  exact hp.comp contMDiff_subtype_val

private def rawSubstitutedBase : rawInverseOpen X Y f hf r V → V :=
  ratioBase X Y f hf r V ∘ rawRetraction X Y f hf r V

private theorem rawSubstitutedBase_holomorphic :
    ContMDiff 𝓘(ℂ,ComplexModel ((d+r)+n)) 𝓘(ℂ,ComplexModel (d+r)) ∞
      (rawSubstitutedBase X Y f hf r V) :=
  (ratioBase_holomorphic X Y f hf r V).comp (rawRetraction_holomorphic X Y f hf r V)

private theorem rawRestrictedBase_first :
    rawPhi r V ∘ rawRestrictedBase X Y f hf r V =
      (Subtype.val : Y → ComplexModel d) ∘ graphTarget X Y ∘ rawRestrictedSource X Y f hf r V := by
  funext w
  exact (projection_point_square d (d+r) n (graphOpen X Y) V
    (rawPhi r V) (rawPhi_holomorphic r V) w.val).symm

private theorem rawSubstitutedBase_first :
    rawPhi r V ∘ rawSubstitutedBase X Y f hf r V =
      (Subtype.val : Y → ComplexModel d) ∘ f ∘ graphSource X Y ∘ rawRestrictedSource X Y f hf r V := by
  funext w
  change rawPhi r V (ratioBase X Y f hf r V (rawRetraction X Y f hf r V w)) = _
  rw [ratioBase_first]
  change (f (ratioCylinderSource X r (rawDelete X Y r V w.val))).val =
    (f (graphSource X Y (sourceProjection d (d+r) n (graphOpen X Y) V
      (rawPhi r V) (rawPhi_holomorphic r V) w.val))).val
  rw [rawDelete_source]

private theorem rawBase_normal_eq (w : rawInverseOpen X Y f hf r V) :
    actualJointNormalProjection d r (rawRestrictedBase X Y f hf r V w).val =
      actualJointNormalProjection d r (rawSubstitutedBase X Y f hf r V w).val := by
  change actualJointNormalProjection d r
    (baseProjection d (d+r) n (graphOpen X Y) V (rawPhi r V) (rawPhi_holomorphic r V) w.val).val =
      actualJointNormalProjection d r (join
        (f (ratioSource X Y f hf r V (rawRetraction X Y f hf r V w))).val
        (tangentProjection r n (rawDelete X Y r V w.val).val))
  rw [second_join,rawDelete_baseNormal]

private theorem rawRestrictedSource_ideal (I : GermIdeal n X) (hI : I.IsCoherent)
    (q : GermIdeal (d+r) V) :
    (GermIdeal.pullback (rawRestrictedSource X Y f hf r V) (graphIdeal X Y f I)).Le
      (quotientOpenIdeal (rawIdeal X Y f r V I q) (rawInverseOpen X Y f hf r V)) := by
  let A := graphIdeal X Y f I
  let hA := graphIdeal_coherent X Y f hf I hI
  let s : rawOpen X Y r V → graphOpen X Y := sourceProjection d (d+r) n
    (graphOpen X Y) V (rawPhi r V) (rawPhi_holomorphic r V)
  let hs : ContMDiff 𝓘(ℂ,ComplexModel ((d+r)+n)) 𝓘(ℂ,ComplexModel (d+n)) ∞ s :=
    sourceProjection_holomorphic d (d+r) n (graphOpen X Y) V (rawPhi r V) (rawPhi_holomorphic r V)
  let p : rawOpen X Y r V → V := baseProjection d (d+r) n
    (graphOpen X Y) V (rawPhi r V) (rawPhi_holomorphic r V)
  let j : rawInverseOpen X Y f hf r V → rawOpen X Y r V := Subtype.val
  let hj : ContMDiff 𝓘(ℂ,ComplexModel ((d+r)+n)) 𝓘(ℂ,ComplexModel ((d+r)+n)) ∞ j :=
    contMDiff_subtype_val
  change (GermIdeal.pullback (s ∘ j) A).Le
    (GermIdeal.pullback j (sumIdeal (GermIdeal.pullback s A) (GermIdeal.pullback p q)))
  rw [whole_pullback_comp hs hj A hA]
  exact pullback_le_pullback (le_sumIdeal_left (isCoherent_pullback hs hA))

/-- The ordinary graph model forces the FULL first-block equality on the
actual raw restriction, before any q-preservation or inverse is assumed. -/
private theorem rawBase_full_block (I : GermIdeal n X) (hI : I.IsCoherent)
    (q : GermIdeal (d+r) V) (hq : q.IsCoherent) :
    quotientInclusion
      (quotientOpenIdeal (rawIdeal X Y f r V I q) (rawInverseOpen X Y f hf r V))
      (quotientOpenIdeal_coherent _ (rawIdeal_coherent X Y f hf r V I hI q hq) _) ≫
        ChartedSpace.locallyRingedSpaceMap
          (rawPhi r V ∘ rawRestrictedBase X Y f hf r V)
          ((rawPhi_holomorphic r V).comp (rawRestrictedBase_holomorphic X Y f hf r V)) =
    quotientInclusion
      (quotientOpenIdeal (rawIdeal X Y f r V I q) (rawInverseOpen X Y f hf r V))
      (quotientOpenIdeal_coherent _ (rawIdeal_coherent X Y f hf r V I hI q hq) _) ≫
        ChartedSpace.locallyRingedSpaceMap
          (rawPhi r V ∘ rawSubstitutedBase X Y f hf r V)
          ((rawPhi_holomorphic r V).comp (rawSubstitutedBase_holomorphic X Y f hf r V)) := by
  let A := graphIdeal X Y f I
  let hA := graphIdeal_coherent X Y f hf I hI
  let C := quotientOpenIdeal (rawIdeal X Y f r V I q) (rawInverseOpen X Y f hf r V)
  let hC : C.IsCoherent := quotientOpenIdeal_coherent (rawIdeal X Y f r V I q)
    (rawIdeal_coherent X Y f hf r V I hI q hq) (rawInverseOpen X Y f hf r V)
  let s : rawInverseOpen X Y f hf r V → graphOpen X Y := rawRestrictedSource X Y f hf r V
  let hs : ContMDiff 𝓘(ℂ,ComplexModel ((d+r)+n)) 𝓘(ℂ,ComplexModel (d+n)) ∞ s :=
    rawRestrictedSource_holomorphic X Y f hf r V
  let F := quotientMap hs C hC A hA (rawRestrictedSource_ideal X Y f hf r V I hI q)
  have hF : quotientInclusion C hC ≫ ChartedSpace.locallyRingedSpaceMap s hs = F ≫ quotientInclusion A hA :=
    quotientMap_inclusion hs C hC A hA (rawRestrictedSource_ideal X Y f hf r V I hI q)
  have hl : ChartedSpace.locallyRingedSpaceMap
      (rawPhi r V ∘ rawRestrictedBase X Y f hf r V)
      ((rawPhi_holomorphic r V).comp (rawRestrictedBase_holomorphic X Y f hf r V)) =
      ChartedSpace.locallyRingedSpaceMap s hs ≫
        ChartedSpace.locallyRingedSpaceMap (graphTarget X Y) (graphTarget_holomorphic X Y) ≫
          ChartedSpace.locallyRingedSpaceMap (Subtype.val : Y → ComplexModel d) contMDiff_subtype_val := by
    have he := nativeMap_congr (a := (d+r)+n) (c := d)
      (hu := (rawPhi_holomorphic r V).comp (rawRestrictedBase_holomorphic X Y f hf r V))
      (hv := contMDiff_subtype_val.comp ((graphTarget_holomorphic X Y).comp hs))
      (rawRestrictedBase_first X Y f hf r V)
    refine he.trans ?_
    simp only [←ChartedSpace.locallyRingedSpace_comp]
    exact nativeMap_congr (a := (d+r)+n) (c := d) rfl
  have hr : ChartedSpace.locallyRingedSpaceMap
      (rawPhi r V ∘ rawSubstitutedBase X Y f hf r V)
      ((rawPhi_holomorphic r V).comp (rawSubstitutedBase_holomorphic X Y f hf r V)) =
      ChartedSpace.locallyRingedSpaceMap s hs ≫
        ChartedSpace.locallyRingedSpaceMap (graphSource X Y) (graphSource_holomorphic X Y) ≫
          ChartedSpace.locallyRingedSpaceMap f hf ≫
            ChartedSpace.locallyRingedSpaceMap (Subtype.val : Y → ComplexModel d) contMDiff_subtype_val := by
    have he := nativeMap_congr (a := (d+r)+n) (c := d)
      (hu := (rawPhi_holomorphic r V).comp (rawSubstitutedBase_holomorphic X Y f hf r V))
      (hv := contMDiff_subtype_val.comp (hf.comp ((graphSource_holomorphic X Y).comp hs)))
      (rawSubstitutedBase_first X Y f hf r V)
    refine he.trans ?_
    simp only [←ChartedSpace.locallyRingedSpace_comp]
    exact nativeMap_congr (a := (d+r)+n) (c := d) rfl
  have hrel := congrArg (fun k => F ≫ k ≫
    ChartedSpace.locallyRingedSpaceMap (Subtype.val : Y → ComplexModel d) contMDiff_subtype_val)
      (graph_base_relation X Y f hf I hI)
  have hrel' : (F ≫ quotientInclusion A hA) ≫
      ChartedSpace.locallyRingedSpaceMap (graphTarget X Y) (graphTarget_holomorphic X Y) ≫
        ChartedSpace.locallyRingedSpaceMap (Subtype.val : Y → ComplexModel d) contMDiff_subtype_val =
    (F ≫ quotientInclusion A hA) ≫
      ChartedSpace.locallyRingedSpaceMap (graphSource X Y) (graphSource_holomorphic X Y) ≫
        ChartedSpace.locallyRingedSpaceMap f hf ≫
          ChartedSpace.locallyRingedSpaceMap (Subtype.val : Y → ComplexModel d) contMDiff_subtype_val := by
    simpa only [Category.assoc] using hrel
  rw [←hF] at hrel'
  rw [hl,hr]
  simpa only [Category.assoc] using hrel'

private theorem rawSubstitutedBase_ideal (I : GermIdeal n X) (hI : I.IsCoherent)
    (q : GermIdeal (d+r) V) (hq : q.IsCoherent) :
    (GermIdeal.pullback (rawSubstitutedBase X Y f hf r V) q).Le
      (quotientOpenIdeal (rawIdeal X Y f r V I q) (rawInverseOpen X Y f hf r V)) := by
  let C := quotientOpenIdeal (rawIdeal X Y f r V I q) (rawInverseOpen X Y f hf r V)
  let hC : C.IsCoherent := quotientOpenIdeal_coherent (rawIdeal X Y f r V I q)
    (rawIdeal_coherent X Y f hf r V I hI q hq) (rawInverseOpen X Y f hf r V)
  let b : rawOpen X Y r V → V := baseProjection d (d+r) n (graphOpen X Y) V
    (rawPhi r V) (rawPhi_holomorphic r V)
  let hb : ContMDiff 𝓘(ℂ,ComplexModel ((d+r)+n)) 𝓘(ℂ,ComplexModel (d+r)) ∞ b :=
    baseProjection_holomorphic d (d+r) n (graphOpen X Y) V (rawPhi r V) (rawPhi_holomorphic r V)
  let s : rawOpen X Y r V → graphOpen X Y := sourceProjection d (d+r) n
    (graphOpen X Y) V (rawPhi r V) (rawPhi_holomorphic r V)
  let j : rawInverseOpen X Y f hf r V → rawOpen X Y r V := Subtype.val
  let hj : ContMDiff 𝓘(ℂ,ComplexModel ((d+r)+n)) 𝓘(ℂ,ComplexModel ((d+r)+n)) ∞ j :=
    contMDiff_subtype_val
  have hq0 : (GermIdeal.pullback (rawRestrictedBase X Y f hf r V) q).Le C := by
    change (GermIdeal.pullback (b ∘ j) q).Le
      (GermIdeal.pullback j (sumIdeal
        (GermIdeal.pullback (m := (d+r)+n) s (graphIdeal X Y f I))
        (GermIdeal.pullback (m := (d+r)+n) b q)))
    rw [whole_pullback_comp hb hj q hq]
    exact pullback_le_pullback (le_sumIdeal_right (isCoherent_pullback hb hq))
  obtain ⟨hp,hall,_⟩ := block_congruence (d := d) (t := r) C hC
    (rawRestrictedBase_holomorphic X Y f hf r V) (rawSubstitutedBase_holomorphic X Y f hf r V)
    (rawBase_full_block X Y f hf r V I hI q hq) (rawBase_normal_eq X Y f hf r V)
  exact pullback_le_of_germ_congruence C hC q hq
    (rawRestrictedBase_holomorphic X Y f hf r V) (rawSubstitutedBase_holomorphic X Y f hf r V)
    hq0 hp hall

private theorem rawBase_native_eq (I : GermIdeal n X) (hI : I.IsCoherent)
    (q : GermIdeal (d+r) V) (hq : q.IsCoherent) :
    quotientInclusion
      (quotientOpenIdeal (rawIdeal X Y f r V I q) (rawInverseOpen X Y f hf r V))
      (quotientOpenIdeal_coherent _ (rawIdeal_coherent X Y f hf r V I hI q hq) _) ≫
        ChartedSpace.locallyRingedSpaceMap (rawRestrictedBase X Y f hf r V)
          (rawRestrictedBase_holomorphic X Y f hf r V) =
    quotientInclusion
      (quotientOpenIdeal (rawIdeal X Y f r V I q) (rawInverseOpen X Y f hf r V))
      (quotientOpenIdeal_coherent _ (rawIdeal_coherent X Y f hf r V I hI q hq) _) ≫
        ChartedSpace.locallyRingedSpaceMap (rawSubstitutedBase X Y f hf r V)
          (rawSubstitutedBase_holomorphic X Y f hf r V) :=
  (block_congruence (d := d) (t := r) _
    (quotientOpenIdeal_coherent _ (rawIdeal_coherent X Y f hf r V I hI q hq) _)
    (rawRestrictedBase_holomorphic X Y f hf r V) (rawSubstitutedBase_holomorphic X Y f hf r V)
    (rawBase_full_block X Y f hf r V I hI q hq) (rawBase_normal_eq X Y f hf r V)).2.2

private theorem rawRetraction_source (w : rawInverseOpen X Y f hf r V) :
    ratioSource X Y f hf r V (rawRetraction X Y f hf r V w) =
      graphSource X Y (rawRestrictedSource X Y f hf r V w) :=
  rawDelete_source X Y r V w.val

/-- ALL q equations descend by185 at every actual point; combined with the
unchanged source equations this derives the WHOLE inverse ideal condition. -/
private theorem rawRetraction_ideal (I : GermIdeal n X) (hI : I.IsCoherent)
    (q : GermIdeal (d+r) V) (hq : q.IsCoherent) :
    (GermIdeal.pullback (rawRetraction X Y f hf r V) (ratioIdeal X Y f hf r V I q)).Le
      (quotientOpenIdeal (rawIdeal X Y f r V I q) (rawInverseOpen X Y f hf r V)) := by
  let C := quotientOpenIdeal (rawIdeal X Y f r V I q) (rawInverseOpen X Y f hf r V)
  let hC : C.IsCoherent := quotientOpenIdeal_coherent (rawIdeal X Y f r V I q)
    (rawIdeal_coherent X Y f hf r V I hI q hq) (rawInverseOpen X Y f hf r V)
  have hs : ratioSource X Y f hf r V ∘ rawRetraction X Y f hf r V =
      graphSource X Y ∘ rawRestrictedSource X Y f hf r V :=
    funext (rawRetraction_source X Y f hf r V)
  have hI0 : (GermIdeal.pullback
      (ratioSource X Y f hf r V ∘ rawRetraction X Y f hf r V) I).Le C := by
    rw [hs,whole_pullback_comp (graphSource_holomorphic X Y)
      (rawRestrictedSource_holomorphic X Y f hf r V) I hI]
    intro x g hg
    apply rawRestrictedSource_ideal X Y f hf r V I hI q x g
    exact pullback_le_pullback (le_sumIdeal_left
      (isCoherent_pullback (graphSource_holomorphic X Y) hI)) x g hg
  unfold ratioIdeal
  rw [whole_pullback_sum (rawRetraction_holomorphic X Y f hf r V) _ _
    (isCoherent_pullback (ratioSource_holomorphic X Y f hf r V) hI)
    (isCoherent_pullback (ratioBase_holomorphic X Y f hf r V) hq),
    ←whole_pullback_comp (ratioSource_holomorphic X Y f hf r V)
      (rawRetraction_holomorphic X Y f hf r V) I hI,
    ←whole_pullback_comp (ratioBase_holomorphic X Y f hf r V)
      (rawRetraction_holomorphic X Y f hf r V) q hq]
  exact whole_sum_le _ _ C hC hI0 (rawSubstitutedBase_ideal X Y f hf r V I hI q hq)

/-- ACTUAL native inverse candidate, whose whole ideal condition was just
produced from the ordinary input graph and every q equation. -/
private def rawReverseQuotientMap (I : GermIdeal n X) (hI : I.IsCoherent)
    (q : GermIdeal (d+r) V) (hq : q.IsCoherent) :
    quotientLocallyRingedSpace
      (quotientOpenIdeal (rawIdeal X Y f r V I q) (rawInverseOpen X Y f hf r V))
      (quotientOpenIdeal_coherent _ (rawIdeal_coherent X Y f hf r V I hI q hq) _) ⟶
    quotientLocallyRingedSpace (ratioIdeal X Y f hf r V I q)
      (ratioIdeal_coherent X Y f hf r V I hI q hq) :=
  quotientMap (rawRetraction_holomorphic X Y f hf r V)
    _ (quotientOpenIdeal_coherent _ (rawIdeal_coherent X Y f hf r V I hI q hq) _)
    _ (ratioIdeal_coherent X Y f hf r V I hI q hq)
    (rawRetraction_ideal X Y f hf r V I hI q hq)

private theorem rawInsertOnInverseOpen_ideal (I : GermIdeal n X) (hI : I.IsCoherent)
    (q : GermIdeal (d+r) V) (hq : q.IsCoherent) :
    (GermIdeal.pullback (rawInsertOnInverseOpen X Y f hf r V)
      (quotientOpenIdeal (rawIdeal X Y f r V I q) (rawInverseOpen X Y f hf r V))).Le
        (ratioIdeal X Y f hf r V I q) := by
  let J := rawIdeal X Y f r V I q
  let hJ := rawIdeal_coherent X Y f hf r V I hI q hq
  let D := rawInverseOpen X Y f hf r V
  let j : D → rawOpen X Y r V := Subtype.val
  let hj : ContMDiff 𝓘(ℂ,ComplexModel ((d+r)+n)) 𝓘(ℂ,ComplexModel ((d+r)+n)) ∞ j :=
    contMDiff_subtype_val
  change (GermIdeal.pullback (rawInsertOnInverseOpen X Y f hf r V) (GermIdeal.pullback j J)).Le _
  rw [←whole_pullback_comp hj (rawInsertOnInverseOpen_holomorphic X Y f hf r V) J hJ]
  exact rawInsert_ideal X Y f hf r V I hI q hq

private def rawInsertRestrictedQuotientMap (I : GermIdeal n X) (hI : I.IsCoherent)
    (q : GermIdeal (d+r) V) (hq : q.IsCoherent) :
    quotientLocallyRingedSpace (ratioIdeal X Y f hf r V I q)
      (ratioIdeal_coherent X Y f hf r V I hI q hq) ⟶
    quotientLocallyRingedSpace
      (quotientOpenIdeal (rawIdeal X Y f r V I q) (rawInverseOpen X Y f hf r V))
      (quotientOpenIdeal_coherent _ (rawIdeal_coherent X Y f hf r V I hI q hq) _) :=
  quotientMap (rawInsertOnInverseOpen_holomorphic X Y f hf r V)
    _ (ratioIdeal_coherent X Y f hf r V I hI q hq)
    _ (quotientOpenIdeal_coherent _ (rawIdeal_coherent X Y f hf r V I hI q hq) _)
    (rawInsertOnInverseOpen_ideal X Y f hf r V I hI q hq)

private theorem rawInsertRestricted_to_raw (I : GermIdeal n X) (hI : I.IsCoherent)
    (q : GermIdeal (d+r) V) (hq : q.IsCoherent) :
    rawInsertRestrictedQuotientMap X Y f hf r V I hI q hq ≫
      quotientOpenMap (rawIdeal X Y f r V I q) (rawIdeal_coherent X Y f hf r V I hI q hq)
        (rawInverseOpen X Y f hf r V) = rawQuotientMap X Y f hf r V I hI q hq := by
  let K := ratioIdeal X Y f hf r V I q
  let hK := ratioIdeal_coherent X Y f hf r V I hI q hq
  let J := rawIdeal X Y f r V I q
  let hJ := rawIdeal_coherent X Y f hf r V I hI q hq
  let D := rawInverseOpen X Y f hf r V
  let C := quotientOpenIdeal J D
  let hC : C.IsCoherent := quotientOpenIdeal_coherent J hJ D
  let j : D → rawOpen X Y r V := Subtype.val
  let hj : ContMDiff 𝓘(ℂ,ComplexModel ((d+r)+n)) 𝓘(ℂ,ComplexModel ((d+r)+n)) ∞ j :=
    contMDiff_subtype_val
  have ha := quotientMap_inclusion (rawInsertOnInverseOpen_holomorphic X Y f hf r V)
    K hK C hC (rawInsertOnInverseOpen_ideal X Y f hf r V I hI q hq)
  have hj' := quotientMap_inclusion hj C hC J hJ (fun _ _ h => h)
  have he := quotientMap_inclusion (rawGraphInsert_holomorphic X Y f hf r V)
    K hK J hJ (rawInsert_ideal X Y f hf r V I hI q hq)
  apply (cancel_mono (quotientInclusion J hJ)).mp
  change (quotientMap (rawInsertOnInverseOpen_holomorphic X Y f hf r V) K hK C hC
    (rawInsertOnInverseOpen_ideal X Y f hf r V I hI q hq) ≫
      quotientMap hj C hC J hJ (fun _ _ h => h)) ≫ quotientInclusion J hJ =
    quotientMap (rawGraphInsert_holomorphic X Y f hf r V) K hK J hJ
      (rawInsert_ideal X Y f hf r V I hI q hq) ≫ quotientInclusion J hJ
  rw [Category.assoc,←hj',←Category.assoc,←ha,←he,Category.assoc,
    ←ChartedSpace.locallyRingedSpace_comp]
  apply congrArg (fun k => quotientInclusion K hK ≫ k)
  exact nativeMap_congr (a := r+n) (c := (d+r)+n) rfl

/-- The first FULL inverse identity follows the literal actual RΓ=id,
using native quotient inclusion monomorphism, including every sheaf component. -/
private theorem rawInsertReverse_id (I : GermIdeal n X) (hI : I.IsCoherent)
    (q : GermIdeal (d+r) V) (hq : q.IsCoherent) :
    rawInsertRestrictedQuotientMap X Y f hf r V I hI q hq ≫
      rawReverseQuotientMap X Y f hf r V I hI q hq =
        𝟙 (quotientLocallyRingedSpace (ratioIdeal X Y f hf r V I q)
          (ratioIdeal_coherent X Y f hf r V I hI q hq)) := by
  let K := ratioIdeal X Y f hf r V I q
  let hK := ratioIdeal_coherent X Y f hf r V I hI q hq
  let J := rawIdeal X Y f r V I q
  let hJ := rawIdeal_coherent X Y f hf r V I hI q hq
  let D := rawInverseOpen X Y f hf r V
  let C := quotientOpenIdeal J D
  let hC : C.IsCoherent := quotientOpenIdeal_coherent J hJ D
  have ha := quotientMap_inclusion (rawInsertOnInverseOpen_holomorphic X Y f hf r V)
    K hK C hC (rawInsertOnInverseOpen_ideal X Y f hf r V I hI q hq)
  have hb := quotientMap_inclusion (rawRetraction_holomorphic X Y f hf r V)
    C hC K hK (rawRetraction_ideal X Y f hf r V I hI q hq)
  apply (cancel_mono (quotientInclusion K hK)).mp
  change (quotientMap (rawInsertOnInverseOpen_holomorphic X Y f hf r V) K hK C hC
    (rawInsertOnInverseOpen_ideal X Y f hf r V I hI q hq) ≫
      quotientMap (rawRetraction_holomorphic X Y f hf r V) C hC K hK
        (rawRetraction_ideal X Y f hf r V I hI q hq)) ≫ quotientInclusion K hK =
      (𝟙 (quotientLocallyRingedSpace K hK)) ≫ quotientInclusion K hK
  rw [Category.id_comp,Category.assoc,←hb,←Category.assoc,←ha,Category.assoc,
    ←ChartedSpace.locallyRingedSpace_comp]
  have he : rawRetraction X Y f hf r V ∘ rawInsertOnInverseOpen X Y f hf r V = id :=
    funext (rawRetraction_insert X Y f hf r V)
  have hm := nativeMap_congr (a := r+n) (c := r+n)
    (hu := (rawRetraction_holomorphic X Y f hf r V).comp
      (rawInsertOnInverseOpen_holomorphic X Y f hf r V)) (hv := contMDiff_id) he
  rw [hm,ChartedSpace.locallyRingedSpace_id,Category.comp_id]

/-- Original source projection on the genuine eliminated quotient. -/
def ratioSourceQuotientProjection (I : GermIdeal n X) (hI : I.IsCoherent)
    (q : GermIdeal (d+r) V) (hq : q.IsCoherent) :
    quotientLocallyRingedSpace (ratioIdeal X Y f hf r V I q)
      (ratioIdeal_coherent X Y f hf r V I hI q hq) ⟶ quotientLocallyRingedSpace I hI :=
  quotientMap (ratioSource_holomorphic X Y f hf r V)
    _ (ratioIdeal_coherent X Y f hf r V I hI q hq) I hI
    (le_sumIdeal_left (isCoherent_pullback (ratioSource_holomorphic X Y f hf r V) hI))

/-- Original q-base projection on the same actual eliminated quotient. -/
def ratioBaseQuotientProjection (I : GermIdeal n X) (hI : I.IsCoherent)
    (q : GermIdeal (d+r) V) (hq : q.IsCoherent) :
    quotientLocallyRingedSpace (ratioIdeal X Y f hf r V I q)
      (ratioIdeal_coherent X Y f hf r V I hI q hq) ⟶ quotientLocallyRingedSpace q hq :=
  quotientMap (ratioBase_holomorphic X Y f hf r V)
    _ (ratioIdeal_coherent X Y f hf r V I hI q hq) q hq
    (le_sumIdeal_right (isCoherent_pullback (ratioBase_holomorphic X Y f hf r V) hq))

/-- The native insertion retains the FULL ORIGINAL graph-source projection. -/
theorem rawQuotientMap_source (I : GermIdeal n X) (hI : I.IsCoherent)
    (q : GermIdeal (d+r) V) (hq : q.IsCoherent) :
    rawQuotientMap X Y f hf r V I hI q hq ≫
      sourceQuotientProjection d (d+r) n (rawPhi r V) (rawPhi_holomorphic r V)
        (graphIdeal X Y f I) (graphIdeal_coherent X Y f hf I hI) q hq =
      ratioSourceQuotientProjection X Y f hf r V I hI q hq ≫
        (graphQuotientIso X Y f hf I hI).hom := by
  let K := ratioIdeal X Y f hf r V I q
  let hK := ratioIdeal_coherent X Y f hf r V I hI q hq
  let J := rawIdeal X Y f r V I q
  let hJ := rawIdeal_coherent X Y f hf r V I hI q hq
  let A := graphIdeal X Y f I
  let hA := graphIdeal_coherent X Y f hf I hI
  let s : rawOpen X Y r V → graphOpen X Y := sourceProjection d (d+r) n
    (graphOpen X Y) V (rawPhi r V) (rawPhi_holomorphic r V)
  let hs : ContMDiff 𝓘(ℂ,ComplexModel ((d+r)+n)) 𝓘(ℂ,ComplexModel (d+n)) ∞ s :=
    sourceProjection_holomorphic d (d+r) n (graphOpen X Y) V (rawPhi r V) (rawPhi_holomorphic r V)
  let η : quotientLocallyRingedSpace K hK ⟶ quotientLocallyRingedSpace J hJ :=
    rawQuotientMap X Y f hf r V I hI q hq
  let S : quotientLocallyRingedSpace J hJ ⟶ quotientLocallyRingedSpace A hA :=
    sourceQuotientProjection d (d+r) n (rawPhi r V) (rawPhi_holomorphic r V) A hA q hq
  let T : quotientLocallyRingedSpace K hK ⟶ quotientLocallyRingedSpace I hI :=
    ratioSourceQuotientProjection X Y f hf r V I hI q hq
  have hη : quotientInclusion K hK ≫ ChartedSpace.locallyRingedSpaceMap (rawGraphInsert X Y f hf r V)
      (rawGraphInsert_holomorphic X Y f hf r V) = η ≫ quotientInclusion J hJ :=
    quotientMap_inclusion (rawGraphInsert_holomorphic X Y f hf r V) K hK J hJ
      (rawInsert_ideal X Y f hf r V I hI q hq)
  have hS : quotientInclusion J hJ ≫ ChartedSpace.locallyRingedSpaceMap s hs = S ≫ quotientInclusion A hA :=
    quotientMap_inclusion hs J hJ A hA (le_sumIdeal_left (isCoherent_pullback hs hA))
  have hT : quotientInclusion K hK ≫ ChartedSpace.locallyRingedSpaceMap (ratioSource X Y f hf r V)
      (ratioSource_holomorphic X Y f hf r V) = T ≫ quotientInclusion I hI :=
    quotientMap_inclusion (ratioSource_holomorphic X Y f hf r V) K hK I hI
      (le_sumIdeal_left (isCoherent_pullback (ratioSource_holomorphic X Y f hf r V) hI))
  apply (cancel_mono (quotientInclusion A hA)).mp
  have hl : (η ≫ S) ≫ quotientInclusion A hA = quotientInclusion K hK ≫
      ChartedSpace.locallyRingedSpaceMap (s ∘ rawGraphInsert X Y f hf r V)
        (hs.comp (rawGraphInsert_holomorphic X Y f hf r V)) := by
    rw [Category.assoc,←hS,←Category.assoc,←hη,Category.assoc,←ChartedSpace.locallyRingedSpace_comp]
  have hr : (T ≫ (graphQuotientIso X Y f hf I hI).hom) ≫ quotientInclusion A hA =
      quotientInclusion K hK ≫ ChartedSpace.locallyRingedSpaceMap
        (graphMap X Y f ∘ ratioSource X Y f hf r V)
        ((graphMap_holomorphic X Y f hf).comp (ratioSource_holomorphic X Y f hf r V)) := by
    rw [Category.assoc,graphQuotientIso_ambient,←Category.assoc,←hT,Category.assoc,
      ←ChartedSpace.locallyRingedSpace_comp]
  refine hl.trans ((congrArg (fun k => quotientInclusion K hK ≫ k) ?_).trans hr.symm)
  exact nativeMap_congr (a := r+n) (c := d+n) (funext (rawGraphInsert_source X Y f hf r V))

/-- The FULL base-q triangle fixes the genuine native quotient scalar action. -/
theorem rawQuotientMap_base (I : GermIdeal n X) (hI : I.IsCoherent)
    (q : GermIdeal (d+r) V) (hq : q.IsCoherent) :
    rawQuotientMap X Y f hf r V I hI q hq ≫
      baseQuotientProjection d (d+r) n (rawPhi r V) (rawPhi_holomorphic r V)
        (graphIdeal X Y f I) (graphIdeal_coherent X Y f hf I hI) q hq =
      ratioBaseQuotientProjection X Y f hf r V I hI q hq := by
  let K := ratioIdeal X Y f hf r V I q
  let hK := ratioIdeal_coherent X Y f hf r V I hI q hq
  let J := rawIdeal X Y f r V I q
  let hJ := rawIdeal_coherent X Y f hf r V I hI q hq
  let p : rawOpen X Y r V → V := baseProjection d (d+r) n
    (graphOpen X Y) V (rawPhi r V) (rawPhi_holomorphic r V)
  let hp : ContMDiff 𝓘(ℂ,ComplexModel ((d+r)+n)) 𝓘(ℂ,ComplexModel (d+r)) ∞ p :=
    baseProjection_holomorphic d (d+r) n (graphOpen X Y) V (rawPhi r V) (rawPhi_holomorphic r V)
  let η : quotientLocallyRingedSpace K hK ⟶ quotientLocallyRingedSpace J hJ :=
    rawQuotientMap X Y f hf r V I hI q hq
  let B : quotientLocallyRingedSpace J hJ ⟶ quotientLocallyRingedSpace q hq :=
    baseQuotientProjection d (d+r) n (rawPhi r V) (rawPhi_holomorphic r V)
      (graphIdeal X Y f I) (graphIdeal_coherent X Y f hf I hI) q hq
  let T : quotientLocallyRingedSpace K hK ⟶ quotientLocallyRingedSpace q hq :=
    ratioBaseQuotientProjection X Y f hf r V I hI q hq
  have hη : quotientInclusion K hK ≫ ChartedSpace.locallyRingedSpaceMap (rawGraphInsert X Y f hf r V)
      (rawGraphInsert_holomorphic X Y f hf r V) = η ≫ quotientInclusion J hJ :=
    quotientMap_inclusion (rawGraphInsert_holomorphic X Y f hf r V) K hK J hJ
      (rawInsert_ideal X Y f hf r V I hI q hq)
  have hB : quotientInclusion J hJ ≫ ChartedSpace.locallyRingedSpaceMap p hp = B ≫ quotientInclusion q hq :=
    quotientMap_inclusion hp J hJ q hq (le_sumIdeal_right (isCoherent_pullback hp hq))
  have hT : quotientInclusion K hK ≫ ChartedSpace.locallyRingedSpaceMap (ratioBase X Y f hf r V)
      (ratioBase_holomorphic X Y f hf r V) = T ≫ quotientInclusion q hq :=
    quotientMap_inclusion (ratioBase_holomorphic X Y f hf r V) K hK q hq
      (le_sumIdeal_right (isCoherent_pullback (ratioBase_holomorphic X Y f hf r V) hq))
  apply (cancel_mono (quotientInclusion q hq)).mp
  change (η ≫ B) ≫ quotientInclusion q hq = T ≫ quotientInclusion q hq
  rw [Category.assoc,←hB,←Category.assoc,←hη,←hT,Category.assoc,
    ←ChartedSpace.locallyRingedSpace_comp]
  apply congrArg (fun k => quotientInclusion K hK ≫ k)
  exact nativeMap_congr (a := r+n) (c := d+r) (funext (rawGraphInsert_base X Y f hf r V))

private theorem rawRestriction_source_ambient (I : GermIdeal n X) (hI : I.IsCoherent)
    (q : GermIdeal (d+r) V) (hq : q.IsCoherent) :
    (quotientOpenMap (rawIdeal X Y f r V I q) (rawIdeal_coherent X Y f hf r V I hI q hq)
        (rawInverseOpen X Y f hf r V) ≫
      sourceQuotientProjection d (d+r) n (rawPhi r V) (rawPhi_holomorphic r V)
        (graphIdeal X Y f I) (graphIdeal_coherent X Y f hf I hI) q hq) ≫
      quotientInclusion (graphIdeal X Y f I) (graphIdeal_coherent X Y f hf I hI) =
    quotientInclusion (quotientOpenIdeal (rawIdeal X Y f r V I q) (rawInverseOpen X Y f hf r V))
      (quotientOpenIdeal_coherent _ (rawIdeal_coherent X Y f hf r V I hI q hq) _) ≫
        ChartedSpace.locallyRingedSpaceMap (rawRestrictedSource X Y f hf r V)
          (rawRestrictedSource_holomorphic X Y f hf r V) := by
  let J := rawIdeal X Y f r V I q
  let hJ := rawIdeal_coherent X Y f hf r V I hI q hq
  let A := graphIdeal X Y f I
  let hA := graphIdeal_coherent X Y f hf I hI
  let D := rawInverseOpen X Y f hf r V
  let C := quotientOpenIdeal J D
  let hC : C.IsCoherent := quotientOpenIdeal_coherent J hJ D
  let j0 : D → rawOpen X Y r V := Subtype.val
  let hj0 : ContMDiff 𝓘(ℂ,ComplexModel ((d+r)+n)) 𝓘(ℂ,ComplexModel ((d+r)+n)) ∞ j0 :=
    contMDiff_subtype_val
  let s : rawOpen X Y r V → graphOpen X Y := sourceProjection d (d+r) n
    (graphOpen X Y) V (rawPhi r V) (rawPhi_holomorphic r V)
  let hs : ContMDiff 𝓘(ℂ,ComplexModel ((d+r)+n)) 𝓘(ℂ,ComplexModel (d+n)) ∞ s :=
    sourceProjection_holomorphic d (d+r) n (graphOpen X Y) V (rawPhi r V) (rawPhi_holomorphic r V)
  let S : quotientLocallyRingedSpace J hJ ⟶ quotientLocallyRingedSpace A hA :=
    sourceQuotientProjection d (d+r) n (rawPhi r V) (rawPhi_holomorphic r V) A hA q hq
  let j : quotientLocallyRingedSpace C hC ⟶ quotientLocallyRingedSpace J hJ := quotientOpenMap J hJ D
  have hS : quotientInclusion J hJ ≫ ChartedSpace.locallyRingedSpaceMap s hs = S ≫ quotientInclusion A hA :=
    quotientMap_inclusion hs J hJ A hA (le_sumIdeal_left (isCoherent_pullback hs hA))
  have hj : quotientInclusion C hC ≫ ChartedSpace.locallyRingedSpaceMap j0 hj0 = j ≫ quotientInclusion J hJ :=
    quotientMap_inclusion hj0 C hC J hJ (fun _ _ h => h)
  change (j ≫ S) ≫ quotientInclusion A hA = _
  rw [Category.assoc,←hS,←Category.assoc,←hj,Category.assoc,←ChartedSpace.locallyRingedSpace_comp]
  apply congrArg (fun k => quotientInclusion C hC ≫ k)
  exact nativeMap_congr (a := (d+r)+n) (c := d+n) rfl

private theorem rawRestriction_base_ambient (I : GermIdeal n X) (hI : I.IsCoherent)
    (q : GermIdeal (d+r) V) (hq : q.IsCoherent) :
    (quotientOpenMap (rawIdeal X Y f r V I q) (rawIdeal_coherent X Y f hf r V I hI q hq)
        (rawInverseOpen X Y f hf r V) ≫
      baseQuotientProjection d (d+r) n (rawPhi r V) (rawPhi_holomorphic r V)
        (graphIdeal X Y f I) (graphIdeal_coherent X Y f hf I hI) q hq) ≫ quotientInclusion q hq =
    quotientInclusion (quotientOpenIdeal (rawIdeal X Y f r V I q) (rawInverseOpen X Y f hf r V))
      (quotientOpenIdeal_coherent _ (rawIdeal_coherent X Y f hf r V I hI q hq) _) ≫
        ChartedSpace.locallyRingedSpaceMap (rawRestrictedBase X Y f hf r V)
          (rawRestrictedBase_holomorphic X Y f hf r V) := by
  let J := rawIdeal X Y f r V I q
  let hJ := rawIdeal_coherent X Y f hf r V I hI q hq
  let D := rawInverseOpen X Y f hf r V
  let C := quotientOpenIdeal J D
  let hC : C.IsCoherent := quotientOpenIdeal_coherent J hJ D
  let j0 : D → rawOpen X Y r V := Subtype.val
  let hj0 : ContMDiff 𝓘(ℂ,ComplexModel ((d+r)+n)) 𝓘(ℂ,ComplexModel ((d+r)+n)) ∞ j0 := contMDiff_subtype_val
  let p : rawOpen X Y r V → V := baseProjection d (d+r) n (graphOpen X Y) V (rawPhi r V) (rawPhi_holomorphic r V)
  let hp : ContMDiff 𝓘(ℂ,ComplexModel ((d+r)+n)) 𝓘(ℂ,ComplexModel (d+r)) ∞ p :=
    baseProjection_holomorphic d (d+r) n (graphOpen X Y) V (rawPhi r V) (rawPhi_holomorphic r V)
  let B : quotientLocallyRingedSpace J hJ ⟶ quotientLocallyRingedSpace q hq :=
    baseQuotientProjection d (d+r) n (rawPhi r V) (rawPhi_holomorphic r V)
      (graphIdeal X Y f I) (graphIdeal_coherent X Y f hf I hI) q hq
  let j : quotientLocallyRingedSpace C hC ⟶ quotientLocallyRingedSpace J hJ := quotientOpenMap J hJ D
  have hB : quotientInclusion J hJ ≫ ChartedSpace.locallyRingedSpaceMap p hp = B ≫ quotientInclusion q hq :=
    quotientMap_inclusion hp J hJ q hq (le_sumIdeal_right (isCoherent_pullback hp hq))
  have hj : quotientInclusion C hC ≫ ChartedSpace.locallyRingedSpaceMap j0 hj0 = j ≫ quotientInclusion J hJ :=
    quotientMap_inclusion hj0 C hC J hJ (fun _ _ h => h)
  change (j ≫ B) ≫ quotientInclusion q hq = _
  rw [Category.assoc,←hB,←Category.assoc,←hj,Category.assoc,←ChartedSpace.locallyRingedSpace_comp]
  apply congrArg (fun k => quotientInclusion C hC ≫ k)
  exact nativeMap_congr (a := (d+r)+n) (c := d+r) rfl

private theorem rawReverse_source (I : GermIdeal n X) (hI : I.IsCoherent)
    (q : GermIdeal (d+r) V) (hq : q.IsCoherent) :
    rawReverseQuotientMap X Y f hf r V I hI q hq ≫ ratioSourceQuotientProjection X Y f hf r V I hI q hq =
      (quotientOpenMap (rawIdeal X Y f r V I q) (rawIdeal_coherent X Y f hf r V I hI q hq)
          (rawInverseOpen X Y f hf r V) ≫
        sourceQuotientProjection d (d+r) n (rawPhi r V) (rawPhi_holomorphic r V)
          (graphIdeal X Y f I) (graphIdeal_coherent X Y f hf I hI) q hq) ≫
            (graphQuotientIso X Y f hf I hI).inv := by
  let K := ratioIdeal X Y f hf r V I q
  let hK := ratioIdeal_coherent X Y f hf r V I hI q hq
  let J := rawIdeal X Y f r V I q
  let hJ := rawIdeal_coherent X Y f hf r V I hI q hq
  let D := rawInverseOpen X Y f hf r V
  let C := quotientOpenIdeal J D
  let hC : C.IsCoherent := quotientOpenIdeal_coherent J hJ D
  let Θ : quotientLocallyRingedSpace C hC ⟶ quotientLocallyRingedSpace K hK :=
    rawReverseQuotientMap X Y f hf r V I hI q hq
  let T : quotientLocallyRingedSpace K hK ⟶ quotientLocallyRingedSpace I hI :=
    ratioSourceQuotientProjection X Y f hf r V I hI q hq
  have hΘ : quotientInclusion C hC ≫ ChartedSpace.locallyRingedSpaceMap (rawRetraction X Y f hf r V)
      (rawRetraction_holomorphic X Y f hf r V) = Θ ≫ quotientInclusion K hK :=
    quotientMap_inclusion (rawRetraction_holomorphic X Y f hf r V) C hC K hK
      (rawRetraction_ideal X Y f hf r V I hI q hq)
  have hT : quotientInclusion K hK ≫ ChartedSpace.locallyRingedSpaceMap (ratioSource X Y f hf r V)
      (ratioSource_holomorphic X Y f hf r V) = T ≫ quotientInclusion I hI :=
    quotientMap_inclusion (ratioSource_holomorphic X Y f hf r V) K hK I hI
      (le_sumIdeal_left (isCoherent_pullback (ratioSource_holomorphic X Y f hf r V) hI))
  apply (cancel_mono (quotientInclusion I hI)).mp
  have hl : (Θ ≫ T) ≫ quotientInclusion I hI = quotientInclusion C hC ≫
      ChartedSpace.locallyRingedSpaceMap (ratioSource X Y f hf r V ∘ rawRetraction X Y f hf r V)
        ((ratioSource_holomorphic X Y f hf r V).comp (rawRetraction_holomorphic X Y f hf r V)) := by
    rw [Category.assoc,←hT,←Category.assoc,←hΘ,Category.assoc,←ChartedSpace.locallyRingedSpace_comp]
  rw [hl]
  rw [Category.assoc,graphQuotientIso_inv_source X Y f hf I hI,←Category.assoc,
    rawRestriction_source_ambient X Y f hf r V I hI q hq,Category.assoc,←ChartedSpace.locallyRingedSpace_comp]
  apply congrArg (fun k => quotientInclusion C hC ≫ k)
  exact nativeMap_congr (a := (d+r)+n) (c := n) (funext (rawRetraction_source X Y f hf r V))

private theorem rawReverse_base (I : GermIdeal n X) (hI : I.IsCoherent)
    (q : GermIdeal (d+r) V) (hq : q.IsCoherent) :
    rawReverseQuotientMap X Y f hf r V I hI q hq ≫ ratioBaseQuotientProjection X Y f hf r V I hI q hq =
      quotientOpenMap (rawIdeal X Y f r V I q) (rawIdeal_coherent X Y f hf r V I hI q hq)
          (rawInverseOpen X Y f hf r V) ≫
        baseQuotientProjection d (d+r) n (rawPhi r V) (rawPhi_holomorphic r V)
          (graphIdeal X Y f I) (graphIdeal_coherent X Y f hf I hI) q hq := by
  let K := ratioIdeal X Y f hf r V I q
  let hK := ratioIdeal_coherent X Y f hf r V I hI q hq
  let J := rawIdeal X Y f r V I q
  let hJ := rawIdeal_coherent X Y f hf r V I hI q hq
  let C := quotientOpenIdeal J (rawInverseOpen X Y f hf r V)
  let hC : C.IsCoherent := quotientOpenIdeal_coherent J hJ (rawInverseOpen X Y f hf r V)
  let Θ : quotientLocallyRingedSpace C hC ⟶ quotientLocallyRingedSpace K hK :=
    rawReverseQuotientMap X Y f hf r V I hI q hq
  let T : quotientLocallyRingedSpace K hK ⟶ quotientLocallyRingedSpace q hq :=
    ratioBaseQuotientProjection X Y f hf r V I hI q hq
  have hΘ : quotientInclusion C hC ≫ ChartedSpace.locallyRingedSpaceMap (rawRetraction X Y f hf r V)
      (rawRetraction_holomorphic X Y f hf r V) = Θ ≫ quotientInclusion K hK :=
    quotientMap_inclusion (rawRetraction_holomorphic X Y f hf r V) C hC K hK
      (rawRetraction_ideal X Y f hf r V I hI q hq)
  have hT : quotientInclusion K hK ≫ ChartedSpace.locallyRingedSpaceMap (ratioBase X Y f hf r V)
      (ratioBase_holomorphic X Y f hf r V) = T ≫ quotientInclusion q hq :=
    quotientMap_inclusion (ratioBase_holomorphic X Y f hf r V) K hK q hq
      (le_sumIdeal_right (isCoherent_pullback (ratioBase_holomorphic X Y f hf r V) hq))
  apply (cancel_mono (quotientInclusion q hq)).mp
  have hl : (Θ ≫ T) ≫ quotientInclusion q hq = quotientInclusion C hC ≫
      ChartedSpace.locallyRingedSpaceMap (rawSubstitutedBase X Y f hf r V)
        (rawSubstitutedBase_holomorphic X Y f hf r V) := by
    rw [Category.assoc,←hT,←Category.assoc,←hΘ,Category.assoc,←ChartedSpace.locallyRingedSpace_comp]
    apply congrArg (fun k => quotientInclusion C hC ≫ k)
    exact nativeMap_congr (a := (d+r)+n) (c := d+r) rfl
  rw [hl,rawRestriction_base_ambient X Y f hf r V I hI q hq]
  exact (rawBase_native_eq X Y f hf r V I hI q hq).symm

/-- The second FULL inverse equation uses only the two derived ORIGINAL
projection cuts and genuine analytic-test uniqueness; no inverse packet. -/
private theorem rawReverse_to_raw (I : GermIdeal n X) (hI : I.IsCoherent)
    (q : GermIdeal (d+r) V) (hq : q.IsCoherent) :
    rawReverseQuotientMap X Y f hf r V I hI q hq ≫ rawQuotientMap X Y f hf r V I hI q hq =
      quotientOpenMap (rawIdeal X Y f r V I q) (rawIdeal_coherent X Y f hf r V I hI q hq)
        (rawInverseOpen X Y f hf r V) := by
  let K := ratioIdeal X Y f hf r V I q
  let hK := ratioIdeal_coherent X Y f hf r V I hI q hq
  let J := rawIdeal X Y f r V I q
  let hJ := rawIdeal_coherent X Y f hf r V I hI q hq
  let A := graphIdeal X Y f I
  let hA := graphIdeal_coherent X Y f hf I hI
  let D := rawInverseOpen X Y f hf r V
  let C := quotientOpenIdeal J D
  let hC : C.IsCoherent := quotientOpenIdeal_coherent J hJ D
  let η : quotientLocallyRingedSpace K hK ⟶ quotientLocallyRingedSpace J hJ :=
    rawQuotientMap X Y f hf r V I hI q hq
  let Θ : quotientLocallyRingedSpace C hC ⟶ quotientLocallyRingedSpace K hK :=
    rawReverseQuotientMap X Y f hf r V I hI q hq
  let j : quotientLocallyRingedSpace C hC ⟶ quotientLocallyRingedSpace J hJ := quotientOpenMap J hJ D
  let S : quotientLocallyRingedSpace J hJ ⟶ quotientLocallyRingedSpace A hA :=
    sourceQuotientProjection d (d+r) n (rawPhi r V) (rawPhi_holomorphic r V) A hA q hq
  let B : quotientLocallyRingedSpace J hJ ⟶ quotientLocallyRingedSpace q hq :=
    baseQuotientProjection d (d+r) n (rawPhi r V) (rawPhi_holomorphic r V) A hA q hq
  let Ts : quotientLocallyRingedSpace K hK ⟶ quotientLocallyRingedSpace I hI :=
    ratioSourceQuotientProjection X Y f hf r V I hI q hq
  let Tb : quotientLocallyRingedSpace K hK ⟶ quotientLocallyRingedSpace q hq :=
    ratioBaseQuotientProjection X Y f hf r V I hI q hq
  let e : quotientLocallyRingedSpace I hI ≅ quotientLocallyRingedSpace A hA :=
    graphQuotientIso X Y f hf I hI
  have hηs : η ≫ S = Ts ≫ e.hom := rawQuotientMap_source X Y f hf r V I hI q hq
  have hΘs : Θ ≫ Ts = (j ≫ S) ≫ e.inv := rawReverse_source X Y f hf r V I hI q hq
  have hs : (Θ ≫ η) ≫ S = j ≫ S := by
    calc
      _ = Θ ≫ (η ≫ S) := Category.assoc _ _ _
      _ = Θ ≫ (Ts ≫ e.hom) := congrArg (fun k => Θ ≫ k) hηs
      _ = (Θ ≫ Ts) ≫ e.hom := (Category.assoc _ _ _).symm
      _ = ((j ≫ S) ≫ e.inv) ≫ e.hom := congrArg (fun k => k ≫ e.hom) hΘs
      _ = _ := by simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
  have hηb : η ≫ B = Tb := rawQuotientMap_base X Y f hf r V I hI q hq
  have hΘb : Θ ≫ Tb = j ≫ B := rawReverse_base X Y f hf r V I hI q hq
  have hb : (Θ ≫ η) ≫ B = j ≫ B := by rw [Category.assoc,hηb,hΘb]
  have hηp : η ≫ quotientPointMap J hJ = quotientPointMap K hK :=
    quotientMap_point (rawGraphInsert_holomorphic X Y f hf r V) K hK J hJ
      (rawInsert_ideal X Y f hf r V I hI q hq)
  have hΘp : Θ ≫ quotientPointMap K hK = quotientPointMap C hC :=
    quotientMap_point (rawRetraction_holomorphic X Y f hf r V) C hC K hK
      (rawRetraction_ideal X Y f hf r V I hI q hq)
  have hFp : (Θ ≫ η) ≫ quotientPointMap J hJ = quotientPointMap C hC := by
    rw [Category.assoc,hηp,hΘp]
  have hjp : j ≫ quotientPointMap J hJ = quotientPointMap C hC := quotientOpenMap_point J hJ D
  exact HironakaAnalyticTestBaseChangeUniversality.factor_hom_ext
    (rawPhi r V) (rawPhi_holomorphic r V) C hC A hA q hq (Θ ≫ η) j hFp hjp hs hb

/-- Actual graph elimination in the LITERAL raw741 native quotient.
All domains, whole ideal conditions and BOTH FULL inverses were produced
from ordinary f/I/q; arbitrary nonradical ideals and empty supports remain. -/
def rawGraphBaseChangeIso (I : GermIdeal n X) (hI : I.IsCoherent)
    (q : GermIdeal (d+r) V) (hq : q.IsCoherent) :
    quotientLocallyRingedSpace (ratioIdeal X Y f hf r V I q)
      (ratioIdeal_coherent X Y f hf r V I hI q hq) ≅
    quotientLocallyRingedSpace (rawIdeal X Y f r V I q)
      (rawIdeal_coherent X Y f hf r V I hI q hq) := by
  let K := ratioIdeal X Y f hf r V I q
  let hK := ratioIdeal_coherent X Y f hf r V I hI q hq
  let J := rawIdeal X Y f r V I q
  let hJ := rawIdeal_coherent X Y f hf r V I hI q hq
  let C := quotientOpenIdeal J (rawInverseOpen X Y f hf r V)
  let hC : C.IsCoherent := quotientOpenIdeal_coherent J hJ (rawInverseOpen X Y f hf r V)
  let η : quotientLocallyRingedSpace K hK ⟶ quotientLocallyRingedSpace J hJ :=
    rawQuotientMap X Y f hf r V I hI q hq
  let Θ : quotientLocallyRingedSpace C hC ⟶ quotientLocallyRingedSpace K hK :=
    rawReverseQuotientMap X Y f hf r V I hI q hq
  let a : quotientLocallyRingedSpace K hK ⟶ quotientLocallyRingedSpace C hC :=
    rawInsertRestrictedQuotientMap X Y f hf r V I hI q hq
  let e : quotientLocallyRingedSpace C hC ≅ quotientLocallyRingedSpace J hJ :=
    rawRestrictionIso X Y f hf r V I hI q hq
  have ha : a ≫ e.hom = η := rawInsertRestricted_to_raw X Y f hf r V I hI q hq
  have hleft : a ≫ Θ = 𝟙 (quotientLocallyRingedSpace K hK) := rawInsertReverse_id X Y f hf r V I hI q hq
  have hright : Θ ≫ η = e.hom := rawReverse_to_raw X Y f hf r V I hI q hq
  refine ⟨η,e.inv ≫ Θ,?_,?_⟩
  · calc
      _ = (a ≫ e.hom) ≫ (e.inv ≫ Θ) := congrArg (fun k => k ≫ (e.inv ≫ Θ)) ha.symm
      _ = a ≫ Θ := by simp only [Category.assoc,Iso.hom_inv_id_assoc]
      _ = _ := hleft
  · calc
      _ = e.inv ≫ (Θ ≫ η) := Category.assoc _ _ _
      _ = e.inv ≫ e.hom := congrArg (fun k => e.inv ≫ k) hright
      _ = _ := e.inv_hom_id

/-- FULL ORIGINAL graph-source triangle for the constructed native isomorphism. -/
theorem rawGraphBaseChangeIso_source (I : GermIdeal n X) (hI : I.IsCoherent)
    (q : GermIdeal (d+r) V) (hq : q.IsCoherent) :
    (rawGraphBaseChangeIso X Y f hf r V I hI q hq).hom ≫
      sourceQuotientProjection d (d+r) n (rawPhi r V) (rawPhi_holomorphic r V)
        (graphIdeal X Y f I) (graphIdeal_coherent X Y f hf I hI) q hq =
      ratioSourceQuotientProjection X Y f hf r V I hI q hq ≫
        (graphQuotientIso X Y f hf I hI).hom :=
  rawQuotientMap_source X Y f hf r V I hI q hq

/-- The SAME native isomorphism is over the original source Q(I). -/
theorem rawGraphBaseChangeIso_original_source (I : GermIdeal n X) (hI : I.IsCoherent)
    (q : GermIdeal (d+r) V) (hq : q.IsCoherent) :
    ((rawGraphBaseChangeIso X Y f hf r V I hI q hq).hom ≫
      sourceQuotientProjection d (d+r) n (rawPhi r V) (rawPhi_holomorphic r V)
        (graphIdeal X Y f I) (graphIdeal_coherent X Y f hf I hI) q hq) ≫
          (graphQuotientIso X Y f hf I hI).inv = ratioSourceQuotientProjection X Y f hf r V I hI q hq := by
  rw [rawGraphBaseChangeIso_source X Y f hf r V I hI q hq]
  simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id]

/-- FULL native q-base equality, hence the actual q-stalk scalar action. -/
theorem rawGraphBaseChangeIso_base (I : GermIdeal n X) (hI : I.IsCoherent)
    (q : GermIdeal (d+r) V) (hq : q.IsCoherent) :
    (rawGraphBaseChangeIso X Y f hf r V I hI q hq).hom ≫
      baseQuotientProjection d (d+r) n (rawPhi r V) (rawPhi_holomorphic r V)
        (graphIdeal X Y f I) (graphIdeal_coherent X Y f hf I hI) q hq =
      ratioBaseQuotientProjection X Y f hf r V I hI q hq :=
  rawQuotientMap_base X Y f hf r V I hI q hq

/-- EVERY original whole ambient-stalk numerator retains its actual
holomorphic graph substitution; no sampled coordinate-only comparison. -/
theorem rawGraphBaseChangeIso_stalk_mk (I : GermIdeal n X) (hI : I.IsCoherent)
    (q : GermIdeal (d+r) V) (hq : q.IsCoherent) (x : (ratioIdeal X Y f hf r V I q).zeroLocus)
    (g : actualComplexStructureStalk (n := (d+r)+n) (rawGraphInsert X Y f hf r V x.val)) :
    quotientStalkWholeEquiv (ratioIdeal X Y f hf r V I q) (ratioIdeal_coherent X Y f hf r V I hI q hq) x
      ((rawGraphBaseChangeIso X Y f hf r V I hI q hq).hom.stalkMap x
        ((quotientStalkWholeEquiv (rawIdeal X Y f r V I q) (rawIdeal_coherent X Y f hf r V I hI q hq)
          ((rawGraphBaseChangeIso X Y f hf r V I hI q hq).hom.base x)).symm
          (Ideal.Quotient.mk (actualWholeSheafStalkIdeal (rawIdeal X Y f r V I q)
            (rawGraphInsert X Y f hf r V x.val)) g))) =
      Ideal.Quotient.mk (actualWholeSheafStalkIdeal (ratioIdeal X Y f hf r V I q) x.val)
        ((ChartedSpace.locallyRingedSpaceMap (rawGraphInsert X Y f hf r V)
          (rawGraphInsert_holomorphic X Y f hf r V)).stalkMap x.val g) :=
  quotientMap_stalk_mk (rawGraphInsert_holomorphic X Y f hf r V)
    _ (ratioIdeal_coherent X Y f hf r V I hI q hq) _ (rawIdeal_coherent X Y f hf r V I hI q hq)
    (rawInsert_ideal X Y f hf r V I hI q hq) x g

/-- EVERY raw support point is covered; no point of a future strict image
is an input to the whole-kernel comparison. -/
theorem rawGraphBaseChangeIso_base_surjective (I : GermIdeal n X) (hI : I.IsCoherent)
    (q : GermIdeal (d+r) V) (hq : q.IsCoherent) :
    Function.Surjective (rawGraphBaseChangeIso X Y f hf r V I hI q hq).hom.base := by
  intro y
  refine ⟨(rawGraphBaseChangeIso X Y f hf r V I hI q hq).inv.base y,?_⟩
  exact LocallyRingedSpace.iso_inv_base_hom_base_apply _ y

private theorem quotientMap_ambient_kernel_of_injective
    {a c : ℕ} {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (ComplexModel a) M] [IsComplexManifold a M]
    [ChartedSpace (ComplexModel c) N] [IsComplexManifold c N]
    {g : M → N} (hg : ContMDiff 𝓘(ℂ,ComplexModel a) 𝓘(ℂ,ComplexModel c) ∞ g)
    (A : GermIdeal a M) (hA : A.IsCoherent) (B : GermIdeal c N) (hB : B.IsCoherent)
    (hAB : GermIdeal.Le (GermIdeal.pullback (m := a) g B) A)
    (x : A.zeroLocus)
    (hinj : Function.Injective ((quotientMap hg A hA B hB hAB).stalkMap x)) :
    RingHom.ker (((quotientInclusion A hA).stalkMap x).hom.comp
      ((ChartedSpace.locallyRingedSpaceMap g hg).stalkMap x.val).hom) =
        actualWholeSheafStalkIdeal B (g x.val) := by
  let y : B.zeroLocus := (quotientMap hg A hA B hB hAB).base x
  let E := quotientStalkWholeEquiv A hA x
  let F := quotientStalkWholeEquiv B hB y
  ext v
  change actualComplexStructureStalk (n := c) (g x.val) at v
  have hn : F.symm (Ideal.Quotient.mk (actualWholeSheafStalkIdeal B (g x.val)) v) =
      (quotientInclusion B hB).stalkMap y v := by
    apply F.injective
    exact (F.apply_symm_apply _).trans (quotientInclusion_stalk B hB y v).symm
  have hc : (quotientInclusion A hA).stalkMap x
      ((ChartedSpace.locallyRingedSpaceMap g hg).stalkMap x.val v) =
      (quotientMap hg A hA B hB hAB).stalkMap x ((quotientInclusion B hB).stalkMap y v) := by
    apply E.injective
    calc
      _ = Ideal.Quotient.mk (actualWholeSheafStalkIdeal A x.val)
          ((ChartedSpace.locallyRingedSpaceMap g hg).stalkMap x.val v) :=
        quotientInclusion_stalk A hA x _
      _ = E ((quotientMap hg A hA B hB hAB).stalkMap x
          (F.symm (Ideal.Quotient.mk (actualWholeSheafStalkIdeal B (g x.val)) v))) :=
        (quotientMap_stalk_mk hg A hA B hB hAB x v).symm
      _ = _ := congrArg (fun w => E ((quotientMap hg A hA B hB hAB).stalkMap x w)) hn
  change (quotientInclusion A hA).stalkMap x
    ((ChartedSpace.locallyRingedSpaceMap g hg).stalkMap x.val v) = 0 ↔ _
  rw [hc]
  have hker : RingHom.ker ((quotientInclusion B hB).stalkMap y).hom =
      actualWholeSheafStalkIdeal B (g x.val) := quotientInclusion_stalk_kernel B hB y
  constructor
  · intro hv
    have hz : (quotientInclusion B hB).stalkMap y v = 0 := hinj (by simpa only [map_zero] using hv)
    have hm : v ∈ RingHom.ker ((quotientInclusion B hB).stalkMap y).hom := hz
    rw [hker] at hm
    exact hm
  · intro hv
    have hm : v ∈ RingHom.ker ((quotientInclusion B hB).stalkMap y).hom := by
      rw [hker]
      exact hv
    change (quotientInclusion B hB).stalkMap y v = 0 at hm
    rw [hm,map_zero]

/-- The ENTIRE original raw ideal is the actual graph-substitution kernel
in the eliminated native stalk, with every nilpotent class retained. -/
theorem rawGraphBaseChangeIso_ambient_kernel (I : GermIdeal n X) (hI : I.IsCoherent)
    (q : GermIdeal (d+r) V) (hq : q.IsCoherent) (x : (ratioIdeal X Y f hf r V I q).zeroLocus) :
    RingHom.ker (((quotientInclusion (ratioIdeal X Y f hf r V I q)
      (ratioIdeal_coherent X Y f hf r V I hI q hq)).stalkMap x).hom.comp
        ((ChartedSpace.locallyRingedSpaceMap (rawGraphInsert X Y f hf r V)
          (rawGraphInsert_holomorphic X Y f hf r V)).stalkMap x.val).hom) =
      actualWholeSheafStalkIdeal (rawIdeal X Y f r V I q) (rawGraphInsert X Y f hf r V x.val) := by
  let K := ratioIdeal X Y f hf r V I q
  let hK := ratioIdeal_coherent X Y f hf r V I hI q hq
  let J := rawIdeal X Y f r V I q
  let hJ := rawIdeal_coherent X Y f hf r V I hI q hq
  let e : quotientLocallyRingedSpace K hK ≅ quotientLocallyRingedSpace J hJ :=
    rawGraphBaseChangeIso X Y f hf r V I hI q hq
  let : IsIso e.hom.toShHom.hom := by infer_instance
  have hinj : Function.Injective (e.hom.stalkMap x) := by
    change Function.Injective (e.hom.toHom.stalkMap x)
    exact (ConcreteCategory.bijective_of_isIso (e.hom.toHom.stalkMap x)).1
  exact quotientMap_ambient_kernel_of_injective
    (rawGraphInsert_holomorphic X Y f hf r V) K hK J hJ
    (rawInsert_ideal X Y f hf r V I hI q hq) x hinj

end RawBaseChange

end Hironaka.HironakaGraphBaseChangeElimination
