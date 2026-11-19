import Hironaka.Resolution.HironakaG10RegularCentreUniformArtinRees
import Hironaka.Resolution.HironakaGraphBaseChangeElimination
import Hironaka.Resolution.HironakaActualSingularSubmersionPullback
import Hironaka.Resolution.HironakaSmoothSubmersionMonomialOpenCharts
import Hironaka.Analytic.ConstantRankSubmanifold
import Hironaka.Analytic.PointSupportedIdealPrincipalization
import Hironaka.Resolution.HironakaHilbertSamuelTangentValue
import Hironaka.Resolution.HironakaG10FlatOrdinaryPointFlattener
import Hironaka.Resolution.HironakaActualCoherentWeightedCoefficientMarked

/-!
# Uniform Artin--Rees for actual local holomorphic generator functions

Mathematics first:
`work/hironaka-codex-20261112/G10-GRAPH-BRIDGE-MATHEMATICS.md`.
Blueprint: `hironaka-g10-graph-centre-uniform-artin-rees.tex`.
Source: Hironaka (1975), Lemma 3.2, printed p. 531 (PDF p. 30).

Reuse the already coherent whole graph ideal on actual source/target opens.
The regular target-zero fibre has the full coordinate ideal. Actual graph
trace maps that ideal to the original function-generator ideal, preserving
all multiplicities. It also maps intersection with a whole comap ideal
exactly. No global extension or uniformity certificate is assumed.
-/

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG10GraphCentreUniformArtinRees

noncomputable section

open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaG10ChowUniformArtinRees HironakaG10RegularCentreUniformArtinRees
  HironakaGraphBaseChangeElimination HironakaChowRelativeGraphPresentation
  HironakaRelativeNormalIdeal HironakaActualCentreJointJets
  HironakaActualIntrinsicStableAmbientIso HironakaActualJointBaseFibre
  HironakaRelativeNormalFibreHilbertSamuel
  HironakaHolomorphicJetMonomialSpan
  HironakaActualWholeStalkHolomorphicPullback HironakaHolomorphicJetChartInvariance
  HironakaActualOpenIntrinsicHS
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaHolomorphicJetRankLoci
  HironakaActualSingularSubmersionPullback
  HironakaSmoothSubmersionMonomialChartPullback
  HironakaActualCoherentWeightedCoefficientMarked

private theorem opens_chart_apply {a : ℕ} (U : Opens (ComplexModel a)) (x z : U) :
    chartAt (ComplexModel a) x z = z.val := by
  simp only [Opens.chartAt_eq, chartAt_self_eq,
    OpenPartialHomeomorph.subtypeRestr_coe, OpenPartialHomeomorph.refl_apply]
  rfl

private theorem opens_chart_source {a : ℕ} (U : Opens (ComplexModel a)) (x : U) :
    (chartAt (ComplexModel a) x).source = univ := by
  simp only [Opens.chartAt_eq, chartAt_self_eq,
    OpenPartialHomeomorph.subtypeRestr_source, OpenPartialHomeomorph.refl_source,
    preimage_univ]

/-- Mapping an intersection with a WHOLE preimage ideal preserves that
intersection for a surjective map, with no radical or support replacement. -/
theorem map_inf_comap_eq_of_surjective {R S : Type*} [CommRing R] [CommRing S]
    (q : R →+* S) (hq : Function.Surjective q) (J : Ideal R) (L : Ideal S) :
    Ideal.map q (J ⊓ Ideal.comap q L) = Ideal.map q J ⊓ L := by
  apply le_antisymm
  · exact (Ideal.map_inf_le q).trans (inf_le_inf_left _ (Ideal.map_comap_le))
  · intro z hz
    obtain ⟨a,ha,rfl⟩ := (Ideal.mem_map_iff_of_surjective q hq).mp hz.1
    exact Ideal.mem_map_of_mem q ⟨ha,hz.2⟩

/-- A surjective whole graph/quotient map carries an Artin--Rees bound
against a complete preimage ideal to the SAME bound downstairs. -/
theorem isArtinReesNumber_of_comap {R S : Type*} [CommRing R] [CommRing S]
    (q : R →+* S) (hq : Function.Surjective q) (L : Ideal S) (J : Ideal R)
    (α : ℕ) (h : IsArtinReesNumber (Ideal.comap q L) J α) :
    IsArtinReesNumber L (Ideal.map q J) α := by
  have hmap : ∀ K : Ideal R, Ideal.map q (Ideal.comap q L ⊓ K) = L ⊓ Ideal.map q K := by
    intro K
    rw [inf_comm, map_inf_comap_eq_of_surjective q hq, inf_comm]
  intro m hm
  have hh : Ideal.map q (Ideal.comap q L ⊓ J^m) ≤
      Ideal.map q (J^(m-α) * (Ideal.comap q L ⊓ J^α)) := Ideal.map_mono (h m hm)
  simpa only [hmap, Ideal.map_pow, Ideal.map_mul] using hh

private theorem whole_point_ideal {a : ℕ} {P : Type} [TopologicalSpace P]
    [ChartedSpace (ComplexModel a) P] [IsComplexManifold a P] (p : P) :
    wholeChartStalkIdeal (vanishingIdeal (n := a) ({p} : Set P)) p p
      (mem_chart_source _ p) = IsLocalRing.maximalIdeal (HolGerm (ComplexModel a)) := by
  apply le_antisymm
  · exact HironakaHilbertSamuelTangentValue.whole_vanishing_stalk_le_maximalIdeal
      (Set.mem_singleton p)
  · intro g hg
    obtain ⟨H,hH,rfl⟩ := HolGerm.exists_eq_mk g
    have hH0 : H 0 = 0 := by
      simpa only [HolGerm.eval_mk] using (HolGerm.mem_maximalIdeal_iff _).mp hg
    apply HironakaG10FlatOrdinaryPointFlattener.mk_mem_wholeChartStalkIdeal_vanishing
      ({p} : Set P) p H hH
    exact Eventually.of_forall fun y hy => by
      rw [Set.mem_singleton_iff.mp hy, sub_self]
      exact hH0

section Graph

variable {r n : ℕ} (X : Opens (ComplexModel n)) (Y : Opens (ComplexModel r))

/-- The smooth coordinate fibre in the EXISTING real graph ambient. -/
def targetZeroFibre : Set (graphOpen X Y) := {w | (graphTarget X Y w).val = 0}

theorem regularAtDim_targetZeroFibre (w : graphOpen X Y) (hw : w ∈ targetZeroFibre X Y) :
    RegularAtDim (n := r+n) (targetZeroFibre X Y) w n := by
  let Q := actualJointNormalProjection r n
  let k := actualJointNormalInclusion r n
  have hset : {z : ComplexModel (r+n) | Q z ∈ (univ : Set (ComplexModel n)) ∧ k (Q z) = z} =
      {z : ComplexModel (r+n) | tangentProjection r n z = 0} := by
    ext z
    simp only [mem_ofPred_eq, mem_univ, true_and]
    constructor
    · intro hz
      have hh := congrArg (tangentProjection r n) hz
      simpa only [k, tangentProjection_actualJointNormalInclusion] using hh.symm
    · intro hz
      have hh := join_projections z
      simpa only [HironakaActualIntrinsicStableAmbientIso.join, hz, map_zero, zero_add, k, Q] using hh
  have hky : k (Q w.val) = w.val := by
    have hh := join_projections w.val
    simpa only [HironakaActualIntrinsicStableAmbientIso.join, show tangentProjection r n w.val = 0 from hw,
      map_zero, zero_add, k, Q] using hh
  have hreg := ConstantRankSubmanifold.regularAtDim_graph Q isOpen_univ
    k.differentiable.differentiableOn (fun v _ => actualJointNormalProjection_inclusion r n v)
    (mem_univ (Q w.val)) hky
  change RegularAtDim (n := r+n)
    ((Subtype.val : graphOpen X Y → ComplexModel (r+n)) ⁻¹'
      {z | tangentProjection r n z = 0}) w n
  apply AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr
  simpa only [hset, finrank_euclideanSpace_fin] using hreg

/-- The actual target projection is a submersion on its genuine open. -/
theorem isSubmersion_graphTarget :
    Manifold.IsSubmersion 𝓘(ℂ,ComplexModel (r+n)) 𝓘(ℂ,ComplexModel r) ∞
      (graphTarget X Y) := by
  have h : Manifold.IsSubmersionOfComplement (ComplexModel n)
      𝓘(ℂ,ComplexModel (r+n)) 𝓘(ℂ,ComplexModel r) ∞ (graphTarget X Y) := by
    intro w
    let g := graphTarget X Y
    let a := chartAt (ComplexModel (r+n)) w
    let b := chartAt (ComplexModel r) (g w)
    apply Manifold.IsSubmersionAtOfComplement.mk_of_charts
      (splitCoordinates r n) a b (mem_chart_source _ w) (mem_chart_source _ (g w))
      (IsManifold.chart_mem_maximalAtlas _) (IsManifold.chart_mem_maximalAtlas _)
    · intro z hz
      change g z ∈ b.source
      rw [opens_chart_source]
      exact mem_univ _
    · intro z hz
      have hz' : z ∈ a.target := by simpa using hz
      have hsymm : (a.symm z).val = z := by
        have he := a.right_inv hz'
        change chartAt (ComplexModel (r+n)) w (a.symm z) = z at he
        rwa [opens_chart_apply] at he
      change b (g (a.symm z)) = (splitCoordinates r n z).1
      rw [opens_chart_apply]
      change tangentProjection r n (a.symm z).val = fibreProjection r n z
      rw [hsymm]
      ext i
      rw [tangentProjection_apply, fibreProjection_apply]
  exact h.isSubmersion

private theorem graphTarget_germ (w : graphOpen X Y) :
    actualHolomorphicGermPullback (graphTarget_holomorphic X Y) w = tangentPullback r n := by
  have ht : actualTranslatedMap (graphTarget X Y) w =ᶠ[𝓝 (0 : ComplexModel (r+n))]
      tangentProjection r n := by
    filter_upwards [actualTranslatedMap_val_eventually (graphOpen X Y) w] with z hz
    change tangentProjection r n
      (((chartAt (ComplexModel (r+n)) w).symm
        (z+(chartAt (ComplexModel (r+n)) w) w)).val) - tangentProjection r n w.val = _
    rw [← map_sub]
    exact congrArg (tangentProjection r n) hz
  apply AlgHom.ext
  intro g
  induction g using HolGerm.induction_on with
  | h H hH =>
      unfold actualHolomorphicGermPullback tangentPullback
      rw [compAlgHom_mk, compAlgHom_mk]
      exact HolGerm.mk_eq_mk_iff.mpr (ht.mono fun z hz => congrArg H hz)

/-- The full smooth fibre ideal is the actual first-coordinate ideal,
at every true fibre point of the EXISTING real graph open. -/
theorem whole_targetZeroFibre_ideal (w : graphOpen X Y) (hw : w ∈ targetZeroFibre X Y) :
    wholeChartStalkIdeal (vanishingIdeal (n := r+n) (targetZeroFibre X Y)) w w
      (mem_chart_source _ w) = originalBaseMaximalIdeal r n := by
  let p := graphTarget X Y w
  have hp0 : p.val = 0 := hw
  have hp : (vanishingIdeal (n := r) ({p} : Set Y)).IsCoherent := by
    simpa only [GermIdealOrder.pointIdeal] using
      (PointSupportedIdealPrincipalization.singleton_geometry_and_coherence p).2
  have hpre : (graphTarget X Y) ⁻¹' ({p} : Set Y) = targetZeroFibre X Y := by
    ext z
    change graphTarget X Y z = p ↔ (graphTarget X Y z).val = 0
    constructor
    · intro hz
      exact (congrArg Subtype.val hz).trans hp0
    · intro hz
      apply Subtype.ext
      exact hz.trans hp0.symm
  have hh := map_wholeChartStalkIdeal_actual_pullback (graphTarget_holomorphic X Y)
    (vanishingIdeal (n := r) ({p} : Set Y)) hp w
  rw [pullback_vanishingIdeal_submersion (isSubmersion_graphTarget X Y), hpre,
    whole_point_ideal, graphTarget_germ X Y] at hh
  exact hh.symm

/-- The actual original ideal generated by the coordinate functions of the
given holomorphic map. It retains powers and non-radical multiplicities. -/
abbrev functionCentreIdeal (f : X → Y) : GermIdeal n X :=
  finiteFunctionIdeal (fun i : Fin r => fun y : X => (f y).val i)

variable (f : X → Y)
  (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel r) ∞ f)

include hf in
private theorem coordinateFunction_holomorphic (i : Fin r) (y : X) :
    HolomorphicAt n (fun z : X => (f z).val i) y :=
  Eventually.of_forall fun _ =>
    ((((EuclideanSpace.proj i : ComplexModel r →L[ℂ] ℂ)).contDiff.contMDiff.comp
      (contMDiff_subtype_val.comp hf)).contMDiffAt).mdifferentiableAt (by simp)

private theorem whole_functionCentreIdeal (y : X) :
    wholeChartStalkIdeal (functionCentreIdeal X Y f) y y (mem_chart_source _ y) =
      Ideal.span (range fun i : Fin r => chartTranslatedGerm y y (mem_chart_source _ y)
        (fun z : X => (f z).val i) (coordinateFunction_holomorphic X Y f hf i y)) :=
  wholeChartStalkIdeal_eq_actual_generator_span _ y _
    (fun i => coordinateFunction_holomorphic X Y f hf i y) (fun _ => Iff.rfl)

/-- At a zero of the original generator map, actual graph substitution sends
the WHOLE ambient coordinate-fibre ideal to the SAME original generated ideal. -/
theorem graphTrace_image_functionCentreIdeal (y : X) (hy : (f y).val = 0) :
    Ideal.map (relativeGraphTrace r n (actualTranslatedMap f y)
      (actualTranslatedMap_holomorphic hf y) (actualTranslatedMap_zero f y)).toRingHom
      (originalBaseMaximalIdeal r n) =
        wholeChartStalkIdeal (functionCentreIdeal X Y f) y y (mem_chart_source _ y) := by
  let F : ComplexModel n → ComplexModel r := actualTranslatedMap (n := r) (m := n) f y
  let hF := actualTranslatedMap_holomorphic hf y
  let hF0 := actualTranslatedMap_zero (n := r) (m := n) f y
  have hcoord (i : Fin r) : compAlgHom F hF hF0 (coordinateGerm i) =
      chartTranslatedGerm y y (mem_chart_source _ y) (fun z : X => (f z).val i)
        (coordinateFunction_holomorphic X Y f hf i y) := by
    unfold coordinateGerm chartTranslatedGerm translatedGerm
    rw [compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun z => by
      change actualTranslatedMap f y z i = _
      unfold actualTranslatedMap
      simp only [opens_chart_apply, hy, sub_zero]
  have hbasecoord (i : Fin r) : coordinateGerm (i.castAdd n) =
      tangentPullback r n (coordinateGerm i) := by
    unfold tangentPullback coordinateGerm
    rw [compAlgHom_mk]
    rfl
  rw [baseMaximalIdeal_eq_tangent_span, Ideal.map_span,
    ← Set.range_comp, whole_functionCentreIdeal X Y f hf y]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  change relativeGraphTrace r n F hF hF0 (coordinateGerm (i.castAdd n)) = _
  rw [hbasecoord, relativeGraphTrace_basePullback]
  exact hcoord i

include hf in
private theorem whole_functionCentreIdeal_eq_top_of_ne_zero
    (y : X) (hy : (f y).val ≠ 0) :
    wholeChartStalkIdeal (functionCentreIdeal X Y f) y y (mem_chart_source _ y) = ⊤ := by
  classical
  have hi : ∃ i : Fin r, (f y).val i ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hy
    ext i
    exact hn i
  obtain ⟨i,hi⟩ := hi
  rw [whole_functionCentreIdeal X Y f hf y]
  let G := fun j : Fin r => chartTranslatedGerm y y (mem_chart_source _ y)
    (fun z : X => (f z).val j) (coordinateFunction_holomorphic X Y f hf j y)
  have hu : IsUnit (G i) := by
    apply (HolGerm.isUnit_iff_eval_ne_zero _).mpr
    simpa only [G, chartTranslatedGerm, translatedGerm, HolGerm.eval_mk, zero_add,
      (chartAt (ComplexModel n) y).left_inv (mem_chart_source _ y)] using hi
  exact (Ideal.span (range G)).eq_top_of_isUnit_mem (Ideal.subset_span ⟨i,rfl⟩) hu

private theorem regular_uniform_any_dimension {a b : ℕ} {P : Type}
    [TopologicalSpace P] [ChartedSpace (ComplexModel a) P] [IsComplexManifold a P]
    (C : Set P) (x : P) (hreg : RegularAtDim (n := a) C x b)
    (I : GermIdeal a P) (hI : I.IsCoherent) :
    ∃ α : ℕ, ∃ O : Set P, IsOpen O ∧ x ∈ O ∧ ∀ y ∈ C ∩ O,
      IsArtinReesNumber (wholeChartStalkIdeal I y y (mem_chart_source _ y))
        (wholeChartStalkIdeal (vanishingIdeal (n := a) C) y y (mem_chart_source _ y)) α := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le hreg.1
  exact exists_original_regular_centre_uniform_artinRees C x hreg I hI

include hf in
/-- Genuine local holomorphic generator functions and an arbitrary coherent
original ideal supply ONE Artin--Rees exponent on ONE original open, including
points away from the zero fibre. The graph and its regular ambient fibre are
constructed by existing APIs; no uniformity certificate is an input. -/
theorem exists_uniform_artinRees_functionCentre (I : GermIdeal n X) (hI : I.IsCoherent)
    (x : X) (hx : (f x).val = 0) :
    ∃ α : ℕ, ∃ O : Set X, IsOpen O ∧ x ∈ O ∧ ∀ y ∈ O,
      IsArtinReesNumber (wholeChartStalkIdeal I y y (mem_chart_source _ y))
        (wholeChartStalkIdeal (functionCentreIdeal X Y f) y y (mem_chart_source _ y)) α := by
  have hxC : graphMap X Y f x ∈ targetZeroFibre X Y := by
    change (graphTarget X Y (graphMap X Y f x)).val = 0
    rwa [graphTarget_graphMap]
  obtain ⟨α,V,hV,hxV,hAR⟩ := regular_uniform_any_dimension (targetZeroFibre X Y)
    (graphMap X Y f x) (regularAtDim_targetZeroFibre X Y _ hxC)
    (graphIdeal X Y f I) (graphIdeal_coherent X Y f hf I hI)
  let O : Set X := (graphMap X Y f) ⁻¹' V
  refine ⟨α,O,hV.preimage (graphMap_holomorphic X Y f hf).continuous,hxV,fun y hy => ?_⟩
  by_cases hy0 : (f y).val = 0
  · have hyC : graphMap X Y f y ∈ targetZeroFibre X Y := by
      change (graphTarget X Y (graphMap X Y f y)).val = 0
      rwa [graphTarget_graphMap]
    let F : ComplexModel n → ComplexModel r := actualTranslatedMap (n := r) (m := n) f y
    let hF := actualTranslatedMap_holomorphic hf y
    let hF0 := actualTranslatedMap_zero (n := r) (m := n) f y
    let q := relativeGraphTrace r n F hF hF0
    let L := wholeChartStalkIdeal I y y (mem_chart_source _ y)
    have hq : Function.Surjective q := fun g =>
      ⟨relativeSourcePullback r n g, relativeGraphTrace_sourcePullback r n F hF hF0 g⟩
    have hh := hAR (graphMap X Y f y) ⟨hyC,hy⟩
    rw [whole_graph_chart X Y f hf I hI y,
      relativeGraphIdeal_eq_comap r n F hF hF0,
      whole_targetZeroFibre_ideal X Y _ hyC] at hh
    have hdown := isArtinReesNumber_of_comap q.toRingHom hq L
      (originalBaseMaximalIdeal r n) α hh
    rwa [graphTrace_image_functionCentreIdeal X Y f hf y hy0] at hdown
  · have htop := whole_functionCentreIdeal_eq_top_of_ne_zero X Y f hf y hy0
    simp [IsArtinReesNumber, htop, Ideal.top_pow, Ideal.top_mul]

include hf in
/-- The original starting point may be arbitrary: at a nonzero generator
value continuity supplies a whole neighbourhood with unit centre ideal. -/
theorem exists_uniform_artinRees_functionCentre_all_starts
    (I : GermIdeal n X) (hI : I.IsCoherent) (x : X) :
    ∃ α : ℕ, ∃ O : Set X, IsOpen O ∧ x ∈ O ∧ ∀ y ∈ O,
      IsArtinReesNumber (wholeChartStalkIdeal I y y (mem_chart_source _ y))
        (wholeChartStalkIdeal (functionCentreIdeal X Y f) y y (mem_chart_source _ y)) α := by
  by_cases hx : (f x).val = 0
  · exact exists_uniform_artinRees_functionCentre X Y f hf I hI x hx
  · let O : Set X := {y | (f y).val ≠ 0}
    have hcont : Continuous (fun y : X => (f y).val) :=
      continuous_subtype_val.comp hf.continuous
    have hO : IsOpen O := by
      convert ((isClosed_singleton : IsClosed ({0} : Set (ComplexModel r))).preimage
        hcont).isOpen_compl using 1
      ext y
      simp [O]
    refine ⟨0,O,hO,hx,fun y hy => ?_⟩
    have htop := whole_functionCentreIdeal_eq_top_of_ne_zero X Y f hf y hy
    simp [IsArtinReesNumber, htop, Ideal.top_pow, Ideal.top_mul]

end Graph

end

end Hironaka.HironakaG10GraphCentreUniformArtinRees
