import Hironaka.Resolution.HironakaChowGeometricStrictSaturation
import Hironaka.Resolution.HironakaActualLocalFGStrictSaturation
import Hironaka.Resolution.HironakaActualOpenIntrinsicHS
import Hironaka.Analytic.ClosureDifferenceAnalytic
import Hironaka.Blowup.BlowupRestrictOpen

/-! Geometric strict saturation on ACTUAL open domains.
BP FIRST: hironaka-real-open-geometric-strict-saturation.tex.
The real-open dictionaries and both whole ordinary-input consumers are
implemented for frontend review. No readiness or canonical P8 claim is made.
Old geometric/local-FG/Oka/Noetherian engines have zero duplicate credit. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaRealOpenGeometricStrictSaturation
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm
  OkaRelationSheaf OkaIdealOperations OkaCoherence RelativePrincipalizationSpan
  HironakaHolomorphicJetChartInvariance HironakaHolomorphicJetMonomialSpan
  HironakaRelativeNormalDeformationInitialRelations HironakaActualPointGeometricBennett
  HironakaActualPointExceptionalVanishing HironakaActualAnalyticBlowupTaylor
  HironakaActualCoefficientPresentationCentrePower HironakaActualStrictExceptionalRegularity
  HironakaActualStrictPullbackSaturation HironakaChowGeometricStrictSaturation
  HironakaActualLocalStrictSaturation HironakaActualLocalFGStrictSaturation
  HironakaRelativeNormalCoherentSaturation HironakaRelativeNormalAnalyticGraphQuotient
  HironakaActualOpenIntrinsicHS HironakaActualWholeStalkHolomorphicPullback HironakaHolomorphicJetRankLoci
  ClosureDifferenceAnalytic AnalyticGermDecomposition BlowupStrictSubmanifold BlowupRestrictOpen

/-- The actual REAL-OPEN analytic presentation supplies a SET GERM of its
ambient image. No function or analytic set is extended holomorphically
across the boundary of the stated open. -/
private theorem image_analytic_germ {n : ℕ} (U : Opens (ComplexModel n))
    (h0 : (0 : ComplexModel n) ∈ U) (W : Set U)
    (hW : IsComplexAnalyticSubset (n := n) W) :
    IsAnalyticGerm ((Subtype.val : U → ComplexModel n) '' W) := by
  let x : U := ⟨0,h0⟩
  obtain ⟨p⟩ := hW x
  let e := (complexChartAt (n := n) x).val
  have he (y : U) : e y = y.val := rfl
  have hxval : x.val = 0 := rfl
  have hs (y : U) : y ∈ e.source := by trivial
  have hset : {z : ComplexModel n | z + e x ∈ e.target ∩ e.symm ⁻¹' W} =
      (Subtype.val : U → ComplexModel n) '' W := by
    ext z
    constructor
    · rintro ⟨hzT,hzW⟩
      refine ⟨e.symm (z+e x),hzW,?_⟩
      have hz := e.right_inv hzT
      change (e.symm (z+e x)).val = z
      simpa only [he,hxval,add_zero] using hz
    · rintro ⟨y,hy,rfl⟩
      have hyT := e.map_source (hs y)
      have hyW : e.symm (e y) ∈ W := (e.left_inv (hs y)).symm ▸ hy
      change y.val + e x ∈ e.target ∩ e.symm ⁻¹' W
      simpa only [he,hxval,add_zero,mem_inter_iff,mem_preimage] using And.intro hyT hyW
  rw [←hset]
  exact isAnalyticGerm_chart_translate p

private theorem contMDiff_blowup {n : ℕ} (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (actualAnalyticBlowupMap A e b) := by
  have hp (i : Fin n) : ContDiff ℂ ∞ (fun z : ComplexModel n => z i) :=
    (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).contDiff
  have hc (i : Fin n) : ContDiff ℂ ∞ (actualAnalyticBlowupCoordinate A e b i) := by
    unfold actualAnalyticBlowupCoordinate
    split_ifs
    · exact hp e
    · exact (hp e).mul ((contDiff_const (c := b i)).add (hp i))
    · exact hp i
  exact ((EuclideanSpace.equiv (Fin n) ℂ).symm.contDiff.comp (contDiff_pi.mpr hc)).contMDiff

/-- The genuine158 geometric closure/cancellation argument uses only LOCAL
source FG, supplied internally later from the actual open analytic model.
This is centre-relative geoStrictTransform also in codimension one. -/
private theorem geometric_saturation_of_local_fg
    (d t : ℕ) (j : Fin t) (b : Fin (d+t) → ℂ)
    (W : Set (ComplexModel (d+t)))
    (hFG : IdealFGAt (vanishingIdeal (n := d+t) W).mem (0 : ComplexModel (d+t)))
    (g : HolGerm (ComplexModel (d+t))) :
    g ∈ originalCoherentOriginIdeal (vanishingIdeal (n := d+t)
      (geoStrictTransform (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b)
        (complexCoordinatePlane (d+t) d) W)) ↔
      ∃ N : ℕ, (coordinateGerm (j.natAdd d))^N*g ∈
        Ideal.map (actualAnalyticBlowupPullback (actualTangentCentreVariables d t) (j.natAdd d) b).toRingHom
          (originalCoherentOriginIdeal (vanishingIdeal (n := d+t) W)) := by
  let A := actualTangentCentreVariables d t
  let e := j.natAdd d
  let π := actualAnalyticBlowupMap A e b
  let C := complexCoordinatePlane (d+t) d
  let I := vanishingIdeal (n := d+t) W
  let J := GermIdeal.pullback (m := d+t) π I
  have hπ := contMDiff_blowup A e b
  have hπ0 : π 0 = 0 := actualAnalyticBlowupMap_zero A e b
  have hJ : IdealFGAt J.mem (0 : ComplexModel (d+t)) := local_fg_pullback π hπ hπ0 I hFG
  have hmap : originalCoherentOriginIdeal J =
      Ideal.map (actualAnalyticBlowupPullback A e b).toRingHom (originalCoherentOriginIdeal I) :=
    local_origin_pullback_eq π hπ hπ0 I hFG
  have hπnear : ∀ᶠ z in 𝓝 (0 : ComplexModel (d+t)), DifferentiableAt ℂ π z :=
    Eventually.of_forall fun _ => (differentiable_actualAnalyticBlowupMap A e b).differentiableAt
  have htπ : Tendsto π (𝓝 (0 : ComplexModel (d+t))) (𝓝 (0 : ComplexModel (d+t))) := by
    have h := hπ.continuous.tendsto 0
    change Tendsto π (𝓝 0) (𝓝 (π 0)) at h
    rwa [hπ0] at h
  constructor
  · intro hg
    obtain ⟨G,hG,rfl⟩ := HolGerm.exists_eq_mk g
    have hzero := (mk_mem_original_vanishing_origin_ideal_iff _ G hG).mp hg
    obtain ⟨V,hVprop,hV,h0V⟩ := eventually_nhds_iff.mp (hG.and hzero)
    have hOff : ∀ᶠ y in 𝓝 (0 : ComplexModel (d+t)), y e ≠ 0 → J.mem y G := by
      filter_upwards [hV.mem_nhds h0V] with y hy hye
      apply (pullback_vanishingIdeal_mem_iff_off_coordinate A e b W y hye G).mpr
      have hGV : DifferentiableOn ℂ G V := fun z hz => (hVprop z hz).1.differentiableWithinAt
      refine ⟨(holAt_of_differentiableOn hV hGV hy).mono (fun _ h => h.mdifferentiableAt),?_⟩
      filter_upwards [hV.mem_nhds hy,
        (EuclideanSpace.proj e : ComplexModel (d+t) →L[ℂ] ℂ).continuous.continuousAt.eventually_ne hye]
        with z hz hze hzW
      apply (hVprop z hz).2
      rw [geoStrictTransform_eq_closure_off_pivot]
      exact subset_closure ⟨hzW,hze⟩
    obtain ⟨N,hN⟩ := exists_power_of_local_fg_off_divisor J hJ G hG e hOff
    exact ⟨N,by rwa [hmap] at hN⟩
  · rintro ⟨N,hN⟩
    apply (coordinate_pow_mul_mem_geoStrict_ideal_iff d t j b W N g).mp
    have hle : Ideal.map (actualAnalyticBlowupPullback A e b).toRingHom (originalCoherentOriginIdeal I) ≤
        originalCoherentOriginIdeal (vanishingIdeal (n := d+t) (geoStrictTransform π C W)) := by
      apply Ideal.map_le_iff_le_comap.mpr
      apply Ideal.span_le.mpr
      rintro _ ⟨F,hF,hFW,rfl⟩
      change actualAnalyticBlowupPullback A e b (HolGerm.mk F hF) ∈
        originalCoherentOriginIdeal (vanishingIdeal (n := d+t) (geoStrictTransform π C W))
      rw [actualAnalyticBlowupPullback,compAlgHom_mk]
      apply (mk_mem_original_vanishing_origin_ideal_iff _ (F ∘ π) _).mpr
      apply eventually_zero_on_closure_of_eventually_continuous (F ∘ π) (π ⁻¹' (W \ C))
        ((holomorphic_comp π hπnear hπ0 hF).mono fun _ h => h.continuousAt)
      filter_upwards [htπ.eventually hFW.2] with z hz hzS
      exact hz hzS.1
    exact hle hN

/-- The source-open pullback span dictionary needs no coherence or analytic
extension of the source ideal. -/
private theorem pullback_source_open_mem {n m : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    (P : Opens (ComplexModel m)) (f : ComplexModel m → X) (A : GermIdeal n X)
    (p : P) (g : P → ℂ) :
    (GermIdeal.pullback (m := m) (f ∘ Subtype.val : P → X) A).mem p g ↔
      (GermIdeal.pullback (m := m) f A).mem p.val (extendOpens P g) := by
  rw [GermIdeal.mem_pullback_iff,GermIdeal.mem_pullback_iff]
  let S : (ComplexModel m → ℂ) → Prop := fun h =>
    ∃a,A.mem (f p.val) a ∧ h = a ∘ f
  constructor
  · intro hg
    apply (isInSpanAt_comp_val_iff P (S := S)).mp
    apply hg.mono
    rintro s ⟨a,ha,rfl⟩
    exact ⟨a ∘ f,⟨a,ha,rfl⟩,rfl⟩
  · intro hg
    have h := (isInSpanAt_comp_val_iff P (S := S)).mpr hg
    apply h.mono
    rintro s ⟨h,⟨a,ha,rfl⟩,rfl⟩
    exact ⟨a,ha,rfl⟩

/-- The actual source-open of the literal monomial chart. -/
def realOpenChartDomain (d t : ℕ) (j : Fin t) (b : Fin (d+t) → ℂ)
    (U : Opens (ComplexModel (d+t))) : Opens (ComplexModel (d+t)) :=
  ⟨(actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b) ⁻¹' U,
    (contMDiff_blowup _ _ _).continuous.isOpen_preimage _ U.isOpen⟩

/-- The genuine chart map into its stated open target, with no extension of W. -/
def realOpenProjection (d t : ℕ) (j : Fin t) (b : Fin (d+t) → ℂ)
    (U : Opens (ComplexModel (d+t))) (p : realOpenChartDomain d t j b U) : U :=
  ⟨actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b p.val,p.property⟩

/-- The closure is taken INSIDE the actual source-open, relative to the actual centre. -/
def realOpenStrictTransform (d t : ℕ) (j : Fin t) (b : Fin (d+t) → ℂ)
    (U : Opens (ComplexModel (d+t))) (W : Set U) : Set (realOpenChartDomain d t j b U) :=
  geoStrictTransform (realOpenProjection d t j b U)
    ((Subtype.val : U → ComplexModel (d+t)) ⁻¹' complexCoordinatePlane (d+t) d) W

/-- The actual whole pullback vanishing ideal on the genuine source-open. -/
def realOpenTotalIdeal (d t : ℕ) (j : Fin t) (b : Fin (d+t) → ℂ)
    (U : Opens (ComplexModel (d+t))) (W : Set U) :
    GermIdeal (d+t) (realOpenChartDomain d t j b U) :=
  GermIdeal.pullback (m := d+t) (realOpenProjection d t j b U) (vanishingIdeal (n := d+t) W)

/-- The actual geometric strict vanishing ideal, including a unit strict stalk. -/
def realOpenStrictIdeal (d t : ℕ) (j : Fin t) (b : Fin (d+t) → ℂ)
    (U : Opens (ComplexModel (d+t))) (W : Set U) :
    GermIdeal (d+t) (realOpenChartDomain d t j b U) :=
  vanishingIdeal (n := d+t) (realOpenStrictTransform d t j b U W)

/-- The RAW chart origin. No strict-support hypothesis is used. -/
def realOpenOrigin (d t : ℕ) (j : Fin t) (b : Fin (d+t) → ℂ)
    (U : Opens (ComplexModel (d+t))) (h0 : (0 : ComplexModel (d+t)) ∈ U) :
    realOpenChartDomain d t j b U :=
  ⟨0,by
    change actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b 0 ∈ U
    rwa [actualAnalyticBlowupMap_zero]⟩

private theorem projection_holomorphic (d t : ℕ) (j : Fin t) (b : Fin (d+t) → ℂ)
    (U : Opens (ComplexModel (d+t))) :
    ContMDiff 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ComplexModel (d+t)) ∞
      (realOpenProjection d t j b U) :=
  contMDiff_opens_mk ((contMDiff_blowup _ _ _).comp contMDiff_subtype_val) (fun p => p.property)

private theorem total_mem_model (d t : ℕ) (j : Fin t) (b : Fin (d+t) → ℂ)
    (U : Opens (ComplexModel (d+t))) (W : Set U)
    (p : realOpenChartDomain d t j b U) (g : realOpenChartDomain d t j b U → ℂ) :
    (realOpenTotalIdeal d t j b U W).mem p g ↔
      (GermIdeal.pullback (m := d+t)
        (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b)
        (vanishingIdeal (n := d+t) ((Subtype.val : U → ComplexModel (d+t)) '' W))).mem p.val
          (extendOpens (realOpenChartDomain d t j b U) g) := by
  have h := pullback_vanishingIdeal_opens (n := d+t) (m := d+t) U (realOpenProjection d t j b U)
    ((Subtype.val : U → ComplexModel (d+t)) '' W)
  rw [Set.preimage_image_eq _ Subtype.val_injective] at h
  rw [realOpenTotalIdeal,h]
  exact pullback_source_open_mem (n := d+t) (m := d+t)
    (realOpenChartDomain d t j b U)
    (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b)
    (vanishingIdeal (n := d+t) ((Subtype.val : U → ComplexModel (d+t)) '' W)) p g

private theorem strict_restrict_model (d t : ℕ) (j : Fin t) (b : Fin (d+t) → ℂ)
    (U : Opens (ComplexModel (d+t))) (W : Set U) :
    realOpenStrictTransform d t j b U W =
      (Subtype.val : realOpenChartDomain d t j b U → ComplexModel (d+t)) ⁻¹'
        geoStrictTransform
          (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b)
          (complexCoordinatePlane (d+t) d) ((Subtype.val : U → ComplexModel (d+t)) '' W) := by
  let P := realOpenChartDomain d t j b U
  let π := actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b
  let C := complexCoordinatePlane (d+t) d
  have hS : (realOpenProjection d t j b U) ⁻¹' (W \ (Subtype.val ⁻¹' C)) =
      (Subtype.val : P → ComplexModel (d+t)) ⁻¹' (π ⁻¹' ((Subtype.val '' W) \ C)) := by
    ext p
    change (_ ∧ ¬_) ↔ (_ ∧ ¬_)
    constructor
    · rintro ⟨hp,hc⟩
      exact ⟨⟨realOpenProjection d t j b U p,hp,rfl⟩,hc⟩
    · rintro ⟨⟨y,hy,he⟩,hc⟩
      have hey : y = realOpenProjection d t j b U p := Subtype.ext he
      exact ⟨hey ▸ hy,hc⟩
  change closure ((realOpenProjection d t j b U) ⁻¹' (W \ (Subtype.val ⁻¹' C))) =
    (Subtype.val : P → ComplexModel (d+t)) ⁻¹' closure (π ⁻¹' ((Subtype.val '' W) \ C))
  rw [hS]
  exact (P.isOpen.isOpenEmbedding_subtypeVal.isOpenMap.preimage_closure_eq_closure_preimage
    continuous_subtype_val (π ⁻¹' ((Subtype.val '' W) \ C))).symm

private theorem strict_mem_model (d t : ℕ) (j : Fin t) (b : Fin (d+t) → ℂ)
    (U : Opens (ComplexModel (d+t))) (W : Set U)
    (p : realOpenChartDomain d t j b U) (g : realOpenChartDomain d t j b U → ℂ) :
    (realOpenStrictIdeal d t j b U W).mem p g ↔
      (vanishingIdeal (n := d+t) (geoStrictTransform
        (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b)
        (complexCoordinatePlane (d+t) d) ((Subtype.val : U → ComplexModel (d+t)) '' W))).mem p.val
          (extendOpens (realOpenChartDomain d t j b U) g) := by
  rw [realOpenStrictIdeal,strict_restrict_model]
  exact vanishingIdeal_opens_mem_iff _

private theorem tangent_plane_analytic (d t : ℕ) :
    IsComplexAnalyticSubset (n := d+t) (complexCoordinatePlane (d+t) d) := by
  intro x
  refine ⟨{ generatorCount := t
            generator := fun i z => z (i.natAdd d)
            coordinateNeighborhood := univ
            isOpen_coordinateNeighborhood := isOpen_univ
            center_mem_coordinateNeighborhood := mem_univ _
            coordinateNeighborhood_subset_target := by intro z _; trivial
            generator_holomorphic := fun i =>
              (EuclideanSpace.proj (i.natAdd d) : ComplexModel (d+t) →L[ℂ] ℂ).differentiable.differentiableOn
            zeroLocus := ?_ }⟩
  intro y _ _
  change (∀i : Fin (d+t),d ≤ i.val → y i = 0) ↔ ∀i : Fin t,y (i.natAdd d) = 0
  constructor
  · intro hy i
    exact hy (i.natAdd d) (by simp)
  · intro hy i hi
    let a : Fin t := ⟨i.val-d,by omega⟩
    have ha : a.natAdd d = i := Fin.ext (by dsimp [a];omega)
    simpa only [ha] using hy a

private theorem strict_analytic (d t : ℕ) (j : Fin t) (b : Fin (d+t) → ℂ)
    (U : Opens (ComplexModel (d+t))) (W : Set U)
    (hW : IsComplexAnalyticSubset (n := d+t) W) :
    IsComplexAnalyticSubset (n := d+t) (realOpenStrictTransform d t j b U W) := by
  have hπ := projection_holomorphic d t j b U
  have hC := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage
    (contMDiff_subtype_val : ContMDiff 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ComplexModel (d+t)) ∞
      (Subtype.val : U → ComplexModel (d+t))) (tangent_plane_analytic d t)
  have h := isComplexAnalyticSubset_closure_diff
    (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hπ hW)
    (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hπ hC)
  simpa only [realOpenStrictTransform,geoStrictTransform,preimage_sdiff] using h

private theorem strict_model_local_fg (d t : ℕ) (j : Fin t) (b : Fin (d+t) → ℂ)
    (U : Opens (ComplexModel (d+t))) (h0 : (0 : ComplexModel (d+t)) ∈ U)
    (W : Set U) (hW : IsComplexAnalyticSubset (n := d+t) W) :
    IdealFGAt (vanishingIdeal (n := d+t) (geoStrictTransform
      (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b)
      (complexCoordinatePlane (d+t) d) ((Subtype.val : U → ComplexModel (d+t)) '' W))).mem
        (0 : ComplexModel (d+t)) := by
  let P := realOpenChartDomain d t j b U
  let T := realOpenStrictTransform d t j b U W
  let S := geoStrictTransform
    (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b)
    (complexCoordinatePlane (d+t) d) ((Subtype.val : U → ComplexModel (d+t)) '' W)
  have h0P : (0 : ComplexModel (d+t)) ∈ P := (realOpenOrigin d t j b U h0).property
  have hT : IsComplexAnalyticSubset (n := d+t) T := strict_analytic d t j b U W hW
  have hTS (p : P) : p ∈ T ↔ p.val ∈ S := by
    change p ∈ realOpenStrictTransform d t j b U W ↔ _
    rw [strict_restrict_model]
    rfl
  have hg := image_analytic_germ P h0P T hT
  apply actual_analytic_germ_vanishing_local_fg S
  apply hg.congr
  apply eventuallyEq_set.mpr
  filter_upwards [P.isOpen.mem_nhds h0P] with z hz
  constructor
  · rintro ⟨p,hp,rfl⟩
    exact (hTS p).mp hp
  · intro hzS
    exact ⟨⟨z,hz⟩,(hTS ⟨z,hz⟩).mpr hzS,rfl⟩

private theorem chart_open_origin_extension {n : ℕ} (P : Opens (ComplexModel n))
    (h0 : (0 : ComplexModel n) ∈ P) (f : P → ℂ)
    (hf : HolomorphicAt n f (⟨0,h0⟩ : P)) :
    chartTranslatedGerm (⟨0,h0⟩ : P) (⟨0,h0⟩ : P) (mem_chart_source _ _) f hf =
      HolGerm.mk (extendOpens P f)
        (((holomorphicAt_iff_extendOpens P).mp hf).mono fun _ h => h.differentiableAt) := by
  let o : P := ⟨0,h0⟩
  let F := extendOpens P f
  have hF : HolomorphicAt n F (0 : ComplexModel n) := (holomorphicAt_iff_extendOpens P).mp hf
  have h := actualHolomorphicGermPullback_original_function
    (contMDiff_subtype_val : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      (Subtype.val : P → ComplexModel n)) o F hF
  rw [actualHolomorphicGermPullback_val,AlgHom.id_apply] at h
  have he : F ∘ (Subtype.val : P → ComplexModel n) = f := funext (extendOpens_val P f)
  have he' : chartTranslatedGerm o o (mem_chart_source _ _) (F ∘ Subtype.val)
      ((holomorphicAt_comp_val_iff P).mpr hF) =
      chartTranslatedGerm o o (mem_chart_source _ _) f hf := by
    unfold chartTranslatedGerm translatedGerm
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun z => congrFun he
      ((chartAt (ComplexModel n) o).symm (z + (chartAt (ComplexModel n) o) o))
  refine (h.trans he').symm.trans ?_
  unfold chartTranslatedGerm translatedGerm
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun z => by
    change F ((chartAt (ComplexModel n) (0 : ComplexModel n)).symm
      (z + (chartAt (ComplexModel n) (0 : ComplexModel n)) 0)) = F z
    simp only [chartAt_self_eq,OpenPartialHomeomorph.refl_apply,
      OpenPartialHomeomorph.refl_symm,id_eq,add_zero]

/-- Both actual whole ideal directions follow from the real-open function
dictionary and source LOCAL FG, without a global coherent extension. -/
private theorem whole_open_origin_eq {n : ℕ} (P : Opens (ComplexModel n))
    (h0 : (0 : ComplexModel n) ∈ P) (A : GermIdeal n P)
    (B : GermIdeal n (ComplexModel n)) (hB : IdealFGAt B.mem (0 : ComplexModel n))
    (hmem : ∀f,A.mem (⟨0,h0⟩ : P) f ↔ B.mem 0 (extendOpens P f)) :
    wholeChartStalkIdeal A (⟨0,h0⟩ : P) (⟨0,h0⟩ : P) (mem_chart_source _ _) =
      originalCoherentOriginIdeal B := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro g ⟨f,hf,hAf,rfl⟩
    rw [chart_open_origin_extension P h0 f hf]
    exact Ideal.subset_span ⟨extendOpens P f,
      ((holomorphicAt_iff_extendOpens P).mp hf).mono (fun _ h => h.differentiableAt),
      (hmem f).mp hAf,rfl⟩
  · apply Ideal.span_le.mpr
    rintro g ⟨G,hG,hBG,rfl⟩
    let f : P → ℂ := G ∘ Subtype.val
    have hGhol : HolomorphicAt n G (0 : ComplexModel n) := hG.mono fun _ h => h.mdifferentiableAt
    have hf : HolomorphicAt n f (⟨0,h0⟩ : P) := (holomorphicAt_comp_val_iff P).mpr hGhol
    have hExt := ((holomorphicAt_iff_extendOpens P).mp hf).mono fun _ h => h.differentiableAt
    have he : HolGerm.mk (extendOpens P f) hExt = HolGerm.mk G hG := by
      apply HolGerm.mk_eq_mk_iff.mpr
      filter_upwards [P.isOpen.mem_nhds h0] with z hz
      exact extendOpens_val P f ⟨z,hz⟩
    have hBExt : B.mem 0 (extendOpens P f) :=
      (mk_mem_origin_iff_of_local_fg B hB hExt).mp
        (he.symm ▸ Ideal.subset_span ⟨G,hG,hBG,rfl⟩)
    have hm := Ideal.subset_span (s := {g | ∃ (f : P → ℂ)
      (hf : HolomorphicAt n f (⟨0,h0⟩ : P)),A.mem (⟨0,h0⟩ : P) f ∧
        g = chartTranslatedGerm (⟨0,h0⟩ : P) (⟨0,h0⟩ : P) (mem_chart_source _ _) f hf})
      ⟨f,hf,(hmem f).mpr hBExt,rfl⟩
    rwa [chart_open_origin_extension P h0 f hf,he] at hm

/-- At the RAW origin the actual whole native strict ideal is precisely the
pivot saturation of the actual whole native total ideal. Ordinary real-open
analytic geometry supplies every finite-generation/coherence hypothesis. -/
theorem mem_realOpen_geoStrict_iff_exists_pivot_power
    (d t : ℕ) (j : Fin t) (b : Fin (d+t) → ℂ)
    (U : Opens (ComplexModel (d+t))) (h0 : (0 : ComplexModel (d+t)) ∈ U)
    (W : Set U) (hW : IsComplexAnalyticSubset (n := d+t) W) :
    let o := realOpenOrigin d t j b U h0
    IsComplexAnalyticSubset (n := d+t) (realOpenStrictTransform d t j b U W) ∧
      (realOpenStrictIdeal d t j b U W).IsCoherent ∧
      ∀g : HolGerm (ComplexModel (d+t)),
        g ∈ wholeChartStalkIdeal (realOpenStrictIdeal d t j b U W) o o (mem_chart_source _ _) ↔
          ∃m : ℕ,(coordinateGerm (j.natAdd d))^m*g ∈
            wholeChartStalkIdeal (realOpenTotalIdeal d t j b U W) o o (mem_chart_source _ _) := by
  let P := realOpenChartDomain d t j b U
  let o := realOpenOrigin d t j b U h0
  let π := actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b
  let W0 := (Subtype.val : U → ComplexModel (d+t)) '' W
  let I := vanishingIdeal (n := d+t) W0
  let J := GermIdeal.pullback (m := d+t) π I
  let S := vanishingIdeal (n := d+t) (geoStrictTransform π (complexCoordinatePlane (d+t) d) W0)
  have h0P : (0 : ComplexModel (d+t)) ∈ P := o.property
  have hIFG : IdealFGAt I.mem (0 : ComplexModel (d+t)) :=
    actual_analytic_germ_vanishing_local_fg W0 (image_analytic_germ U h0 W hW)
  have hπ := contMDiff_blowup (actualTangentCentreVariables d t) (j.natAdd d) b
  have hπ0 : π 0 = 0 := actualAnalyticBlowupMap_zero _ _ _
  have hJFG : IdealFGAt J.mem (0 : ComplexModel (d+t)) := local_fg_pullback π hπ hπ0 I hIFG
  have hSFG : IdealFGAt S.mem (0 : ComplexModel (d+t)) := strict_model_local_fg d t j b U h0 W hW
  have hLWhole := whole_open_origin_eq P h0P (realOpenStrictIdeal d t j b U W) S hSFG
    (fun f => strict_mem_model d t j b U W o f)
  change wholeChartStalkIdeal (realOpenStrictIdeal d t j b U W) o o _ =
    originalCoherentOriginIdeal S at hLWhole
  have hIWhole := whole_open_origin_eq P h0P (realOpenTotalIdeal d t j b U W) J hJFG
    (fun f => total_mem_model d t j b U W o f)
  change wholeChartStalkIdeal (realOpenTotalIdeal d t j b U W) o o _ =
    originalCoherentOriginIdeal J at hIWhole
  have hJimage : originalCoherentOriginIdeal J =
      Ideal.map (actualAnalyticBlowupPullback (actualTangentCentreVariables d t) (j.natAdd d) b).toRingHom
        (originalCoherentOriginIdeal I) := local_origin_pullback_eq π hπ hπ0 I hIFG
  have hT := strict_analytic d t j b U W hW
  refine ⟨hT,CartanIrreducible.cartanCoherence _ hT,?_⟩
  intro g
  change g ∈ wholeChartStalkIdeal (realOpenStrictIdeal d t j b U W) o o _ ↔
    ∃m,(coordinateGerm (j.natAdd d))^m*g ∈ wholeChartStalkIdeal (realOpenTotalIdeal d t j b U W) o o _
  rw [hLWhole,hIWhole,hJimage]
  exact geometric_saturation_of_local_fg d t j b W0 hIFG g

private theorem extend_pivot_mul {n : ℕ} (P : Opens (ComplexModel n))
    (f : P → ℂ) (e : Fin n) (q : ℕ) :
    extendOpens P (fun p => f p*p.val e^q) =
      (fun z => extendOpens P f z*z e^q) := by
  funext z
  by_cases hz : z ∈ P
  · simp only [extendOpens,dif_pos hz]
  · simp only [extendOpens,dif_neg hz,zero_mul]

/-- ONE actual source-open and ONE internally chosen exponent retain the
ENTIRE strict ideal, the whole saturation union and EVERY later power at
EVERY raw point. No strict-support, exponent or equality packet is an input. -/
theorem exists_realOpen_geoStrict_uniform_power
    (d t : ℕ) (j : Fin t) (b : Fin (d+t) → ℂ)
    (U : Opens (ComplexModel (d+t))) (h0 : (0 : ComplexModel (d+t)) ∈ U)
    (W : Set U) (hW : IsComplexAnalyticSubset (n := d+t) W) :
    ∃N : ℕ,∃D : Opens (realOpenChartDomain d t j b U),
      realOpenOrigin d t j b U h0 ∈ D ∧
      ∀y ∈ D,∀f : realOpenChartDomain d t j b U → ℂ,HolomorphicAt (d+t) f y →
        ((realOpenStrictIdeal d t j b U W).mem y f ↔
          ∃m : ℕ,(realOpenTotalIdeal d t j b U W).mem y (fun p => f p*p.val (j.natAdd d)^m)) ∧
        ((realOpenStrictIdeal d t j b U W).mem y f ↔
          (realOpenTotalIdeal d t j b U W).mem y (fun p => f p*p.val (j.natAdd d)^N)) ∧
        ∀q : ℕ,((realOpenTotalIdeal d t j b U W).mem y (fun p => f p*p.val (j.natAdd d)^(N+q)) ↔
          (realOpenTotalIdeal d t j b U W).mem y (fun p => f p*p.val (j.natAdd d)^N)) := by
  let P := realOpenChartDomain d t j b U
  let o := realOpenOrigin d t j b U h0
  let e := j.natAdd d
  let π := actualAnalyticBlowupMap (actualTangentCentreVariables d t) e b
  let W0 := (Subtype.val : U → ComplexModel (d+t)) '' W
  let I := vanishingIdeal (n := d+t) W0
  let J := GermIdeal.pullback (m := d+t) π I
  let S := vanishingIdeal (n := d+t) (geoStrictTransform π (complexCoordinatePlane (d+t) d) W0)
  let ε : ComplexModel (d+t) → ℂ := fun z => z e
  have hε : HolAt ε 0 := Eventually.of_forall fun _ =>
    (EuclideanSpace.proj e : ComplexModel (d+t) →L[ℂ] ℂ).differentiableAt
  have hJF (y : ComplexModel (d+t)) (f : ComplexModel (d+t) → ℂ) (hf : J.mem y f) : HolAt f y :=
    (GermIdeal.mem_pullback_iff.mp hf).1.mono fun _ h => h.differentiableAt
  have hIFG : IdealFGAt I.mem (0 : ComplexModel (d+t)) :=
    actual_analytic_germ_vanishing_local_fg W0 (image_analytic_germ U h0 W hW)
  have hπ := contMDiff_blowup (actualTangentCentreVariables d t) e b
  have hπ0 : π 0 = 0 := actualAnalyticBlowupMap_zero _ _ _
  have hJFG : IdealFGAt J.mem (0 : ComplexModel (d+t)) := local_fg_pullback π hπ hπ0 I hIFG
  have hSFG : IdealFGAt S.mem (0 : ComplexModel (d+t)) := strict_model_local_fg d t j b U h0 W hW
  have hJimage : originalCoherentOriginIdeal J =
      Ideal.map (actualAnalyticBlowupPullback (actualTangentCentreVariables d t) e b).toRingHom
        (originalCoherentOriginIdeal I) := local_origin_pullback_eq π hπ hπ0 I hIFG
  have hsat (f : ComplexModel (d+t) → ℂ) :
      S.mem 0 f ↔ ∃q : ℕ,actualColonChain J.mem ε q 0 f := by
    by_cases hf : HolAt f 0
    · rw [←mk_mem_origin_iff_of_local_fg S hSFG hf]
      have h := geometric_saturation_of_local_fg d t j b W0 hIFG (HolGerm.mk f hf)
      rw [←hJimage] at h
      rw [h]
      apply exists_congr
      intro q
      have hεq : HolAt (fun z => ε z^q) 0 := hε.mono fun _ h => h.pow q
      rw [actualColonChain_power_dictionary (hJF 0) hε q f,and_iff_right hf,
        ←mk_mem_origin_iff_of_local_fg J hJFG (hf.mul hεq)]
      have hp : HolGerm.mk (fun z => f z*ε z^q) (hf.mul hεq) =
          (coordinateGerm e)^q*HolGerm.mk f hf := by
        change _ = (HolGerm.mk ε hε)^q*HolGerm.mk f hf
        rw [HolGerm.mk_mul f (fun z => ε z^q) hf hεq,HolGerm.mk_pow ε hε q,mul_comm]
      rw [hp]
    · constructor
      · intro hs
        exact (hf (hs.1.mono fun _ h => h.differentiableAt)).elim
      · rintro ⟨q,hq⟩
        exact (hf (actualColonChain_holomorphic (hJF 0) q hq)).elim
  let := isNoetherianRing_holGerm_euclidean (d+t)
  have hX := okaProperty_euclidean (d+t)
  obtain ⟨N,Uj,hUj,h0Uj,hεUj,hstable,_hpowers,hunion⟩ :=
    exists_uniform_original_coherent_saturation_union hX hJFG hε
  have hColonFG := actualColonChain_finitely_generated hX hJFG hε N
  obtain ⟨V,hV,h0V,heq⟩ := exists_open_coherent_equality hSFG hColonFG
    (fun f => (hsat f).trans (hunion 0 h0Uj f))
  let D : Opens P := ⟨Subtype.val ⁻¹' (Uj ∩ V),(hUj.inter hV).preimage continuous_subtype_val⟩
  refine ⟨N,D,⟨h0Uj,h0V⟩,?_⟩
  intro y hy f hf
  change y.val ∈ Uj ∩ V at hy
  have hF : HolAt (extendOpens P f) y.val :=
    ((holomorphicAt_iff_extendOpens P).mp hf).mono fun _ h => h.differentiableAt
  have hcolon (q : ℕ) : actualColonChain J.mem ε q y.val (extendOpens P f) ↔
      (realOpenTotalIdeal d t j b U W).mem y (fun p => f p*p.val e^q) := by
    rw [actualColonChain_power_dictionary (hJF y.val) (hεUj y.val hy.1) q (extendOpens P f),
      and_iff_right hF,total_mem_model d t j b U W y,extend_pivot_mul]
  have hL : (realOpenStrictIdeal d t j b U W).mem y f ↔
      actualColonChain J.mem ε N y.val (extendOpens P f) :=
    (strict_mem_model d t j b U W y f).trans (heq y.val hy.2 (extendOpens P f))
  refine ⟨hL.trans ((hunion y.val hy.1 (extendOpens P f)).symm.trans
    (exists_congr fun q => hcolon q)),hL.trans (hcolon N),?_⟩
  intro q
  exact (hcolon (N+q)).symm.trans ((hstable y.val hy.1 q (extendOpens P f)).trans (hcolon N))

end
end Hironaka.HironakaRealOpenGeometricStrictSaturation
