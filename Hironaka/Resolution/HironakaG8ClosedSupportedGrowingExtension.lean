import Hironaka.Resolution.HironakaG8SurfaceLimitEndpoint
import Hironaka.Resolution.HironakaG8SingularFootprintExtension
import Hironaka.Resolution.HironakaActualLocallyFiniteBoundary
import Hironaka.Resolution.HironakaLocallyFiniteResolutionSequence
import Hironaka.Resolution.HironakaG8FirstFootprintOrder
import Hironaka.Resolution.HironakaClosedFootprintOpenTowerExtension


/-! Ambient extension of an actual growing TEST with closed support. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8ClosedSupportedGrowingExtension

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupTowerIsomorphism RestrictEmptyTower ResolutionInvariantSeq
  HironakaLocallyFiniteResolutionSequence HironakaClosedFootprintOpenTowerExtension
  HironakaActualLocallyFiniteBoundary
  HironakaG8OccupiedSlotComparison HironakaG8FirstFootprintOrder

variable {n : ℕ} {X : CMfd.{0} n}
local notation "𝓘c" => 𝓘(ℂ, ComplexModel n)

private structure StageLift (U : Opens X) (K : Set X)
    (s : GrowingSeq (CMfd.of (n := n) U)) (i : ℕ) where
  global : Σ Y : CMfd.{0} n, BlowupTower X Y
  supported : CentresOver K global.2
  localIso : ∃ e : (s.stage i).1 ≃ₘ⟮𝓘c,𝓘c⟯ openPreimage global.2 U,
    IsTowerIso (Diffeomorph.refl 𝓘c U ∞) (s.stage i).2 (restrict U global.2) e

private def initialLift (U : Opens X) (K : Set X) (s : GrowingSeq (CMfd.of (n := n) U)) :
    StageLift U K s 0 where
  global := ⟨X,.refl⟩
  supported := trivial
  localIso := by
    generalize h : s.stage 0 = L
    rw [s.zero] at h
    subst L
    exact ⟨Diffeomorph.refl 𝓘c U ∞,.refl⟩

private theorem exists_lift_succ (U : Opens X) (K : Set X) (hK : IsClosed K) (hKU : K ⊆ U)
    (s : GrowingSeq (CMfd.of (n := n) U)) (i : ℕ) (D : StageLift U K s i)
    (hImages : centreImage s i ⊆ (Subtype.val : U → X) ⁻¹' K) :
    ∃ next : StageLift U K s (i+1),
      ∃ (C : Set D.global.1) (π : next.global.1 → D.global.1) (hπ : IsBlowupAlong n C π),
        next.global.2 = .step D.global.2 C π hπ := by
  obtain ⟨e,he⟩ := D.localIso
  obtain ⟨π,hπ,hNext⟩ := exists_step_map s i
  obtain ⟨Z,C,ρ,hρ,hOver,χ,hχ⟩ :=
    exists_closed_footprint_step_extension U K hK hKU (s.stage i).2 D.global.2 e he hπ
      (fun _ hc => hImages ⟨_,hc,rfl⟩)
  exact ⟨⟨⟨Z,.step D.global.2 C ρ hρ⟩,⟨D.supported,hOver⟩,χ,hNext.symm ▸ hχ⟩,C,ρ,hρ,rfl⟩

private noncomputable def lifts (U : Opens X) (K : Set X) (hK : IsClosed K) (hKU : K ⊆ U)
    (s : GrowingSeq (CMfd.of (n := n) U))
    (hImages : ∀ i, centreImage s i ⊆ (Subtype.val : U → X) ⁻¹' K) :
    ∀ i, StageLift U K s i
  | 0 => initialLift U K s
  | i+1 => (exists_lift_succ U K hK hKU s i (lifts U K hK hKU s hImages i) (hImages i)).choose

private noncomputable def extendedSeq (U : Opens X) (K : Set X) (hK : IsClosed K) (hKU : K ⊆ U)
    (s : GrowingSeq (CMfd.of (n := n) U))
    (hImages : ∀ i, centreImage s i ⊆ (Subtype.val : U → X) ⁻¹' K) : GrowingSeq X where
  stage i := (lifts U K hK hKU s hImages i).global
  zero := rfl
  succ i := (exists_lift_succ U K hK hKU s i (lifts U K hK hKU s hImages i) (hImages i)).choose_spec

private theorem slotFootprint_stage_succ (s : GrowingSeq X) (i : ℕ) :
    slotFootprint (s.stage (i+1)).2 i = centreImage s i := by
  obtain ⟨π,hπ,h⟩ := exists_step_map s i
  rw [h]
  simp only [slotFootprint,stage_length,if_true,centreImage]

/-- One growing sequence really extends all the supported local stages.
Every raw projected centre is the inclusion image of its local centre. -/
theorem exists_growing_seq_of_closed_footprint
    (U : Opens X) (K : Set X) (hK : IsClosed K) (hKU : K ⊆ U)
    (s : GrowingSeq (CMfd.of (n := n) U))
    (hImages : ∀ i, centreImage s i ⊆ (Subtype.val : U → X) ⁻¹' K) :
    ∃ g : GrowingSeq X, (∀ i, CentresOver K (g.stage i).2) ∧
      (∀ i, ∃ e : (s.stage i).1 ≃ₘ⟮𝓘c,𝓘c⟯ openPreimage (g.stage i).2 U,
        IsTowerIso (Diffeomorph.refl 𝓘c U ∞) (s.stage i).2 (restrict U (g.stage i).2) e) ∧
      ∀ i, centreImage g i = (Subtype.val : U → X) '' centreImage s i := by
  let g := extendedSeq U K hK hKU s hImages
  have hSupported (i : ℕ) : CentresOver K (g.stage i).2 :=
    (lifts U K hK hKU s hImages i).supported
  have hLocal (i : ℕ) : ∃ e : (s.stage i).1 ≃ₘ⟮𝓘c,𝓘c⟯ openPreimage (g.stage i).2 U,
      IsTowerIso (Diffeomorph.refl 𝓘c U ∞) (s.stage i).2 (restrict U (g.stage i).2) e :=
    (lifts U K hK hKU s hImages i).localIso
  refine ⟨g,hSupported,hLocal,?_⟩
  intro i
  obtain ⟨e,he⟩ := hLocal (i+1)
  have hTrace := slotFootprint_of_isTowerIso he i
  rw [slotFootprint_restrict,Diffeomorph.coe_refl,preimage_id,slotFootprint_stage_succ,
    slotFootprint_stage_succ] at hTrace
  have hSub := slotFootprint_subset_of_centresOver (g.stage (i+1)).2 (hSupported (i+1)) i
  rw [slotFootprint_stage_succ] at hSub
  rw [hTrace]
  ext x
  constructor
  · intro hx
    exact ⟨⟨x,hKU (hSub hx)⟩,hx,rfl⟩
  · rintro ⟨y,hy,rfl⟩
    exact hy

private theorem locallyFinite_image_of_supported
    (U : Opens X) (K : Set X) (hK : IsClosed K) (hKU : K ⊆ U)
    (F : ℕ → Set U) (hLF : LocallyFinite F)
    (hOver : ∀ i, F i ⊆ (Subtype.val : U → X) ⁻¹' K) :
    LocallyFinite (fun i => (Subtype.val : U → X) '' F i) := by
  intro x
  by_cases hx : x ∈ U
  · let u : U := ⟨x,hx⟩
    obtain ⟨V,hV,hFin⟩ := hLF u
    obtain ⟨O,hOV,hO,huO⟩ := mem_nhds_iff.mp hV
    have hOpen := U.isOpen.isOpenMap_subtype_val _ hO
    refine ⟨(Subtype.val : U → X) '' O,hOpen.mem_nhds ⟨u,huO,rfl⟩,hFin.subset ?_⟩
    intro i hi
    obtain ⟨_,⟨a,ha,rfl⟩,b,hb,he⟩ := hi
    have hEq : b = a := Subtype.ext he
    exact ⟨a,ha,hOV (hEq ▸ hb)⟩
  · have hxK : x ∉ K := fun h => hx (hKU h)
    refine ⟨Kᶜ,hK.isOpen_compl.mem_nhds hxK,Set.finite_empty.subset ?_⟩
    intro i hi
    obtain ⟨_,⟨a,ha,rfl⟩,hb⟩ := hi
    exact (hb (hOver i ha)).elim

open HironakaEmbeddedAnalytic HironakaStageCenters HironakaAdmissibleSequence
  HironakaG8SurfaceLimitEndpoint HironakaG8SingularFootprintExtension
  HironakaCompactFootprintJointTests MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism HironakaActualLocallyFiniteHistoryOverlap
  HironakaActualLocallyFiniteHistoryLimit HironakaActualLocallyFiniteLimitStrictTransforms
  HironakaActualLimitCarrierGeometry HironakaActualLimitProtectedOpen HironakaG4CompactComponentLimit

attribute [local instance] limitChartedSpace
local instance (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) :
    IsComplexManifold n (actualHistoryGluedSpace s hLF) := limitSpace_isComplexManifold s hLF

/-- A locally finite original TEST supported in a closed set inside a
window extends to a proper global TEST history. The ambient history
has exactly the same restricted prefixes and is unchanged off the support. -/
theorem exists_supported_growing_test_extension
    (U : Opens X) (K : Set X) (hK : IsClosed K) (hKU : K ⊆ U)
    (s : GrowingSeq (CMfd.of (n := n) U)) (hLF : LocallyFinite (centreImage s))
    (hImages : ∀ i, centreImage s i ⊆ (Subtype.val : U → X) ⁻¹' K)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (hTest : ∀ i, IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → X) M) (s.stage i).2)
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (hSing : ∀ i, StageCentres (fun P C => C ⊆ singularSet (n := n)
      (strictTransform n P.proj ((Subtype.val : U → X) ⁻¹' W))) (s.stage i).2) :
    ∃ g : GrowingSeq X, ∃ hG : LocallyFinite (centreImage g),
      (∀ i, CentresOver K (g.stage i).2) ∧
      (∀ i, IsGeoTestTower M (g.stage i).2) ∧
      (∀ i, StageCentres (fun P C => C ⊆ singularSet (n := n)
        (strictTransform n P.proj W)) (g.stage i).2) ∧
      (∀ i, ∃ e : (s.stage i).1 ≃ₘ⟮𝓘c,𝓘c⟯ openPreimage (g.stage i).2 U,
        IsTowerIso (Diffeomorph.refl 𝓘c U ∞) (s.stage i).2 (restrict U (g.stage i).2) e) ∧
      (∀ i, centreImage g i = (Subtype.val : U → X) '' centreImage s i) ∧
      limitStrictTransform g hG W = strictTransform n (gluedProjection g hG) W ∧
      IsProperMap (gluedProjection g hG) ∧ Function.Surjective (gluedProjection g hG) ∧
      ContMDiff 𝓘c 𝓘c ∞ (gluedProjection g hG : limitManifold g hG → X) ∧
      IsIsomorphismOver n (gluedProjection g hG) Kᶜ := by
  obtain ⟨g,hSupport,hLocal,hIm⟩ := exists_growing_seq_of_closed_footprint U K hK hKU s hImages
  have hG : LocallyFinite (centreImage g) := by
    rw [funext hIm]
    exact locallyFinite_image_of_supported U K hK hKU _ hLF hImages
  have hStage (i : ℕ) : StageCentres (fun P C => C ⊆ singularSet (n := n)
      (strictTransform n P.proj W)) (g.stage i).2 := by
    apply singular_stages_of_restrict W U K hKU _ (hSupport i)
    obtain ⟨e,he⟩ := hLocal i
    have h := singular_stages_of_tower_iso (X' := CMfd.of (n := n) U)
      (X := CMfd.of (n := n) U) (T' := (s.stage i).2) (T := restrict U (g.stage i).2)
      (χ := e) ((Subtype.val : U → X) ⁻¹' W)
      (hW.isClosed.preimage continuous_subtype_val) (Diffeomorph.refl 𝓘c U ∞) he
    simp only [Diffeomorph.coe_refl,preimage_id] at h
    exact h (hSing i)
  have hGeo (i : ℕ) : IsGeoTestTower M (g.stage i).2 := by
    obtain ⟨e,he⟩ := hLocal i
    exact isGeoTestTower_of_supported_open_iso M hM.isClosedSubmanifold_N hM.isCoherent
      U K hK hKU (g.stage i).2 (hSupport i) (s.stage i).2 e he (hTest i)
  have hOver (i : ℕ) : centreImage g i ⊆ K := by
    rw [hIm]
    rintro _ ⟨x,hx,rfl⟩
    exact hImages i hx
  have hIso := intrinsic_limit_regular_open_iso W hW g hG hStage
  have hProper := gluedProjection_isProperMap g hG
  exact ⟨g,hG,hSupport,hGeo,hStage,hLocal,hIm,intrinsic_limit_strictTransform_eq_projection W hW g hG hStage hIso,
    hProper,proper_regular_open_iso_surjective (Y := CMfd.of (n := n) (limitManifold g hG)) W _ hProper hIso,
    gluedProjection_contMDiff g hG,
    gluedProjection_isIsomorphismOver_compl_of_centreImages_subset g hG K hOver⟩

end Hironaka.HironakaG8ClosedSupportedGrowingExtension
