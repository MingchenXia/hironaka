import Hironaka.Resolution.HironakaG8GlobalNativeTestAssembly
import Hironaka.Resolution.HironakaClosedFootprintOpenTowerExtension
import Hironaka.Resolution.HironakaG8CompactFootprintObstruction

/-! Closed, possibly noncompact, native TEST footprints and their physical global assembly. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8ClosedNativeTestGlobalization
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealBiholomorphism.MarkedIdeal MarkedIdealRestrictOpen
  HironakaEmbeddedAnalytic HironakaBaseChange NormalCrossings
  HironakaStageCenters ResolutionInvariantSpec HironakaG8FiniteNativeTestServing
  HironakaG8IntrinsicSingularBlockSchedule HironakaG8SurfaceLimitEndpoint
  HironakaG8SingularFootprintExtension HironakaG8CompactLexInduction HironakaLocalPrincipalization
  HironakaExhaustionBlockLocalFiniteness HironakaCountableTowerPrefixes
  HironakaUniformHistoricalSuccessorOriginalRegular HironakaResolutionSpaceLocal
  HironakaLocallyFiniteResolutionSequence HironakaActualLocallyFiniteHistoryLimit
  HironakaActualLocallyFiniteLimitStrictTransforms HironakaActualLimitCarrierGeometry
  HironakaG4CompactComponentLimit HironakaActualLimitProtectedOpen
  HironakaNormalCrossingsOpenRestrictionSeparation HironakaNormalCrossingsSeparationChoiceComparison
  BlowupTowerIsomorphism ResolutionInvariantSeq HomogenizedGlueingTower
  RestrictEmptyTower HironakaActualLocallyFiniteHistoryOverlap HironakaAdmissibleSequence
  HironakaG8GlobalNativeTestAssembly HironakaClosedFootprintOpenTowerExtension
  HironakaCompactFootprintJointTests HironakaG8CompactFootprintObstruction

attribute [local instance] limitChartedSpace
local instance {n : ℕ} {X : CMfd.{0} n} (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) :
    IsComplexManifold n (actualHistoryGluedSpace s hLF) := limitSpace_isComplexManifold s hLF

variable {n : ℕ} {X Y : CMfd.{0} (n+1)}
private abbrev whole {A : CMfd.{0} (n+1)} (W : Set A) (E : List (Set A)) : MarkedIdeal (n+1) A :=
  ⟨univ,E,vanishingIdeal (n := n+1) W,1⟩

/-- A closed footprint contained in the literal working open suffices
for original ordered TEST. Compactness of the footprint is unnecessary. -/
theorem exists_closed_footprint_singular_test_extension
    {Z : CMfd.{0} (n+1)} (M : MarkedIdeal (n+1) X)
    (hN : IsClosedSubmanifold (n+1) M.N) (hI : M.ideal.IsCoherent)
    (W : Set X) (hW : IsClosed W) (U : Opens X) (F : Set X)
    (hF : IsClosed F) (hFU : F ⊆ U)
    (T : BlowupTower (CMfd.of (n := n+1) U) Z)
    (hOver : CentresOver ((Subtype.val : U → X) ⁻¹' F) T)
    (hTest : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → X) M) T)
    (hStage : StageCentres (fun P C => C ⊆ singularSet (n := n+1)
      (strictTransform (n+1) P.proj ((Subtype.val : U → X) ⁻¹' W))) T) :
    ∃ (Y : CMfd.{0} (n+1)) (Q : BlowupTower X Y),
      IsGeoTestTower M Q ∧
      StageCentres (fun P C => C ⊆ singularSet (n := n+1) (strictTransform (n+1) P.proj W)) Q ∧
      CentresOver F Q ∧
      ∃ e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel (n+1)),𝓘(ℂ,ComplexModel (n+1))⟯ openPreimage Q U,
        IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel (n+1)) U ∞) T (restrict U Q) e ∧
        T.length = Q.length ∧ ∀ z, Q.proj (e z).val = (T.proj z).val := by
  obtain ⟨Y,Q,hQ,e,he,hLength,hProj⟩ := exists_closed_footprint_extension U F hF hFU T hOver
  have hTQ := isGeoTestTower_of_supported_open_iso M hN hI U F hF hFU Q hQ T e he hTest
  have hStageU : StageCentres (fun P C => C ⊆ singularSet (n := n+1)
      (strictTransform (n+1) P.proj ((Subtype.val : U → X) ⁻¹' W))) (restrict U Q) := by
    have hs := singular_stages_of_tower_iso
      (X' := CMfd.of (n := n+1) U) (X := CMfd.of (n := n+1) U)
      (T' := T) (T := restrict U Q) (χ := e) ((Subtype.val : U → X) ⁻¹' W)
      (hW.preimage continuous_subtype_val) (Diffeomorph.refl 𝓘(ℂ,ComplexModel (n+1)) U ∞) he
    simp only [Diffeomorph.coe_refl,preimage_id] at hs
    exact hs hStage
  exact ⟨Y,Q,hTQ,singular_stages_of_restrict W U F hFU Q hQ hStageU,hQ,e,he,hLength,hProj⟩


/-- Union of the actual projected centre images of a finite tower. -/
def baseCentreFootprint {Y : CMfd.{0} (n+1)} : BlowupTower X Y → Set X
  | .refl => ∅
  | .step T C _ _ => baseCentreFootprint T ∪ T.proj '' C

/-- A prescribed footprint is exactly a set containing every centre image. -/
theorem centresOver_iff_baseCentreFootprint_subset {F : Set X} (T : BlowupTower X Y) :
    CentresOver F T ↔ baseCentreFootprint T ⊆ F := by
  induction T with
  | refl => simp [CentresOver,baseCentreFootprint]
  | step T C π hπ ih =>
    change (CentresOver F T ∧ C ⊆ T.proj ⁻¹' F) ↔
      baseCentreFootprint T ∪ T.proj '' C ⊆ F
    rw [union_subset_iff,ih,image_subset_iff]

/-- This is the least closed footprint condition for literal extension by
the identity outside the working open. -/
theorem exists_closed_footprint_iff_closure_stays_in_open
    (O : Opens X) (T : BlowupTower (CMfd.of (n := n+1) O) Y) :
    (∃ F : Set X, IsClosed F ∧ F ⊆ O ∧ CentresOver ((Subtype.val : O → X) ⁻¹' F) T) ↔
      closure ((Subtype.val : O → X) '' baseCentreFootprint T) ⊆ O := by
  constructor
  · rintro ⟨F,hF,hFO,hOver⟩
    exact (closure_minimal (image_subset_iff.mpr
      ((centresOver_iff_baseCentreFootprint_subset T).mp hOver)) hF).trans hFO
  · intro h
    exact ⟨_,isClosed_closure,h,(centresOver_iff_baseCentreFootprint_subset T).mpr
      (image_subset_iff.mp subset_closure)⟩

/-- Exact topological obligation for extending a finite native TEST block
by the identity outside its working open. -/
def HasClosedFootprintTestBlock (W : Set Y) (E : List (Set Y)) (K : Set Y) : Prop :=
  ∃ (U : Opens Y), K ⊆ U ∧ ∃ (F : Set Y), IsClosed F ∧ F ⊆ U ∧
    ∃ (Z : CMfd.{0} (n+1)) (S : BlowupTower (CMfd.of (n := n+1) U) Z),
      NativeTestState ((Subtype.val : U → Y) ⁻¹' W) (E.map ((Subtype.val : U → Y) ⁻¹' ·)) S ∧
      CentresOver ((Subtype.val : U → Y) ⁻¹' F) S ∧
      Disjoint (S.proj ⁻¹' ((Subtype.val : U → Y) ⁻¹' K))
        (singularSet (n := n+1) (strictTransform (n+1) S.proj ((Subtype.val : U → Y) ⁻¹' W)))

/-- A working open with singular-free frontier permits the full finite
local TEST to extend by identity, even when its centre support is noncompact. -/
theorem has_closed_footprint_test_block_of_regular_frontier
    (W : Set Y) (E : List (Set Y)) (K : Set Y)
    (hW : IsComplexAnalyticSubset (n := n+1) W)
    (U : Opens Y) (hKU : K ⊆ U)
    (hFront : Disjoint (frontier (U : Set Y)) (singularSet (n := n+1) W))
    {Z : CMfd.{0} (n+1)} (T : BlowupTower (CMfd.of (n := n+1) U) Z)
    (hState : NativeTestState ((Subtype.val : U → Y) ⁻¹' W)
      (E.map ((Subtype.val : U → Y) ⁻¹' ·)) T)
    (hClear : Disjoint (T.proj ⁻¹' ((Subtype.val : U → Y) ⁻¹' K))
      (singularSet (n := n+1) (strictTransform (n+1) T.proj ((Subtype.val : U → Y) ⁻¹' W)))) :
    HasClosedFootprintTestBlock W E K := by
  let G := singularSet (n := n+1) ((Subtype.val : U → Y) ⁻¹' W)
  let V : Opens U := ⟨Gᶜ,(isClosed_singularSet hState.analytic.isClosed).isOpen_compl⟩
  have hAvoid := intrinsic_singular_history_avoids_regular_open hState.analytic V
    disjoint_compl_right T hState.singular
  have hOver : CentresOver G T := by
    have h := centresOver_compl_of_centresAvoid V T hAvoid
    change CentresOver Gᶜᶜ T at h
    rwa [compl_compl] at h
  let F := closure ((Subtype.val : U → Y) '' baseCentreFootprint T)
  have hFclosure : F ⊆ closure (U : Set Y) :=
    closure_mono (fun _ hy => by obtain ⟨x,_,rfl⟩ := hy; exact x.property)
  have hFSing : F ⊆ singularSet (n := n+1) W := by
    apply closure_minimal _ (isClosed_singularSet hW.isClosed)
    intro _ hy
    obtain ⟨x,hx,rfl⟩ := hy
    have hxG := (centresOver_iff_baseCentreFootprint_subset T).mp hOver hx
    change x ∈ singularSet (n := n+1) ((Subtype.val : U → Y) ⁻¹' W) at hxG
    rwa [singularSet_preimage_val] at hxG
  have hFU : F ⊆ U := by
    intro y hy
    by_contra hNot
    have hf : y ∈ frontier (U : Set Y) :=
      ⟨hFclosure hy, fun h => hNot (interior_subset h)⟩
    exact disjoint_left.mp hFront hf (hFSing hy)
  have hTF : CentresOver ((Subtype.val : U → Y) ⁻¹' F) T :=
    (centresOver_iff_baseCentreFootprint_subset T).mpr
      (fun x hx => subset_closure ⟨x,hx,rfl⟩)
  exact ⟨U,hKU,F,isClosed_closure,hFU,Z,T,hState,hTF,hClear⟩

/-- The actual open-extension isomorphism preserves singular-fibre clearance. -/
theorem singular_fibre_clear_of_extension_iso
    {Z : CMfd.{0} (n+1)} (W : Set X) (hW : IsClosed W) (K : Set X)
    (O : Opens X) (hKO : K ⊆ O) (Q : BlowupTower X Y)
    (S : BlowupTower (CMfd.of (n := n+1) O) Z)
    (e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel (n+1)),𝓘(ℂ,ComplexModel (n+1))⟯ openPreimage Q O)
    (he : IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel (n+1)) O ∞) S (restrict O Q) e)
    (hProj : ∀ z, Q.proj (e z).val = (S.proj z).val)
    (hClear : Disjoint (S.proj ⁻¹' ((Subtype.val : O → X) ⁻¹' K))
      (singularSet (n := n+1) (strictTransform (n+1) S.proj ((Subtype.val : O → X) ⁻¹' W)))) :
    Disjoint (singularSet (n := n+1) (strictTransform (n+1) Q.proj W)) (Q.proj ⁻¹' K) := by
  have hStrict := strictTransform_preimage_of_square
    (Diffeomorph.refl 𝓘(ℂ,ComplexModel (n+1)) O ∞) e S.contMDiff_proj
    (restrict O Q).contMDiff_proj ((Subtype.val : O → X) ⁻¹' W)
    (hW.preimage continuous_subtype_val) (fun z => (he.proj_comm z).symm)
  simp only [Diffeomorph.coe_refl,preimage_id] at hStrict
  rw [strictTransform_restricted_tower O Q W] at hStrict
  apply disjoint_left.mpr
  intro y hy hKy
  let q : openPreimage Q O := ⟨y,hKO hKy⟩
  let z := e.symm q
  have hEq : e z = q := e.apply_symm_apply q
  have hzOn : z ∈ S.proj ⁻¹' ((Subtype.val : O → X) ⁻¹' (K)) := by
    change (S.proj z).val ∈ K
    rw [← hProj z,hEq]
    exact hKy
  have hqSing : q ∈ singularSet (n := n+1)
      ((Subtype.val : openPreimage Q O → Y) ⁻¹' strictTransform (n+1) Q.proj W) := by
    rw [singularSet_preimage_val]
    exact hy
  have hzSing : z ∈ singularSet (n := n+1)
      (strictTransform (n+1) S.proj ((Subtype.val : O → X) ⁻¹' W)) := by
    rw [hStrict]
    obtain ⟨hmem,hReg⟩ := mem_singularSet_iff.mp hqSing
    apply mem_singularSet_iff.mpr
    refine ⟨?_,fun k hk => hReg k ?_⟩
    · change e z ∈ ((Subtype.val : openPreimage Q O → Y) ⁻¹' strictTransform (n+1) Q.proj W)
      rwa [hEq]
    · have heReg := (CodimOnePartCanonical.regularAtDim_preimage_iff e).mp hk
      rwa [hEq] at heReg
  exact disjoint_left.mp hClear hzOn hzSing

/-- The compact-footprint block hypothesis fails on affine tasks with an
infinite singular trace, regardless of boundary. -/
theorem not_hasCompactFootprintTestBlock_of_infinite_singular_task
    (W K : Set (ComplexModel (n+1))) (E : List (Set (ComplexModel (n+1)))) (hW : IsClosed W)
    (hInf : (singularSet (n := n+1) W ∩ K).Infinite) :
    ¬ HasCompactFootprintTestBlock (Y := CMfd.of (n := n+1) (ComplexModel (n+1))) W E K := by
  rintro ⟨O,hKO,F,hF,hFO,Z,S,_,hOver,hClear⟩
  obtain ⟨Y,Q,hQ,e,he,_,hProj⟩ := exists_closed_footprint_extension O F hF.isClosed hFO S hOver
  have hClear' := singular_fibre_clear_of_extension_iso W hW K O hKO Q S e he hProj hClear
  exact hInf (finite_original_singular_points_of_compact_footprint_service W K F hW hF Q hQ hClear')

/-- An extendable finite TEST tail gives a literal global append,
including all old boundary slots. -/
theorem global_block_of_closed_footprint
    {W : Set X} {E : List (Set X)} {P : BlowupTower X Y} (hP : NativeTestState W E P)
    (K : Set X)
    (hBlock : HasClosedFootprintTestBlock (strictTransform (n+1) P.proj W)
      (geoTransformAlong (whole W E) P).E (P.proj ⁻¹' K)) :
    ∃ (Z : CMfd.{0} (n+1)) (Q : BlowupTower Y Z),
      IsGeoTestTower (geoTransformAlong (whole W E) P) Q ∧
      StageCentres (fun T C => C ⊆ singularSet (n := n+1)
        (strictTransform (n+1) T.proj (strictTransform (n+1) P.proj W))) Q ∧
      Disjoint (singularSet (n := n+1) (strictTransform (n+1) (P.append Q).proj W))
        ((P.append Q).proj ⁻¹' K) := by
  let M := whole W E
  let U := strictTransform (n+1) P.proj W
  let B := (geoTransformAlong M P).E
  let A := whole U B
  have hU := HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_proj hP.analytic P
  obtain ⟨O,hKO,F,hF,hFO,Z,S,hState,hOver,hClear⟩ := hBlock
  have hST : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : O → Y) A) S := by
    rw [HironakaEmbeddedBoundary.pullback_val_mk_vanishingIdeal O B U]
    exact hState.tested
  obtain ⟨V,Q,hQT,hQS,_,e,he,_,hProj⟩ := exists_closed_footprint_singular_test_extension
    A HomogenizedGlueingTower.isClosedSubmanifold_univ (CartanIrreducible.cartanCoherence U hU)
    U hU.isClosed O F hF hFO S hOver hST hState.singular
  have hWhole := (original_test_and_singular_stages_append hP.analytic hP.snc
    P Q hP.tested hP.singular hQT hQS).1
  refine ⟨V,Q,(isGeoTestTower_append_iff (𝔪 := M) P Q).1 hWhole |>.2,hQS,?_⟩
  have hClearQ := singular_fibre_clear_of_extension_iso U hU.isClosed (P.proj ⁻¹' K)
    O hKO Q S e he hProj hClear
  rw [BlowupTower.proj_append,StrictTransformComposition.strictTransform_comp
    P.contMDiff_proj Q.contMDiff_proj]
  exact hClearQ


def HasClosedNativeFootprintExtensions (W : Set X) (E : List (Set X)) : Prop :=
  ∀ {B : CMfd.{0} (n+1)} {P : BlowupTower X B},
    NativeTestState W E P → ∀ K : Set X, IsCompact K →
      HasClosedFootprintTestBlock (strictTransform (n+1) P.proj W)
        (geoTransformAlong (whole W E) P).E (P.proj ⁻¹' K)

/-- Protected finite physical blocks assemble into a proper smooth limit
in every positive ambient dimension. The existence of the indicated
closed footprint extensions is the only local-to-global input. -/
theorem global_native_test_finite_or_proper_limit_of_closed_footprints
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n+1) W)
    (E : List (Set X)) (hE : IsSNCDivisor (n+1) E)
    (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (lift : HasClosedNativeFootprintExtensions W E) :
    (∃ (Y : CMfd.{0} (n+1)) (T : BlowupTower X Y),
      NativeTestState W E T ∧ IsClosedSubmanifold (n+1) (strictTransform (n+1) T.proj W) ∧
      IsProperMap T.proj ∧ Function.Surjective T.proj ∧
      IsIsomorphismOver (n+1) T.proj (singularSet (n := n+1) W)ᶜ) ∨
    ∃ (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)),
      (∀ i, NativeTestState W E (s.stage i).2) ∧
      (∀ x : X, ∃ (V : Opens X) (N : ℕ), x ∈ V ∧ ∀ r,
        ResolutionInvariantExt.IsEmptyTower
          (restrict (openPreimage (s.stage N).2 V) (tailTower s N r))) ∧
      IsClosedSubmanifold (n+1) (limitStrictTransform s hLF W) ∧
      limitStrictTransform s hLF W = strictTransform (n+1) (gluedProjection s hLF) W ∧
      IsProperMap (gluedProjection s hLF) ∧ Function.Surjective (gluedProjection s hLF) ∧
      IsIsomorphismOver (n+1) (gluedProjection s hLF) (singularSet (n := n+1) W)ᶜ ∧
      ContMDiff 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ComplexModel (n+1)) ∞ (gluedProjection s hLF) := by
  apply global_native_test_finite_or_proper_limit_of_global_tails W hW E hE hDense
  intro B P hP K hK
  exact global_block_of_closed_footprint hP K (lift hP K hK)

end
end Hironaka.HironakaG8ClosedNativeTestGlobalization
