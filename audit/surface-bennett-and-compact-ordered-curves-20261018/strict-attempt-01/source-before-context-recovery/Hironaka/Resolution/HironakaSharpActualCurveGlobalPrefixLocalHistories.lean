/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveStoppedSuccessorNaturality
import Hironaka.Resolution.HironakaSharpActualCurveGlobalPrefixTowers

/-! Canonical actual local maps precede the genuine full local/global
prefix-history comparison; no desired stagewise certificate is an input. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveGlobalPrefixLocalHistories
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerIsoTail
  BlowupTowerIsomorphism HironakaSharpActualCurveUniformPrefixSuccessors
  HironakaSharpActualCurveUniformInitialStage HironakaSharpActualCurveUniformSuccessorComparison
  HironakaSharpActualCurveGlobalSuccessorMap HironakaSharpActualCurveGlobalSuccessorCentre
  HironakaSharpActualCurveUniformPrefixes HironakaSharpActualCurveUniformStageAtlas
  HironakaSharpActualCurveTopologicalGluing HironakaSharpActualCurveGlobalManifold
  HironakaSharpActualCurveGluedProjection HironakaSharpActualCurveLocalRangeBiholomorphism
  HironakaSharpActualCurveGlobalPrefixTowers HironakaSharpActualCurveOriginalRecipeAtlas
  HironakaSharpOriginalMemberProductDomain HironakaSharpOriginalMemberProduct
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen NormalCrossingsInvariance
  NormalCrossings BlowupRestrictOpen
open HomogenizedGlueingTower (strictAlong)
attribute [local instance] endpointChartedSpace
variable {n : ℕ} {X : CMfd.{u} n} {J : Type u}

theorem originalPrefix_chart_open (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (N : ℕ) (i : J) :
    openPreimage (uniformOriginalPositiveTower A hc N) (A.openSet i)=
      localRangeOpen (uniformStageHistories A (N+1)) hc i := by
  apply Opens.ext
  ext z
  have hProj := uniformOriginalPositiveTower_projection A hc N z
  have hSet := localInclusion_range (uniformStageHistories A (N+1)) i
  have hPoint := congrArg (fun S : Set (endpointGluedSpace (uniformStageHistories A (N+1))) => z∈S) hSet
  change (z∈range (endpointLocalInclusion (uniformStageHistories A (N+1)) i))=
    (gluedProjection (uniformStageHistories A (N+1)) z∈A.openSet i) at hPoint
  change (uniformOriginalPositiveTower A hc N).proj z∈A.openSet i ↔
    z∈range (endpointLocalInclusion (uniformStageHistories A (N+1)) i)
  constructor
  · intro hz
    exact Eq.mpr hPoint (Eq.mp (congrArg (·∈A.openSet i) hProj) hz)
  · intro hz
    exact Eq.mpr (congrArg (·∈A.openSet i) hProj) (Eq.mp hPoint hz)

def localOriginalPrefixBiholomorphism (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (N : ℕ) (i : J) :
    (uniformPrefix ((A.prefixTower i).append (A.tail i)) (N+1)).1
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage (uniformOriginalPositiveTower A hc N) (A.openSet i)) :=
  (localBiholomorphism (uniformStageHistories A (N+1)) hc i).trans
    (opensCongr (originalPrefix_chart_open A hc N i).symm)

theorem localOriginalPrefixBiholomorphism_point (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (N : ℕ) (i : J)
    (z : (uniformPrefix ((A.prefixTower i).append (A.tail i)) (N+1)).1) :
    (localOriginalPrefixBiholomorphism A hc N i z).val=
      endpointLocalInclusion (uniformStageHistories A (N+1)) i z := rfl

/-- The true initial range pulls back to the entire SAME local stage range. -/
theorem globalPrefix_chart_open (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (k : ℕ) (i : J) :
    openPreimage (uniformGlobalTower A hc k)
      (localRangeOpen (uniformStageHistories A 0) hc i)=
        localRangeOpen (uniformStageHistories A k) hc i := by
  apply Opens.ext
  ext z
  have hProj := uniformGlobalTower_projection A hc k z
  have hZero := congrArg (fun S : Set (endpointGluedSpace (uniformStageHistories A 0)) =>
    (uniformGlobalTower A hc k).proj z∈S)
      (localInclusion_range (uniformStageHistories A 0) i)
  have hStage := congrArg (fun S : Set (endpointGluedSpace (uniformStageHistories A k)) => z∈S)
    (localInclusion_range (uniformStageHistories A k) i)
  change ((uniformGlobalTower A hc k).proj z∈range
    (endpointLocalInclusion (uniformStageHistories A 0) i))=
      (gluedProjection (uniformStageHistories A 0) ((uniformGlobalTower A hc k).proj z)
        ∈A.openSet i) at hZero
  change (z∈range (endpointLocalInclusion (uniformStageHistories A k) i))=
    (gluedProjection (uniformStageHistories A k) z∈A.openSet i) at hStage
  change (uniformGlobalTower A hc k).proj z∈range
    (endpointLocalInclusion (uniformStageHistories A 0) i) ↔
      z∈range (endpointLocalInclusion (uniformStageHistories A k) i)
  exact ⟨fun hz => Eq.mpr hStage
    (Eq.mp (congrArg (·∈A.openSet i) hProj) (Eq.mp hZero hz)),
    fun hz => Eq.mpr hZero
      (Eq.mpr (congrArg (·∈A.openSet i) hProj) (Eq.mp hStage hz))⟩

def localGlobalPrefixBiholomorphism (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (k : ℕ) (i : J) :
    (uniformPrefix ((A.prefixTower i).append (A.tail i)) k).1
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage (uniformGlobalTower A hc k)
          (localRangeOpen (uniformStageHistories A 0) hc i)) :=
  (localBiholomorphism (uniformStageHistories A k) hc i).trans
    (opensCongr (globalPrefix_chart_open A hc k i).symm)

theorem localGlobalPrefixBiholomorphism_point (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (k : ℕ) (i : J)
    (z : (uniformPrefix ((A.prefixTower i).append (A.tail i)) k).1) :
    (localGlobalPrefixBiholomorphism A hc k i z).val=
      endpointLocalInclusion (uniformStageHistories A k) i z := rfl

private theorem zero_prefix_isTowerIso {Y R : CMfd.{u} n} (T : BlowupTower X Y)
    (Φ : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ R)
    (e : (uniformPrefix T 0).1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ R)
    (he : ∀ z,e z=Φ ((uniformPrefix T 0).2.proj z)) :
    IsTowerIso Φ (uniformPrefix T 0).2 .refl e := by
  let P : (Σ V : CMfd.{u} n,BlowupTower X V) → Prop := fun S =>
    ∀ e : S.1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ R,
      (∀ z,e z=Φ (S.2.proj z)) → IsTowerIso Φ S.2 .refl e
  have hRefl : P ⟨X,BlowupTower.refl⟩ := by
    intro e he
    have hh : e=Φ := Diffeomorph.ext he
    subst e
    exact IsTowerIso.refl
  have hWhole : P (uniformPrefix T 0) :=
    Eq.mpr (congrArg P (uniformPrefix_zero T)) hRefl
  exact hWhole e he

def localGlobalBaseBiholomorphism (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (i : J) :
    CMfd.of (n := n) (A.openSet i) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (localRangeOpen (uniformStageHistories A 0) hc i) :=
  (zeroPrefixBiholomorphism ((A.prefixTower i).append (A.tail i))).symm.trans
    (localGlobalPrefixBiholomorphism A hc 0 i)

/-- Every real local constructor is the corresponding restricted global constructor. -/
theorem localGlobalPrefix_isTowerIso (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (k : ℕ) (i : J) :
    IsTowerIso (localGlobalBaseBiholomorphism A hc i)
      (uniformPrefix ((A.prefixTower i).append (A.tail i)) k).2
      (restrict (localRangeOpen (uniformStageHistories A 0) hc i) (uniformGlobalTower A hc k))
      (localGlobalPrefixBiholomorphism A hc k i) := by
  induction k with
  | zero =>
    apply zero_prefix_isTowerIso
    intro z
    change localGlobalPrefixBiholomorphism A hc 0 i z=
      localGlobalPrefixBiholomorphism A hc 0 i
        ((zeroPrefixBiholomorphism ((A.prefixTower i).append (A.tail i))).symm
          ((uniformPrefix ((A.prefixTower i).append (A.tail i)) 0).2.proj z))
    rw [←zeroPrefixBiholomorphism_point,Diffeomorph.symm_apply_apply]
  | succ k ih =>
    rw [(actualUniformSuccessor ((A.prefixTower i).append (A.tail i)) k).step_eq]
    refine IsTowerIso.step ih _ _ (localGlobalPrefixBiholomorphism A hc (k+1) i) ?_ ?_
    · intro z
      apply Subtype.ext
      exact globalUniformSuccessor_local A k i z
    · ext z
      exact mem_globalUniformCentre_iff A k i z

theorem mem_initial_range_iff (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (i : J)
    (p : endpointManifold (uniformStageHistories A 0) hc) :
    p∈localRangeOpen (uniformStageHistories A 0) hc i ↔
      initialProjectionBiholomorphism A hc p∈A.openSet i := by
  have h := congrArg (fun S : Set (endpointGluedSpace (uniformStageHistories A 0)) => p∈S)
    (localInclusion_range (uniformStageHistories A 0) i)
  exact Eq.to_iff h

theorem localGlobalBaseBiholomorphism_projection (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (i : J) (x : A.openSet i) :
    initialProjectionBiholomorphism A hc (localGlobalBaseBiholomorphism A hc i x).val=x.val := by
  change gluedProjection (uniformStageHistories A 0)
    (endpointLocalInclusion (uniformStageHistories A 0) i
      ((zeroPrefixBiholomorphism ((A.prefixTower i).append (A.tail i))).symm x))=x.val
  let z : (uniformStageHistories A 0).finalSpace i :=
    (zeroPrefixBiholomorphism ((A.prefixTower i).append (A.tail i))).symm x
  have hLocal := gluedProjection_local_full (uniformStageHistories A 0) i z
  refine hLocal.trans ?_
  change (((uniformPrefix ((A.prefixTower i).append (A.tail i)) 0).2.proj z) : X)=x.val
  exact congrArg Subtype.val ((zeroPrefixBiholomorphism_point _ z).symm.trans
    ((zeroPrefixBiholomorphism ((A.prefixTower i).append (A.tail i))).apply_symm_apply x))

/-- The canonical actual inclusion compares EVERY original-base history stage. -/
theorem localOriginalPrefix_isTowerIso (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (N : ℕ) (i : J) :
    IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) (A.openSet i)) ∞)
      (uniformPrefix ((A.prefixTower i).append (A.tail i)) (N+1)).2
      (restrict (A.openSet i) (uniformOriginalPositiveTower A hc N))
      (localOriginalPrefixBiholomorphism A hc N i) := by
  let e := initialProjectionBiholomorphism A hc
  have hV (x : X) : x∈A.openSet i ↔ e.symm x∈localRangeOpen (uniformStageHistories A 0) hc i := by
    rw [mem_initial_range_iff]
    change x∈A.openSet i ↔ e (e.symm x)∈A.openSet i
    exact Eq.to_iff (congrArg (·∈A.openSet i) (e.apply_symm_apply x)).symm
  have hTransport := transport_isTowerIso e.symm (uniformGlobalTower A hc (N+1))
  have hRestricted := StepOneTangentChange.isTowerIso_restrictOpens hV hTransport
    (StepOneTangentChange.isTowerIso_mem_openPreimage_iff hTransport hV)
  have hWhole := (localGlobalPrefix_isTowerIso A hc (N+1) i).trans hRestricted.symm
  have hBase := BlowupTowerSplitIso.IsTowerIso.congr_base hWhole
    (Φ' := Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) (A.openSet i)) ∞)
    (fun x => by
      apply Subtype.ext
      exact (localGlobalBaseBiholomorphism_projection A hc i x).symm)
  exact BlowupTowerSplitIso.IsTowerIso.congr_last hBase (fun z => by
    apply Subtype.ext
    rfl)

private theorem local_test_and_readouts (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (N : ℕ) (i : J)
    (M : MarkedIdeal n (CMfd.of (n := n) (A.openSet i)))
    (hN : IsClosedSubmanifold n M.N) (hcoh : M.ideal.IsCoherent)
    (hLocal : IsGeoTestTower M (uniformPrefix ((A.prefixTower i).append (A.tail i)) (N+1)).2) :
    IsGeoTestTower M (restrict (A.openSet i) (uniformOriginalPositiveTower A hc N)) ∧
      geoTransformAlong M (uniformPrefix ((A.prefixTower i).append (A.tail i)) (N+1)).2=
        MarkedIdeal.pullback (localOriginalPrefixBiholomorphism A hc N i)
          (geoTransformAlong M (restrict (A.openSet i) (uniformOriginalPositiveTower A hc N))) ∧
      ∀ S : Set (A.openSet i),
        strictAlong (uniformPrefix ((A.prefixTower i).append (A.tail i)) (N+1)).2 S=
          (localOriginalPrefixBiholomorphism A hc N i) ⁻¹'
            strictAlong (restrict (A.openSet i) (uniformOriginalPositiveTower A hc N)) S := by
  have hIso := localOriginalPrefix_isTowerIso A hc N i
  have hId : MarkedIdeal.pullback
      (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) (A.openSet i)) ∞) M=M :=
    ContactCanonicalAlong.pullback_id M hcoh
  have hTests := IsTowerIso.isGeoTestTower_iff (𝔪 := M) _ hN hcoh hIso
  rw [hId] at hTests
  have hGlobal := hTests.mp hLocal
  have hRecord := IsTowerIso.geoTransformAlong_eq (𝔪 := M) _ hN hcoh hIso hGlobal
  rw [hId] at hRecord
  refine ⟨hGlobal,hRecord,?_⟩
  intro S
  exact hIso.strictAlong_eq S

section OriginalInput
variable (hn : 0<n) {W : Set X} {E : List (Set X)}
  (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
  (hdense : W⊆closure (W \ ⋃ H∈E,H)) (hr : ∀ x∈W,RegularAtDim (n := n) W x 1)

/-- ONLY original geometry supplies the actual local global-prefix TEST,
whole marked record and strict-set readouts at EVERY original position. -/
theorem originalPrefix_local_test_and_readouts (N : ℕ) (x : X) :
    let A := originalEndpointHistories hn hW hE hdense hr
    let hc := originalEndpointHistories_cover hn hW hE hdense hr
    let U := A.openSet x
    let M := originalMemberProductMarked (X := CMfd.of (n := n) U)
      ((Subtype.val : U → X) ⁻¹' W) (E.map ((Subtype.val : U → X) ⁻¹' ·)) 1
    IsGeoTestTower M (restrict U (uniformOriginalPositiveTower A hc N)) ∧
      geoTransformAlong M (uniformPrefix ((A.prefixTower x).append (A.tail x)) (N+1)).2=
        MarkedIdeal.pullback (localOriginalPrefixBiholomorphism A hc N x)
          (geoTransformAlong M (restrict U (uniformOriginalPositiveTower A hc N))) ∧
      ∀ S : Set U,
        strictAlong (uniformPrefix ((A.prefixTower x).append (A.tail x)) (N+1)).2 S=
          (localOriginalPrefixBiholomorphism A hc N x) ⁻¹'
            strictAlong (restrict U (uniformOriginalPositiveTower A hc N)) S := by
  let A := originalEndpointHistories hn hW hE hdense hr
  let U := A.openSet x
  have hWU := isClosedSubmanifold_preimage_val hW U
  have hEU := isSNCDivisor_map_preimage (pullsBackCoordinates_val U) continuous_subtype_val hE
  exact local_test_and_readouts A (originalEndpointHistories_cover hn hW hE hdense hr) N x _
    hWU (isCoherent_originalMemberProduct hn hEU)
      (originalUniformStage_test hn hW hE hdense hr (N+1) x)

end OriginalInput

end
end Hironaka.HironakaSharpActualCurveGlobalPrefixLocalHistories
