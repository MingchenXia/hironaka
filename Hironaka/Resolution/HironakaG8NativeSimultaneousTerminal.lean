import Hironaka.Resolution.HironakaG8NativeEmptyStep
import Hironaka.Resolution.HironakaG8EmptyAwareTestTransport
import Hironaka.Resolution.HironakaG8SingularFootprintExtension

/-! Whole same-profile native comparison with arbitrary actual empty stages. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8NativeSimultaneousTerminal

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdealBiholomorphism
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec CanonicalCentres
  HironakaStageCenters HironakaEmbeddedAnalytic HironakaHolomorphicJetChartInvariance
  NormalCrossings HironakaG8NativeRelativeClearing HironakaG8NativeSimultaneousCentre
  HironakaG8NativeSimultaneousPrefix HironakaG8NativeEmptyStep
  HironakaG3EmptyAwareHistory HironakaG3EmptyAwareComposition HironakaG3InteriorEmptyAligned
  HironakaOriginalActualEmptyNormalization HironakaOriginalInteriorEmptyHistory
  HironakaOriginalFiniteEmptyCompression HironakaG8EmptyAwareTestTransport
  HironakaG8SingularFootprintExtension

variable {n : ℕ} {X Y Z : CMfd.{0} n} {I J : Type}
variable {W D : Set X} {E : List (Set X)} {H : ℕ → ℕ}

local notation "HS[" A "]" => hilbertSamuelAt (vanishingIdeal (n := n) A)
local notation "ref" B => Diffeomorph.refl 𝓘(ℂ,ComplexModel n) B ∞
local notation "inv" => ResolutionInvariantSeq.ResolutionInvariant.inv (canonicalInvariant n)
local notation "original[" W ";" E "]" =>
  (MarkedIdeal.mk univ E (vanishingIdeal (n := n) W) 1 : MarkedIdeal n _)

/-- Actual terminal histories allow empty global stages while retaining
a simultaneous maximum at each nonempty one. -/
structure NativeSynchronizedTerminal (A : NativeWindows X I W E H D)
    (T : BlowupTower X Y) : Prop where
  test : IsGeoTestTower original[W;E] T
  singular : StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T
  canonical : ∀ i, IsCanonical (A.powered i) (inv (A.powered i)) (restrict (A.openSet i) T)
  simultaneous : NativeSimultaneousStages (canonicalInvariant n) A.openSet A.powered T
  terminal : ∀ i, (geoTransformAlong (A.powered i) (restrict (A.openSet i) T)).cosupp = ∅

private theorem NativeSynchronizedTerminal.delete (hn : 0 < n)
    (hW : IsComplexAnalyticSubset (n := n) W) (hE : IsSNCDivisor n E)
    {A : NativeWindows X I W E H D}
    {P Q : CMfd.{0} n} (T₀ : BlowupTower X P) (π : Q → P) (hπ : IsBlowupAlong n (∅ : Set P) π)
    (S : BlowupTower Q Y) (hT : NativeSynchronizedTerminal A ((T₀.step ∅ π hπ).append S)) :
    ∃ (Y' : CMfd.{0} n) (S' : BlowupTower P Y')
      (χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y),
      S'.length = S.length ∧ EmptyAwareTowerIso (ref X) (T₀.append S') ((T₀.step ∅ π hπ).append S) χ ∧
        NativeSynchronizedTerminal A (T₀.append S') := by
  obtain ⟨Y',S',χ,hLen,hIso⟩ := exists_actual_empty_step_normalization T₀ π hπ S
  have hCan i := canonical_window_at_same_base_iso (canonicalInvariant n) (A.openSet i)
    (A.powered i) (A.powered_domain i) hIso (hT.canonical i)
  have hClear i := window_cosupp_empty_at_same_base_iso (canonicalInvariant n) (A.openSet i)
    (A.powered i) (A.powered_domain i) hIso (hT.canonical i) (hT.terminal i)
  have hSync := simultaneous_stages_at_same_base_iso A.openSet A.powered hIso
    A.powered_domain hT.canonical hT.simultaneous
  have hClock (i : I) : (A.powered i).E.length = E.length := by
    change (A.record i).E.length = _
    rw [A.boundary,List.length_map]
  have hSynced := simultaneous_stages_delete_identity_empty A.openSet A.powered
    hn E.length A.powered_domain hClock T₀ S' hCan hSync
  obtain ⟨hCanonical,hTerminal⟩ := canonical_window_delete_identity_empty A.openSet A.powered
    hn A.powered_domain T₀ S' hCan hClear
  have hPhys : EmptyAwareTowerIso (ref X) (T₀.append S') ((T₀.step ∅ π hπ).append S) χ := by
    simpa only [Diffeomorph.refl_trans] using HironakaG3EmptyAwareComposition.trans
      (interior_empty_aligned T₀ S') (emptyAware_of_isTowerIso hIso)
  have hM : original[W;E].IsWellFormed := ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ,
    CartanIrreducible.cartanCoherence W hW,hE,SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE⟩
  have hGeo := isGeoTestTower_iff_of_emptyAware original[W;E] hM (ref X) hPhys |>.mpr hT.test
  have hPull : MarkedIdeal.pullback (ref X) original[W;E] = original[W;E] :=
    ContactCanonicalAlong.pullback_id _ hM.isCoherent
  rw [hPull] at hGeo
  have hBack : EmptyAwareTowerIso (ref X) ((T₀.step ∅ π hπ).append S) (T₀.append S') χ.symm := by
    simpa only [Diffeomorph.symm_refl] using HironakaG3EmptyAwareSymmetry.symm hPhys
  have hSing := singular_stages_of_emptyAware W hW.isClosed (ref X) hBack hT.singular
  exact ⟨Y',S',χ,hLen,hPhys,⟨hGeo,hSing,hCanonical,hSynced,hTerminal⟩⟩

/-- A single global compression is used by every native window and
preserves all simultaneous stages and their terminal certificates. -/
theorem exists_nonempty_simultaneous_terminal (hn : 0 < n)
    (hW : IsComplexAnalyticSubset (n := n) W) (hE : IsSNCDivisor n E)
    {A : NativeWindows X I W E H D}
    (T : BlowupTower X Y) (hT : NativeSynchronizedTerminal A T) :
    ∃ (Z : CMfd.{0} n) (Q : BlowupTower X Z)
      (χ : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y),
      Q.length ≤ T.length ∧ EmptyAwareTowerIso (ref X) Q T χ ∧
        NativeNonemptySegment A Q ∧
        ∀ i, (geoTransformAlong (A.powered i) (restrict (A.openSet i) Q)).cosupp = ∅ := by
  classical
  generalize hLen : T.length = l
  induction l using Nat.strong_induction_on generalizing Y with
  | h l ih =>
    by_cases hNe : StageCentres (fun _ C => C.Nonempty) T
    · exact ⟨Y,T,ref Y,hLen.le,emptyAware_of_isTowerIso (IsTowerIso.refl_self T),
        ⟨hT.test,hT.singular,hT.canonical,hT.simultaneous,hNe⟩,hT.terminal⟩
    obtain ⟨P,Q,T₀,π,hπ,S,hEq⟩ := exists_actual_empty_step_split T hNe
    subst T
    obtain ⟨Y',S',χ,hDel,hPhys,hT'⟩ := NativeSynchronizedTerminal.delete hn hW hE T₀ π hπ S hT
    have hLt : (T₀.append S').length < l := by
      rw [BlowupTower.length_append,hDel]
      rw [BlowupTower.length_append] at hLen
      change T₀.length + 1 + S.length = l at hLen
      omega
    obtain ⟨Z,R,ψ,hLe,hPhys',hR,hTerminal⟩ := ih _ hLt (T₀.append S') hT' rfl
    refine ⟨Z,R,ψ.trans χ,hLe.trans hLt.le,?_,hR,hTerminal⟩
    simpa only [Diffeomorph.refl_trans] using HironakaG3EmptyAwareComposition.trans hPhys' hPhys

/-- Complete same-profile native phases over one actual base physically
agree up to empty stages, with different window covers and common
positive marks allowed. -/
theorem native_simultaneous_terminal_emptyAware (hn : 0 < n)
    (hW : IsComplexAnalyticSubset (n := n) W) (hE : IsSNCDivisor n E)
    (hExact : D = {x | ∀ ℓ, HS[W] x ℓ = H ℓ})
    (hNot : ∀ B ∈ E, ∀ x ∈ D, x ∈ B → ¬ ∀ᶠ z in 𝓝 x, z ∈ B → z ∈ W)
    {A : NativeWindows X I W E H D} {B : NativeWindows X J W E H D}
    {T : BlowupTower X Y} {S : BlowupTower X Z}
    (hT : NativeSynchronizedTerminal A T) (hS : NativeSynchronizedTerminal B S) :
    ∃ χ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z, EmptyAwareTowerIso (ref X) T S χ := by
  obtain ⟨Y',T',ψ,_,hPhysT,hT',hEndT⟩ := exists_nonempty_simultaneous_terminal hn hW hE T hT
  obtain ⟨Z',S',φ,_,hPhysS,hS',hEndS⟩ := exists_nonempty_simultaneous_terminal hn hW hE S hS
  obtain ⟨τ,hMatch⟩ := exists_isTowerIso_of_simultaneous_terminal hn hW hE hExact hNot hT' hS' hEndT hEndS
  refine ⟨ψ.symm.trans (τ.trans φ),?_⟩
  simpa only [Diffeomorph.refl_trans,Diffeomorph.symm_refl] using HironakaG3EmptyAwareComposition.trans
    (HironakaG3EmptyAwareSymmetry.symm hPhysT)
    (HironakaG3EmptyAwareComposition.trans (emptyAware_of_isTowerIso hMatch) hPhysS)

end
end Hironaka.HironakaG8NativeSimultaneousTerminal
