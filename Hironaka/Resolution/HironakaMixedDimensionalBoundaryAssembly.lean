import Hironaka.Resolution.HironakaOriginalNCMarkedStratumCompactDriver
import Hironaka.Resolution.HironakaPrincipalizationBoundary
import Hironaka.Resolution.HironakaSeparation

/-!
# Retained-boundary principalization and pair separation

The prescribed genuine normal-crossings carrier and the ordered initial
SNC list are both retained. The actual arbitrary-boundary marked driver
constructs one tower; all whole-ideal, born-support, branch-test, and terminal
adaptation conclusions refer to that same tower. Pair separation is then
derived for actual analytic sets from their original sum of vanishing ideals.

These are the initial geometric steps of mixed-dimensional boundary assembly.
No finite mixed-list resolution or original mixed embedded endpoint is claimed.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaMixedDimensionalBoundaryAssembly

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings GermIdealTotalTransform DivisorExponentAlong RestrictedIdealExtension
  HironakaAdmissibleSequence HironakaNormalCrossingsLocalBranches
  HironakaNormalCrossingsBoundaryTransform HironakaOriginalOldBranchOpenHistory
  HironakaOriginalNCOldStratumStrictEquality HironakaOriginalNCMarkedStratumHistoryValue
  HironakaOriginalNCMarkedStratumCompactDriver

open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open HomogenizedGlueingTower (strictAlong)

variable {n : ℕ}

/-- Mark-one principalization retaining the prescribed carrier and the entire
original labelled list, with every output on the same actual native tower. -/
theorem exists_retained_boundary_principalization {X : CMfd.{u} n}
    {I : GermIdeal n X} (hI : I.IsCoherent) (hne : ∀ x, IsNonzeroAlongAt univ I x)
    {E₀ : List (Set X)} (hE₀ : IsSNCDivisor n E₀)
    {H : Set X} (hH : IsBoundaryAdaptedCarrier (n := n) H E₀)
    (hZ : IsCompact I.zeroLocus) :
    let M : MarkedIdeal n X := ⟨univ, E₀, I, 1⟩
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      let E := (geoTransformAlong M T).E
      let D := exceptionalDivisor T
      IsGeoResolution M T ∧ IsCanonical M (markedStratumHistoryValue M H) T ∧
      IsOriginalBranchTestTower M H T ∧
      IsAdmissibleBlowupSequence n X E₀ I.zeroLocus Y T.proj E ∧
      IsSNCDivisor n E ∧ GermIdeal.pullback (m := n) T.proj I = D.ideal ∧
      D.support = (⋃ A ∈ E.drop E₀.length, A) ∧
      D.support = T.proj ⁻¹' I.zeroLocus ∧
      IsIsomorphismOver n T.proj I.zeroLocusᶜ ∧
      IsBoundaryAdaptedCarrier (n := n) (strictAlong T H) E := by
  let M : MarkedIdeal n X := ⟨univ, E₀, I, 1⟩
  have hM : IsInvDomain n M :=
    HironakaPrincipalizationBoundary.isInvDomain_univ_of_isSNCDivisor hI hne hE₀
  have hcos : M.cosupp = I.zeroLocus := by
    show GermIdealOrder.cosupport n univ I 1 = I.zeroLocus
    rw [GermIdealOrder.cosupport_one
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hg),
      univ_inter]
  have hK : IsCompact M.cosupp := by rw [hcos]; exact hZ
  obtain ⟨Y, T, hRes, hCan, hHistory⟩ :=
    exists_markedStratum_canonical_resolving_tower M hM hK hH
  have hpb : GermIdeal.pullback (m := n) T.proj I = (exceptionalDivisor T).ideal :=
    pullback_eq_exceptionalDivisor_of_isGeoResolution M rfl hI rfl T hRes
  have hsuppZ : (exceptionalDivisor T).support = T.proj ⁻¹' I.zeroLocus := by
    rw [EffectiveDivisor.support, ← hpb,
      BlowupExceptionalDivisor.zeroLocus_pullback T.contMDiff_proj hI]
  have hadm := isAdmissibleBlowupSequence_proj M _ T hRes.1
    (centresOver_cosupp M hM.isWellFormed.isClosedSubmanifold_N hI T hRes.1)
  rw [hcos] at hadm
  have hsupp := HironakaPrincipalizationBoundary.support_exceptionalDivisor_eq_biUnion_drop
    M hE₀.1 T
  have hIso : IsIsomorphismOver n T.proj I.zeroLocusᶜ := by
    refine HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset
      T.isBlowupSequence ?_
    rintro x ⟨y, hy, rfl⟩
    have hy' := HironakaPrincipalization.exceptionalLocus_subset_support T hy
    rw [hsuppZ] at hy'
    exact hy'
  have hPair := (current_old_strata_eq_strict M hH T hRes.1 hHistory).1
  exact ⟨Y, T, hRes, hCan, hHistory, hadm,
    (InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hRes.1).isWellFormed.isSNCDivisor,
    hpb, hsupp, hsuppZ, hIso, hPair⟩

/-- The sum of the actual vanishing ideals supplies one separation tower;
the original carrier, old labels, and whole born suffix remain literal. -/
theorem exists_retained_boundary_pair_separation {X : CMfd.{u} n}
    {A B : Set X} (hAa : IsComplexAnalyticSubset (n := n) A)
    (hBa : IsComplexAnalyticSubset (n := n) B) (hint : interior A = ∅)
    (hK : IsCompact (A ∩ B)) (hAB : A ⊆ closure (A \ B)) (hBA : B ⊆ closure (B \ A))
    {E₀ : List (Set X)} (hE₀ : IsSNCDivisor n E₀)
    {H : Set X} (hH : IsBoundaryAdaptedCarrier (n := n) H E₀) :
    let J := sumIdeal (vanishingIdeal (n := n) A) (vanishingIdeal (n := n) B)
    let M : MarkedIdeal n X := ⟨univ, E₀, J, 1⟩
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      let E := (geoTransformAlong M T).E
      let D := exceptionalDivisor T
      IsGeoResolution M T ∧ IsCanonical M (markedStratumHistoryValue M H) T ∧
      IsOriginalBranchTestTower M H T ∧
      IsAdmissibleBlowupSequence n X E₀ (A ∩ B) Y T.proj E ∧
      IsSNCDivisor n E ∧ GermIdeal.pullback (m := n) T.proj J = D.ideal ∧
      D.support = (⋃ C ∈ E.drop E₀.length, C) ∧
      D.support = T.proj ⁻¹' (A ∩ B) ∧
      IsIsomorphismOver n T.proj (A ∩ B)ᶜ ∧
      IsBoundaryAdaptedCarrier (n := n) (strictAlong T H) E ∧
      Disjoint (strictTransform n T.proj A) (strictTransform n T.proj B) := by
  let J := sumIdeal (vanishingIdeal (n := n) A) (vanishingIdeal (n := n) B)
  have hJ : J.IsCoherent :=
    isCoherent_sumIdeal (CartanIrreducible.cartanCoherence A hAa)
      (CartanIrreducible.cartanCoherence B hBa)
  have hne : ∀ x, IsNonzeroAlongAt univ J x := fun x =>
    InvDomainCompanion.isNonzeroAlongAt_sumIdeal_left (𝔟 := vanishingIdeal (n := n) A)
      (𝔠 := vanishingIdeal (n := n) B) (fun _ _ h => h.1)
      (HironakaEmbeddedReducible.isNonzeroAlongAt_vanishingIdeal_of_interior_eq_empty hAa hint x)
  have hZ : J.zeroLocus = A ∩ B :=
    HironakaSeparation.zeroLocus_sumIdeal_vanishingIdeal hAa.isClosed hBa.isClosed
  obtain ⟨Y, T, hRes, hCan, hHistory, hadm, hsnc, hpb, hsupp, hsuppZ, hIso, hPair⟩ :=
    exists_retained_boundary_principalization hJ hne hE₀ hH (by rw [hZ]; exact hK)
  rw [hZ] at hadm hsuppZ hIso
  exact ⟨Y, T, hRes, hCan, hHistory, hadm, hsnc, hpb, hsupp, hsuppZ, hIso, hPair,
    HironakaSeparation.disjoint_strictTransform_of_pullback_sumIdeal
      T.contMDiff_proj hAB hBA (exceptionalDivisor T) hpb hsuppZ.le⟩

end

end Hironaka.HironakaMixedDimensionalBoundaryAssembly
