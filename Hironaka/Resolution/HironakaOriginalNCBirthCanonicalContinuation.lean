import Hironaka.Resolution.HironakaOriginalNCBirthRemainderValues

set_option autoImplicit false

/-!
# Actual canonical futures of the internally produced birth remainder

The future tower is allowed to have nonempty centres. Its canonicality for
the fresh current remainder is an explicit generic history domain, and is
transported to the concatenation with the SAME actual empty birth suffix.
The natural completed-phase producer internally supplies all birth data and
domains. It does not choose a future phase or infer canonicality from ordinary
testness, and makes no original parent canonical-invariant identification.

Blueprint: hironaka-original-nc-birth-canonical-continuation-extension.tex.
Source-only draft; no kernel-check claim.
-/

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u v

namespace Hironaka.HironakaOriginalNCBirthCanonicalContinuation

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  NormalCrossings GermIdealOrder CoefficientIdeal CoefficientIdealRestriction
  HomogenizedGlueingTower MemberInterTowerAlong HironakaStepOneSpecialAnalyticLoci
  HironakaStepOneZeroContactRemainderExtension
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsMultiplicityStrata
  HironakaNormalCrossingsBoundaryTransform HironakaNormalCrossingsOpenRestrictionSeparation
  HironakaOriginalOldBranchOpenHistory HironakaOriginalNCCountHistory
  HironakaOriginalNCBirthRemainderValues
open MarkedIdealOperationsAlong.MarkedIdeal MarkedIdealEquivalence.MarkedIdeal
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open ResolutionInvariantExt (IsEmptyTower)

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- The genuine per-sequence dictionary extends across any actual canonical
future, including nonempty steps. Canonicality of the concatenation is proved
internally from canonicality of the fresh representative's future. Ordinary
testness is a conclusion, not a substitute for that explicit history domain. -/
theorem empty_history_canonical_continuation
    {k : ℕ} {Λ : Type v} [LinearOrder Λ]
    (V : ResolutionInvariantSeq.ResolutionInvariant.{u, v} n k Λ)
    (A : MarkedIdeal n X) (hA : IsInvDomain k A)
    (S : BlowupTower X Y) (he : IsEmptyTower S)
    (B : MarkedIdeal n Y) (hBI : B.ideal.IsCoherent)
    (hEq : RestrictEquiv B (geoTransformAlong A S)) :
    IsInvDomain k (geoTransformAlong A S) ∧ IsInvDomain k B ∧
      ∀ {Z : CMfd.{u} n} (P : BlowupTower Y Z),
        (IsCanonical B (V.inv B) P ↔ IsCanonical A (V.inv A) (S.append P)) ∧
        (IsCanonical B (V.inv B) P →
          IsCanonical A (V.inv A) (S.append P) ∧
          IsGeoTestTower B P ∧ IsGeoTestTower A (S.append P) ∧
          (geoTransformAlong A (S.append P)).E = (geoTransformAlong B P).E ∧
          (geoTransformAlong A (S.append P)).cosupp = (geoTransformAlong B P).cosupp ∧
          ResolutionDriver.maxLocus (V.inv A (S.append P)) (geoTransformAlong A (S.append P)).cosupp =
            ResolutionDriver.maxLocus (V.inv B P) (geoTransformAlong B P).cosupp ∧
          (S.append P).length = S.length + P.length ∧
          ∀ z ∈ (geoTransformAlong B P).cosupp, V.inv A (S.append P) z = V.inv B P z) := by
  have hAS : IsInvDomain k (geoTransformAlong A S) :=
    InvDomainRebase.isInvDomain_geoTransformAlong_of_isEmptyTower hA S he
  have hSymm := InvDomainRebase.restrictEquiv_symm hEq
  have hB : IsInvDomain k B := InvDomainRebase.isInvDomain_of_restrictEquiv hAS hSymm hBI
  refine ⟨hAS, hB, ?_⟩
  intro Z P
  have hAppend := Seq.ResolutionInvariantExt.isCanonical_append_iff V hA S he P
  have hCanIff : IsCanonical B (V.inv B) P ↔ IsCanonical A (V.inv A) (S.append P) := by
    constructor
    · intro hPB
      exact hAppend.mpr (Seq.InvDomainRebase.isCanonical_of_restrictEquiv V hB hAS hEq P hPB)
    · intro hPA
      exact Seq.InvDomainRebase.isCanonical_of_restrictEquiv V hAS hB hSymm P (hAppend.mp hPA)
  refine ⟨hCanIff, ?_⟩
  intro hPB
  have hPA := hCanIff.mp hPB
  have hPBTest : IsGeoTestTower B P :=
    ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical V.isInvValue hB P hPB
  have hPATest : IsGeoTestTower A (S.append P) :=
    ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical V.isInvValue hA (S.append P) hPA
  have hCos : (geoTransformAlong A (S.append P)).cosupp = (geoTransformAlong B P).cosupp := by
    rw [geoTransformAlong_append]
    exact (MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.cosupp_admissible_geoTransformAlong
      hSymm hAS.isWellFormed.isClosedSubmanifold_N.1
      hAS.isWellFormed.isCoherent hBI P).1
  have hE : (geoTransformAlong A (S.append P)).E = (geoTransformAlong B P).E := by
    rw [geoTransformAlong_append]
    exact E_geoTransformAlong_eq hSymm.E_eq P
  obtain ⟨_hB', _hPB', hValues⟩ := Seq.InvDomainRebase.inv_rebase V hA S he hEq hBI P hPA
  have hValuesB : ∀ z ∈ (geoTransformAlong B P).cosupp,
      V.inv A (S.append P) z = V.inv B P z := by
    intro z hz
    exact hValues z (by rw [hCos]; exact hz)
  have hMax : ResolutionDriver.maxLocus (V.inv A (S.append P))
      (geoTransformAlong A (S.append P)).cosupp =
      ResolutionDriver.maxLocus (V.inv B P) (geoTransformAlong B P).cosupp := by
    rw [hCos]
    exact ResolutionInvariantExt.maxLocus_congr hValuesB
  exact ⟨hPA, hPBTest, hPATest, hE, hCos, hMax, BlowupTower.length_append S P, hValuesB⟩

/-- Natural original data internally choose the completed phase and all
actual birth/empty-tail/domain/representative data. The dictionary for a
future tower is explicitly conditional on that future being canonical for
the current fresh remainder; this theorem does not select such a future. -/
theorem exists_original_birth_canonical_continuation
    (I : GermIdeal n X) (hI : I.IsCoherent) (d : ℕ) (hd : 1 ≤ d)
    (hCompact : IsCompact (cosupport n univ I d))
    {H : Set X} {E : List (Set X)} (h : IsBoundaryAdaptedCarrier (n := n) H E)
    {r : ℕ} (hr : 0 < r)
    (hBound : ∀ x : X, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ r) :
    let M : MarkedIdeal n X := ⟨univ, E, I, d⟩
    let Z := {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}
    let L := withN (coeffMarked M) Z
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsGeoResolution L T ∧ IsGeoTestTower M T ∧ IsOriginalBranchTestTower M H T ∧
      ∀ y ∈ (geoTransformAlong M T).cosupp,
        let β := birthYear H T y
        let K := head T (T.length - β)
        let Q := tail T (T.length - β)
        let q := oldCount H T y
        q < r ∧ ∃ (hc : IsBoundaryAdaptedCarrier (n := n) (strictAlong K H) (geoTransformAlong M K).E)
          (W : Opens (split T (T.length - β)).1),
          (W : Set (split T (T.length - β)).1) =
            {z | q + 1 ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) z}ᶜ ∧
          Q.proj y ∈ W ∧ IsEmptyTower (restrict W Q) ∧ (restrict W Q).length = T.length - β ∧
          let MW := MarkedIdeal.pullback (Subtype.val : W → (split T (T.length - β)).1)
            (geoTransformAlong M K)
          let HW := (Subtype.val : W → (split T (T.length - β)).1) ⁻¹' strictAlong K H
          let hW := boundaryAdapted_open W hc
          let S := restrict W Q
          let Zq := {z : W | q ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hW) z}
          let Aq := contactRemainderMarked (withN (coeffMarked MW) Zq) 0
          geoTransformAlong MW S = MarkedIdeal.pullback (Subtype.val : openPreimage Q W → Y)
            (geoTransformAlong M T) ∧
          strictAlong S HW = (Subtype.val : openPreimage Q W → Y) ⁻¹' strictAlong T H ∧
          ∃ hcS : IsBoundaryAdaptedCarrier (n := n) (strictAlong S HW) (geoTransformAlong MW S).E,
            let B := contactRemainderMarked (withN (coeffMarked (geoTransformAlong MW S))
              {z | q ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hcS) z}) 0
            let V := CanonicalCentres.canonicalInvariant n
            IsInvDomain n Aq ∧ IsInvDomain n (geoTransformAlong Aq S) ∧ IsInvDomain n B ∧
              RestrictEquiv B (geoTransformAlong Aq S) ∧ B.E = (geoTransformAlong MW S).E ∧
              ∀ {J : CMfd.{u} n} (P : BlowupTower (CMfd.of (n := n) (openPreimage Q W)) J),
                (IsCanonical B (V.inv B) P ↔ IsCanonical Aq (V.inv Aq) (S.append P)) ∧
                (IsCanonical B (V.inv B) P →
                  IsCanonical Aq (V.inv Aq) (S.append P) ∧
                  IsGeoTestTower B P ∧ IsGeoTestTower Aq (S.append P) ∧
                  (geoTransformAlong Aq (S.append P)).E = (geoTransformAlong B P).E ∧
                  (geoTransformAlong Aq (S.append P)).cosupp = (geoTransformAlong B P).cosupp ∧
                  ResolutionDriver.maxLocus (V.inv Aq (S.append P))
                      (geoTransformAlong Aq (S.append P)).cosupp =
                    ResolutionDriver.maxLocus (V.inv B P) (geoTransformAlong B P).cosupp ∧
                  (S.append P).length = S.length + P.length ∧
                  ∀ z ∈ (geoTransformAlong B P).cosupp, V.inv Aq (S.append P) z = V.inv B P z) := by
  dsimp only
  obtain ⟨Y, T, hRes, hMT, hHistory, hBirths⟩ :=
    exists_original_birth_current_remainder_values I hI d hd hCompact h hr hBound
  refine ⟨Y, T, hRes, hMT, hHistory, ?_⟩
  intro y hy
  obtain ⟨hqr, hc, W, hWSet, hyW, hEmpty, hLen, hParent, hOld, hcS,
      hBirthDomain, hCurrentDomain, hCompare, hE, _hValues⟩ := hBirths y hy
  obtain ⟨hAS, hB, hFuture⟩ := empty_history_canonical_continuation
    (CanonicalCentres.canonicalInvariant n) _ hBirthDomain _ hEmpty _
      hCurrentDomain.isWellFormed.isCoherent hCompare
  exact ⟨hqr, hc, W, hWSet, hyW, hEmpty, hLen, hParent, hOld, hcS,
    hBirthDomain, hAS, hB, hCompare, hE, hFuture⟩

end
end Hironaka.HironakaOriginalNCBirthCanonicalContinuation
