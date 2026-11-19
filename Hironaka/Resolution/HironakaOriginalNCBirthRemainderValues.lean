import Hironaka.Resolution.HironakaOriginalNCBirthRemainderTransport
import Hironaka.Invariant.InvDomainRebase

set_option autoImplicit false

/-!
# Real per-sequence values across the actual internally produced birth suffix

The SAME empty suffix is internally canonical, with all actual empty years and
whole ordered boundary positions retained. Seq.IsInvValue.emptyPrefix and its
representative property compare birth and current remainder values only on
their actual common cosupport. The natural final producer supplies its phase,
birth history, empty suffix, domains and representative comparison internally.

There is no rebase across a nonempty prefix, no finite canonical phase choice
on a possibly noncompact local birth open, and no original general-NC driver
or original parent canonical-invariant identification.

Blueprint: hironaka-original-nc-birth-remainder-values-extension.tex.
Source-only draft; no kernel-check claim.
-/

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u v

namespace Hironaka.HironakaOriginalNCBirthRemainderValues

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  NormalCrossings GermIdealOrder CoefficientIdeal CoefficientIdealRestriction
  HomogenizedGlueingTower MemberInterTowerAlong
  HironakaStepOneSpecialAnalyticLoci HironakaStepOneMemberLowerExtension
  HironakaDimensionTwoStepOneAnalyticSuperlevels HironakaStepOneZeroContactRemainderExtension
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsMultiplicityStrata
  HironakaNormalCrossingsBoundaryTransform HironakaNormalCrossingsOpenRestrictionSeparation
  HironakaBoundaryCoefficientStratumResolution HironakaOriginalOldBranchOpenHistory
  HironakaOriginalNCCountHistory HironakaOriginalNCBirthRemainderTransport
open MarkedIdealOperationsAlong.MarkedIdeal
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open ResolutionInvariantExt (IsEmptyTower isGeoTestTower_of_isEmptyTower isCanonical_of_isEmptyTower)

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- A true empty history is internally canonical. The actual per-sequence
empty-prefix and representative fields give values on the common cosupport;
no canonicality or invariant-value certificate is a premise. -/
theorem empty_history_representative_value
    {k : ℕ} {Λ : Type v} [LinearOrder Λ]
    (V : ResolutionInvariantSeq.ResolutionInvariant.{u, v} n k Λ)
    (A : MarkedIdeal n X) (hA : IsInvDomain k A)
    (S : BlowupTower X Y) (he : IsEmptyTower S)
    (B : MarkedIdeal n Y) (hBI : B.ideal.IsCoherent)
    (hEq : RestrictEquiv B (geoTransformAlong A S)) :
    IsInvDomain k B ∧ ∀ z ∈ B.cosupp, V.inv A S z = V.inv B .refl z := by
  have hAS : IsInvDomain k (geoTransformAlong A S) :=
    InvDomainTowerAlong.isInvDomain_geoTransformAlong hA S (isGeoTestTower_of_isEmptyTower A S he)
  have hSymm := InvDomainRebase.restrictEquiv_symm hEq
  have hB : IsInvDomain k B := InvDomainRebase.isInvDomain_of_restrictEquiv hAS hSymm hBI
  have hCan : IsCanonical A (V.inv A) S := isCanonical_of_isEmptyTower A (V.inv A) S he
  have hCanAppend : IsCanonical A (V.inv A) (S.append .refl) := by
    simpa only [BlowupTower.append_refl] using hCan
  refine ⟨hB, ?_⟩
  intro z hz
  have hzAS : z ∈ (geoTransformAlong A S).cosupp := hEq.cosupp_eq ▸ hz
  have hEmpty := V.isInvValue.emptyPrefix A hA S .refl he hCanAppend z
    (by simpa only [BlowupTower.append_refl] using hzAS)
  have hEmpty' : V.inv A S z = V.inv (geoTransformAlong A S) .refl z := by
    simpa only [BlowupTower.append_refl] using hEmpty
  exact hEmpty'.trans (V.isInvValue.representative (geoTransformAlong A S) B hAS hB hSymm
    .refl trivial z hzAS)

private theorem coefficient_remainder_domain
    (M : MarkedIdeal n X) (hN : M.N = univ) (hI : M.ideal.IsCoherent)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E) {q : ℕ}
    (hBound : ∀ x : X, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ q) :
    IsInvDomain n (contactRemainderMarked (withN (coeffMarked M)
      {x | q ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}) 0) := by
  let Z := {x | q ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}
  let L := withN (coeffMarked M) Z
  have hZ := isClosedSubmanifold_highest_superlevel (isNormalCrossingsCarrier_of_boundaryAdapted h) hBound
  have hLI : L.ideal.IsCoherent := isCoherent_coeffMarked (𝔪 := M) hN hI
  have hLW : L.IsWellFormed :=
    ⟨hZ, hLI, isSNCDivisor_of_boundaryAdapted h, highest_stratum_isTransverse h hBound⟩
  have hLd : 1 ≤ L.d := by
    change 1 ≤ (Finset.range M.d).prod (fun i => M.d - i)
    have hp : 0 < (Finset.range M.d).prod (fun i => M.d - i) :=
      Finset.prod_pos fun i hi => by
        have hi' := Finset.mem_range.mp hi
        omega
    omega
  exact (contactRemainder_boundary_domain L hLW hLd).1

/-- Natural original data internally select the SAME completed phase and its
causal birth suffix. At every terminal original cosupport point, the fresh
endpoint intrinsic-q datum has the actual birth-datum value on its common
remainder cosupport. No caller phase, history, domain, empty suffix, transport
or canonicality certificate is assumed. -/
theorem exists_original_birth_current_remainder_values
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
            let A' := contactRemainderMarked (withN (coeffMarked (geoTransformAlong MW S))
              {z | q ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hcS) z}) 0
            IsInvDomain n Aq ∧ IsInvDomain n A' ∧ RestrictEquiv A' (geoTransformAlong Aq S) ∧
              A'.E = (geoTransformAlong MW S).E ∧
              ∀ z ∈ A'.cosupp, (CanonicalCentres.canonicalInvariant n).inv Aq S z =
                (CanonicalCentres.canonicalInvariant n).inv A' .refl z := by
  dsimp only
  let M : MarkedIdeal n X := ⟨univ, E, I, d⟩
  obtain ⟨Y, T, hRes, hMT, hHistory, hBirths⟩ :=
    exists_original_birth_current_remainder_transport I hI d hd hCompact h hr hBound
  refine ⟨Y, T, hRes, hMT, hHistory, ?_⟩
  intro y hy
  let β := birthYear H T y
  let k := T.length - β
  let K := head T k
  let Q := tail T k
  let q := oldCount H T y
  obtain ⟨hqr, hc, W, hWSet, hyW, hEmpty, hLen, hParent, hOld, hcS,
      hCurrentDomain, hCompare, hE, _hCosupp, _hCentres⟩ := hBirths y hy
  let MW := MarkedIdeal.pullback (Subtype.val : W → (split T k).1) (geoTransformAlong M K)
  let hW := boundaryAdapted_open W hc
  let S := restrict W Q
  let Zq := {z : W | q ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hW) z}
  let Aq := contactRemainderMarked (withN (coeffMarked MW) Zq) 0
  let A' := contactRemainderMarked (withN (coeffMarked (geoTransformAlong MW S))
    {z | q ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hcS) z}) 0
  have hMK := ((isGeoTestTower_iff_head_tail M T k).mp hMT).1
  have hKI := (isClosedSubmanifold_N_and_isCoherent_geoTransformAlong
    (𝔪 := M) isClosedSubmanifold_univ hI K hMK).2
  have hKN : (geoTransformAlong M K).N = univ :=
    (DerivativeIdealTower.inclusions_tower M rfl hI (j := 0) (Nat.zero_le _) K hMK).2.1
  have hMWN : MW.N = univ := by
    change (Subtype.val : W → (split T k).1) ⁻¹' (geoTransformAlong M K).N = univ
    rw [hKN, preimage_univ]
  have hMWI : MW.ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hKI
  have hWBound : ∀ z : W, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hW) z ≤ q := by
    intro z
    have hz : z.val ∈ (W : Set (split T k).1) := z.property
    rw [hWSet] at hz
    have hLow : branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) z.val ≤ q := by
      change ¬ q + 1 ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) z.val at hz
      omega
    exact (branchMultiplicity_open W (isNormalCrossingsCarrier_of_boundaryAdapted hc)
      (isNormalCrossingsCarrier_of_boundaryAdapted hW) z).trans_le hLow
  have hBirthDomain : IsInvDomain n Aq :=
    coefficient_remainder_domain (X := CMfd.of (n := n) W) MW hMWN hMWI hW hWBound
  obtain ⟨_hDomain, hValues⟩ := empty_history_representative_value
    (CanonicalCentres.canonicalInvariant n) Aq hBirthDomain S hEmpty A'
      hCurrentDomain.isWellFormed.isCoherent hCompare
  exact ⟨hqr, hc, W, hWSet, hyW, hEmpty, hLen, hParent, hOld,
    hcS, hBirthDomain, hCurrentDomain, hCompare, hE, hValues⟩

end
end Hironaka.HironakaOriginalNCBirthRemainderValues
