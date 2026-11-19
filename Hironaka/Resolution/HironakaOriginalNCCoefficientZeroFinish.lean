import Hironaka.Resolution.HironakaOriginalNCNextHighestBirthWindows
import Hironaka.Resolution.HironakaOriginalNCZeroCountCompletion
import Hironaka.Resolution.HironakaStepOneZeroContactRemainderGlueing
import Hironaka.Invariant.InvDomainCompanion

set_option autoImplicit false

/-!
# The zero-count finish retains the coefficient-birth invariant itself

The original nonzero ideal supplies a genuine nonzero coefficient germ from
the actual zeroth summand. Thus the selected-zero coefficient part is EMPTY
and Rem0(coeffM)=coeffM as a whole record. A genuine coefficient-canonical
resolving Q then resolves the SAME parent via the actual coefficient tower
dictionary, preserving all original old-branch histories and every empty
slot. No equality between parent and coefficient invariant values is used.

The final original-only producer internally selects the SAME completed T
and a matching current coefficient-canonical zero-count tail. This does not
assert canonicality of the full original composite or close the total NC
causal history interpreter.

Blueprint: hironaka-original-nc-coefficient-zero-finish-extension.tex.
Source-only draft; no kernel-check claim.
-/

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaOriginalNCCoefficientZeroFinish

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  MarkedIdealOperationsAlong.MarkedIdeal MarkedIdealEquivalence.MarkedIdeal
  NormalCrossings GermIdealOrder GermIdealPullbackCalculus CoefficientIdeal
  CoefficientIdealRestriction HomogenizedGlueing HomogenizedGlueingTower
  IdealWeightPowers DivisorExponentAlong InvDomainCompanion DerivativeIdealTower
  HironakaDimensionTwoStepOneAnalyticSuperlevels
  HironakaStepOneSpecialAnalyticLoci HironakaStepOneZeroContactRemainderExtension
  HironakaStepOneZeroContactRemainderGlueing
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsMultiplicityStrata
  HironakaNormalCrossingsBoundaryTransform HironakaNormalCrossingsOpenRestrictionSeparation
  HironakaOriginalOldBranchOpenHistory HironakaOriginalOldBranchCompactExtension
  HironakaOriginalNCNextHighestPhase HironakaOriginalNCNextHighestBirthWindows
  HironakaOriginalNCZeroCountCompletion
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

variable {n : ℕ} {X : CMfd.{u} n}

private theorem coefficient_positive (M : MarkedIdeal n X) : 1 ≤ (coeffMarked M).d := by
  change 1 ≤ (Finset.range M.d).prod (fun i => M.d - i)
  have hp : 0 < (Finset.range M.d).prod (fun i => M.d - i) :=
    Finset.prod_pos fun i hi => by
      have hi' := Finset.mem_range.mp hi
      omega
  omega

private theorem ambient_domain (M : MarkedIdeal n X) (hN : M.N = univ)
    (hI : M.ideal.IsCoherent) (hd : 1 ≤ M.d)
    (hne : ∀ x, IsNonzeroAlongAt univ M.ideal x) (hE : IsSNCDivisor n M.E) :
    IsInvDomain n M := by
  refine ⟨⟨?_, hI, hE, ?_⟩, ?_, hd, ?_⟩
  · rw [hN]
    exact isClosedSubmanifold_univ
  · rw [hN]
    exact SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE
  · rw [hN]
    exact fun x _ => ⟨n, le_rfl, AnalyticIrreducibleComponents.regularAtDim_univ x⟩
  · intro x _hx
    simpa only [hN] using hne x

/-- The actual zeroth finite-sum summand produces the coefficient's genuine
nonzero germ. Neither a coefficient-domain nor a nonzero certificate is an
extra hypothesis. The same witness works along the specified original set. -/
theorem isNonzeroAlongAt_coeffMarked (M : MarkedIdeal n X)
    (hI : M.ideal.IsCoherent) (hd : 1 ≤ M.d)
    {N : Set X} {x : X} (hne : IsNonzeroAlongAt N M.ideal x) :
    IsNonzeroAlongAt N (coeffMarked M).ideal x := by
  let e := sumExp (fun j => (derivMarked M j).d) M.d 0
  obtain ⟨g, hg, hFreq⟩ := isNonzeroAlongAt_idealPow
    (fun _ _ hf => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hf) hne e
  refine ⟨g, ?_, hFreq⟩
  change IsInSpanAt (n := n)
    (fun f => ∃ i, i < M.d ∧
      (idealPow (derivMarked M i).ideal (sumExp (fun j => (derivMarked M j).d) M.d i)).mem x f) x g
  exact InvertibleIdealQuotient.isInSpanAt_self ⟨0, hd, hg⟩
    (RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
      (isCoherent_idealPow hI e) hg)

/-- With the original nonzero hypothesis the selected coefficient part is
actually empty. Rem0 is literally the whole coefficient record, retaining
its product mark and its entire ordered boundary. -/
theorem coefficient_selected_empty_remainder_eq (M : MarkedIdeal n X)
    (hN : M.N = univ) (hI : M.ideal.IsCoherent) (hd : 1 ≤ M.d)
    (hne : ∀ x, IsNonzeroAlongAt univ M.ideal x) :
    selectedComponents (n := n) (coeffMarked M).N (coeffMarked M).cosupp = ∅ ∧
      contactRemainderMarked (coeffMarked M) 0 = coeffMarked M := by
  let L := coeffMarked M
  have hLN : L.N = univ := hN
  have hLS : IsClosedSubmanifold n L.N := hLN ▸ isClosedSubmanifold_univ
  have hLI : L.ideal.IsCoherent := isCoherent_coeffMarked (𝔪 := M) hN hI
  have hLd : 1 ≤ L.d := coefficient_positive M
  have hLne : ∀ x, IsNonzeroAlongAt L.N L.ideal x := by
    intro x
    rw [hLN]
    exact isNonzeroAlongAt_coeffMarked M hI hd (hne x)
  have hF : selectedComponents (n := n) L.N L.cosupp = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxN : x ∈ L.N := by rw [hLN]; exact mem_univ x
    exact ((selectedComponents_iff_not_isNonzeroAlongAt L hLS hLI hLd hxN).mp hx) (hLne x)
  have hR : remainingComponents (n := n) L.N L.cosupp = L.N := by
    rw [remainingComponents_eq_diff_selected hLS, hF, sdiff_empty]
  refine ⟨hF, MarkedIdealOperationsTransform.MarkedIdeal.ext_of hR ?_ rfl rfl⟩
  simp only [contactRemainderMarked, List.replicate_zero, List.drop_zero, List.nil_append]

/-- The zero branch uses the SAME coefficient-birth invariant. Actual
coefficient canonicality is retained, while test/resolution transfer to the
parent is proved by the genuine tower dictionary, with all old histories. -/
theorem exists_zero_count_coefficient_canonical_resolution (M : MarkedIdeal n X)
    (hN : M.N = univ) (hI : M.ideal.IsCoherent) (hd : 1 ≤ M.d)
    (hne : ∀ x, IsNonzeroAlongAt univ M.ideal x) (hK : IsCompact M.cosupp)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (hZero : ∀ x ∈ M.cosupp,
      branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ 0) :
    let A₀ := contactRemainderMarked (coeffMarked M) 0
    A₀ = coeffMarked M ∧ IsInvDomain n A₀ ∧
      ∃ (Y : CMfd.{u} n) (Q : BlowupTower X Y),
        IsCanonical A₀ ((CanonicalCentres.canonicalInvariant n).inv A₀) Q ∧
        IsGeoResolution A₀ Q ∧ IsGeoResolution M Q ∧ IsOriginalBranchTestTower M H Q ∧
        ∀ j : ℕ,
          (geoTransformAlong A₀ (head Q j)).cosupp = (geoTransformAlong M (head Q j)).cosupp ∧
          (geoTransformAlong A₀ (head Q j)).E = (geoTransformAlong M (head Q j)).E := by
  obtain ⟨_hF, hAeq⟩ := coefficient_selected_empty_remainder_eq M hN hI hd hne
  dsimp only
  rw [hAeq]
  have hCoeffI := isCoherent_coeffMarked (𝔪 := M) hN hI
  have hCoeffNe : ∀ x, IsNonzeroAlongAt univ (coeffMarked M).ideal x :=
    fun x => isNonzeroAlongAt_coeffMarked M hI hd (hne x)
  have hDom := ambient_domain (coeffMarked M) hN hCoeffI (coefficient_positive M)
    hCoeffNe (isSNCDivisor_of_boundaryAdapted h)
  have hCos : (coeffMarked M).cosupp = M.cosupp :=
    (coeff_tower M hN hI hd .refl).2 trivial
  have hKC : IsCompact (coeffMarked M).cosupp := by
    rw [hCos]
    exact hK
  obtain ⟨Y, Q, hCan, hRes⟩ :=
    HironakaAdmissibleSequence.exists_isGeoResolution_isCanonical_of_isCompact
      (CanonicalCentres.canonicalInvariant n) hDom hKC
  have hMQ : IsGeoTestTower M Q := (coeff_tower M hN hI hd Q).1.mp hRes.1
  have hMRes : IsGeoResolution M Q :=
    ⟨hMQ, ((coeff_tower M hN hI hd Q).2 hMQ).symm.trans hRes.2⟩
  have hDis : Disjoint M.cosupp H := by
    apply Set.disjoint_left.mpr
    intro x hx hxH
    have hp := (branchMultiplicity_pos_iff (isNormalCrossingsCarrier_of_boundaryAdapted h) x).mpr hxH
    have hz := hZero x hx
    omega
  have hHistory : IsOriginalBranchTestTower M H Q :=
    isOriginalBranchTestTower_of_disjoint_carrier M (hN ▸ isClosedSubmanifold_univ) hI hDis Q hMQ
  refine ⟨rfl, hDom, Y, Q, hCan, hRes, hMRes, hHistory, ?_⟩
  intro j
  have hHead := ((isGeoTestTower_iff_head_tail M Q j).mp hMQ).1
  exact ⟨(coeff_tower M hN hI hd (head Q j)).2 hHead,
    E_geoTransformAlong_eq (𝔪 := coeffMarked M) (𝔫 := M) rfl (head Q j)⟩

/-- Original natural data choose the completed T once. Its true zero-count
branch internally selects a whole-ambient coefficient-canonical parent
finish, preserving the original coefficient-birth value and all histories. -/
theorem exists_original_next_phase_with_coefficient_zero_finish
    (I : GermIdeal n X) (hI : I.IsCoherent) (d : ℕ) (hd : 1 ≤ d)
    (hne : ∀ x, IsNonzeroAlongAt univ I x)
    (hK : IsCompact (cosupport n univ I d))
    {H : Set X} {E : List (Set X)} (h : IsBoundaryAdaptedCarrier (n := n) H E)
    {r : ℕ} (hr : 0 < r)
    (hBound : ∀ x : X, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ r) :
    let M : MarkedIdeal n X := ⟨univ, E, I, d⟩
    let Z := {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}
    let L := withN (coeffMarked M) Z
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsGeoResolution L T ∧ IsGeoTestTower M T ∧ IsOriginalBranchTestTower M H T ∧
      ∃ hc : IsBoundaryAdaptedCarrier (n := n) (strictAlong T H) (geoTransformAlong M T).E,
        (geoTransformAlong M T).cosupp = ∅ ∨
          ∃ (q : ℕ) (V : Opens Y), q < r ∧
            (V : Set Y) = {z | q + 1 ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) z}ᶜ ∧
            (geoTransformAlong M T).cosupp ⊆ V ∧
            let MV := MarkedIdeal.pullback (Subtype.val : V → Y) (geoTransformAlong M T)
            let hV := boundaryAdapted_open V hc
            (∀ z : V, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hV) z ≤ q) ∧
            (∃ z ∈ MV.cosupp,
              branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hV) z = q) ∧
            IsCompact MV.cosupp ∧ HasCanonicalHighestRemainderPhase (X := CMfd.of (n := n) V) MV hV q ∧
            (∀ y ∈ (geoTransformAlong M T).cosupp, HasNestedBirthWindow M H T hc q V y) ∧
            (q = 0 →
              let A₀ := contactRemainderMarked (coeffMarked (geoTransformAlong M T)) 0
              A₀ = coeffMarked (geoTransformAlong M T) ∧ IsInvDomain n A₀ ∧
                ∃ (D : CMfd.{u} n) (Q : BlowupTower Y D),
                  IsCanonical A₀ ((CanonicalCentres.canonicalInvariant n).inv A₀) Q ∧
                  IsGeoResolution A₀ Q ∧ IsGeoResolution (geoTransformAlong M T) Q ∧
                  IsOriginalBranchTestTower (geoTransformAlong M T) (strictAlong T H) Q ∧
                  IsGeoResolution M (T.append Q) ∧ IsOriginalBranchTestTower M H (T.append Q) ∧
                  ∀ j : ℕ,
                    (geoTransformAlong A₀ (head Q j)).cosupp =
                      (geoTransformAlong (geoTransformAlong M T) (head Q j)).cosupp ∧
                    (geoTransformAlong A₀ (head Q j)).E =
                      (geoTransformAlong (geoTransformAlong M T) (head Q j)).E) := by
  dsimp only
  let M : MarkedIdeal n X := ⟨univ, E, I, d⟩
  obtain ⟨Y, T, hResL, hMT, hHistory, hc, hNext⟩ :=
    exists_original_next_highest_phase_with_nested_birth_windows I hI d hd hK h hr hBound
  refine ⟨Y, T, hResL, hMT, hHistory, hc, ?_⟩
  rcases hNext with hEmpty | ⟨q, V, hqr, hVSet, hCover, hVBound, hAttained, hKV, hPhase, hBirths⟩
  · exact Or.inl hEmpty
  · refine Or.inr ⟨q, V, hqr, hVSet, hCover, hVBound, hAttained, hKV, hPhase, hBirths, ?_⟩
    intro hq
    have hDom := ambient_domain M rfl hI hd hne (isSNCDivisor_of_boundaryAdapted h)
    have hDomT := InvDomainTowerAlong.isInvDomain_geoTransformAlong hDom T hMT
    have hTN : (geoTransformAlong M T).N = univ :=
      (DerivativeIdealTower.inclusions_tower M rfl hI (j := 0) (Nat.zero_le _) T hMT).2.1
    have hNeT : ∀ y, IsNonzeroAlongAt univ (geoTransformAlong M T).ideal y := by
      intro y
      have hyN : y ∈ (geoTransformAlong M T).N := by rw [hTN]; exact mem_univ y
      simpa only [hTN] using hDomT.isNonzeroAlongAt y hyN
    have hKT : IsCompact (geoTransformAlong M T).cosupp :=
      current_cosupport_compact M isClosedSubmanifold_univ hI hK T hMT
    have hZero : ∀ y ∈ (geoTransformAlong M T).cosupp,
        branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) y ≤ 0 := by
      intro y hy
      let p : V := ⟨y, hCover hy⟩
      have hb := hVBound p
      rw [hq] at hb
      exact (branchMultiplicity_open V (isNormalCrossingsCarrier_of_boundaryAdapted hc)
        (isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_open V hc)) p).symm.trans_le hb
    obtain ⟨hAeq, hA, D, Q, hCan, hResA, hResM, hHistoryQ, hPrefixes⟩ :=
      exists_zero_count_coefficient_canonical_resolution (geoTransformAlong M T)
        hTN hDomT.isWellFormed.isCoherent hDomT.one_le_d hNeT hKT hc hZero
    have hTestAppend : IsGeoTestTower M (T.append Q) :=
      (isGeoTestTower_append_iff M T Q).mpr ⟨hMT, hResM.1⟩
    have hResAppend : IsGeoResolution M (T.append Q) := by
      refine ⟨hTestAppend, ?_⟩
      rw [geoTransformAlong_append]
      exact hResM.2
    exact ⟨hAeq, hA, D, Q, hCan, hResA, hResM, hHistoryQ, hResAppend,
      isOriginalBranchTestTower_append M rfl hI T Q hMT hHistory hHistoryQ, hPrefixes⟩

end
end Hironaka.HironakaOriginalNCCoefficientZeroFinish
