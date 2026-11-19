import Hironaka.Resolution.HironakaG1LocalizedBornNormalOrder

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace

namespace Hironaka.HironakaG1LocalizedBornNormalHistory
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism ResolutionInvariantSpec
  CompanionRebase CompanionReductionAlong NonmonomialOrderLocal NonmonomialOrderRegime
  InvDomainCompanion InvDomainTowerAlong NonmonomialOrderTail
  MarkedIdealOperationsAlong MarkedIdealOperationsAlong.MarkedIdeal
  MarkedIdealEquivalence MarkedIdealEquivalence.MarkedIdeal
  RestrictedIdealExtension HironakaG8ContactMax MaximalContactAlongTower
  TangentDirectionAlong HironakaG8LocalHistory HironakaG1RecursiveMemberValueTransport
  StepOneValue StepOneRegime StepOneLowerDomain BoundaryCount InvDomainMemberRestriction
  HironakaG1LocalizedLaterBornCanonical HironakaG1LocalizedBornNormalOrder
open HomogenizedGlueingTower (strictAlong)

set_option maxHeartbeats 1000000 in
/-- A same-mark carrier-restricted companion fixes the nonmonomial
order at every surviving point of every genuine test. A genuine
base tangent also carries its exact zero trace through that history. -/
theorem same_mark_test_order_and_strict_contact {n k : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (K : MarkedIdeal n X) (hK : IsInvDomain k K)
    (u : X → ℂ) (hu : IsTangentDirectionAlong K.N K.ideal K.d univ u)
    (hBase : ∀ z ∈ K.cosupp, nmOrd K z = K.d)
    (hEq : companionOf n K K.d = (⟨K.N, K.E, restrictOn n K.N K.ideal, K.d⟩ : MarkedIdeal n X))
    (T : BlowupTower X Y) (hT : IsGeoTestTower K T) :
    let D := K.N ∩ {x : X | u x = 0}
    (∀ z ∈ (geoTransformAlong K T).cosupp, nmOrd (geoTransformAlong K T) z = K.d) ∧
    MaxContact (geoTransformAlong K T) (strictAlong T D) ∧
    (geoTransformAlong K T).cosupp ⊆ strictAlong T D := by
  intro D
  let C := companionOf n K K.d
  have hC := isInvDomain_companionAlong (X := X) (𝔪 := K) hn hK hK.one_le_d
  have hRE : RestrictEquiv C K := by
    unfold C
    rw [hEq]
    exact ⟨rfl, rfl, rfl, restrictLe_restrictOn, restrictLe_self_restrictOn hK.isWellFormed.isCoherent⟩
  have hW : WEquiv (X := X) C K := RestrictEquiv.wEquiv hRE
    hC.isWellFormed.isClosedSubmanifold_N.1 hC.isWellFormed.isCoherent hK.isWellFormed.isCoherent
  have hTC := ((hW.2 T).1).mpr hT
  have hB : ∀ z ∈ K.cosupp, z ∉ ordGe K (K.d + 1) := by
    intro z hz hHigh
    have h := (mem_ordGe_iff hK.isWellFormed hK.isNonzeroAlongAt hz.1 (K.d + 1)).mp hHigh
    rw [hBase z hz] at h
    omega
  have hFacts := companionOf_tower_facts hn hK hK.one_le_d hB T hTC
  have hKT := isInvDomain_geoTransformAlong hK T hT
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    have hzC : z ∈ (geoTransformAlong C T).cosupp := ((hW.2 T).2 hTC).symm ▸ hz
    exact le_antisymm (nmOrd_le_of_notMem (hFacts.2.1 z hz))
      ((mem_ordGe_iff hKT.isWellFormed hKT.isNonzeroAlongAt hz.1 K.d).mp (hFacts.2.2 hzC).1)
  · intro z hz
    obtain ⟨O, w, hzO, hO, _, hHol, hMem, hSimple, hTrace⟩ :=
      exists_contact_along K hK.isWellFormed.isClosedSubmanifold_N hK.isWellFormed.isCoherent
        hK.one_le_d hu T hT z hz (mem_univ _)
    have hMark := d_geoTransformAlong K T
    refine ⟨O, w, hzO, hO, hHol, ?_, hSimple, ?_⟩
    · rw [hMark]
      exact hMem
    · simpa only [inter_univ] using hTrace
  · intro z hz
    have := cosupp_subset_strictAlong_along K hK.isWellFormed.isClosedSubmanifold_N
      hK.isWellFormed.isCoherent hK.one_le_d hu T hT ⟨hz, mem_univ _⟩
    simpa only [inter_univ] using this

/-- Selection on the same ordered members preserves the exact zero trace
between the two localized carriers. -/
theorem positive_members_zero_trace {n : ℕ} {X : CMfd.{0} n}
    (J R : MarkedIdeal n X) (a : X) (W : Opens X) (u : X → ℂ)
    (hE : J.E = R.E) (hTrace : J.N ∩ {x | u x = 0} = R.N) :
    let H : BlowupTower X X := .refl
    let K := positiveMemberOn J H a W
    let S := positiveMemberOn R H a W
    K.N ∩ {z : W | u z.val = 0} = S.N := by
  intro H K S
  let B := barMarked J
  let D := barMarked R
  have hOrig : origMembers J H = origMembers R H := HironakaG8MemberLoci.origMembers_eq_of_E_eq hE H
  have hB : ∀ F ∈ origMembers J H, F ∈ B.E := fun _ h => List.mem_of_mem_take h
  have hD : ∀ F ∈ origMembers R H, F ∈ D.E := fun _ h => List.mem_of_mem_take h
  change ((Subtype.val : W → X) ⁻¹' (J.N ∩ memberInter B.E
    (membersThrough B.E (origMembers J H) a))) ∩ {z : W | u z.val = 0} =
      (Subtype.val : W → X) ⁻¹' (R.N ∩ memberInter D.E (membersThrough D.E (origMembers R H) a))
  rw [memberInter_membersThrough hB a, memberInter_membersThrough hD a, hOrig]
  ext z
  exact ⟨fun hz => ⟨hTrace ▸ ⟨hz.1.1, hz.2⟩, hz.1.2⟩,
    fun hz => ⟨⟨(hTrace ▸ hz.1).1, hz.2⟩, (hTrace ▸ hz.1).2⟩⟩

set_option maxHeartbeats 1800000 in
/-- The literal next-born cut has fixed true order on every genuine test
from one common window. Its transformed contact is precisely the strict
transform of the supported selected carrier, including at every prefix. -/
theorem exists_localized_born_normal_history {n k l : ℕ} (hn : 0 < n) {X : CMfd.{0} n}
    (J R : MarkedIdeal n X) (hJ : IsInvDomain k J) (hR : IsInvDomain l R)
    (hClass : LocWPEquiv J R) (a : X) (ha : a ∈ R.N) (u : X → ℂ)
    (hu : IsTangentDirectionAlong J.N J.ideal J.d univ u)
    (hTrace : J.N ∩ {z | u z = 0} = R.N)
    (hWitness : LocalizedBornWitness (k := k) (l := l) hn J R a u) :
    let H : BlowupTower X X := .refl
    ∃ W : Opens X, a ∈ W ∧ W ≤ maskA J H a ∧ W ≤ maskA R H a ∧
      let A := CMfd.of (n := n) W
      let K := positiveMemberOn J H a W
      let S := positiveMemberOn R H a W
      IsInvDomain (k - 1) K ∧ K.N ∩ {z : W | u z.val = 0} = S.N ∧
      ∀ {Y : CMfd.{0} n} (T : BlowupTower A Y), IsGeoTestTower K T →
        (∀ z ∈ (geoTransformAlong K T).cosupp, nmOrd (geoTransformAlong K T) z = K.d) ∧
        MaxContact (geoTransformAlong K T) (strictAlong T S.N) ∧
        (geoTransformAlong K T).cosupp ⊆ strictAlong T S.N ∧
        (∀ z ∈ (geoTransformAlong K T).cosupp,
          regimeRun (OrdRegime K K.d) T z = T.length ∧
          ∀ i, i ≤ T.length →
            OrdRegime K K.d (head T i) ((tail T i).proj z) ∧
            (tail T i).proj z ∈ strictAlong (head T i) S.N) := by
  intro H
  obtain ⟨W, haW, hWJ, hWR, hK, hTan, _, _, hBase, hEq⟩ :=
    exists_localized_born_normal_order hn J R hJ hR hClass a ha u hu hTrace hWitness
  let A := CMfd.of (n := n) W
  let K := positiveMemberOn J H a W
  let S := positiveMemberOn R H a W
  have hZero : K.N ∩ {z : W | u z.val = 0} = S.N :=
    positive_members_zero_trace J R a W u hClass.wEquiv.1 hTrace
  refine ⟨W, haW, hWJ, hWR, hK, hZero, fun T hT => ?_⟩
  have hFacts := same_mark_test_order_and_strict_contact hn K hK _ hTan hBase hEq T hT
  change (∀ z ∈ (geoTransformAlong K T).cosupp, nmOrd (geoTransformAlong K T) z = K.d) ∧
    MaxContact (geoTransformAlong K T) (strictAlong T (K.N ∩ {z : W | u z.val = 0})) ∧
    (geoTransformAlong K T).cosupp ⊆ strictAlong T (K.N ∩ {z : W | u z.val = 0}) at hFacts
  rw [hZero] at hFacts
  refine ⟨hFacts.1, hFacts.2.1, hFacts.2.2, fun z hz => ?_⟩
  have hPrefixes (i : ℕ) : OrdRegime K K.d (head T i) ((tail T i).proj z) ∧
      (tail T i).proj z ∈ strictAlong (head T i) S.N := by
    have hSplit := (isGeoTestTower_iff_head_tail K T i).mp hT
    have hCur := isInvDomain_geoTransformAlong hK (head T i) hSplit.1
    have hz' := hz
    rw [geoTransformAlong_head_tail K T i] at hz'
    have hp := proj_mem_cosupp_of_mem_cosupp hCur.isWellFormed.isClosedSubmanifold_N
      hCur.isWellFormed.isCoherent (tail T i) hSplit.2 hz'
    have h := same_mark_test_order_and_strict_contact hn K hK _ hTan hBase hEq (head T i) hSplit.1
    refine ⟨⟨hp, h.1 _ hp⟩, ?_⟩
    rw [← hZero]
    exact h.2.2 hp
  refine ⟨le_antisymm (regimeRun_le_length (OrdRegime K K.d) T z) (le_of_not_gt ?_),
    fun i _ => hPrefixes i⟩
  intro hlt
  exact not_regime_head_regimeRun (OrdRegime K K.d) T z hlt (hPrefixes _).1

end
end Hironaka.HironakaG1LocalizedBornNormalHistory
