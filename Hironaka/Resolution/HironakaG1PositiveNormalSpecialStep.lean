import Hironaka.Resolution.HironakaG1PositiveNormalPhase
import Hironaka.Resolution.HironakaActualNativeSectionMemberLocus
import Hironaka.Resolution.HironakaStepOneZeroContactRemainderGlueing

/-!
# The positive special step on the actual normal section

At a positive padded nonspecial point that is special on the strict
section, the native bar record has an admissible maximal-level member
locus on the padded mask. Blowing up this locus clears that special level.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1PositiveNormalSpecialStep

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  ResolutionInvariantSpec ResolutionDriver ResolutionInvariantDriver NormalCrossings BoundaryCount
  NormalCrossingsInvariance DivisorExponentAlong
  MemberInterLocusAlong InvDomainMemberRestriction InvDomainRebase
  StepOneValue StepOneValueMasked StepOneLowerDomain
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalContact
  HironakaG1ProperCarrierNormalLocalClass HironakaG1ProperNormalPhaseNative
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionOrderHistory
  HironakaActualSectionBoundaryGeometry HironakaActualNativeSectionInitialBar
  HironakaActualOpenZeroSectionDifferentials HironakaActualNativeSectionMemberLocus
  HironakaDisjointNativeOpenLift
  HironakaActualNativeInvariantDomain HironakaG8HomStable RelativePrincipalizationSpan
  HironakaG1PositiveNormalPhase HironakaG1RecursiveMemberValueTransport HironakaG8LocalHistory
  HironakaActualNativeSectionPositiveLowerRecords HironakaActualNativeSectionNormalCrossings
  HironakaActualNativeSectionCoefficientRecords
open HomogenizedGlueingTower (N_geoTransformAlong strictAlong)
open HomogenizedIdealAlong (coeffMarkedAlong)

/-- On the fixed positive mask, the special locus at the anchor's level
is exactly the part of the selected carrier on which its coefficient
ideal vanishes identically in a neighbourhood. -/
theorem selected_member_nonzero_failure_locus {n : ℕ} {X : CMfd.{0} n}
    (hn : 0 < n) (A : MarkedIdeal n X) (hA : A.IsWellFormed) (hd : 1 ≤ A.d)
    {E : List (Set X)} (hE : E.Sublist A.E) (q : X) {s : ℕ} (hq : boundaryCount E q = s)
    (hMask : ∀ x : X, ∀ D ∈ E, x ∈ D → q ∈ D) :
    let K := memberRestrict A (membersThrough A.E E q)
    {x | x ∈ K.N ∧ ¬ IsNonzeroAlongAt K.N K.ideal x} =
      memberInterLocus A.N E A.cosupp ∩ {x | boundaryCount E x = s} := by
  classical
  intro K
  have hK := isWellFormed_memberRestrict hn hA (membersThrough A.E E q)
  have hKN : K.N = A.N ∩ {x | ∀ D ∈ E, q ∈ D → x ∈ D} := by
    change A.N ∩ memberInter A.E (membersThrough A.E E q) = _
    rw [memberInter_membersThrough hE.subset q]
  have hKCos : K.cosupp = A.cosupp ∩ {x | ∀ D ∈ E, q ∈ D → x ∈ D} := by
    rw [show K.cosupp = A.cosupp ∩ memberInter A.E (membersThrough A.E E q) from
      cosupp_memberRestrict hA hd _, memberInter_membersThrough hE.subset q]
  ext x
  constructor
  · rintro ⟨hxN, hxZero⟩
    rw [hKN] at hxN
    have hSame (D : Set X) (hD : D ∈ E) : x ∈ D ↔ q ∈ D :=
      ⟨hMask x D hD, hxN.2 D hD⟩
    refine ⟨?_, (boundaryCount_eq_of_forall_iff hSame).trans hq⟩
    by_contra hx
    have hNZ := isNonzeroAlongAt_coeffMarkedAlong_of_notMem_memberInterLocus
      A hA.isClosedSubmanifold_N hA.isCoherent hd E hxN.1 hx
    have hEq : A.N ∩ {z | ∀ D ∈ E, x ∈ D → z ∈ D} = K.N := by
      rw [hKN]
      exact congrArg (A.N ∩ ·) (Set.ext fun z => by
        exact ⟨fun hz D hD hqD => hz D hD ((hSame D hD).mpr hqD),
          fun hz D hD hxD => hz D hD ((hSame D hD).mp hxD)⟩)
    change IsNonzeroAlongAt (A.N ∩ {z | ∀ D ∈ E, x ∈ D → z ∈ D})
      (coeffMarkedAlong A).ideal x at hNZ
    rw [hEq] at hNZ
    exact hxZero hNZ
  · rintro ⟨hxLocus, hxCount⟩
    have hxCos := (mem_memberInterLocus_iff.mp hxLocus).1
    have hxNear := (mem_memberInterLocus_iff.mp hxLocus).2
    have hSame := forall_iff_of_forall_imp_of_boundaryCount_le (hMask x) (hq.trans hxCount.symm).le
    refine ⟨?_, ?_⟩
    · rw [hKN]
      exact ⟨A.cosupp_subset_N hxCos, fun D hD hqD => (hSame D hD).mp hqD⟩
    · rintro ⟨g, hg, hFreq⟩
      have hMem := HomogenizedGlueing.eventually_mem hK.isCoherent hg
      have hVan : ∀ᶠ z in 𝓝 x, z ∈ K.N → g z = 0 := by
        filter_upwards [hMem, hxNear] with z hzMem hzNear hzN
        rw [hKN] at hzN
        have hzCos : z ∈ K.cosupp := by
          rw [hKCos]
          exact ⟨hzNear hzN.1 (fun D hD hxD => hzN.2 D hD ((hSame D hD).mpr hxD)), hzN.2⟩
        have hgHol := GermIdeal.IsCoherent.holomorphicAt_mem hK.isCoherent hzMem
        exact (GermIdealOrder.vanishesToOrderOn_one_iff hzCos.1 hgHol).mp
          ((hzCos.2 g hzMem).mono (one_le_memberRestrict_d A (membersThrough A.E E q)))
      obtain ⟨z, hz, hVanZ⟩ := (hFreq.and_eventually hVan).exists
      exact hz.2 (hVanZ hz.1)

/-- The member cut on the fixed positive mask has the lower invariant
domain precisely when the special level locus is empty. Any member of
that locus rules out the domain at every recursive bound. -/
theorem isInvDomain_selected_iff_special_locus_empty {n k : ℕ} {X : CMfd.{0} n}
    (hn : 0 < n) (A : MarkedIdeal n X) (hA : IsInvDomain k A)
    {E : List (Set X)} (hE : E.Sublist A.E) (q : X) {s : ℕ} (hq : boundaryCount E q = s) (hs : 0 < s)
    (hMask : ∀ x : X, ∀ D ∈ E, x ∈ D → q ∈ D) :
    let K := memberRestrict A (membersThrough A.E E q)
    let C := memberInterLocus A.N E A.cosupp ∩ {x | boundaryCount E x = s}
    (IsInvDomain (k - 1) K ↔ C = ∅) ∧
      (C.Nonempty → ∀ j, ¬ IsInvDomain j K) := by
  classical
  intro K C
  have hFailure : {x | x ∈ K.N ∧ ¬ IsNonzeroAlongAt K.N K.ideal x} = C :=
    selected_member_nonzero_failure_locus hn A hA.isWellFormed hA.one_le_d hE q hq hMask
  have hNecessary {j : ℕ} (h : IsInvDomain j K) : C = ∅ := by
    rw [← hFailure]
    exact eq_empty_iff_forall_notMem.mpr fun x ⟨hxN, hBad⟩ => hBad (h.isNonzeroAlongAt x hxN)
  refine ⟨⟨hNecessary, fun hEmpty => ?_⟩, fun hC _ h => hC.ne_empty (hNecessary h)⟩
  exact ⟨isWellFormed_memberRestrict hn hA.isWellFormed (membersThrough A.E E q),
    dimLE_memberRestrict hn hA.isWellFormed (membersThrough_nonempty hE.subset (hq ▸ hs)) hA.dimLE,
    one_le_memberRestrict_d A (membersThrough A.E E q), fun x hxN => by
      by_contra! hxVan
      have hxC : x ∈ C := hFailure ▸ ⟨hxN, hxVan⟩
      rw [hEmpty] at hxC
      exact notMem_empty x hxC⟩

/-- An open subwindow carries the lower invariant exactly when it misses
the special level locus of the original fixed cut. The anchor need not
belong to the subwindow. -/
theorem isInvDomain_selected_pullback_val_iff {n k : ℕ} {X : CMfd.{0} n}
    (hn : 0 < n) (A : MarkedIdeal n X) (hA : IsInvDomain k A)
    {E : List (Set X)} (hE : E.Sublist A.E) (q : X) {s : ℕ} (hq : boundaryCount E q = s) (hs : 0 < s)
    (hMask : ∀ x : X, ∀ D ∈ E, x ∈ D → q ∈ D) (U : Opens X) :
    let K := memberRestrict A (membersThrough A.E E q)
    let C := memberInterLocus A.N E A.cosupp ∩ {x | boundaryCount E x = s}
    IsInvDomain (k - 1) (MarkedIdeal.pullback (Subtype.val : U → X) K) ↔ Disjoint (U : Set X) C := by
  classical
  intro K C
  have hK := isWellFormed_memberRestrict hn hA.isWellFormed (membersThrough A.E E q)
  have hFailure : {x | x ∈ K.N ∧ ¬ IsNonzeroAlongAt K.N K.ideal x} = C :=
    selected_member_nonzero_failure_locus hn A hA.isWellFormed hA.one_le_d hE q hq hMask
  rw [Set.disjoint_left]
  constructor
  · intro hDomain x hxU hxC
    have hx : x ∈ {x | x ∈ K.N ∧ ¬ IsNonzeroAlongAt K.N K.ideal x} := hFailure.symm ▸ hxC
    exact hx.2
      ((HironakaStepOneZeroContactRemainderGlueing.isNonzeroAlongAt_pullback_val_iff
        hK.isCoherent U ⟨x, hxU⟩).mp (hDomain.isNonzeroAlongAt ⟨x, hxU⟩ hx.1))
  · intro hDisjoint
    exact isInvDomain_pullback_val_of_forall hK
      (dimLE_memberRestrict hn hA.isWellFormed (membersThrough_nonempty hE.subset (hq ▸ hs)) hA.dimLE)
      (one_le_memberRestrict_d A (membersThrough A.E E q)) U fun x hxN hxU => by
        by_contra! hVan
        exact hDisjoint hxU (hFailure ▸ ⟨hxN, hVan⟩)

/-- On a mask allowing only members through the anchor, the special
centre is relatively open in the selected carrier. After blowing up
that centre the selected record is in the lower invariant domain. -/
theorem isInvDomain_selected_geoTransform_of_special_step {n k s : ℕ} {X Y : CMfd.{0} n}
    (hn : 0 < n) (A : MarkedIdeal n X) (hA : IsInvDomain k A)
    {E : List (Set X)} (hE : E.Sublist A.E) (q : X) (hq : boundaryCount E q = s) (hs : 0 < s)
    (hMask : ∀ x : X, ∀ D ∈ E, x ∈ D → q ∈ D) (π : Y → X) :
    let C := memberInterLocus A.N E A.cosupp ∩ {x | boundaryCount E x = s}
    let K := memberRestrict A (membersThrough A.E E q)
    IsBlowupAlong n C π → K.IsAdmissibleCentre C →
      IsInvDomain (k - 1) (K.geoTransform C π) ∧
        (K.geoTransform C π).N ⊆ π ⁻¹' Cᶜ := by
  classical
  intro C K hπ hAdm
  have hK := isWellFormed_memberRestrict hn hA.isWellFormed (membersThrough A.E E q)
  have hKN : K.N = A.N ∩ {x | ∀ D ∈ E, q ∈ D → x ∈ D} := by
    change A.N ∩ memberInter A.E (membersThrough A.E E q) = _
    rw [memberInter_membersThrough hE.subset q]
  have hKDim : DimLE n K.N (k - 1) :=
    dimLE_memberRestrict hn hA.isWellFormed (membersThrough_nonempty hE.subset (hq ▸ hs)) hA.dimLE
  have hRelativeOpen (x : X) (hx : x ∈ C) : ∀ᶠ z in 𝓝 x, z ∈ K.N → z ∈ C := by
    have hClosed : ∀ D ∈ E, IsClosed D := fun D hD => hA.isWellFormed.isSNCDivisor.1 D (hE.subset hD)
    filter_upwards [eventually_mem_level_iff hClosed A.cosupp_subset_N hx] with z hz hzK
    rw [hKN] at hzK
    exact hz.mpr ⟨hzK.1, fun D hD hxD => hzK.2 D hD (hMask x D hD hxD)⟩
  have hAvoid : (K.geoTransform C π).N ⊆ π ⁻¹' Cᶜ := by
    intro y hy hyC
    have hNear := hπ.contMDiff.continuous.continuousAt.eventually (hRelativeOpen (π y) hyC)
    have hFreq : ∃ᶠ z in 𝓝 y, z ∈ π ⁻¹' (K.N \ C) := mem_closure_iff_frequently.mp hy
    obtain ⟨z, hz, hNearZ⟩ := (hFreq.and_eventually hNear).exists
    exact hz.2 (hNearZ hz.1)
  refine ⟨⟨GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hK hAdm hπ,
    InvDomainTowerAlong.dimLE_geoStrictTransform hπ hK.isClosedSubmanifold_N.1 hAdm.subset_N hKDim,
    one_le_memberRestrict_d A (membersThrough A.E E q), ?_⟩, hAvoid⟩
  intro y hy
  have hy' : π y ∈ K.N := geoStrictTransform_subset_preimage hπ.contMDiff.continuous
    hK.isClosedSubmanifold_N.1 hy
  have hyOff : π y ∉ C := hAvoid hy
  have hFailure : {x | x ∈ K.N ∧ ¬ IsNonzeroAlongAt K.N K.ideal x} = C :=
    selected_member_nonzero_failure_locus hn A hA.isWellFormed hA.one_le_d hE q hq hMask
  have hNZ : IsNonzeroAlongAt K.N K.ideal (π y) := by
    by_contra! hVan
    exact hyOff (hFailure ▸ ⟨hy', hVan⟩)
  exact InvDomainTowerAlong.isNonzeroAlongAt_geoTransform_of_notMem hπ K hK.isCoherent hyOff hNZ

set_option maxHeartbeats 1200000 in
set_option backward.isDefEq.respectTransparency false in
/-- On the padded positive mask, a section-special anchor lies in the
admissible centre of the native section bar. One actual blowup clears
the entire special locus of the anchor level. -/
theorem positive_normal_native_special_step {n k s : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n + 1)} (H : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hH : IsGeoTestTower (properNormalMarked Q) H) (p : Y)
    (hLevel : level (properNormalMarked Q) H p = s + 1)
    (hNS : ¬ IsSpecial (properNormalMarked Q) H p)
    (hSpecial : IsSpecial (sectionMarked Q) H p) :
    let O := maskA (properNormalMarked Q) H p
    let W := openSection (strictAlong H (zeroPlane U)) O
    let B := geoTransformAlong (barMarked (sectionMarked Q)) H
    let M := MarkedIdeal.pullback (Subtype.val : O → Y) B
    ∃ (hWc : IsClosed W) (hW : ∀ z ∈ W, RegularAtDim (n := n + 1) W z n)
      (q : nativeManifold (Nat.le_succ n) W hW),
      q.val.val = p ∧
      let A := nativePullback (Nat.le_succ n) W hW M
      let E := ((origMembers (sectionMarked Q) H).map ((Subtype.val : O → Y) ⁻¹' ·)).map
        ((Subtype.val : W → O) ⁻¹' ·)
      let C := memberInterLocus A.N E A.cosupp ∩ {z | boundaryCount E z = s + 1}
      let D := (Subtype.val : W → O) '' C
      let L := lowerMarkedM (X := CMfd.of (n := n + 1) (productOpen U))
        (properNormalMarked Q) (s + 1) H p
      let J := positiveMemberOn (sectionMarked Q) H p O
      let K := memberRestrict A (membersThrough A.E E q)
      q ∈ C ∧ A.IsAdmissibleCentre C ∧
        M.IsAdmissibleCentre D ∧
        L.IsAdmissibleCentre D ∧
        nativePullback (Nat.le_succ n) W hW J = K ∧ K.IsAdmissibleCentre C ∧
        ∃ (Z : CMfd.{0} (n + 1)) (π : Z → O) (hπ : IsBlowupAlong (n + 1) D π),
          let V := geoStrictTransform π D W
          let hV := strictRegular hWc hW C π hπ
          let ρ := nativeProjection (Nat.le_succ n) hWc hW C π hπ
          let Y' := nativeManifold (Nat.le_succ n) V hV
          let K' : MarkedIdeal n Y' := K.geoTransform C ρ
          IsBlowupAlong n C ρ ∧ IsProperMap π ∧ IsProperMap ρ ∧
            A.geoTransform C ρ = nativePullback (Nat.le_succ n) V hV (M.geoTransform D π) ∧
            LocWPEquiv (L.geoTransform D π) (J.geoTransform D π) ∧
            K' = nativePullback (Nat.le_succ n) V hV (J.geoTransform D π) ∧
            IsInvDomain (Nat.pred k) K' ∧
            K'.N ⊆ ρ ⁻¹' Cᶜ ∧
            (Subtype.val : V → Z) '' K'.cosupp = (L.geoTransform D π).cosupp ∧
            (L.geoTransform D π).cosupp ⊆ π ⁻¹' Dᶜ ∧
            memberInterLocus (A.geoTransform C ρ).N
                (E.map (geoStrictTransform ρ C)) (A.geoTransform C ρ).cosupp ∩
              {z | boundaryCount (E.map (geoStrictTransform ρ C)) z = s + 1} = ∅ := by
  classical
  let X := CMfd.of (n := n + 1) (productOpen U)
  let P := properNormalMarked Q
  let Sec := sectionMarked Q
  let O := maskA P H p
  let V := strictAlong H (zeroPlane U)
  let W := openSection V O
  let B := geoTransformAlong (barMarked Sec) H
  let M := MarkedIdeal.pullback (Subtype.val : O → Y) B
  let E₀ := origMembers Sec H
  let E₁ := E₀.map ((Subtype.val : O → Y) ⁻¹' ·)
  have hP := properNormalMarked_isInvDomain Q hQ
  have hSec : IsInvDomain k Sec := section_projected_domain k Q.N Q.E Q.ideal Q.d hQ
  have hBarPTest := ((bar_local_any_boundary (X := X) P hP).wEquiv.2 H).1.mp hH
  have hSecTest := ((properNormalMarked_locWPEquiv_section Q hQ).wEquiv.2 H).1.mp hH
  have hBarSecTest := ((bar_local_any_boundary (X := X) Sec hSec).wEquiv.2 H).1.mp hSecTest
  have hB : IsInvDomain k B := InvDomainTowerAlong.isInvDomain_geoTransformAlong
    (HironakaCoherentTransformExtension.isInvDomain_barMarked (X := X) Sec hSec) H hBarSecTest
  have hM : IsInvDomain k M := InvDomainTowerAlong.isInvDomain_pullback_val O hB
  have hEqual : P.E = Sec.E := rfl
  have hOriginal := HironakaG8MemberLoci.origMembers_eq_of_E_eq hEqual H
  have hLevelSec := (HironakaG8MemberLoci.level_eq_of_E_eq hEqual H p).symm.trans hLevel
  have hPositive : 1 ≤ level P H p := hLevel ▸ Nat.succ_le_succ (Nat.zero_le s)
  have hpO : p ∈ O :=
    mem_maskA (X := X) P hP.isWellFormed hP.one_le_d (Nat.succ_pos n) H hBarPTest hPositive hNS
  have hpMember : p ∈ memberInterLocus B.N E₀ B.cosupp := by
    rcases hSpecial with ⟨hZero, _⟩ | ⟨_, hp⟩
    · exact (Nat.succ_ne_zero s (hLevelSec.symm.trans hZero)).elim
    · exact hp
  have hBHol : ∀ x g, B.ideal.mem x g → HolomorphicAt (n + 1) g x :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hB.isWellFormed.isCoherent hg
  have hMCos : M.cosupp = (Subtype.val : O → Y) ⁻¹' B.cosupp :=
    cosupp_pullback_val B hBHol O
  let pO : O := ⟨p, hpO⟩
  have hpRestricted : pO ∈ memberInterLocus M.N E₁ M.cosupp := by
    rw [hMCos]
    exact (mem_memberInterLocus_preimage_iff Subtype.val
      (O.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq pO) B.N E₀ B.cosupp).2 hpMember
  have hMN : M.N ⊆ W := by
    intro x hx
    have hxB : (x : Y) ∈ (geoTransformAlong (barMarked Sec) H).N := hx
    rw [N_geoTransformAlong] at hxB
    exact MemberInterTowerAlong.strictAlong_mono H
      (show (barMarked Sec).N ⊆ zeroPlane U from fun _ hz => ⟨mem_univ _, hz.2⟩) hxB
  obtain ⟨F, hFc, hF, _, hLift, _, _, _, hFTr, _, _⟩ :=
    exists_upper_native_test_history Q hQ H hH
  have hFEq : F = V := hLift.carrier
  have hBoundary : B.E = (geoTransformAlong (sectionBarCoefficient Q) H).E :=
    MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq
      (𝔪 := barMarked Sec) (𝔫 := sectionBarCoefficient Q) rfl H
  have hVTr : IsTransverse (n + 1) V B.E := by
    rw [← hFEq, hBoundary]
    exact hFTr
  have hWTr : IsTransverse (n + 1) W M.E :=
    isTransverse_preimage (pullsBackCoordinates_val O) hVTr
  have hWc : IsClosed W := (hFEq ▸ hFc).preimage continuous_subtype_val
  have hV : ∀ z ∈ V, RegularAtDim (n := n + 1) V z n := hFEq ▸ hF
  have hW : ∀ z ∈ W, RegularAtDim (n := n + 1) W z n := openSection_regular hV O
  let A := nativePullback (Nat.le_succ n) W hW M
  let i : W → O := Subtype.val
  let E := E₁.map (i ⁻¹' ·)
  have hESub : E.Sublist A.E := ((List.take_sublist _ B.E).map _).map _
  have hA : IsInvDomain k A := isInvDomain_nativePullback (X := CMfd.of (n := n + 1) O)
    (Nat.succ_pos n) (Nat.le_succ n) hW M hM hMN hWTr
  have hMHol : ∀ x g, M.ideal.mem x g → HolomorphicAt (n + 1) g x :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent hg
  have hACos : A.cosupp = i ⁻¹' M.cosupp :=
    cosupp_nativePullback (Nat.le_succ n) W hW M hMN hMHol
  have hImageN : i '' A.N = M.N := by
    change i '' (i ⁻¹' M.N) = M.N
    rw [image_preimage_eq_inter_range, Subtype.range_coe]
    exact inter_eq_left.mpr hMN
  have hImageCos : i '' A.cosupp = M.cosupp := by
    rw [hACos, image_preimage_eq_inter_range, Subtype.range_coe]
    exact inter_eq_left.mpr (M.cosupp_subset_N.trans hMN)
  let q : nativeManifold (Nat.le_succ n) W hW := ⟨pO, hMN (M.cosupp_subset_N hpRestricted.1)⟩
  have hLocus : i ⁻¹' memberInterLocus M.N E₁ M.cosupp = memberInterLocus A.N E A.cosupp := by
    have hL := memberInterLocus_native_preimage A.N A.cosupp E₁
    change i ⁻¹' memberInterLocus (i '' A.N) E₁ (i '' A.cosupp) = _ at hL
    rw [hImageN, hImageCos] at hL
    exact hL
  have hq : q ∈ memberInterLocus A.N E A.cosupp := by
    rw [← hLocus]
    exact hpRestricted
  have hCount (z : W) : boundaryCount E z = boundaryCount E₀ (z.val : Y) :=
    (CodimOnePartCanonical.boundaryCount_map_preimage i E₁ z).trans
      (CodimOnePartCanonical.boundaryCount_map_preimage (Subtype.val : O → Y) E₀ z.val)
  have hMax (z : O) : boundaryCount E₀ (z : Y) ≤ s + 1 := by
    rw [← hLevelSec]
    change (Finset.univ.filter fun j : Fin E₀.length => (z : Y) ∈ E₀.get j).card ≤
      (Finset.univ.filter fun j : Fin E₀.length => p ∈ E₀.get j).card
    exact Finset.card_le_card fun j hj => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact (interior_subset z.property).1 _ (hOriginal ▸ List.get_mem E₀ j) hj
  let C := memberInterLocus A.N E A.cosupp ∩ {z | boundaryCount E z = s + 1}
  have hqC : q ∈ C := ⟨hq, (hCount q).trans hLevelSec⟩
  have hn : 0 < n := by
    have hCountPos : 0 < boundaryCount E q := hqC.2 ▸ Nat.succ_pos s
    change 0 < (Finset.univ.filter fun j : Fin E.length => q ∈ E.get j).card at hCountPos
    obtain ⟨j, hj⟩ := Finset.card_pos.mp hCountPos
    have hSNC := NormalCrossingsComparison.isSNCDivisor_of_sublist hA.isWellFormed.isSNCDivisor hESub
    obtain ⟨S, _, hS, _⟩ := hSNC.2 q
    have hCard : (S j).card = 1 := hS j (Finset.mem_filter.mp hj).2
    obtain ⟨a, _⟩ := Finset.card_pos.mp (show 0 < (S j).card by rw [hCard]; decide)
    exact Nat.zero_lt_of_lt a.isLt
  have hC : A.IsAdmissibleCentre C := isAdmissibleCentre_memberInterLocus_level
    A hA.isWellFormed hA.one_le_d hn hESub (s + 1) (fun z _ => (hCount z).trans_le (hMax z.val))
  have hThin : interior C = ∅ :=
    eq_empty_of_subset_empty ((interior_mono hC.2.1).trans (interior_cosupp_eq_empty hA).subset)
  let J := memberInterLocus M.N E₁ M.cosupp ∩ {z | boundaryCount E₁ z = s + 1}
  have hPreJ : i ⁻¹' J = C := by
    change (i ⁻¹' memberInterLocus M.N E₁ M.cosupp) ∩
      {z | boundaryCount E₁ (i z) = s + 1} = C
    rw [hLocus]
    have hLevels : {z | boundaryCount E₁ (i z) = s + 1} = {z | boundaryCount E z = s + 1} := by
      ext z
      change boundaryCount E₁ (i z) = s + 1 ↔ boundaryCount E z = s + 1
      rw [CodimOnePartCanonical.boundaryCount_map_preimage i E₁ z]
    rw [hLevels]
    rfl
  have hJW : J ⊆ W := fun _ hz => hMN (M.cosupp_subset_N hz.1.1)
  have hImageC : i '' C = J := by
    rw [← hPreJ, image_preimage_eq_inter_range, Subtype.range_coe]
    exact inter_eq_left.mpr hJW
  have hE₁Sub : E₁.Sublist M.E := (List.take_sublist _ B.E).map _
  have hJ : M.IsAdmissibleCentre J := isAdmissibleCentre_memberInterLocus_level
    M hM.isWellFormed hM.one_le_d (Nat.succ_pos n) hE₁Sub (s + 1)
    (fun z _ => (CodimOnePartCanonical.boundaryCount_map_preimage
      (Subtype.val : O → Y) E₀ z).trans_le (hMax z))
  have hAmbient : M.IsAdmissibleCentre (i '' C) := hImageC ▸ hJ
  let BPad := geoTransformAlong (barMarked P) H
  let L := lowerMarkedM P (s + 1) H p
  have hBarsCos : BPad.cosupp = B.cosupp :=
    (((bar_local_any_boundary (X := X) P hP).wEquiv.2 H).2 hH).symm.trans
      ((((properNormalMarked_locWPEquiv_section Q hQ).trans
        (bar_local_any_boundary (X := X) Sec hSec)).wEquiv.2 H).2 hH)
  have hBarsE : BPad.E = B.E :=
    MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq
      (𝔪 := barMarked (X := X) P) (𝔫 := barMarked (X := X) Sec) hEqual H
  have hLSub : L.E.Sublist M.E := by
    have hSub : (memberRestrict BPad (membersThrough BPad.E (origMembers P H) p)).E.Sublist BPad.E := by
      rw [memberRestrict_membersThrough_E]
      exact List.filter_sublist
    have hPull : L.E.Sublist (BPad.E.map ((Subtype.val : O → Y) ⁻¹' ·)) :=
      hSub.map ((Subtype.val : O → Y) ⁻¹' ·)
    exact hPull.trans (hBarsE ▸ List.Sublist.refl _)
  have hLower : L.IsAdmissibleCentre (i '' C) := by
    refine ⟨hAmbient.1, ?_, NormalCrossingsComparison.hasNormalCrossings_of_forall_mem
      hAmbient.2.2 hLSub.subset⟩
    intro z hz
    have hzJ : z ∈ J := hImageC ▸ hz
    have hzBCos : (z : Y) ∈ B.cosupp := by
      have hzM := hzJ.1.1
      rw [hMCos] at hzM
      exact hzM
    have hzCount : boundaryCount E₀ (z : Y) = s + 1 :=
      (CodimOnePartCanonical.boundaryCount_map_preimage (Subtype.val : O → Y) E₀ z).symm.trans hzJ.2
    have hCoincide := forall_iff_of_forall_imp_of_boundaryCount_le
      (fun D hD hzD => (interior_subset z.property).1 D (hOriginal ▸ hD) hzD)
      ((hLevelSec.trans hzCount.symm).le)
    have hLowerCos := (positive_lower_cosupport Q hQ (s := s) H hH p).1
    rw [hLowerCos]
    exact ⟨hBarsCos ▸ hzBCos, fun D hD hpD => (hCoincide D (hOriginal ▸ hD)).mp hpD⟩
  have hAmbientThin : interior (i '' C) = ∅ := eq_empty_of_subset_empty
    ((interior_mono hAmbient.2.1).trans (interior_cosupp_eq_empty hM).subset)
  obtain ⟨Z, π, hπ⟩ := exists_blowup (Y := CMfd.of (n := n + 1) O) (i '' C) hAmbient.1 hAmbientThin
  let V' := geoStrictTransform π (i '' C) W
  let hV' := strictRegular hWc hW C π hπ
  let ρ := nativeProjection (Nat.le_succ n) hWc hW C π hπ
  have hρ : IsBlowupAlong n C ρ := nativeProjection_genuine (Nat.le_succ n) hWc hW C hC.1 hThin π hπ
  have hStep : Lift (Nat.le_succ n) W hWc hW M.E
      (.step .refl (i '' C) π hπ) V' isClosed_closure hV' (.step .refl C ρ hρ) :=
    Lift.step Lift.refl C hC.1 hThin π hπ hAmbient.2.2
  have hRecords : A.geoTransform C ρ =
      nativePullback (Nat.le_succ n) V' hV' (M.geoTransform (i '' C) π) :=
    hStep.whole_records (Nat.succ_pos n) hM.isWellFormed.isSNCDivisor hWTr M rfl hMN hMHol
  let S := positiveMemberOn (X := X) Sec H p O
  let K := memberRestrict A (membersThrough A.E E q)
  have hSCut : S = memberRestrict M (membersThrough M.E E₁ pO) :=
    pullback_val_memberRestrict_membersThrough hB.isWellFormed hB.one_le_d
      (fun _ hD => List.mem_of_mem_take hD) O pO
  have hCut : nativePullback (Nat.le_succ n) W hW S = K := by
    rw [hSCut]
    exact nativePullback_memberRestrict_membersThrough (Nat.le_succ n) hW (Nat.succ_pos n)
      M hMN hMHol hM.isWellFormed.isSNCDivisor hWTr E₁ hE₁Sub.subset q
  have hClass := positive_lower_section_class Q hQ H hH p
  have hSC : LocWPEquiv L S := hClass.1
  have hSN : S.N ⊆ W := hClass.2.1
  have hSSub : S.E.Sublist M.E := hSC.E_eq ▸ hLSub
  have hSWell : S.IsWellFormed := hSCut ▸ isWellFormed_memberRestrict (Nat.succ_pos n) hM.isWellFormed _
  have hSHol : ∀ x g, S.ideal.mem x g → HolomorphicAt (n + 1) g x :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hSWell.isCoherent hg
  let T : BlowupTower (CMfd.of (n := n + 1) O) Z := .step .refl (i '' C) π hπ
  have hLTest : IsGeoTestTower L T := ⟨trivial, hLower⟩
  have hSTest : IsGeoTestTower S T := ((hSC.wEquiv.2 T).1).mp hLTest
  have hSmall := Lift.forget_boundary hStep hSSub
  have hSTr := NormalCrossingsComparison.isTransverse_of_forall_mem hWTr hSSub.subset
  have hKTest := HironakaActualNativeSectionNormalCrossings.Lift.native_test hSmall
    (Nat.succ_pos n) hSWell.isSNCDivisor hSTr S rfl hSN hSHol hSTest
  rw [hCut] at hKTest
  have hKAdm : K.IsAdmissibleCentre C := hKTest.2
  have hCutRecords : K.geoTransform C ρ =
      nativePullback (Nat.le_succ n) V' hV' (S.geoTransform (i '' C) π) := by
    rw [← hCut]
    exact hSmall.whole_records (Nat.succ_pos n) hSWell.isSNCDivisor hSTr S rfl hSN hSHol
  have hMask : ∀ z : nativeManifold (Nat.le_succ n) W hW, ∀ D ∈ E, z ∈ D → q ∈ D := by
    intro z D hD hz
    obtain ⟨D₁, hD₁, h₁⟩ := List.mem_map.mp
      (show D ∈ E₁.map (i ⁻¹' ·) from hD)
    obtain ⟨D₀, hD₀, h₀⟩ := List.mem_map.mp
      (show D₁ ∈ E₀.map ((Subtype.val : O → Y) ⁻¹' ·) from hD₁)
    rw [← h₁, ← h₀] at hz ⊢
    exact (interior_subset z.val.property).1 D₀ (hOriginal ▸ hD₀) hz
  have hAfter : IsInvDomain (k - 1) (K.geoTransform C ρ) ∧
      (K.geoTransform C ρ).N ⊆ ρ ⁻¹' Cᶜ :=
    isInvDomain_selected_geoTransform_of_special_step (X := nativeManifold (Nat.le_succ n) W hW)
      (Y := nativeManifold (Nat.le_succ n) V' hV') (s := s + 1) hn A hA hESub q
      hqC.2 (Nat.succ_pos s) hMask ρ hρ hKAdm
  have hAmbientCos : (L.geoTransform (i '' C) π).cosupp = (S.geoTransform (i '' C) π).cosupp :=
    (hSC.wEquiv.2 T).2 hLTest
  have hNativeCos : (K.geoTransform C ρ).cosupp =
      (Subtype.val : V' → Z) ⁻¹' (S.geoTransform (i '' C) π).cosupp := by
    rw [← hCut]
    exact HironakaActualNativeSectionOrderHistory.Lift.current_cosupport hSmall
      (Nat.succ_pos n) hSWell.isSNCDivisor hSTr S rfl hSN hSHol
  have hSNewN : (S.geoTransform (i '' C) π).N ⊆ V' :=
    HironakaActualNativeSectionOrderHistory.Lift.current_carrier_subset hSmall S hSN
  have hImageNew : (Subtype.val : V' → Z) '' (K.geoTransform C ρ).cosupp =
      (L.geoTransform (i '' C) π).cosupp := by
    rw [hNativeCos, image_preimage_eq_inter_range, Subtype.range_coe, hAmbientCos]
    exact inter_eq_left.mpr ((S.geoTransform (i '' C) π).cosupp_subset_N.trans hSNewN)
  have hAvoidNew : (L.geoTransform (i '' C) π).cosupp ⊆ π ⁻¹' (i '' C)ᶜ := by
    rw [← hImageNew]
    rintro _ ⟨z, hz, rfl⟩ ⟨x, hx, hπx⟩
    have hSame : x = ρ z := Subtype.val_injective (hπx.trans (hStep.square z))
    exact hAfter.2 ((K.geoTransform C ρ).cosupp_subset_N hz) (hSame ▸ hx)
  have hClear := memberInterLocus_level_geoTransform_eq_empty A hA.isWellFormed hESub (s + 1) hρ hC
  exact ⟨hWc, hW, q, rfl, hqC, hC, hAmbient, hLower, hCut, hKAdm, Z, π, hπ, hρ,
    HironakaLocalPrincipalization.isProperMap_of_isBlowupAlong hπ,
    HironakaLocalPrincipalization.isProperMap_of_isBlowupAlong hρ, hRecords,
    hSC.geoTransformAlong T hLTest, hCutRecords,
    by simpa only [Nat.pred_eq_sub_one] using hAfter.1, hAfter.2, hImageNew, hAvoidNew, hClear⟩

end

end Hironaka.HironakaG1PositiveNormalSpecialStep
