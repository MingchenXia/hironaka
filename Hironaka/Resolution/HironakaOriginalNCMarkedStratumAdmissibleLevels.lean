import Hironaka.Resolution.HironakaOriginalNCMarkedStratumNativeFields

/-!
# All open upper levels of the prescribed-H native marked-stratum value

The actual entire count-level cosupport of the SAME marked sum supplies the
native lower admissible field. Every boundary slot and the original native
carrier are retained. Actual phase, test, ALLbranch, lower canonicality and
empty-birth facts are produced internally from the given raw NEW-Psi CAN.

Mathematics/API first: work/hironaka-g9-new-marked-stratum-driver-fields-20261023/
admissible-levels-20261024/. SOURCE ONLY: no Lean or kernel acceptance,
complete invariant installation, noncompact resolving driver, terminal NC,
Blueprint credit or original G9 closure is asserted.
-/

set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaOriginalNCMarkedStratumAdmissibleLevels

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit BlowupTowerSplitIso
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  MarkedIdealTowerTransport MarkedIdealEquivalence.MarkedIdeal
  MarkedIdealOperationsAlong.MarkedIdeal GermIdealOrder GermIdealPullbackCalculus
  HomogenizedGlueingTower MemberInterTowerAlong MaxLocusLocal BlowupTowerIsomorphism
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsMultiplicityStrata
  HironakaNormalCrossingsBoundaryTransform HironakaNormalCrossingsOpenRestrictionSeparation
  HironakaOriginalOldBranchOpenHistory HironakaOriginalNCCountHistory
  HironakaOriginalNCCausalHistoryValue HironakaOriginalNCCausalEmptyState
  HironakaOriginalNCMarkedStratum HironakaOriginalNCMarkedStratumHistoryValue
  HironakaOriginalNCMarkedStratumBranchHistory HironakaOriginalNCMarkedStratumBirthFrame
  HironakaOriginalNCMarkedStratumCanonicalHistory HironakaOriginalNCMarkedStratumNativeFields
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open ResolutionInvariantExt (IsEmptyTower)

variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem admissible_of_same_boundary_cosupport_subset
    (A B : MarkedIdeal n X) (hE : A.E = B.E) (hCos : A.cosupp ⊆ B.cosupp)
    {C : Set X} (hC : A.IsAdmissibleCentre C) : B.IsAdmissibleCentre C :=
  ⟨hC.1, hC.2.1.trans hCos, hE ▸ hC.2.2⟩

/-- A genuine entire count-level dictionary suffices for EVERY open upper
level. The final natural consumer produces all these actual dictionaries. -/
private theorem admissible_level_of_native_dictionary
    (A : MarkedIdeal n X) (hA : IsInvDomain n A) (Q : BlowupTower X Y)
    (hCan : IsCanonical A ((CanonicalCentres.canonicalInvariant n).inv A) Q)
    (B : MarkedIdeal n Y) (hBI : B.ideal.IsCoherent)
    (hE : (geoTransformAlong A Q).E = B.E)
    (f : Y → ℕ ×ₗ WithBot (CanonicalCentres.ValTy n)) (a : ℕ)
    (hPart : (geoTransformAlong A Q).cosupp =
      {y | y ∈ B.cosupp ∧ (ofLex (f y)).1 = a})
    (hValue : ∀ y ∈ B.cosupp, (ofLex (f y)).1 = a →
      f y = toLex (a, if y ∈ (geoTransformAlong A Q).cosupp then
        ((CanonicalCentres.canonicalInvariant n).inv A Q y :
          WithBot (CanonicalCentres.ValTy n)) else ⊥))
    (O : Opens Y) (μ : WithBot (CanonicalCentres.ValTy n))
    (hUpper : ∀ y ∈ B.cosupp, y ∈ O → f y ≤ toLex (a, μ)) :
    (MarkedIdeal.pullback (Subtype.val : O → Y) B).IsAdmissibleCentre
      ((Subtype.val : O → Y) ⁻¹' {y | y ∈ B.cosupp ∧ f y = toLex (a, μ)}) := by
  let R := CanonicalCentres.canonicalInvariant n
  let D := (geoTransformAlong A Q).cosupp
  have hATest := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical R.isInvValue hA Q hCan
  have hAD := InvDomainTowerAlong.isInvDomain_geoTransformAlong hA Q hATest
  have hPartD : D = {y | y ∈ B.cosupp ∧ (ofLex (f y)).1 = a} := hPart
  have hSub : D ⊆ B.cosupp := fun y hy => (hPartD ▸ hy).1
  have hTop : ∀ y ∈ D, (ofLex (f y)).1 = a := fun y hy => (hPartD ▸ hy).2
  by_cases hμ : μ = ⊥
  · subst μ
    have hEmpty : (Subtype.val : O → Y) ⁻¹'
        {y | y ∈ B.cosupp ∧ f y = toLex (a, (⊥ : WithBot (CanonicalCentres.ValTy n)))} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      have hpa : (ofLex (f p.val)).1 = a :=
        congrArg (fun v : ℕ ×ₗ WithBot (CanonicalCentres.ValTy n) => (ofLex v).1) hp.2
      have hpD : p.val ∈ D := hPartD.symm ▸ ⟨hp.1, hpa⟩
      have hEq := hp.2
      rw [hValue p.val hp.1 hpa, if_pos hpD] at hEq
      have hBad := congrArg (fun v : ℕ ×ₗ WithBot (CanonicalCentres.ValTy n) => (ofLex v).2) hEq
      exact WithBot.coe_ne_bot hBad
    rw [hEmpty]
    exact MarkedIdeal.isAdmissibleCentre_empty _
  · obtain ⟨levelValue, hLevelValue⟩ := WithBot.ne_bot_iff_exists.mp hμ
    subst μ
    have hRUpper : ∀ y ∈ D, y ∈ O → R.inv A Q y ≤ levelValue := by
      intro y hy hyO
      have hb := hUpper y (hSub hy) hyO
      rw [hValue y (hSub hy) (hTop y hy), if_pos hy] at hb
      simpa only [Prod.Lex.toLex_le_toLex, lt_self_iff_false, eq_self_iff_true,
        false_or, true_and, WithBot.coe_le_coe] using hb
    have hAdm := R.isInvValue.admissible A hA Q hCan O levelValue hRUpper
    have hEPull : (MarkedIdeal.pullback (Subtype.val : O → Y) (geoTransformAlong A Q)).E =
        (MarkedIdeal.pullback (Subtype.val : O → Y) B).E := by
      change (geoTransformAlong A Q).E.map _ = B.E.map _
      rw [hE]
    have hCosPull : (MarkedIdeal.pullback (Subtype.val : O → Y) (geoTransformAlong A Q)).cosupp ⊆
        (MarkedIdeal.pullback (Subtype.val : O → Y) B).cosupp := by
      rw [cosupp_pullback_val _
        (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
          hAD.isWellFormed.isCoherent hg),
        cosupp_pullback_val _
        (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hBI hg)]
      exact preimage_mono hSub
    have hAdmB := admissible_of_same_boundary_cosupport_subset
      (X := CMfd.of (n := n) O) _ _ hEPull hCosPull hAdm
    have hLevel : (Subtype.val : O → Y) ⁻¹'
        {y | y ∈ B.cosupp ∧ f y = toLex (a, (levelValue : WithBot (CanonicalCentres.ValTy n)))} =
        (Subtype.val : O → Y) ⁻¹' {y | y ∈ D ∧ R.inv A Q y = levelValue} := by
      ext p
      constructor
      · rintro ⟨hpB, hpf⟩
        have hpa : (ofLex (f p.val)).1 = a :=
          congrArg (fun v : ℕ ×ₗ WithBot (CanonicalCentres.ValTy n) => (ofLex v).1) hpf
        have hpD : p.val ∈ D := hPartD.symm ▸ ⟨hpB, hpa⟩
        rw [hValue p.val hpB hpa, if_pos hpD] at hpf
        have he := congrArg (fun v : ℕ ×ₗ WithBot (CanonicalCentres.ValTy n) => (ofLex v).2) hpf
        exact ⟨hpD, WithBot.coe_inj.mp he⟩
      · rintro ⟨hpD, hpR⟩
        refine ⟨hSub hpD, ?_⟩
        rw [hValue p.val (hSub hpD) (hTop p.val hpD), if_pos hpD, hpR]
    rw [hLevel]
    exact hAdmB

/-- Actual nested-open transport of the whole marked record. -/
private theorem admissible_intersection_of_subtype
    (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent) (U W : Opens X) (C : Set X) :
    let O := nestedOpens U W
    (MarkedIdeal.pullback (Subtype.val : O → U)
      (MarkedIdeal.pullback (Subtype.val : U → X) M)).IsAdmissibleCentre
      ((fun p : O => p.val.val) ⁻¹' C) →
    (MarkedIdeal.pullback (Subtype.val : (U ⊓ W : Opens X) → X) M).IsAdmissibleCentre
      ((Subtype.val : (U ⊓ W : Opens X) → X) ⁻¹' C) := by
  let O := nestedOpens U W
  let η := nestedDiffeo (n := n) U O (U ⊓ W)
    (fun p => ⟨fun hp => ⟨p.property, hp⟩, fun hp => hp.2⟩) inf_le_left
  let MUW := MarkedIdeal.pullback (Subtype.val : (U ⊓ W : Opens X) → X) M
  have hMUWI : MUW.ideal.IsCoherent := isCoherent_pullback contMDiff_subtype_val hI
  have hRecord : MarkedIdeal.pullback η MUW =
      MarkedIdeal.pullback (Subtype.val : O → U)
        (MarkedIdeal.pullback (Subtype.val : U → X) M) := by
    refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl ?_ ?_ rfl
    · change (M.E.map _).map _ = (M.E.map _).map _
      simp only [List.map_map]
      rfl
    · change GermIdeal.pullback (m := n) η
          (GermIdeal.pullback (m := n) (Subtype.val : (U ⊓ W : Opens X) → X) M.ideal) =
        GermIdeal.pullback (m := n) (Subtype.val : O → U)
          (GermIdeal.pullback (m := n) (Subtype.val : U → X) M.ideal)
      rw [← GermIdealTotalTransform.pullback_comp contMDiff_subtype_val η.contMDiff hI,
        ← GermIdealTotalTransform.pullback_comp contMDiff_subtype_val contMDiff_subtype_val hI]
      rfl
  dsimp only
  intro hLocal
  apply (MarkedIdealTowerTransport.isAdmissibleCentre_pullback_iff (Φ := η) hMUWI).mp
  rw [hRecord]
  exact hLocal

/-- Only the actual native cosupport INSIDE W must be covered by U. -/
private theorem admissible_of_cosupport_cover_inside_open
    (M : MarkedIdeal n X) (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent)
    (U W : Opens X) (C : Set X) (hC : C ⊆ M.cosupp)
    (hCover : ∀ x ∈ M.cosupp, x ∈ W → x ∈ U)
    (hLocal : (MarkedIdeal.pullback (Subtype.val : (U ⊓ W : Opens X) → X) M).IsAdmissibleCentre
      ((Subtype.val : (U ⊓ W : Opens X) → X) ⁻¹' C)) :
    (MarkedIdeal.pullback (Subtype.val : W → X) M).IsAdmissibleCentre ((Subtype.val : W → X) ⁻¹' C) := by
  have hClosed : IsClosed M.cosupp := GiraudAlong.isClosed_cosupport_along hI hN M.d
  apply isAdmissibleCentre_pullback_val_of_forall_exists_opens hI W
  intro x hxW
  by_cases hxU : x ∈ U
  · exact ⟨U ⊓ W, ⟨hxU, hxW⟩, inf_le_right, hLocal⟩
  · have hxM : x ∉ M.cosupp := fun hx => hxU (hCover x hx hxW)
    let V := W ⊓ (⟨M.cosuppᶜ, hClosed.isOpen_compl⟩ : Opens X)
    refine ⟨V, ⟨hxW, hxM⟩, inf_le_left, ?_⟩
    have hEmpty : (Subtype.val : V → X) ⁻¹' C = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact p.property.2 (hC hp)
    rw [hEmpty]
    exact MarkedIdeal.isAdmissibleCentre_empty _

private theorem active_top_level_admissible
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (T : BlowupTower X Y) (f : MarkedStratumPhaseFrame M H T)
    (W : Opens Y) (μ : WithBot (CanonicalCentres.ValTy n))
    (hUpper : ∀ y ∈ (geoTransformAlong M T).cosupp, y ∈ W →
      markedStratumHistoryValue M H T y ≤ toLex (f.q, μ)) :
    (MarkedIdeal.pullback (Subtype.val : W → Y) (geoTransformAlong M T)).IsAdmissibleCentre
      ((Subtype.val : W → Y) ⁻¹' {y | y ∈ (geoTransformAlong M T).cosupp ∧
        markedStratumHistoryValue M H T y = toLex (f.q, μ)}) := by
  rcases f with ⟨B0, K, P, hEq, hK, hHistoryK, hEmptyK, q, hCover,
    hP, hHistoryP, _hHigh, _hBound, _hAttained, hCan⟩
  subst T
  let MK := geoTransformAlong M K
  let MC := geoTransformAlong M (K.append P)
  let V := oldCountLowOpen H K q
  let U := openPreimage P V
  let MV := MarkedIdeal.pullback (Subtype.val : V → B0) MK
  let BU := MarkedIdeal.pullback (Subtype.val : U → Y) MC
  let A := phaseAuxiliary M H K q
  let Q := restrict V P
  let O := nestedOpens U W
  let fU : U → ℕ ×ₗ WithBot (CanonicalCentres.ValTy n) :=
    fun z => markedStratumHistoryValue M H (K.append P) z.val
  let C := {y | y ∈ MC.cosupp ∧ markedStratumHistoryValue M H (K.append P) y = toLex (q, μ)}
  have hKD := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM K hK
  have hAll := (isGeoTestTower_append_iff M K P).mpr ⟨hK, hP⟩
  have hCD := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM (K.append P) hAll
  have hBUD : IsInvDomain n BU := InvDomainTowerAlong.isInvDomain_pullback_val U hCD
  have hAD := (phaseAuxiliary_domain M hM h K hK hHistoryK q).1
  have hATest := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical
    (CanonicalCentres.canonicalInvariant n).isInvValue hAD Q hCan
  have hCurrent : geoTransformAlong MV Q = BU := by
    have hv := geoTransformAlong_restrict V hKD.isWellFormed.isClosedSubmanifold_N
      hKD.isWellFormed.isCoherent P hP
    simpa only [MV, MK, Q, BU, MC, geoTransformAlong_append] using hv
  have hE : (geoTransformAlong A Q).E = BU.E := by
    have he := E_geoTransformAlong_eq (𝔪 := A) (𝔫 := MV) rfl Q
    rwa [hCurrent] at he
  have hCosB : BU.cosupp = (Subtype.val : U → Y) ⁻¹' MC.cosupp :=
    cosupp_pullback_val MC
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
        hCD.isWellFormed.isCoherent hg) U
  have hCos := phase_whole_cosupp M hM h K hK hHistoryK q P hP hHistoryP hATest
  have hPart : (geoTransformAlong A Q).cosupp =
      {z | z ∈ BU.cosupp ∧ (ofLex (fU z)).1 = q} := by
    rw [hCos, hCosB]
    rfl
  have hValue : ∀ z ∈ BU.cosupp, (ofLex (fU z)).1 = q →
      fU z = toLex (q, if z ∈ (geoTransformAlong A Q).cosupp then
        ((CanonicalCentres.canonicalInvariant n).inv A Q z :
          WithBot (CanonicalCentres.ValTy n)) else ⊥) := by
    intro z hz hzq
    have hzC : z.val ∈ MC.cosupp := by rw [hCosB] at hz; exact hz
    exact (phase_value_at_top M hM h K hK hHistoryK hEmptyK q hCover
      P hP hHistoryP hCan z hzC hzq).2
  have hUpperU : ∀ z ∈ BU.cosupp, z ∈ O → fU z ≤ toLex (q, μ) := by
    intro z hz hzO
    have hzC : z.val ∈ MC.cosupp := by rw [hCosB] at hz; exact hz
    exact hUpper z.val hzC hzO
  have hLocal := admissible_level_of_native_dictionary A hAD Q hCan BU
    hBUD.isWellFormed.isCoherent hE fU q hPart hValue O μ hUpperU
  have hLevel : (Subtype.val : O → U) ⁻¹'
      {z | z ∈ BU.cosupp ∧ fU z = toLex (q, μ)} = (fun z : O => z.val.val) ⁻¹' C := by
    ext z
    change (z.val ∈ BU.cosupp ∧ fU z.val = toLex (q, μ)) ↔ _
    rw [hCosB]
    rfl
  rw [hLevel] at hLocal
  have hIntersection := admissible_intersection_of_subtype MC hCD.isWellFormed.isCoherent U W C hLocal
  apply admissible_of_cosupport_cover_inside_open MC hCD.isWellFormed.isClosedSubmanifold_N
    hCD.isWellFormed.isCoherent U W C (fun _ hy => hy.1) _ hIntersection
  intro y hy _hyW
  have hy' : y ∈ (geoTransformAlong MK P).cosupp := by
    simpa only [MC, MK, geoTransformAlong_append] using hy
  exact hCover (TransformOffCentre.cosupp_geoTransformAlong_subset MK
    hKD.isWellFormed.isClosedSubmanifold_N hKD.isWellFormed.isCoherent P hP hy')

/- Fixed reuse of the same authorized geometric mother as the frozen
StepDrop and NativeFields slices; no new private proof is exported. -/
macro "markedAdmissibleEmptyPhaseProof%" : term =>
  pure <| Lean.mkIdent <| Lean.mkPrivateNameCore
    `Hironaka.Resolution.HironakaOriginalNCMarkedStratumCanonicalHistory
    `Hironaka.HironakaOriginalNCMarkedStratumCanonicalHistory.empty_birth_state_after_phase

private theorem lower_birth_tails_of_actual_frame
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (T : BlowupTower X Y) (f : MarkedStratumPhaseFrame M H T) :
    ∀ y ∈ (geoTransformAlong M T).cosupp, oldCount H T y < f.q →
      IsEmptyTower (causalBirthTail H T y) := by
  rcases f with ⟨B, K, P, hEq, hK, hHistoryK, hEmptyK, q, _hCover,
    hP, hHistoryP, hHigh, _hBound, _hAttained, _hCan⟩
  subst T
  exact (markedAdmissibleEmptyPhaseProof%) M hM h K hK hHistoryK hEmptyK q P hP hHistoryP hHigh

private theorem lower_count_level_admissible
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (hHistory : IsOriginalBranchTestTower M H T) (f : MarkedStratumPhaseFrame M H T)
    (W : Opens Y) (a : ℕ) (μ : WithBot (CanonicalCentres.ValTy n)) (ha : a < f.q)
    (hUpper : ∀ y ∈ (geoTransformAlong M T).cosupp, y ∈ W →
      markedStratumHistoryValue M H T y ≤ toLex (a, μ)) :
    (MarkedIdeal.pullback (Subtype.val : W → Y) (geoTransformAlong M T)).IsAdmissibleCentre
      ((Subtype.val : W → Y) ⁻¹' {y | y ∈ (geoTransformAlong M T).cosupp ∧
        markedStratumHistoryValue M H T y = toLex (a, μ)}) := by
  let MC := geoTransformAlong M T
  let U := oldCountLowOpen H T a
  let BU := MarkedIdeal.pullback (Subtype.val : U → Y) MC
  let A := phaseAuxiliary M H T a
  let Q : BlowupTower (CMfd.of (n := n) U) (CMfd.of (n := n) U) := .refl
  let O := nestedOpens U W
  let fU : U → ℕ ×ₗ WithBot (CanonicalCentres.ValTy n) :=
    fun z => markedStratumHistoryValue M H T z.val
  let C := {y | y ∈ MC.cosupp ∧ markedStratumHistoryValue M H T y = toLex (a, μ)}
  have hCD := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hT
  have hBUD : IsInvDomain n BU := InvDomainTowerAlong.isInvDomain_pullback_val U hCD
  obtain ⟨hAD, hZA⟩ := phaseAuxiliary_domain M hM h T hT hHistory a
  have hCosB : BU.cosupp = (Subtype.val : U → Y) ⁻¹' MC.cosupp :=
    cosupp_pullback_val MC
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
        hCD.isWellFormed.isCoherent hg) U
  have hCosA : A.cosupp = BU.cosupp ∩ {z : U | a ≤ oldCount H T z.val} :=
    markedStratum_cosupp (X := CMfd.of (n := n) U)
      BU hBUD.isWellFormed hBUD.one_le_d hZA
  have hPart : (geoTransformAlong A Q).cosupp =
      {z | z ∈ BU.cosupp ∧ (ofLex (fU z)).1 = a} := by
    change A.cosupp = _
    rw [hCosA]
    ext z
    change (z ∈ BU.cosupp ∧ a ≤ oldCount H T z.val) ↔
      z ∈ BU.cosupp ∧ oldCount H T z.val = a
    exact ⟨fun hz => ⟨hz.1, le_antisymm z.property hz.2⟩,
      fun hz => ⟨hz.1, hz.2.ge⟩⟩
  have hValue : ∀ z ∈ BU.cosupp, (ofLex (fU z)).1 = a →
      fU z = toLex (a, if z ∈ (geoTransformAlong A Q).cosupp then
        ((CanonicalCentres.canonicalInvariant n).inv A Q z :
          WithBot (CanonicalCentres.ValTy n)) else ⊥) := by
    intro z hz hza
    have hzC : z.val ∈ MC.cosupp := by rw [hCosB] at hz; exact hz
    have hLow : oldCount H T z.val < f.q := hza.trans_lt ha
    have he := lower_birth_tails_of_actual_frame M hM h T f z.val hzC hLow
    exact (markedStratum_empty_birth_value_on_current_low_open M hM h T hT hHistory a z hzC hza he).2
  have hUpperU : ∀ z ∈ BU.cosupp, z ∈ O → fU z ≤ toLex (a, μ) := by
    intro z hz hzO
    have hzC : z.val ∈ MC.cosupp := by rw [hCosB] at hz; exact hz
    exact hUpper z.val hzC hzO
  have hLocal := admissible_level_of_native_dictionary A hAD Q trivial BU
    hBUD.isWellFormed.isCoherent rfl fU a hPart hValue O μ hUpperU
  have hLevel : (Subtype.val : O → U) ⁻¹'
      {z | z ∈ BU.cosupp ∧ fU z = toLex (a, μ)} = (fun z : O => z.val.val) ⁻¹' C := by
    ext z
    change (z.val ∈ BU.cosupp ∧ fU z.val = toLex (a, μ)) ↔ _
    rw [hCosB]
    rfl
  rw [hLevel] at hLocal
  have hIntersection := admissible_intersection_of_subtype MC hCD.isWellFormed.isCoherent U W C hLocal
  apply admissible_of_cosupport_cover_inside_open MC hCD.isWellFormed.isClosedSubmanifold_N
    hCD.isWellFormed.isCoherent U W C (fun _ hy => hy.1) _ hIntersection
  intro y hy hyW
  have hb := hUpper y hy hyW
  rcases Prod.Lex.toLex_le_toLex.mp hb with hlt | ⟨heq, _⟩
  · exact hlt.le
  · exact heq.le

/-- The genuine all-open admissible field of the SAME NEW prescribed-H
native value. Every auxiliary dictionary is produced internally from the
given raw canonical history and the defining upper-level bound. -/
theorem markedStratum_history_value_levels_admissible
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (T : BlowupTower X Y) (hCan : IsCanonical M (markedStratumHistoryValue M H) T)
    (W : Opens Y) (l : ℕ ×ₗ WithBot (CanonicalCentres.ValTy n))
    (hUpper : ∀ y ∈ (geoTransformAlong M T).cosupp, y ∈ W →
      markedStratumHistoryValue M H T y ≤ l) :
    (MarkedIdeal.pullback (Subtype.val : W → Y) (geoTransformAlong M T)).IsAdmissibleCentre
      ((Subtype.val : W → Y) ⁻¹' {y | y ∈ (geoTransformAlong M T).cosupp ∧
        markedStratumHistoryValue M H T y = l}) := by
  let a := (ofLex l).1
  let μ := (ofLex l).2
  have hl : toLex (a, μ) = l := toLex_ofLex l
  rw [← hl] at hUpper ⊢
  by_cases hNe : {y | y ∈ (geoTransformAlong M T).cosupp ∧ y ∈ W ∧
      markedStratumHistoryValue M H T y = toLex (a, μ)}.Nonempty
  · obtain ⟨x, hx, _hxW, hxValue⟩ := hNe
    obtain ⟨hT, hHistory, _hBirth, hFrames⟩ :=
      markedStratum_canonical_history_joint_interpretation M hM h T hCan
    obtain ⟨f⟩ := hFrames ⟨x, hx⟩
    have hxa : oldCount H T x = a :=
      congrArg (fun v : ℕ ×ₗ WithBot (CanonicalCentres.ValTy n) => (ofLex v).1) hxValue
    by_cases hTop : a = f.q
    · have hUpperTop : ∀ y ∈ (geoTransformAlong M T).cosupp, y ∈ W →
          markedStratumHistoryValue M H T y ≤ toLex (f.q, μ) := by
        simpa only [hTop] using hUpper
      have hAdm := active_top_level_admissible M hM h T f W μ hUpperTop
      simpa only [hTop] using hAdm
    · have hLow : a < f.q := by
        have hb := f.currentBound x hx
        omega
      exact lower_count_level_admissible M hM h T hT hHistory f W a μ hLow hUpper
  · have hEmpty : (Subtype.val : W → Y) ⁻¹'
        {y | y ∈ (geoTransformAlong M T).cosupp ∧
          markedStratumHistoryValue M H T y = toLex (a, μ)} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact hNe ⟨p.val, hp.1, p.property, hp.2⟩
    rw [hEmpty]
    exact MarkedIdeal.isAdmissibleCentre_empty _

end
end Hironaka.HironakaOriginalNCMarkedStratumAdmissibleLevels
