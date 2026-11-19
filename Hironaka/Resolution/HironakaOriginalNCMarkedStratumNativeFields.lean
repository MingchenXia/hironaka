import Hironaka.Resolution.HironakaOriginalNCMarkedStratumCanonicalHistory
import Hironaka.Invariant.StepOneUSC

/-!
# Native USC and whole representative algebra for the prescribed-H NEW value

The value is the actual marked-stratum history value on its original native
carrier and entire ordered boundary.  The low-count comparison transports
each point's own empty birth window to one common current auxiliary; equal
counts are never assumed to imply equal birth years. The representative
field uses whole restricted equivalence, including at the initial birth.
All tests, histories,
phase frames and lower empty tails used by the natural USC endpoint come
from its given raw NEW-Psi canonical history.

Mathematics/API first: work/hironaka-g9-new-marked-stratum-driver-fields-20261023/
usc-naturality-20261024/. This is SOURCE ONLY, not Lean checked. It does not
install the remaining numerical/naturality fields, prove a noncompact
resolving driver, change Blueprint credit, or close original G9.
-/

set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u v

namespace Hironaka.HironakaOriginalNCMarkedStratumNativeFields

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit BlowupTowerSplitIso
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  MarkedIdealTowerTransport MarkedIdealOperationsAlong MarkedIdealOperationsAlong.MarkedIdeal
  MarkedIdealEquivalence.MarkedIdeal
  GermIdealOrder GermIdealPullbackCalculus IdealWeightPowers
  RestrictedIdealExtension RestrictedIdealWeight RestrictLeCalculus
  HomogenizedGlueingTower MemberInterTowerAlong MaxLocusLocal BlowupTowerIsomorphism
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsMultiplicityStrata
  HironakaNormalCrossingsBoundaryTransform HironakaNormalCrossingsOpenRestrictionSeparation
  HironakaOriginalOldBranchOpenHistory HironakaOriginalNCCountHistory
  HironakaOriginalNCCausalHistoryValue HironakaOriginalNCCausalEmptyState
  HironakaOriginalNCOldStratumStrictEquality HironakaOriginalNCMarkedStratum
  HironakaOriginalNCMarkedStratumHistoryValue HironakaOriginalNCMarkedStratumBranchHistory
  HironakaOriginalNCMarkedStratumBirthFrame HironakaOriginalNCMarkedStratumCanonicalHistory
  ResolutionInvariantOrder
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open ResolutionInvariantExt (IsEmptyTower)

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Whole restricted equivalence passes to the NEW sum on the SAME carrier,
ordered boundary and mark. This is not ambient ideal equality. -/
theorem markedStratum_restrictEquiv (M M' : MarkedIdeal n X)
    (hI : M.ideal.IsCoherent) (hI' : M'.ideal.IsCoherent)
    (hMM' : RestrictEquiv M M') {Z : Set X} (hZ : IsClosedSubmanifold n Z) :
    RestrictEquiv (markedStratum M Z) (markedStratum M' Z) := by
  have hV := VanishingIdealCoherent.isCoherent_vanishingIdeal hZ
  refine ⟨hMM'.N_eq, hMM'.E_eq, congrArg (fun d => d * 1) hMM'.d_eq, ?_, ?_⟩
  · change RestrictLe M.N
      (sumIdeal (idealPow M.ideal 1) (idealPow (vanishingIdeal (n := n) Z) M.d))
      (sumIdeal (idealPow M'.ideal 1) (idealPow (vanishingIdeal (n := n) Z) M'.d))
    rw [hMM'.d_eq]
    exact restrictLe_sumIdeal
      (fun _ _ hg => holomorphicAt_of_mem_idealPow hg)
      (fun _ _ hg => holomorphicAt_of_mem_idealPow hg)
      (restrictLe_idealPow (fun _ _ hg =>
        RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI' hg) hMM'.le 1)
      (restrictLe_refl (isCoherent_idealPow hV M'.d))
  · change RestrictLe M.N
      (sumIdeal (idealPow M'.ideal 1) (idealPow (vanishingIdeal (n := n) Z) M'.d))
      (sumIdeal (idealPow M.ideal 1) (idealPow (vanishingIdeal (n := n) Z) M.d))
    rw [← hMM'.d_eq]
    exact restrictLe_sumIdeal
      (fun _ _ hg => holomorphicAt_of_mem_idealPow hg)
      (fun _ _ hg => holomorphicAt_of_mem_idealPow hg)
      (restrictLe_idealPow (fun _ _ hg =>
        RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hg) hMM'.ge 1)
      (restrictLe_refl (isCoherent_idealPow hV M.d))

private theorem native_restrictEquiv_pullback_val
    (M M' : MarkedIdeal n X) (hI : M.ideal.IsCoherent) (hI' : M'.ideal.IsCoherent)
    (hMM' : RestrictEquiv M M') (U : Opens X) :
    RestrictEquiv (MarkedIdeal.pullback (Subtype.val : U → X) M)
      (MarkedIdeal.pullback (Subtype.val : U → X) M') := by
  refine ⟨congrArg (fun N : Set X => (Subtype.val : U → X) ⁻¹' N) hMM'.N_eq,
    congrArg (fun E : List (Set X) => E.map ((Subtype.val : U → X) ⁻¹' ·)) hMM'.E_eq,
    hMM'.d_eq, ?_, ?_⟩
  · exact restrictLe_pullback contMDiff_subtype_val (fun _ hy => hy) hI' hMM'.le
  · exact restrictLe_pullback contMDiff_subtype_val (fun _ hy => hy) hI hMM'.ge

private theorem native_restrictEquiv_geoTransformAlong
    (M M' : MarkedIdeal n X) (hM : IsInvDomain n M) (hM' : IsInvDomain n M')
    (hMM' : RestrictEquiv M M') {B : CMfd.{u} n}
    (K : BlowupTower X B) (hK : IsGeoTestTower M K) :
    RestrictEquiv (geoTransformAlong M K) (geoTransformAlong M' K) := by
  cases K with
  | refl => exact hMM'
  | step K C π hπ =>
    have hEq := MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.geoTransformAlong_step_eq
      hMM' hM.isWellFormed.isClosedSubmanifold_N.1
      hM.isWellFormed.isCoherent hM'.isWellFormed.isCoherent K C π hπ
    have hCurrent := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM (.step K C π hπ) hK
    rw [← hEq]
    exact RestrictEquiv.refl hCurrent.isWellFormed.isCoherent

/-- The actual birth record of a native equivalent representative has its
real domain and whole equivalence, with the SAME H/T chronology. -/
private theorem native_birth_representative
    (M M' : MarkedIdeal n X) (hM : IsInvDomain n M) (hM' : IsInvDomain n M')
    (hMM' : RestrictEquiv M M')
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (hHistory : IsOriginalBranchTestTower M H T) (y : Y) :
    IsInvDomain n (markedStratumBirth M' H T y) ∧
      RestrictEquiv (markedStratumBirth M H T y) (markedStratumBirth M' H T y) := by
  let k := T.length - birthYear H T y
  let K := head T k
  let W := causalBirthOpen H T y
  let MW := causalBirthParent M H T y
  let M'W := causalBirthParent M' H T y
  have hK := ((isGeoTestTower_iff_head_tail M T k).mp hT).1
  have hKHistory := originalBranchHistory_head M T hHistory k
  have hWEquiv := MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.wEquiv
    hMM' hM.isWellFormed.isClosedSubmanifold_N.1
    hM.isWellFormed.isCoherent hM'.isWellFormed.isCoherent
  have hK' : IsGeoTestTower M' K := (hWEquiv.2 K).1.mp hK
  have hKD := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM K hK
  have hK'D := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM' K hK'
  have hMW : IsInvDomain n MW := InvDomainTowerAlong.isInvDomain_pullback_val W hKD
  have hM'W : IsInvDomain n M'W := InvDomainTowerAlong.isInvDomain_pullback_val W hK'D
  have hParents : RestrictEquiv MW M'W :=
    native_restrictEquiv_pullback_val (geoTransformAlong M K) (geoTransformAlong M' K)
      hKD.isWellFormed.isCoherent hK'D.isWellFormed.isCoherent
      (native_restrictEquiv_geoTransformAlong M M' hM hM' hMM' K hK) W
  have hZ : IsClosedSubmanifold n (causalBirthStratum H T y) :=
    (phaseAuxiliary_domain M hM h K hK hKHistory (oldCount H T y)).2
  exact ⟨markedStratum_isInvDomain (X := CMfd.of (n := n) W) M'W hM'W hZ,
    markedStratum_restrictEquiv (X := CMfd.of (n := n) W) MW M'W hMW.isWellFormed.isCoherent
      hM'W.isWellFormed.isCoherent hParents hZ⟩

/-- The genuine native representative field for prescribed H. The same
chronology is used, including birth year zero, where ambient ideals may
differ. Target canonicality and birth equivalence are produced or unnecessary. -/
theorem markedStratum_history_value_representative
    (M M' : MarkedIdeal n X) (hM : IsInvDomain n M) (hM' : IsInvDomain n M')
    (hMM' : RestrictEquiv M M')
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (T : BlowupTower X Y) (hCan : IsCanonical M (markedStratumHistoryValue M H) T)
    (y : Y) (hy : y ∈ (geoTransformAlong M T).cosupp) :
    markedStratumHistoryValue M H T y = markedStratumHistoryValue M' H T y := by
  let R := CanonicalCentres.canonicalInvariant n
  let A := markedStratumBirth M H T y
  let A' := markedStratumBirth M' H T y
  let S := causalBirthTail H T y
  let z := causalBirthPoint H T y
  obtain ⟨hT, hHistory, hBirth, _hFrames⟩ :=
    markedStratum_canonical_history_joint_interpretation M hM h T hCan
  obtain ⟨hA, hCanA, hz⟩ := hBirth y hy
  obtain ⟨hA', hAA'⟩ := native_birth_representative M M' hM hM' hMM' h T hT hHistory y
  have hCos := (MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.cosupp_admissible_geoTransformAlong
    hAA' hA.isWellFormed.isClosedSubmanifold_N.1
    hA.isWellFormed.isCoherent hA'.isWellFormed.isCoherent S).1
  have hz' : z ∈ (geoTransformAlong A' S).cosupp := hCos ▸ hz
  have hv := R.isInvValue.representative A A' hA hA' hAA' S hCanA z hz
  change toLex (oldCount H T y,
    if z ∈ (geoTransformAlong A S).cosupp then
      (R.inv A S z : WithBot (CanonicalCentres.ValTy n)) else ⊥) =
    toLex (oldCount H T y,
      if z ∈ (geoTransformAlong A' S).cosupp then
        (R.inv A' S z : WithBot (CanonicalCentres.ValTy n)) else ⊥)
  rw [if_pos hz, if_pos hz', hv]

/-- The generic actual nested-open comparison at refl. Only native invariant
fields are used; this is independent of any causal numerical value. -/
private theorem native_subopen_refl_value
    (V J : Opens X) (hJV : J ≤ V)
    (A : MarkedIdeal n (CMfd.of (n := n) V)) (hA : IsInvDomain n A) :
    let O := nestedOpens V J
    let χ := (nestedOpensDiffeo (n := n) hJV).symm
    let AO := MarkedIdeal.pullback (Subtype.val : O → V) A
    let B := MarkedIdeal.pullback χ AO
    ∀ p : J,
      (p ∈ B.cosupp ↔ (⟨p.val, hJV p.property⟩ : V) ∈ A.cosupp) ∧
      ((⟨p.val, hJV p.property⟩ : V) ∈ A.cosupp →
        (CanonicalCentres.canonicalInvariant n).inv B .refl p =
          (CanonicalCentres.canonicalInvariant n).inv A .refl ⟨p.val, hJV p.property⟩) := by
  let R := CanonicalCentres.canonicalInvariant n
  let O := nestedOpens V J
  let χ := (nestedOpensDiffeo (n := n) hJV).symm
  let AO := MarkedIdeal.pullback (Subtype.val : O → V) A
  let B := MarkedIdeal.pullback χ AO
  have hAO := InvDomainTowerAlong.isInvDomain_pullback_val O hA
  have hCosOpen := cosupp_pullback_val A
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
      hA.isWellFormed.isCoherent hg) O
  have hCos := MarkedIdealTowerTransport.cosupp_pullback_eq
    (Φ := χ) hAO.isWellFormed.isCoherent
  dsimp only
  intro p
  refine ⟨?_, ?_⟩
  · change p ∈ (MarkedIdeal.pullback χ AO).cosupp ↔ _
    rw [hCos, hCosOpen]
    rfl
  · intro hp
    have hpO : χ p ∈ AO.cosupp := by
      rw [hCosOpen]
      exact hp
    have hInvIso := R.isInvValue.towerIso χ AO hAO .refl .refl χ
      BlowupTowerIsomorphism.IsTowerIso.refl trivial p hpO
    have hInvOpen := R.isInvValue.restrictOpen A hA O .refl trivial (χ p) hp
    exact hInvIso.trans hInvOpen

/-- Every surviving equal-count point with its own actual empty birth tail
reads the SAME current native auxiliary on the exact intrinsic low open.
No comparison or constancy of the points' birth years is assumed. -/
theorem markedStratum_empty_birth_value_on_current_low_open
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (hHistory : IsOriginalBranchTestTower M H T) (a : ℕ)
    (p : oldCountLowOpen H T a) (hp : p.val ∈ (geoTransformAlong M T).cosupp)
    (hpa : oldCount H T p.val = a) (he : IsEmptyTower (causalBirthTail H T p.val)) :
    IsInvDomain n (phaseAuxiliary M H T a) ∧
      markedStratumHistoryValue M H T p.val = toLex (a,
        if p ∈ (phaseAuxiliary M H T a).cosupp then
          ((CanonicalCentres.canonicalInvariant n).inv
            (X := CMfd.of (n := n) (oldCountLowOpen H T a))
            (phaseAuxiliary M H T a) .refl p :
            WithBot (CanonicalCentres.ValTy n)) else ⊥) := by
  let R := CanonicalCentres.canonicalInvariant n
  let MC := geoTransformAlong M T
  let V := oldCountLowOpen H T a
  let A := phaseAuxiliary M H T a
  let W := causalBirthOpen H T p.val
  let D := tail T (T.length - birthYear H T p.val)
  let J := openPreimage D W
  let Aold := markedStratumBirth M H T p.val
  let Sold := causalBirthTail H T p.val
  let BJ := markedStratum (X := CMfd.of (n := n) J)
    (MarkedIdeal.pullback (Subtype.val : J → Y) MC) {z : J | a ≤ oldCount H T z.val}
  let z := causalBirthPoint H T p.val
  have hCurrent := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hT
  obtain ⟨hA, hZA⟩ := phaseAuxiliary_domain M hM h T hT hHistory a
  have hWindow := empty_birth_window M hM h T hT hHistory p.val he
  rw [hpa] at hWindow
  obtain ⟨hAold, hBJ, hRE, _hZJ, hBound⟩ := hWindow
  have hJV : J ≤ V := by
    intro t ht
    exact hBound ⟨t, ht⟩
  let O := nestedOpens V J
  let χ := (nestedOpensDiffeo (n := n) hJV).symm
  have hPull : MarkedIdeal.pullback χ
      (MarkedIdeal.pullback (Subtype.val : O → V) A) = BJ :=
    markedStratum_nested_pullback MC hCurrent.isWellFormed.isCoherent V J hJV
      {t | a ≤ oldCount H T t} hZA
  have hSub := native_subopen_refl_value V J hJV A hA z
  change (z ∈ (MarkedIdeal.pullback χ
      (MarkedIdeal.pullback (Subtype.val : O → V) A)).cosupp ↔ p ∈ A.cosupp) ∧
    (p ∈ A.cosupp → R.inv (X := CMfd.of (n := n) J) (MarkedIdeal.pullback χ
      (MarkedIdeal.pullback (Subtype.val : O → V) A)) .refl z =
        R.inv (X := CMfd.of (n := n) V) A .refl p) at hSub
  rw [hPull] at hSub
  have hz : z ∈ (geoTransformAlong Aold Sold).cosupp :=
    empty_birth_membership M hM h T hT hHistory p.val hp he
  have hzB : z ∈ BJ.cosupp := by
    rw [hRE.cosupp_eq]
    exact hz
  have hpA : p ∈ A.cosupp := hSub.1.mp hzB
  have hCanOld : IsCanonical Aold (R.inv Aold) Sold :=
    ResolutionInvariantExt.isCanonical_of_isEmptyTower Aold (R.inv Aold) Sold he
  have hTestOld := ResolutionInvariantExt.isGeoTestTower_of_isEmptyTower Aold Sold he
  have hOldCurrent := InvDomainTowerAlong.isInvDomain_geoTransformAlong hAold Sold hTestOld
  have hEmpty := R.isInvValue.emptyPrefix Aold hAold Sold .refl he hCanOld z hz
  change R.inv Aold Sold z = R.inv (geoTransformAlong Aold Sold) .refl z at hEmpty
  have hRep := R.isInvValue.representative BJ (geoTransformAlong Aold Sold)
    hBJ hOldCurrent hRE .refl trivial z hzB
  refine ⟨hA, ?_⟩
  change toLex (oldCount H T p.val,
    if z ∈ (geoTransformAlong Aold Sold).cosupp then
      (R.inv Aold Sold z : WithBot (CanonicalCentres.ValTy n)) else ⊥) = _
  rw [hpa, if_pos hz, if_pos hpA, hEmpty, ← hRep, hSub.2 hpA]

/- Fixed proof reuse of the one previously authorized geometric mother.
Its complete original type/proof/hash is in the API evidence. No arbitrary
proof name, environment search, new hypothesis or new credit is introduced. -/
macro "markedNativeEmptyPhaseProof%" : term =>
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
  exact (markedNativeEmptyPhaseProof%) M hM h K hK hHistoryK hEmptyK q P hP hHistoryP hHigh

private theorem masked_eventually_le {B : Type u} [TopologicalSpace B]
    {Λ : Type v} [LinearOrder Λ] (D : Set B) (hD : IsClosed D)
    (v : B → Λ) (hv : IsInvUSCOn v D) (x : B) :
    ∀ᶠ z in 𝓝 x,
      (if z ∈ D then (v z : WithBot Λ) else ⊥) ≤
        (if x ∈ D then (v x : WithBot Λ) else ⊥) := by
  by_cases hx : x ∈ D
  · filter_upwards [hv x hx] with z hz
    by_cases hzd : z ∈ D
    · simpa only [if_pos hx, if_pos hzd, WithBot.coe_le_coe] using hz hzd
    · simp only [if_pos hx, if_neg hzd, bot_le]
  · filter_upwards [hD.isOpen_compl.mem_nhds hx] with z hz
    simp only [if_neg hx, if_neg hz, le_refl]

private theorem lex_mask_eventually_le {B : Type u} [TopologicalSpace B]
    {Λ : Type v} [LinearOrder Λ] (S D : Set B) (hD : IsClosed D)
    (v : B → Λ) (hv : IsInvUSCOn v D)
    (f : B → ℕ ×ₗ WithBot Λ) (q : ℕ)
    (hBound : ∀ z ∈ S, (ofLex (f z)).1 ≤ q)
    (hValue : ∀ z ∈ S, (ofLex (f z)).1 = q →
      f z = toLex (q, if z ∈ D then (v z : WithBot Λ) else ⊥))
    (x : B) (hx : x ∈ S) (hxq : (ofLex (f x)).1 = q) :
    ∀ᶠ z in 𝓝 x, z ∈ S → f z ≤ f x := by
  filter_upwards [masked_eventually_le D hD v hv x] with z hz hzS
  by_cases hlt : (ofLex (f z)).1 < q
  · rw [hValue x hx hxq, ← toLex_ofLex (f z), Prod.Lex.toLex_le_toLex]
    exact Or.inl hlt
  · have heq : (ofLex (f z)).1 = q := by
      have hb := hBound z hzS
      omega
    rw [hValue z hzS heq, hValue x hx hxq, Prod.Lex.toLex_le_toLex]
    exact Or.inr ⟨rfl, hz⟩

private theorem native_cosupport_isClosed
    (A : MarkedIdeal n X) (hA : IsInvDomain n A) (Q : BlowupTower X Y)
    (hCan : IsCanonical A ((CanonicalCentres.canonicalInvariant n).inv A) Q) :
    IsClosed (geoTransformAlong A Q).cosupp := by
  have hTest := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical
    (CanonicalCentres.canonicalInvariant n).isInvValue hA Q hCan
  have hCurrent := InvDomainTowerAlong.isInvDomain_geoTransformAlong hA Q hTest
  exact GiraudAlong.isClosed_cosupport_along hCurrent.isWellFormed.isCoherent
    hCurrent.isWellFormed.isClosedSubmanifold_N _

private theorem active_top_eventually_le
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (T : BlowupTower X Y) (f : MarkedStratumPhaseFrame M H T)
    (x : Y) (hx : x ∈ (geoTransformAlong M T).cosupp) (hxq : oldCount H T x = f.q) :
    ∀ᶠ z in 𝓝 x, z ∈ (geoTransformAlong M T).cosupp →
      markedStratumHistoryValue M H T z ≤ markedStratumHistoryValue M H T x := by
  rcases f with ⟨B, K, P, hEq, hK, hHistoryK, hEmptyK, q, hCover,
    hP, hHistoryP, _hHigh, hBound, _hAttained, hCan⟩
  subst T
  let V := oldCountLowOpen H K q
  let U := openPreimage P V
  let A := phaseAuxiliary M H K q
  let Q := restrict V P
  let R := CanonicalCentres.canonicalInvariant n
  let C := (geoTransformAlong M (K.append P)).cosupp
  let S : Set U := (Subtype.val : U → Y) ⁻¹' C
  let fU : U → ℕ ×ₗ WithBot (CanonicalCentres.ValTy n) :=
    fun z => markedStratumHistoryValue M H (K.append P) z.val
  have hKD := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM K hK
  have hA := (phaseAuxiliary_domain M hM h K hK hHistoryK q).1
  have hIn : C ⊆ U := by
    intro y hy
    have hy' : y ∈ (geoTransformAlong (geoTransformAlong M K) P).cosupp := by
      simpa only [C, geoTransformAlong_append] using hy
    exact hCover (TransformOffCentre.cosupp_geoTransformAlong_subset (geoTransformAlong M K)
      hKD.isWellFormed.isClosedSubmanifold_N hKD.isWellFormed.isCoherent P hP hy')
  have hClosed := native_cosupport_isClosed A hA Q hCan
  have hUSC := R.isInvValue.usc A hA Q hCan
  have hBoundU : ∀ z ∈ S, (ofLex (fU z)).1 ≤ q := fun z hz => hBound z.val hz
  have hValue : ∀ z ∈ S, (ofLex (fU z)).1 = q →
      fU z = toLex (q, if z ∈ (geoTransformAlong A Q).cosupp then
        (R.inv A Q z : WithBot (CanonicalCentres.ValTy n)) else ⊥) := by
    intro z hz hzq
    exact (phase_value_at_top M hM h K hK hHistoryK hEmptyK q hCover
      P hP hHistoryP hCan z hz hzq).2
  have hxU : x ∈ U := hIn hx
  let p : U := ⟨x, hxU⟩
  have hLocal := lex_mask_eventually_le S (geoTransformAlong A Q).cosupp hClosed
    (R.inv A Q) hUSC fU q hBoundU hValue p hx hxq
  have hAmbient := StepOneUSC.eventually_forall_mem_of_eventually U hxU hLocal
  filter_upwards [hAmbient, U.isOpen.mem_nhds hxU] with z hz hzU hzC
  exact hz hzU hzC

private theorem lower_count_eventually_le
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (hHistory : IsOriginalBranchTestTower M H T) (f : MarkedStratumPhaseFrame M H T)
    (x : Y) (hx : x ∈ (geoTransformAlong M T).cosupp) (hxLow : oldCount H T x < f.q) :
    ∀ᶠ z in 𝓝 x, z ∈ (geoTransformAlong M T).cosupp →
      markedStratumHistoryValue M H T z ≤ markedStratumHistoryValue M H T x := by
  let a := oldCount H T x
  let U := oldCountLowOpen H T a
  let A := phaseAuxiliary M H T a
  let R := CanonicalCentres.canonicalInvariant n
  let S : Set U := (Subtype.val : U → Y) ⁻¹' (geoTransformAlong M T).cosupp
  let fU : U → ℕ ×ₗ WithBot (CanonicalCentres.ValTy n) :=
    fun z => markedStratumHistoryValue M H T z.val
  have hA := (phaseAuxiliary_domain M hM h T hT hHistory a).1
  have hClosed := native_cosupport_isClosed
    (X := CMfd.of (n := n) U) (Y := CMfd.of (n := n) U) A hA .refl trivial
  have hUSC := R.isInvValue.usc
    (X := CMfd.of (n := n) U) (Y := CMfd.of (n := n) U) A hA .refl trivial
  have hBound : ∀ z ∈ S, (ofLex (fU z)).1 ≤ a := fun z _ => z.property
  have hValue : ∀ z ∈ S, (ofLex (fU z)).1 = a →
      fU z = toLex (a, if z ∈ A.cosupp then
        (R.inv (X := CMfd.of (n := n) U) A .refl z : WithBot (CanonicalCentres.ValTy n)) else ⊥) := by
    intro z hz hza
    have hLow : oldCount H T z.val < f.q := hza.trans_lt hxLow
    have hEmpty := lower_birth_tails_of_actual_frame M hM h T f z.val hz hLow
    exact (markedStratum_empty_birth_value_on_current_low_open
      M hM h T hT hHistory a z hz hza hEmpty).2
  have hxU : x ∈ U := by
    change oldCount H T x ≤ oldCount H T x
    exact le_rfl
  let p : U := ⟨x, hxU⟩
  have hLocal := lex_mask_eventually_le S A.cosupp hClosed
    (R.inv (X := CMfd.of (n := n) U) A .refl) hUSC
    fU a hBound hValue p hx rfl
  have hAmbient := StepOneUSC.eventually_forall_mem_of_eventually U hxU hLocal
  filter_upwards [hAmbient, U.isOpen.mem_nhds hxU] with z hz hzU hzC
  exact hz hzU hzC

/-- The natural prescribed-H USC field for the SAME defined NEW value on an
arbitrary native carrier, guarded by its given raw canonical history. -/
theorem markedStratum_history_value_isInvUSCOn
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (T : BlowupTower X Y)
    (hCan : IsCanonical M (markedStratumHistoryValue M H) T) :
    IsInvUSCOn (markedStratumHistoryValue M H T) (geoTransformAlong M T).cosupp := by
  obtain ⟨hT, hHistory, _hBirth, hFrames⟩ :=
    markedStratum_canonical_history_joint_interpretation M hM h T hCan
  intro x hx
  obtain ⟨f⟩ := hFrames ⟨x, hx⟩
  by_cases hLow : oldCount H T x < f.q
  · exact lower_count_eventually_le M hM h T hT hHistory f x hx hLow
  · have hTop : oldCount H T x = f.q := by
      have hb := f.currentBound x hx
      omega
    exact active_top_eventually_le M hM h T f x hx hTop

end
end Hironaka.HironakaOriginalNCMarkedStratumNativeFields
