import Hironaka.Resolution.HironakaG8ActualQuotientResidualRestart
import Hironaka.Resolution.HironakaG8PrincipalEpochSuccession

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8ChronologicalNativeClassAtlas
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism ResolutionInvariantSpec ResolutionDriver
  NonmonomialOrderLocal GermIdealOrder RelativePrincipalizationSpan
  HironakaG11InvBMClass HironakaG8LocalHistory HironakaG8NativeSimultaneousCentre
  HironakaG8NativePrefixOriginalCanonical HironakaG1OriginalInvariantClassFunctorial
  HironakaG8OccupiedAtlasRestart HironakaActualPowerBoundaryExponents HironakaG8LocalPower
  HironakaG1OriginalUnequalMarkCanonical HironakaG8NativeRelativeClearing CanonicalCentres
  HironakaG8PrincipalEpochSuccession HironakaG8OccupiedMixedRestart
  HironakaG8PrincipalRetainedEpochFinite HomogenizedIdealAlong DivisorExponentAlong GeneralCompanionPhase NonmonomialOrderRegime
  HironakaActualCoherentWeightedCoefficientMarked HironakaActualWeightedCoefficientCompression
  HironakaG8NativeCommonDenominatorReduction HironakaG8ActualQuotientResidualRestart

/-- Simultaneous values transfer together on the same physical tower
when each chart is compared at its literal common mark. -/
theorem simultaneous_stages_of_chart_class
    {n : ℕ} {X Y : CMfd.{0} n} {I : Type}
    (U : I → Opens X) (P Q : ∀ i, MarkedIdeal n (CMfd.of (n := n) (U i)))
    (hp : ∀ i, IsInvDomain n (P i)) (hq : ∀ i, IsInvDomain n (Q i))
    (hClass : ∀ i, LocWPEquiv (P i) (Q i)) (hd : ∀ i, (P i).d = (Q i).d)
    (hDim : ∀ i, SameCarrierDim (P i) (Q i)) (hExp : ∀ i, ExpAgree (P i) (Q i))
    (T : BlowupTower X Y)
    (hSync : NativeSimultaneousStages (canonicalInvariant n) U P T) :
    NativeSimultaneousStages (canonicalInvariant n) U Q T := by
  induction T with
  | refl => trivial
  | step S C π hπ ih =>
    refine ⟨ih hSync.1,?_⟩
    rcases hSync.2 with he | ⟨m, hm⟩
    · exact Or.inl he
    right
    have hCan (i : I) := simultaneous_stages_original_canonical (canonicalInvariant n) U P S hSync.1 i
    have hTest (i : I) := (canonicalInvariant n).isInvValue.isGeoTestTower_of_isCanonical
      (hp i) (restrict (U i) S) (hCan i)
    have hCos (i : I) := ((hClass i).wEquiv.2 (restrict (U i) S)).2 (hTest i)
    have hVal (i : I) := (classFunctorialFor_canonicalInvariant n).inv_eq (P i) (Q i)
      (hp i) (hq i) (hClass i) (hd i) (hClass i).E_eq.symm (hDim i) (hExp i)
      (restrict (U i) S) (hCan i)
    refine ⟨m,hm.covered,?_,?_⟩
    · intro i z hz
      have hzP : z ∈ (geoTransformAlong (P i) (restrict (U i) S)).cosupp := hCos i ▸ hz
      rw [← hVal i z hzP]
      exact hm.upper i z hzP
    · intro i
      rw [hm.trace i]
      ext z
      constructor
      · rintro ⟨hz,hv⟩
        exact ⟨hCos i ▸ hz,(hVal i z hz).symm.trans hv⟩
      · rintro ⟨hz,hv⟩
        have hpz : z ∈ (geoTransformAlong (P i) (restrict (U i) S)).cosupp := hCos i ▸ hz
        exact ⟨hpz,(hVal i z hpz).trans hv⟩

/-- The actual native windows need only match the common-powered local
class and scaled boundary data of the lower reference. Synchronization
then gives the original canonical tower of the whole lower reference. -/
theorem canonical_of_native_class_cover
    {n : ℕ} {X Y : CMfd.{0} (n+1)} {I : Type}
    {W D : Set X} {E : List (Set X)} {H : ℕ → ℕ}
    (A : NativeWindows X I W E H D) (F : MarkedIdeal (n+1) X) (hF : IsInvDomain (n+1) F)
    (e : ℕ) (he : 1 ≤ e) (hMark : A.mark = F.d*e)
    (hLevel : F.cosupp ⊆ D)
    (hClass : ∀ i, LocWPEquiv (A.record i) (MarkedIdeal.pullback (Subtype.val : A.openSet i → X) F))
    (hN : ∀ i, (A.record i).N = (Subtype.val : A.openSet i → X) ⁻¹' F.N)
    (hExp : ∀ i H x, F.d * divExpAlong (n+1) (A.record i).N (A.record i).ideal H x =
      (A.record i).d * divExpAlong (n+1) ((MarkedIdeal.pullback (Subtype.val : A.openSet i → X) F).N)
        ((MarkedIdeal.pullback (Subtype.val : A.openSet i → X) F).ideal) H x)
    (T : BlowupTower X Y)
    (hSync : NativeSimultaneousStages (canonicalInvariant (n+1)) A.openSet A.powered T) :
    IsCanonical F ((canonicalInvariant (n+1)).inv F) T := by
  let P := powerMarked F e
  let Q (i : I) := MarkedIdeal.pullback (Subtype.val : A.openSet i → X) F
  let R (i : I) := powerMarked (X := CMfd.of (n := n+1) (A.openSet i)) (Q i) e
  have hP := powerMarked_isInvDomain F hF he
  have hQ (i : I) := InvDomainTowerAlong.isInvDomain_pullback_val (A.openSet i) hF
  have hR (i : I) := powerMarked_isInvDomain (X := CMfd.of (n := n+1) (A.openSet i)) (Q i) (hQ i) he
  have hEql (i : I) : (A.powered i).d = (R i).d := (A.commonMark i).trans hMark
  have hLoc (i : I) : LocWPEquiv (A.powered i) (R i) :=
    locEquiv_pow (κ := Kinds.wp) rfl (hClass i) (A.domain i) (hQ i) (A.positive i) he
  have hDims (i : I) : SameCarrierDim (A.powered i) (R i) := SameCarrierDim.of_N_eq (hN i)
  have hNorm (i : I) : ExpAgree (A.powered i) (R i) := by
    intro H _ x _ _
    change divExpAlong (n+1) (A.record i).N
      (IdealWeightPowers.idealPow (A.record i).ideal (A.exponent i)) H x =
      divExpAlong (n+1) (Q i).N (IdealWeightPowers.idealPow (Q i).ideal e) H x
    have hAW := (A.domain i).isWellFormed
    have hQW : (Q i).IsWellFormed := (hQ i).isWellFormed
    rw [divExpAlong_idealPow hAW.isClosedSubmanifold_N hAW.isCoherent (A.positive i),
      divExpAlong_idealPow (X := CMfd.of (n := n+1) (A.openSet i)) hQW.isClosedSubmanifold_N (I := (Q i).ideal) hQW.isCoherent he]
    apply Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_of_lt hF.one_le_d)
    have hD : (A.record i).d * A.exponent i = F.d*e := hEql i
    have hX := hExp i H x
    change F.d * divExpAlong (n+1) (A.record i).N (A.record i).ideal H x =
      (A.record i).d * divExpAlong (n+1) (Q i).N (Q i).ideal H x at hX
    calc
      F.d * (A.exponent i * divExpAlong (n+1) (A.record i).N (A.record i).ideal H x) =
          A.exponent i * (F.d * divExpAlong (n+1) (A.record i).N (A.record i).ideal H x) := by ring
      _ = A.exponent i * ((A.record i).d * divExpAlong (n+1) (Q i).N (Q i).ideal H x) := by rw [hX]
      _ = ((A.record i).d * A.exponent i) * divExpAlong (n+1) (Q i).N (Q i).ideal H x := by ring
      _ = F.d * (e * divExpAlong (n+1) (Q i).N (Q i).ideal H x) := by rw [hD,Nat.mul_assoc]
  have hStage := simultaneous_stages_of_chart_class A.openSet A.powered R A.powered_domain hR
    hLoc hEql hDims hNorm T hSync
  have hRecords : R = fun i => MarkedIdeal.pullback (Subtype.val : A.openSet i → X) P := by
    funext i
    exact (HironakaG11InvCommonMark.pullback_powerMarked contMDiff_subtype_val F hF.isWellFormed.isCoherent e).symm
  rw [hRecords] at hStage
  have hCover (x : X) (hx : x ∈ P.cosupp) : ∃ i, x ∈ A.openSet i :=
    A.covers x (hLevel ((powerMarked_cosupp F hF he) ▸ hx))
  have hCan := canonical_of_simultaneous_pullback_atlas (canonicalInvariant (n+1)) P hP A.openSet hCover T hStage
  exact (canonicalInvariant_isCanonical_power_iff F hF e he T).mpr hCan

/-- Chronological rebase across the occupied higher-order prefix uses the
whole lower reference canonicality supplied by the class-based atlas. -/
theorem append_chronological_canonical_of_native_class_cover
    {n : ℕ} {Z X Y : CMfd.{0} (n+1)} {I : Type}
    {W D : Set X} {E : List (Set X)} {H : ℕ → ℕ}
    (A : NativeWindows X I W E H D)
    (M : MarkedIdeal (n+1) Z) (hM : IsInvDomain (n+1) M)
    (P : BlowupTower Z X) (hCanP : IsCanonical M ((canonicalInvariant (n+1)).inv M) P)
    (F : MarkedIdeal (n+1) X) (hF : IsInvDomain (n+1) F)
    (hFN : F.N = univ) (hNo : HasNoBoundaryFactor F) (hCap : IsMaximalOrderAlong F.N F.ideal F.d)
    (hHigher : CentresOrdGt M F.d P)
    (e : ℕ) (he : 1 ≤ e) (hMark : A.mark = F.d*e)
    (hLevel : F.cosupp ⊆ D)
    (hClass : ∀ i, LocWPEquiv (A.record i) (MarkedIdeal.pullback (Subtype.val : A.openSet i → X) F))
    (hN : ∀ i, (A.record i).N = (Subtype.val : A.openSet i → X) ⁻¹' F.N)
    (hExp : ∀ i H x, F.d * divExpAlong (n+1) (A.record i).N (A.record i).ideal H x =
      (A.record i).d * divExpAlong (n+1) ((MarkedIdeal.pullback (Subtype.val : A.openSet i → X) F).N)
        ((MarkedIdeal.pullback (Subtype.val : A.openSet i → X) F).ideal) H x)
    (T : BlowupTower X Y)
    (hSync : NativeSimultaneousStages (canonicalInvariant (n+1)) A.openSet A.powered T) :
    let L := geoTransformAlong M P
    L.N = univ → L.E = F.E → L.d ≤ F.d → nmPart L = F.ideal →
    IsCanonical M ((canonicalInvariant (n+1)).inv M) (P.append T) := by
  intro L hLN hE hd hResidual
  have hFCan := canonical_of_native_class_cover A F hF e he hMark hLevel hClass hN hExp T hSync
  exact (append_whole_canonical_of_principal_residual_epoch M hM P hCanP F hF hFN hNo hCap hHigher
    T hFCan hLN hE hd hResidual).1

/-- Genuine chart data identifying the weighted record and reconstructing
the active residual of the already advanced original low record. -/
structure NativeRestartQuotientChart
    {n : ℕ} {Y : CMfd.{0} n} {ι : Type} [Fintype ι]
    (L Q : MarkedIdeal n Y) (d : ℕ) where
  Z : CMfd.{0} n
  source : MarkedIdeal n Z
  domain : IsInvDomain n source
  ambient : source.N = univ
  tower : BlowupTower Z Y
  tested : IsGeoTestTower source tower
  endpoint : geoTransformAlong source tower = L
  weight : ι → ℕ
  weightPositive : ∀ j, 0 < weight j
  weightDvd : ∀ j, weight j ∣ d
  commonDvd : d ∣ weightedCommonMark weight
  sourceFn : ι → Z → ℂ
  sourceHol : ∀ j, MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (sourceFn j)
  sourceGen : source.ideal = finiteFunctionIdeal (fun j => sourceFn j ^ (d/weight j))
  fn : ι → Y → ℂ
  fnHol : ∀ j, MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (fn j)
  denominator : Y → ℂ
  denominatorHol : MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) denominator
  quotient : ∀ j y, sourceFn j (tower.proj y) = denominator y ^ weight j * fn j y
  denominatorNonzero : ∀ y, ∃ᶠ z in 𝓝 y, denominator z ≠ 0
  denominatorMono : MonomialPartAlong.IsMonomialAlong n univ
    (finiteFunctionIdeal (fun _ : Unit => denominator^d)) L.E
  noFactor : ∀ y : Y, ∀ i : Fin L.E.length, y ∈ L.E.get i →
    ∃ j, ∃ᶠ z in 𝓝 y, z ∈ L.E.get i ∧ fn j z ≠ 0
  normalizedNonzero : ∀ y ∈ (univ : Set Y), IsNonzeroAlongAt (n := n) univ
    (finiteFunctionIdeal (n := n) (fun j => fn j ^ (d/weight j))) y
  nativeRecord : Q = ⟨univ,L.E,weightedFunctionIdeal weight fn,weightedCommonMark weight⟩

/-- Chart quotient equations and actual ordered trace witnesses reconstruct
the full normalized residual on the chosen window. -/
theorem NativeRestartQuotientChart.nmPart_eq
    {n : ℕ} (hn : 0 < n) {Y : CMfd.{0} n} {ι : Type} [Fintype ι]
    {L Q : MarkedIdeal n Y} {d : ℕ}
    (C : NativeRestartQuotientChart (ι := ι) L Q d) :
    nmPart L = finiteFunctionIdeal (fun j => C.fn j ^ (d/C.weight j)) := by
  have hWF := (InvDomainTowerAlong.isInvDomain_geoTransformAlong C.domain C.tower C.tested).isWellFormed
  have hLW : L.IsWellFormed := C.endpoint ▸ hWF
  have hN0 := (pullback_eq_mul_geoTransformAlong (𝔪 := C.source) C.ambient C.domain.isWellFormed.isCoherent
    C.tower C.tested).1
  have hLN : L.N = univ := C.endpoint ▸ hN0
  have hDen (y : Y) (_ : y ∈ (univ : Set Y)) : IsNonzeroAlongAt (n := n) univ
      (finiteFunctionIdeal (fun _ : Unit => C.denominator^d)) y := by
    refine ⟨C.denominator^d, InvertibleIdealQuotient.isInSpanAt_self
      (S := fun s => s ∈ range (fun _ : Unit => C.denominator^d))
      ⟨(),rfl⟩ (Filter.Eventually.of_forall fun z => (C.denominatorHol.pow d) z), ?_⟩
    exact (C.denominatorNonzero y).mono fun z hz => ⟨mem_univ z,pow_ne_zero d hz⟩
  have h := actual_weighted_quotient_family_nmPart hn C.source C.domain C.ambient C.tower C.tested
    C.weight d C.weightDvd C.sourceFn C.sourceHol C.sourceGen C.fn C.fnHol C.denominator
    C.denominatorHol C.quotient hDen C.normalizedNonzero (C.endpoint.symm ▸ C.denominatorMono)
  rw [C.endpoint] at h
  apply h
  intro y _ i hi
  obtain ⟨j,hj⟩ := C.noFactor y i hi
  have hHol : HolomorphicAt n (C.fn j) y := Filter.Eventually.of_forall fun z => C.fnHol j z
  exact ⟨C.fn j ^ (d/C.weight j),InvertibleIdealQuotient.isInSpanAt_self ⟨j,rfl⟩
    (CompanionReduction.holomorphicAt_pow_of hHol _),
    quotient_power_not_boundary_factor L hLW hLN y i (C.fn j) hHol _ hj⟩

private theorem native_active_ordinary_order_of_large_mark
    {n : ℕ} {X : CMfd.{0} n} {Q : MarkedIdeal n X} {W : Set X} {H : ℕ → ℕ}
    (hNative : HironakaG11PresLineState.NativeHSState Q W H) (hLarge : 1 < Q.d) :
    ∀ x ∈ Q.cosupp, HironakaSharpOriginalProductTraceOrder.ordinaryTraceOrder Q.N Q.ideal x = Q.d := by
  obtain ⟨_, _, hN, hI, V, S, k, a, w, hw, _, _, hMark, _, _, hAt⟩ := hNative
  have hv : V.Nonempty := by
    by_contra hNo
    have hEmpty := Finset.not_nonempty_iff_eq_empty.mp hNo
    have hOne : Q.d = 1 := by
      rw [hMark]
      subst V
      simp [weightedCommonMark]
    omega
  intro x hx
  have hOrd := (HironakaActualHistoricalNativeOrdinaryOrder.actual_native_point_ordinary_order
    S hv a w hw W Q hN hI hMark x hx (hAt x hx)).1
  rwa [hN,hMark]

/-- The actual nonprincipal weighted restart atlas gives chronological
canonicality across the earlier occupied higher-order prefix. Each chart
supplies genuine quotient equations, while its physical centers share
the native simultaneous score. -/
theorem append_chronological_canonical_of_weighted_quotient_atlas
    {n : ℕ} {Z X Y : CMfd.{0} (n+1)} {I : Type} {ι : I → Type} [∀ i, Fintype (ι i)]
    {W D : Set X} {E : List (Set X)} {H : ℕ → ℕ}
    (A : NativeWindows X I W E H D)
    (M : MarkedIdeal (n+1) Z) (hM : IsInvDomain (n+1) M) (hMN : M.N = univ)
    (P : BlowupTower Z X) (hCanP : IsCanonical M ((canonicalInvariant (n+1)).inv M) P)
    (d e : ℕ) (hd : M.d ≤ d) (hdLarge : 1 < d) (he : 1 ≤ e) (hMark : A.mark = d*e)
    (hHigher : CentresOrdGt M d P)
    (T : BlowupTower X Y)
    (hSync : NativeSimultaneousStages (canonicalInvariant (n+1)) A.openSet A.powered T)
    (hContains : cosupport (n+1) univ (nmPart (geoTransformAlong M P)) d ⊆ D)
    (hChart : ∀ i, NativeRestartQuotientChart (ι := ι i)
      (Y := CMfd.of (n := n+1) (A.openSet i))
      (MarkedIdeal.pullback (Subtype.val : A.openSet i → X) (geoTransformAlong M P)) (A.record i) d) :
    IsCanonical M ((canonicalInvariant (n+1)).inv M) (P.append T) := by
  let L := geoTransformAlong M P
  let F : MarkedIdeal (n+1) X := ⟨univ,L.E,nmPart L,d⟩
  have hTP := (canonicalInvariant (n+1)).isInvValue.isGeoTestTower_of_isCanonical hM P hCanP
  have hLD := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM P hTP
  have hLN : L.N = univ := (pullback_eq_mul_geoTransformAlong (𝔪 := M)
    hMN hM.isWellFormed.isCoherent P hTP).1
  have hPart := NonmonomialTransformAlong.parts_hypotheses (Nat.succ_pos n)
    L hLD.isWellFormed hLD.isNonzeroAlongAt
  have hF : IsInvDomain (n+1) F := by
    refine ⟨⟨HomogenizedGlueingTower.isClosedSubmanifold_univ,hPart.1,hLD.isWellFormed.isSNCDivisor,?_⟩,
      ?_,hM.one_le_d.trans hd,?_⟩
    · change NormalCrossings.IsTransverse (n+1) univ L.E
      rw [← hLN]
      exact hLD.isWellFormed.isTransverse
    · change DimLE (n+1) (univ : Set X) (n+1)
      rw [← hLN]
      exact hLD.dimLE
    · change ∀ x ∈ (univ : Set X), IsNonzeroAlongAt univ (nmPart L) x
      rw [← hLN]
      exact hPart.2.2.2.2.2.1
  have hNo : HasNoBoundaryFactor F := by
    have h := hPart.2.2.2.2.1
    change ∀ x ∈ L.N, ∀ i : Fin L.E.length, x ∈ L.E.get i →
      ∃ q, (nmPart L).mem x q ∧
        ¬ IsInSpanOnAt (n := n+1) L.N ((vanishingIdeal (n := n+1) (L.E.get i)).mem x) x q at h
    rw [hLN] at h
    exact h
  let R (i : I) := MarkedIdeal.pullback (Subtype.val : A.openSet i → X) F
  have hClassExp (i : I) : LocWPEquiv (A.record i) (R i) ∧
      ∀ H x, F.d * divExpAlong (n+1) (A.record i).N (A.record i).ideal H x =
        (A.record i).d * divExpAlong (n+1) (R i).N (R i).ideal H x := by
    let C := hChart i
    let l := MarkedIdeal.pullback (Subtype.val : A.openSet i → X) L
    have hChartI : (R i).ideal = nmPart (M := CMfd.of (n := n+1) (A.openSet i)) l := by
      exact MonomialPartEtale.pullback_nonmonomialPartAlong
        (fun y => ⟨DerivativeIdealAlongEtale.openInv (A.openSet i) y,
          DerivativeIdealAlongEtale.isLocalInverseAt_val (A.openSet i) y⟩)
        hLD.isWellFormed.isCoherent hPart.2.1 hPart.1
    have hRShape : R i = ⟨univ,l.E,finiteFunctionIdeal (fun j => C.fn j ^ (d/C.weight j)),d⟩ :=
      MarkedIdealOperationsTransform.MarkedIdeal.ext_of preimage_univ rfl
        (hChartI.trans (C.nmPart_eq (Nat.succ_pos n))) rfl
    have hRd : IsInvDomain (n+1) (R i) := InvDomainTowerAlong.isInvDomain_pullback_val (A.openSet i) hF
    have hQd := A.domain i
    rw [hRShape] at hRd
    rw [C.nativeRecord] at hQd
    have hCmp := common_denominator_native_boundary_class (X := CMfd.of (n := n+1) (A.openSet i))
      C.weight C.weightPositive C.fn C.fnHol d (Nat.zero_lt_of_lt (hM.one_le_d.trans hd))
      C.weightDvd C.commonDvd l.E hRd hQd
    let R₁ : MarkedIdeal (n+1) (CMfd.of (n := n+1) (A.openSet i)) :=
      ⟨univ,l.E,finiteFunctionIdeal (fun j => C.fn j ^ (d/C.weight j)),d⟩
    let Q₁ : MarkedIdeal (n+1) (CMfd.of (n := n+1) (A.openSet i)) :=
      ⟨univ,l.E,weightedFunctionIdeal C.weight C.fn,weightedCommonMark C.weight⟩
    change LocWPEquiv Q₁ R₁ ∧
      ∀ H x, R₁.d * divExpAlong (n+1) Q₁.N Q₁.ideal H x =
        Q₁.d * divExpAlong (n+1) R₁.N R₁.ideal H x at hCmp
    have hR₁ : R i = R₁ := hRShape
    have hQ₁ : A.record i = Q₁ := C.nativeRecord
    rw [← hR₁, ← hQ₁] at hCmp
    exact hCmp
  have hNClass (i : I) : (A.record i).N = (Subtype.val : A.openSet i → X) ⁻¹' F.N := by
    rw [(hChart i).nativeRecord]
    exact preimage_univ.symm
  have hCap : IsMaximalOrderAlong F.N F.ideal F.d := by
    intro x hx
    have hxF : x ∈ F.cosupp := cosupport_anti (Nat.le_succ F.d) hx
    obtain ⟨i,hi⟩ := A.covers x (hContains hxF)
    let z : A.openSet i := ⟨x,hi⟩
    have hRDomain : IsInvDomain (n+1) (R i) := InvDomainTowerAlong.isInvDomain_pullback_val (A.openSet i) hF
    have hLargeQ : 1 < (A.record i).d := by
      let C := hChart i
      have hc : (A.record i).d = weightedCommonMark C.weight := congrArg MarkedIdeal.d C.nativeRecord
      rw [hc]
      exact hdLarge.trans_le (Nat.le_of_dvd (weightedCommonMark_pos C.weight C.weightPositive) C.commonDvd)
    have hActive := native_active_ordinary_order_of_large_mark (A.native i) hLargeQ
    have hRCap := HironakaG8EqualWeightNativeThresholds.reference_cap_of_native_active_order
      (X := CMfd.of (n := n+1) (A.openSet i)) (A.record i) (R i) (A.domain i) hRDomain
      (SameCarrierDim.of_N_eq (hNClass i)) (hClassExp i).1 hActive
    apply hRCap z
    let Fplus := {F with d := F.d + 1}
    have hPull := MarkedIdealRestrictOpen.cosupp_pullback_val Fplus
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hF.isWellFormed.isCoherent hg)
      (A.openSet i)
    change z ∈ (MarkedIdeal.pullback (Subtype.val : A.openSet i → X) Fplus).cosupp
    rw [hPull]
    exact hx
  exact append_chronological_canonical_of_native_class_cover A M hM P hCanP F hF rfl hNo hCap hHigher
    e he hMark hContains (fun i => (hClassExp i).1) hNClass (fun i => (hClassExp i).2)
    T hSync hLN rfl ((d_geoTransformAlong M P).trans_le hd) rfl

end
end Hironaka.HironakaG8ChronologicalNativeClassAtlas
