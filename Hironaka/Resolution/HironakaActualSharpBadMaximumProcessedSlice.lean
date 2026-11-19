import Hironaka.Resolution.HironakaG4ResidualInductionInputs
import Hironaka.Resolution.HironakaG4GeneralSharpBadLocus
import Hironaka.Resolution.HironakaActualProtectedOtherRowLocalStep
import Hironaka.Resolution.HironakaOriginalNCMarkedStratumNativeFields
import Hironaka.Resolution.HironakaBaseChange
import Hironaka.Resolution.HironakaSmoothNestedCentreHomogeneity
import Hironaka.Resolution.HironakaStepOneMemberLowerExtension
import Hironaka.Resolution.HironakaSharpBadProcessedWindowGeometry

/-!
# The actual sharp-bad maximum and processed original slices

The ordinary global source includes current pure dimension and the TRUE
chronological distinct-defect exit. The lower native retained list is empty;
all inherited old/born positions stay in the prescribed ambient carrier.
BP-first mathematical proof and exact ordinary API precede this source.
The dynamic sharp schedule and any boundary/contact drop are separate.
-/

set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaActualSharpBadMaximumProcessedSlice
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  Hironaka.RegularLocusDense BlowupTowers BlowupTowerTransforms
  NormalCrossings NormalCrossingsComparison SimultaneousNormalCrossings BlowupFlatCoordinates
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  RelativePrincipalizationSpan
  RestrictedIdealExtension GermIdealOrder HironakaG4PreparedCentreCoordinates
  InvertibleIdealQuotient MonomialPartAlong DivisorExponentAlong GiraudAlong
  HironakaSharpOriginalProductTraceOrder
  HironakaG4RecordedTowerResidualCompatibility HironakaG4ResidualInductionInputs
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualTraceIncidence
  HironakaSharpActualChronologicalDistinctDefect HironakaSharpActualFiniteMemberProduct
  HironakaSharpOriginalMultiBoundaryBadLocus HironakaG4GeneralSharpBadLocus
  HironakaNormalCrossingsBoundaryTransform HironakaNormalCrossingsSNCBlockCarrier
  HironakaOriginalNCMarkedStratumHistoryValue HironakaOriginalNCMarkedStratumNativeFields
  HironakaActualProtectedOtherRowLocalStep
  HironakaOriginalNCMarkedStratum HironakaOriginalNCMarkedStratumBirthFrame
  HironakaOriginalNCCausalHistoryValue HironakaOriginalOldBranchOpenHistory
  BlowupTowerSplit BlowupTowerIsomorphism HironakaOriginalNCCountHistory
  HironakaNormalCrossingsOpenRestrictionSeparation MaxLocusLocal NormalCrossingsInvariance
open HomogenizedGlueingTower (strictAlong)
open ResolutionInvariantSpec (IsInvDomain)
open ResolutionDriver (maxLocus)

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Genuine source-subopen comparison of an ACTUAL native auxiliary.
The same nested-open biholomorphism supplies membership and native values.
This reuses the held native open/isomorphism engine with zero new credit. -/
private theorem native_subopen_refl_value
    (V U : Opens Y) (hUV : U ≤ V)
    (A : MarkedIdeal n (CMfd.of (n := n) V)) (hA : IsInvDomain n A) :
    let O := nestedOpens V U
    let χ := (nestedOpensDiffeo (n := n) hUV).symm
    let AO := MarkedIdeal.pullback (Subtype.val : O → V) A
    let B := MarkedIdeal.pullback χ AO
    ∀ p : U,
      (p ∈ B.cosupp ↔ (⟨p.val, hUV p.property⟩ : V) ∈ A.cosupp) ∧
      ((⟨p.val, hUV p.property⟩ : V) ∈ A.cosupp →
        (CanonicalCentres.canonicalInvariant n).inv B .refl p =
          (CanonicalCentres.canonicalInvariant n).inv A .refl
            ⟨p.val, hUV p.property⟩) := by
  let R := CanonicalCentres.canonicalInvariant n
  let O := nestedOpens V U
  let χ := (nestedOpensDiffeo (n := n) hUV).symm
  let AO := MarkedIdeal.pullback (Subtype.val : O → V) A
  have hAO := InvDomainTowerAlong.isInvDomain_pullback_val O hA
  have hCosOpen := MarkedIdealRestrictOpen.cosupp_pullback_val A
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hA.isWellFormed.isCoherent hg) O
  have hCos := MarkedIdealTowerTransport.cosupp_pullback_eq (Φ := χ)
    hAO.isWellFormed.isCoherent
  dsimp only
  intro p
  refine ⟨?_, ?_⟩
  · rw [hCos, hCosOpen]
    rfl
  · intro hp
    have hpO : χ p ∈ AO.cosupp := by
      rw [hCosOpen]
      exact hp
    have hIso := R.isInvValue.towerIso χ AO hAO .refl .refl χ
      IsTowerIso.refl trivial p hpO
    have hOpen := R.isInvValue.restrictOpen A hA O .refl trivial (χ p) hp
    exact hIso.trans hOpen

/-- Read the ACTUAL reflexive prescribed-carrier value on the SAME
intrinsic low open. Its auxiliary point is in the cosupport, not bottom. -/
private theorem reflexive_phase_value
    (M : MarkedIdeal n Y) (hM : IsInvDomain n M)
    {H : Set Y} (hH : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (q : ℕ) (p : oldCountLowOpen H (BlowupTower.refl : BlowupTower Y Y) q)
    (hp : p.val ∈ M.cosupp)
    (hq : oldCount H (BlowupTower.refl : BlowupTower Y Y) p.val = q) :
    markedStratumHistoryValue M H (BlowupTower.refl : BlowupTower Y Y) p.val =
      toLex (q, ((CanonicalCentres.canonicalInvariant n).inv
        (X := CMfd.of (n := n) (oldCountLowOpen H (BlowupTower.refl : BlowupTower Y Y) q))
        (phaseAuxiliary M H (BlowupTower.refl : BlowupTower Y Y) q)
        BlowupTower.refl p : WithBot (CanonicalCentres.ValTy n))) := by
  let V := oldCountLowOpen H (BlowupTower.refl : BlowupTower Y Y) q
  have hHistory : IsOriginalBranchTestTower M H (BlowupTower.refl : BlowupTower Y Y) := by
    intro U B hB hUnion
    trivial
  have hDomain := phaseAuxiliary_domain M hM hH BlowupTower.refl trivial hHistory q
  have hMV := InvDomainTowerAlong.isInvDomain_pullback_val V hM
  have hpV : p ∈ (MarkedIdeal.pullback (Subtype.val : V → Y) M).cosupp := by
    rw [MarkedIdealRestrictOpen.cosupp_pullback_val M
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent hg) V]
    exact hp
  have hpA : p ∈ (phaseAuxiliary M H (BlowupTower.refl : BlowupTower Y Y) q).cosupp := by
    change p ∈ (markedStratum (X := CMfd.of (n := n) V)
      (MarkedIdeal.pullback (Subtype.val : V → Y) M)
      {t : V | q ≤ oldCount H (BlowupTower.refl : BlowupTower Y Y) t.val}).cosupp
    rw [markedStratum_cosupp (X := CMfd.of (n := n) V)
      (MarkedIdeal.pullback (Subtype.val : V → Y) M) hMV.isWellFormed hMV.one_le_d hDomain.2]
    exact ⟨hpV, hq.ge⟩
  have he : ResolutionInvariantExt.IsEmptyTower
      (causalBirthTail H (BlowupTower.refl : BlowupTower Y Y) p.val) := by
    have hAll : ∀ k : ℕ, ∀ U : Opens (split (BlowupTower.refl : BlowupTower Y Y) k).1,
        ResolutionInvariantExt.IsEmptyTower
          (restrict U (tail (BlowupTower.refl : BlowupTower Y Y) k)) := by
      intro k
      cases k <;> intro U <;> trivial
    exact hAll _ _
  have hv := (markedStratum_empty_birth_value_on_current_low_open
    M hM hH BlowupTower.refl trivial hHistory q p hp hq he).2
  rw [if_pos hpA] at hv
  exact hv

/-- Compare the ACTUAL flat source auxiliary with the SAME native global
phase and then with the prescribed-carrier value. Source whole-ideal geometry
is consumed; future history or value equality is never an input. -/
theorem native_value_eq_on_flat_auxiliary
    (M : MarkedIdeal n Y) (hM : IsInvDomain n M)
    {H : Set Y} (hH : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (q : ℕ) (U : Opens Y)
    (hUV : U ≤ oldCountLowOpen H (BlowupTower.refl : BlowupTower Y Y) q)
    (Z : Set U) (hZc : IsClosed Z)
    (hZL : Z ⊆ (Subtype.val : U → Y) ⁻¹' M.N)
    (hSource : ∀ z ∈ Z, z.val ∈ M.cosupp)
    (hCount : ∀ z ∈ Z, oldCount H (BlowupTower.refl : BlowupTower Y Y) z.val = q)
    (hRecord : markedStratum (X := CMfd.of (n := n) U)
      (MarkedIdeal.pullback (Subtype.val : U → Y) M)
      {p : U | q ≤ oldCount H (BlowupTower.refl : BlowupTower Y Y) p.val} =
        (⟨(Subtype.val : U → Y) ⁻¹' M.N, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n U))
    (p : U) (hp : p ∈ Z)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) p p))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) p).target)
    (hzero : Φ.toFun (chartAt (ComplexModel n) p p) = 0)
    (SL SZ : Finset (Fin n)) (hMask : SL ⊆ SZ)
    (hLflat : ∀ z ∈ flatDomain Φ,
      z ∈ (Subtype.val : U → Y) ⁻¹' M.N ↔
        Φ.toFun (chartAt (ComplexModel n) p z) ∈ coordSubspace SL)
    (hZflat : ∀ z ∈ flatDomain Φ,
      z ∈ Z ↔ Φ.toFun (chartAt (ComplexModel n) p z) ∈ coordSubspace SZ) :
    ∃ W : Set U, IsOpen W ∧ p ∈ W ∧ ∀ z ∈ Z ∩ W,
      markedStratumHistoryValue M H (BlowupTower.refl : BlowupTower Y Y) z.val =
        markedStratumHistoryValue M H (BlowupTower.refl : BlowupTower Y Y) p.val := by
  let V := oldCountLowOpen H (BlowupTower.refl : BlowupTower Y Y) q
  let A := phaseAuxiliary M H (BlowupTower.refl : BlowupTower Y Y) q
  let O := nestedOpens V U
  let χ := (nestedOpensDiffeo (n := n) hUV).symm
  let B := MarkedIdeal.pullback χ (MarkedIdeal.pullback (Subtype.val : O → V) A)
  let Q : MarkedIdeal n U :=
    ⟨(Subtype.val : U → Y) ⁻¹' M.N, [], vanishingIdeal (n := n) Z, 1⟩
  have hHistory : IsOriginalBranchTestTower M H (BlowupTower.refl : BlowupTower Y Y) := by
    intro V' F hF hUnion
    trivial
  have hA := phaseAuxiliary_domain M hM hH BlowupTower.refl trivial hHistory q
  have hB : IsInvDomain n B := InvDomainTowerAlong.isInvDomain_pullback χ
    (InvDomainTowerAlong.isInvDomain_pullback_val O hA.1)
  have hPull : B = markedStratum (X := CMfd.of (n := n) U)
      (MarkedIdeal.pullback (Subtype.val : U → Y) M)
      {p : U | q ≤ oldCount H (BlowupTower.refl : BlowupTower Y Y) p.val} :=
    markedStratum_nested_pullback M hM.isWellFormed.isCoherent V U hUV
      {y : Y | q ≤ oldCount H (BlowupTower.refl : BlowupTower Y Y) y} hA.2
  have hBQ : B = Q := hPull.trans hRecord
  have hQ : IsInvDomain n Q := hBQ ▸ hB
  have hCosQ : Q.cosupp = Z := SmoothCentreLocus.cosupp_vanishingIdeal hZc hZL
  have hCompare := native_subopen_refl_value V U hUV A hA.1
  change ∀ z : U,
    (z ∈ B.cosupp ↔ (⟨z.val, hUV z.property⟩ : V) ∈ A.cosupp) ∧
      ((⟨z.val, hUV z.property⟩ : V) ∈ A.cosupp →
        (CanonicalCentres.canonicalInvariant n).inv B .refl z =
          (CanonicalCentres.canonicalInvariant n).inv (X := CMfd.of (n := n) V) A .refl
            ⟨z.val, hUV z.property⟩) at hCompare
  rw [hBQ] at hCompare
  have hNative (z : U) (hz : z ∈ Z) :
      (CanonicalCentres.canonicalInvariant n).inv (X := CMfd.of (n := n) U) Q .refl z =
        (CanonicalCentres.canonicalInvariant n).inv (X := CMfd.of (n := n) V) A .refl
          ⟨z.val, hUV z.property⟩ := by
    apply (hCompare z).2
    apply (hCompare z).1.mp
    rw [hCosQ]
    exact hz
  have hRead (z : U) (hz : z ∈ Z) :
      markedStratumHistoryValue M H (BlowupTower.refl : BlowupTower Y Y) z.val =
        toLex (q, ((CanonicalCentres.canonicalInvariant n).inv (X := CMfd.of (n := n) U) Q .refl z :
          WithBot (CanonicalCentres.ValTy n))) := by
    have hv := reflexive_phase_value M hM hH q
      (⟨z.val, hUV z.property⟩ : V) (hSource z hz) (hCount z hz)
    rw [← hNative z hz] at hv
    exact hv
  obtain ⟨W, hWo, hpW, hConst⟩ :=
    HironakaSmoothNestedCentreHomogeneity.native_flat_nested_value_homogeneity
      (X := CMfd.of (n := n) U) hZc hZL hQ Φ hsrc hzero SL SZ hMask hLflat hZflat
  refine ⟨W, hWo, hpW, ?_⟩
  intro z hz
  rw [hRead z hz.1, hRead p hp, hConst z hz]

/-- The exact source count fibre, actual nested auxiliary and one CURRENT
maximum point determine the germ of the SAME entire global maximum. -/
theorem native_maximum_germ_of_flat_auxiliary
    (M : MarkedIdeal n Y) (hM : IsInvDomain n M)
    {H : Set Y} (hH : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (q : ℕ) (U : Opens Y)
    (hUV : U ≤ oldCountLowOpen H (BlowupTower.refl : BlowupTower Y Y) q)
    (Z : Set U) (hZc : IsClosed Z)
    (hZL : Z ⊆ (Subtype.val : U → Y) ⁻¹' M.N)
    (hFibre : ∀ z : U, z ∈ Z ↔ z.val ∈ M.cosupp ∧
      oldCount H (BlowupTower.refl : BlowupTower Y Y) z.val = q)
    (hRecord : markedStratum (X := CMfd.of (n := n) U)
      (MarkedIdeal.pullback (Subtype.val : U → Y) M)
      {p : U | q ≤ oldCount H (BlowupTower.refl : BlowupTower Y Y) p.val} =
        (⟨(Subtype.val : U → Y) ⁻¹' M.N, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n U))
    (p : U) (hp : p ∈ Z)
    (hpMax : p.val ∈ maxLocus
      (markedStratumHistoryValue M H (BlowupTower.refl : BlowupTower Y Y)) M.cosupp)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) p p))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) p).target)
    (hzero : Φ.toFun (chartAt (ComplexModel n) p p) = 0)
    (SL SZ : Finset (Fin n)) (hMask : SL ⊆ SZ)
    (hLflat : ∀ z ∈ flatDomain Φ,
      z ∈ (Subtype.val : U → Y) ⁻¹' M.N ↔
        Φ.toFun (chartAt (ComplexModel n) p z) ∈ coordSubspace SL)
    (hZflat : ∀ z ∈ flatDomain Φ,
      z ∈ Z ↔ Φ.toFun (chartAt (ComplexModel n) p z) ∈ coordSubspace SZ) :
    ∃ W : Set U, IsOpen W ∧ p ∈ W ∧ ∀ z ∈ W,
      (z.val ∈ maxLocus
        (markedStratumHistoryValue M H (BlowupTower.refl : BlowupTower Y Y)) M.cosupp ↔ z ∈ Z) := by
  have hSource (z : U) (hz : z ∈ Z) : z.val ∈ M.cosupp := ((hFibre z).mp hz).1
  have hCount (z : U) (hz : z ∈ Z) :
      oldCount H (BlowupTower.refl : BlowupTower Y Y) z.val = q := ((hFibre z).mp hz).2
  obtain ⟨W, hWo, hpW, hValue⟩ := native_value_eq_on_flat_auxiliary
    M hM hH q U hUV Z hZc hZL hSource hCount hRecord p hp
    Φ hsrc hzero SL SZ hMask hLflat hZflat
  refine ⟨W, hWo, hpW, ?_⟩
  intro z hzW
  constructor
  · intro hzMax
    have he : markedStratumHistoryValue M H (BlowupTower.refl : BlowupTower Y Y) z.val =
        markedStratumHistoryValue M H (BlowupTower.refl : BlowupTower Y Y) p.val :=
      le_antisymm (hpMax.2 z.val hzMax.1) (hzMax.2 p.val hpMax.1)
    have hc := congrArg (fun v : ℕ ×ₗ WithBot (CanonicalCentres.ValTy n) => (ofLex v).1) he
    change oldCount H (BlowupTower.refl : BlowupTower Y Y) z.val =
      oldCount H (BlowupTower.refl : BlowupTower Y Y) p.val at hc
    exact (hFibre z).mpr ⟨hzMax.1, hc.trans (hCount p hp)⟩
  · intro hzZ
    refine ⟨hSource z hzZ, ?_⟩
    intro y hy
    rw [hValue z ⟨hzZ, hzW⟩]
    exact hpMax.2 y hy

/-- Restrict the ENTIRE processed-window chart through a genuine open
embedding. Every original position stays its actual preimage. -/
private theorem processed_geometry_subopen
    {N S : Set Y} (F : List (Set Y))
    (U V : Opens Y) (hVU : V ≤ U) (Haux Z : Set U)
    (hSlice : (Subtype.val : U → Y) ⁻¹' S =
      (Subtype.val : U → Y) ⁻¹' N ∩ Haux)
    (hSNC : IsSNCDivisor n (Haux :: F.map ((Subtype.val : U → Y) ⁻¹' ·)))
    (hTr : IsTransverse n ((Subtype.val : U → Y) ⁻¹' N)
      (Haux :: F.map ((Subtype.val : U → Y) ⁻¹' ·)))
    (hNC : HasNormalCrossings n Z (Haux :: F.map ((Subtype.val : U → Y) ⁻¹' ·))) :
    let ι : V → U := fun z => ⟨z.val, hVU z.property⟩
    ∃ H' : Set V,
      (Subtype.val : V → Y) ⁻¹' S = (Subtype.val : V → Y) ⁻¹' N ∩ H' ∧
      IsSNCDivisor n (H' :: F.map ((Subtype.val : V → Y) ⁻¹' ·)) ∧
      IsTransverse n ((Subtype.val : V → Y) ⁻¹' N)
        (H' :: F.map ((Subtype.val : V → Y) ⁻¹' ·)) ∧
      HasNormalCrossings n (ι ⁻¹' Z) (H' :: F.map ((Subtype.val : V → Y) ⁻¹' ·)) := by
  let ι : V → U := fun z => ⟨z.val, hVU z.property⟩
  have hEmb : HironakaBaseChange.IsOpenHoloEmbedding n ι :=
    (HironakaBaseChange.isOpenHoloEmbedding_val V).codRestrict U (fun z => hVU z.property)
  let H' := ι ⁻¹' Haux
  have hMap : (Haux :: F.map ((Subtype.val : U → Y) ⁻¹' ·)).map (ι ⁻¹' ·) =
      H' :: F.map ((Subtype.val : V → Y) ⁻¹' ·) := by
    simp only [List.map_cons, List.map_map]
    rfl
  have hSlice' : (Subtype.val : V → Y) ⁻¹' S = (Subtype.val : V → Y) ⁻¹' N ∩ H' :=
    congrArg (fun D : Set U => ι ⁻¹' D) hSlice
  refine ⟨H', hSlice', ?_, ?_, ?_⟩
  · have h := isSNCDivisor_map_preimage hEmb.pullsBackCoordinates hEmb.continuous hSNC
    rw [hMap] at h
    exact h
  · have h := isTransverse_preimage hEmb.pullsBackCoordinates hTr
    rw [hMap] at h
    exact h
  · have h := hasNormalCrossings_preimage hEmb.pullsBackCoordinates hNC
    rw [hMap] at h
    exact h

/-- Compose the actual retained order-one row with its whole remaining
boundary. The marked cosupport is exactly the sharp bad locus of this
lower carrier. -/
theorem sharp_bad_native_domain_of_retained_rows
    (hn : 0 < n) {N : Set Y} {old born : List (Set Y)}
    (hN : IsClosedSubmanifold n N) (hFull : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hDense : N ⊆ closure (N \ ⋃ D ∈ old ++ born, D))
    (hOrd : ∀ x ∈ N, ∀ a, ordinaryTraceOrder N (oldResidualPart N old born a) x ≤ 1)
    (hDistinct : ∀ x ∈ N, ∀ a b : Fin old.length, a ≠ b →
      ¬(oldResidualPart N old born a).mem x 1 → ¬(oldResidualPart N old born b).mem x 1 →
      ¬∀ g, (oldResidualPart N old born a).mem x g ↔ (oldResidualPart N old born b).mem x g)
    (j : Fin old.length) :
    let L := N ∩ (oldResidualPart N old born j).zeroLocus
    let Fj := old.eraseIdx j.val ++ born
    let Bj := originalSharpBadLocus (n := n) L Fj
    let M : MarkedIdeal n Y := ⟨L, [], vanishingIdeal (n := n) Bj, 1⟩
    IsClosedSubmanifold n L ∧
      (∀ x ∈ L, ∃ d, RegularAtDim (n := n) N x (d+1) ∧ RegularAtDim (n := n) L x d) ∧
      L ⊆ old.get j ∧ L ⊆ closure (L \ ⋃ D ∈ Fj, D) ∧ IsSNCDivisor n Fj ∧
      IsInvDomain n M ∧ M.cosupp = Bj ∧ IsBoundaryAdaptedCarrier (n := n) (⋃ D ∈ Fj, D) [] := by
  let L := N ∩ (oldResidualPart N old born j).zeroLocus
  let Fj := old.eraseIdx j.val ++ born
  have hGeom := actual_residual_support_local_geometry hn hN hFull hTr hDense hOrd j
  have hDenseL := residual_support_dense_off_remainingBoundary_of_local_dimension
    hn hN hFull hTr hDense hOrd hDistinct j
  have hDims (x : Y) (hx : x ∈ L) := (hGeom.2.2 x hx).2.2
  have hL : IsClosedSubmanifold n L := hGeom.1
  have hLF : L ⊆ closure (L \ ⋃ D ∈ Fj, D) := hDenseL
  have hF : IsSNCDivisor n Fj := isSNCDivisor_of_sublist hFull
    ((List.eraseIdx_sublist old j.val).append (List.Sublist.refl born))
  let Bj := originalSharpBadLocus (n := n) L Fj
  have hBa : IsComplexAnalyticSubset (n := n) Bj :=
    isComplexAnalyticSubset_originalSharpBadLocus hL hF hLF
  have hcB := CartanIrreducible.cartanCoherence Bj hBa
  let M : MarkedIdeal n Y := ⟨L, [], vanishingIdeal (n := n) Bj, 1⟩
  have hCos : M.cosupp = Bj := by
    change cosupport n L (vanishingIdeal (n := n) Bj) 1 = Bj
    rw [SmoothCentreLocus.cosupport_vanishingIdeal_one hBa.isClosed]
    exact inter_eq_right.mpr (fun _ hx => hx.1)
  have hThin := originalSharpBadLocus_thin hL hLF
  have hM : IsInvDomain n M := by
    refine ⟨⟨hL, hcB, isSNCDivisor_nil,
      isTransverse_nil_of_isClosedSubmanifold hL⟩, ?_, Nat.le_refl 1, ?_⟩
    · intro x hx
      obtain ⟨d, _, hReg⟩ := hDims x hx
      exact ⟨d, hReg.1, hReg⟩
    · intro x hx
      apply HironakaStepOneMemberLowerExtension.isNonzeroAlongAt_of_thin_cosupport hcB
        (d := 1) (H := L) ?_ hx
      intro O hO hOB
      apply hThin O hO
      change O ∩ L ⊆ M.cosupp at hOB
      rw [hCos] at hOB
      exact hOB
  exact ⟨hL, hDims, hGeom.2.1, hLF, hF, hM, hCos,
    boundaryAdapted_union_of_snc_append Fj [] (by simpa only [List.append_nil] using hF)⟩

/-- The genuine global sharp-bad native source is derived before any native
open/isomorphism comparison. No future canonical history is supplied. -/
theorem sharp_bad_native_domain
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hOrd : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
      ∀ a : Fin E.length,
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
          (chronologicalMarked (originalRelativeMemberMarked W (E.get a)) T).ideal x ≤ 1)
    (d : ℕ)
    (hReg : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
      RegularAtDim (n := n) (geoTransformAlong (geometricTemplate W []) T).N x (d+1))
    (hDistinct : chronologicalDistinctDefect W E T = ∅)
    (j : Fin E.length) :
    let A := geoTransformAlong (geometricTemplate W []) T
    let L := A.N ∩ (chronologicalMarked
      (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus
    let Fj := (E.map (strictAlong T)).eraseIdx j.val ++ A.E
    let Bj := originalSharpBadLocus (n := n) L Fj
    let M : MarkedIdeal n Y := ⟨L, [], vanishingIdeal (n := n) Bj, 1⟩
    IsClosedSubmanifold n L ∧
      (∀ x ∈ L, RegularAtDim (n := n) L x d) ∧
      L ⊆ closure (L \ ⋃ D ∈ Fj, D) ∧
      IsInvDomain n M ∧ IsBoundaryAdaptedCarrier (n := n) (⋃ D ∈ Fj, D) [] := by
  let A := geoTransformAlong (geometricTemplate W []) T
  let old := E.map (strictAlong T)
  let J := fun a : Fin E.length =>
    (chronologicalMarked (originalRelativeMemberMarked W (E.get a)) T).ideal
  let back : Fin old.length → Fin E.length := fun a =>
    ⟨a.val, by simpa only [old, List.length_map] using a.isLt⟩
  let jo : Fin old.length := ⟨j.val, by simpa only [old, List.length_map] using j.isLt⟩
  have hBack : back jo = j := Fin.ext rfl
  have hGet (a : Fin old.length) : old.get a = strictAlong T (E.get (back a)) := by
    simp [old, back, List.get_eq_getElem]
  have hRecorded := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hN : IsClosedSubmanifold n A.N := hRecorded.1
  have hCurrent (a : Fin old.length) : oldResidualPart A.N old A.E a = J (back a) := by
    change nonmonomialPartAlong n A.N
      (restrictOn n A.N (vanishingIdeal (n := n) (old.get a))) A.E = _
    rw [hGet a]
    exact (hRecorded.2.2.2.2 (back a)).2.2.1
  have hRow (a : Fin E.length) :=
    original_members_actual_finite_chronological_geometry hn hW hE hdense a T hT
  have hc (a : Fin E.length) : (J a).IsCoherent := (hRow a).2.2.2.1.isCoherent
  have hnz (a : Fin E.length) : ∀ x ∈ A.N, IsNonzeroAlongAt A.N (J a) x := by
    have h := (hRow a).2.2.2.2.1
    rw [(hRow a).1] at h
    exact h
  have hpr (a : Fin E.length) : ∀ x ∈ A.N, ∃ f : Y → ℂ, HolomorphicAt n f x ∧
      ∀ g, (J a).mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) A.N (· = f) x g := by
    have h := (hRow a).2.2.2.2.2
    rw [(hRow a).1] at h
    exact h
  have hDistinct' : ∀ x ∈ A.N, ∀ a b : Fin old.length, a ≠ b →
      ¬(oldResidualPart A.N old A.E a).mem x 1 →
      ¬(oldResidualPart A.N old A.E b).mem x 1 →
      ¬∀ g, (oldResidualPart A.N old A.E a).mem x g ↔
        (oldResidualPart A.N old A.E b).mem x g := by
    intro x hx a b hab ha hb heq
    rw [hCurrent a] at ha
    rw [hCurrent b] at hb
    have hne : back a ≠ back b := by
      intro he
      exact hab (Fin.ext (congrArg (fun c : Fin E.length => c.val) he))
    have hDef : x ∈ chronologicalDistinctDefect W E T := by
      apply (actual_distinct_defect_iff_witness hN hc hnz hpr hx).mpr
      right
      refine ⟨back a, back b, hne, ?_, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩
      · intro g
        simpa only [hCurrent a, hCurrent b] using heq g
    rw [hDistinct] at hDef
    exact hDef
  have hOrd' : ∀ x ∈ A.N, ∀ a, ordinaryTraceOrder A.N
      (oldResidualPart A.N old A.E a) x ≤ 1 := by
    intro x hx a
    rw [hCurrent a]
    exact hOrd x hx (back a)
  obtain ⟨hL, hDims, _, hDenseL, _, hM, _, hH⟩ :=
    sharp_bad_native_domain_of_retained_rows hn hN hRecorded.2.1 hRecorded.2.2.1
      hRecorded.2.2.2.1 hOrd' hDistinct' jo
  have hRegL : ∀ x ∈ A.N ∩ (oldResidualPart A.N old A.E jo).zeroLocus,
      RegularAtDim (n := n) (A.N ∩ (oldResidualPart A.N old A.E jo).zeroLocus) x d := by
    intro x hx
    obtain ⟨e, hNe, hLe⟩ := hDims x hx
    have he : e = d := Nat.add_right_cancel (RegularPointDimension.eq_of_regularAtDim hNe (hReg x hx.1))
    exact he ▸ hLe
  have hJ := hCurrent jo
  rw [hBack] at hJ
  rw [hJ] at hL hRegL hDenseL hM
  exact ⟨hL, hRegL, hDenseL, hM, hH⟩

/-- The SAME actual native global maximum has full processed-slice locality. -/
theorem actual_sharp_bad_maximum_processed_slice_locality
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hOrd : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
      ∀ a : Fin E.length,
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
          (chronologicalMarked
            (originalRelativeMemberMarked W (E.get a)) T).ideal x ≤ 1)
    (d : ℕ)
    (hReg : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
      RegularAtDim (n := n)
        (geoTransformAlong (geometricTemplate W []) T).N x (d+1))
    (hDistinct : chronologicalDistinctDefect W E T = ∅)
    (i j : Fin E.length) (hne : j ≠ i)
    (hNCi : let A := geoTransformAlong (geometricTemplate W []) T
      let Si := A.N ∩ (chronologicalMarked
        (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      HasNormalCrossings n Si
        ((E.map (strictAlong T)).eraseIdx i.val ++ A.E))
    (hDensei : let A := geoTransformAlong (geometricTemplate W []) T
      let Si := A.N ∩ (chronologicalMarked
        (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      Si ⊆ closure (Si \ ⋃ H ∈
        (E.map (strictAlong T)).eraseIdx i.val ++ A.E, H)) :
    let A := geoTransformAlong (geometricTemplate W []) T
    let old := E.map (strictAlong T)
    let J := fun a : Fin E.length =>
      (chronologicalMarked (originalRelativeMemberMarked W (E.get a)) T).ideal
    let Si := A.N ∩ (J i).zeroLocus
    let L := A.N ∩ (J j).zeroLocus
    let Fj := old.eraseIdx j.val ++ A.E
    let Bj := originalSharpBadLocus (n := n) L Fj
    let M : MarkedIdeal n Y := ⟨L, [], vanishingIdeal (n := n) Bj, 1⟩
    let H := ⋃ D ∈ Fj, D
    let C := maxLocus
      (markedStratumHistoryValue M H
        (BlowupTower.refl : BlowupTower Y Y)) M.cosupp
    ∀ x ∈ C ∩ Si, ∃ (U : Opens Y), x ∈ U ∧
      ∃ Haux : Set U,
        let NU := (Subtype.val : U → Y) ⁻¹' A.N
        let FiU := (old.eraseIdx i.val ++ A.E).map
          ((Subtype.val : U → Y) ⁻¹' ·)
        (Subtype.val : U → Y) ⁻¹' Si = NU ∩ Haux ∧
        IsSNCDivisor n (Haux :: FiU) ∧
        IsTransverse n NU (Haux :: FiU) ∧
        HasNormalCrossings n ((Subtype.val : U → Y) ⁻¹' C)
          (Haux :: FiU) := by
  dsimp only
  let A := geoTransformAlong (geometricTemplate W []) T
  let old := E.map (strictAlong T)
  let J := fun a : Fin E.length =>
    (chronologicalMarked (originalRelativeMemberMarked W (E.get a)) T).ideal
  let Si := A.N ∩ (J i).zeroLocus
  let L := A.N ∩ (J j).zeroLocus
  let Fi := old.eraseIdx i.val ++ A.E
  let Fj := old.eraseIdx j.val ++ A.E
  let Bj := originalSharpBadLocus (n := n) L Fj
  let M : MarkedIdeal n Y := ⟨L, [], vanishingIdeal (n := n) Bj, 1⟩
  let H := ⋃ D ∈ Fj, D
  let C := maxLocus (markedStratumHistoryValue M H (BlowupTower.refl : BlowupTower Y Y)) M.cosupp
  obtain ⟨hL, _hLreg, hLF, hM, hAdapt⟩ :=
    sharp_bad_native_domain hn hW hE hdense T hT hFull hOrd d hReg hDistinct j
  have hRecorded := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hFj : IsSNCDivisor n Fj := isSNCDivisor_of_sublist hRecorded.2.1
    ((List.eraseIdx_sublist old j.val).append (List.Sublist.refl A.E))
  have hBclosed : IsClosed Bj := isClosed_originalSharpBadLocus hL.1 hFj.1
  have hCos : M.cosupp = Bj :=
    SmoothCentreLocus.cosupp_vanishingIdeal hBclosed (fun _ hx => hx.1)
  intro x hx
  have hxBj : x ∈ Bj := hCos ▸ hx.1.1
  obtain ⟨U, hxU, Haux, Z, Φ, SL, SZ, hBound, hZ, hZL, _hZB, hFibre,
      hRecord, hSlice, hSNC, hTr, hNC, hMask, hsrc, hzero, hLflat, hZflat⟩ :=
    HironakaSharpBadProcessedWindowGeometry.exists_sharp_bad_processed_window_geometry
      hn hW hE hdense T hT hFull hOrd i j hne hNCi hDensei
      hM.isWellFormed.isCoherent hLF x ⟨hxBj, hx.2⟩
  let q := oldCount H (BlowupTower.refl : BlowupTower Y Y) x
  have hUV : U ≤ oldCountLowOpen H (BlowupTower.refl : BlowupTower Y Y) q := by
    intro y hy
    exact hBound ⟨y, hy⟩
  have hpZ : (⟨x, hxU⟩ : U) ∈ Z := (hFibre _).mpr ⟨hxBj, rfl⟩
  have hFibreM : ∀ z : U, z ∈ Z ↔ z.val ∈ M.cosupp ∧
      oldCount H (BlowupTower.refl : BlowupTower Y Y) z.val = q := by
    intro z
    rw [hCos]
    exact hFibre z
  obtain ⟨W', hWo, hxW, hEq⟩ := native_maximum_germ_of_flat_auxiliary
    M hM hAdapt q U hUV Z hZ.1 hZL hFibreM hRecord
    (⟨x, hxU⟩ : U) hpZ hx.1 Φ hsrc hzero SL SZ hMask hLflat hZflat
  let V : Opens Y := ⟨(Subtype.val : U → Y) '' W', U.isOpen.isOpenMap_subtype_val W' hWo⟩
  have hxV : x ∈ V := ⟨⟨x, hxU⟩, hxW, rfl⟩
  have hVU : V ≤ U := by
    intro y hy
    obtain ⟨z, _hzW, hzy⟩ := hy
    rw [← hzy]
    exact z.property
  let ι : V → U := fun y => ⟨y.val, hVU y.property⟩
  have hInW (y : V) : ι y ∈ W' := by
    obtain ⟨z, hzW, hzy⟩ := y.property
    have he : ι y = z := Subtype.ext hzy.symm
    rw [he]
    exact hzW
  have hCV : (Subtype.val : V → Y) ⁻¹' C = ι ⁻¹' Z := by
    ext y
    exact hEq (ι y) (hInW y)
  obtain ⟨H', hSlice', hSNC', hTr', hNC'⟩ :=
    processed_geometry_subopen (N := A.N) (S := Si) Fi U V hVU Haux Z
      hSlice hSNC hTr hNC
  rw [← hCV] at hNC'
  exact ⟨V, hxV, H', hSlice', hSNC', hTr', hNC'⟩

end
end Hironaka.HironakaActualSharpBadMaximumProcessedSlice
