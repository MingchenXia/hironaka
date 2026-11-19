import Hironaka.Resolution.HironakaG8InitialCommonIdealMaximum
import Hironaka.Resolution.HironakaG8OriginalSingularPrefix
import Hironaka.Resolution.HironakaEmbeddedBoundary

/-! A full native comparison window reads the whole original first centre. -/
set_option autoImplicit false
open Set TopologicalSpace

namespace Hironaka.HironakaG8InitialFullWindowTies

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  ResolutionInvariantSpec ResolutionDriver CanonicalCentres HironakaEmbeddedBoundary
  HironakaG8NativeSimultaneousCentre HironakaG8OriginalSingularPrefix
  HironakaActualPowerBoundaryExponents HironakaG8InitialCommonIdealMaximum
  HironakaSharpOriginalProductTraceOrder HironakaG8NativeCommonMarkRank

/-- An occupied window containing the whole original cosupport determines the
literal first centre, if its raw native record is the actual vanishing ideal
with mark equal to its attained top ordinary order. Attainment follows
from the simultaneous stage itself. -/
theorem initial_canonical_of_full_native_window {n : ℕ} {X Y : CMfd.{0} (n+1)}
    {I : Type} (W : Set X) (hW : IsComplexAnalyticSubset (n := n+1) W)
    (hInt : interior W = ∅) (U : I → Opens X)
    (P : ∀ i, MarkedIdeal (n+1) (CMfd.of (n := n+1) (U i))) (e : I → ℕ)
    (D : Set X) (hDW : D ⊆ W) (hD : D.Nonempty) (m : ValTy (n+1))
    (hCentre : NativeSimultaneousCentre (canonicalInvariant (n+1)) U
      (fun i => powerMarked (P i) (e i)) (.refl : BlowupTower X X) D m)
    (i : I) (hCover : W ⊆ U i) (hP : IsInvDomain (n+1) (P i)) (he : 1 ≤ e i)
    (q : ℕ)
    (hRecord : P i = ⟨univ, [], vanishingIdeal (n := n+1) ((Subtype.val : U i → X) ⁻¹' W), q⟩)
    (hOrder : ∀ x : U i, ordinaryTraceOrder (X := CMfd.of (n := n+1) (U i)) univ
      (vanishingIdeal (n := n+1) ((Subtype.val : U i → X) ⁻¹' W)) x ≤ q)
    (π : Y → X) (hπ : IsBlowupAlong (n+1) D π) :
    let M : MarkedIdeal (n+1) X := ⟨univ, [], vanishingIdeal (n := n+1) W, 1⟩
    IsCanonical M ((canonicalInvariant (n+1)).inv M) (.step .refl D π hπ) := by
  intro M
  let R := canonicalInvariant (n+1)
  let U₀ := U i
  let J := vanishingIdeal (n := n+1) ((Subtype.val : U₀ → X) ⁻¹' W)
  let M₀ : MarkedIdeal (n+1) U₀ := ⟨univ, [], J, 1⟩
  have hM : IsInvDomain (n+1) M := isInvDomain_boundary hW hInt NormalCrossings.isSNCDivisor_nil
  have hPull : MarkedIdeal.pullback (Subtype.val : U₀ → X) M = M₀ :=
    pullback_val_mk_vanishingIdeal U₀ [] W
  have hM₀ : IsInvDomain (n+1) M₀ := hPull ▸ InvDomainTowerAlong.isInvDomain_pullback_val U₀ hM
  have hMeet : ((Subtype.val : U₀ → X) ⁻¹' D).Nonempty := by
    obtain ⟨x,hx⟩ := hD
    exact ⟨⟨x,hCover (hDW hx)⟩,hx⟩
  have hTrace := raw_maxLocus_eq_centre_trace U P e (.refl : BlowupTower X X) D m hCentre i hP he trivial hMeet
  change maxLocus (R.inv (P i) (.refl : BlowupTower (CMfd.of (n := n+1) U₀) _)) (P i).cosupp =
    (Subtype.val : U₀ → X) ⁻¹' D at hTrace
  rw [hRecord] at hTrace hP
  have hAttain : ∃ x : U₀, ordinaryTraceOrder (X := CMfd.of (n := n+1) U₀) univ J x = q := by
    obtain ⟨x,hx⟩ := hMeet
    have hMax := hTrace.symm ▸ hx
    have hThresh := ordinaryTraceOrder_cosupport_iff (X := CMfd.of (n := n+1) U₀) (I := J) (W := univ)
      hM₀.isWellFormed.isClosedSubmanifold_N hM₀.isWellFormed.isCoherent hM₀.isNonzeroAlongAt (mem_univ x) q
    exact ⟨x, le_antisymm (hOrder x) (hThresh.mp hMax.1)⟩
  have hLocal := (initial_maxLocus_markOne_eq_topMark (X := CMfd.of (n := n+1) U₀)
    J hM₀ hP.one_le_d hOrder hAttain).trans hTrace
  have hCos : M.cosupp = W := cosupp_mk_vanishingIdeal hW.isClosed []
  have hCos₀ : M₀.cosupp = (Subtype.val : U₀ → X) ⁻¹' W :=
    cosupp_mk_vanishingIdeal (hW.isClosed.preimage continuous_subtype_val) []
  have hVal (x : U₀) (hx : x.val ∈ W) :
      R.inv M₀ (.refl : BlowupTower (CMfd.of (n := n+1) U₀) _) x =
        R.inv M (.refl : BlowupTower X X) x.val := by
    have h := R.isInvValue.restrictOpen M hM U₀ (.refl : BlowupTower X X) trivial x
      (by simpa only [geoTransformAlong_refl, hCos] using hx)
    rw [hPull] at h
    exact h
  have hCentreWhole : D = maxLocus (R.inv M (.refl : BlowupTower X X)) M.cosupp := by
    ext x
    constructor
    · intro hx
      have hxW := hDW hx
      let x₀ : U₀ := ⟨x,hCover hxW⟩
      have hxMax : x₀ ∈ maxLocus (R.inv M₀ (.refl : BlowupTower (CMfd.of (n := n+1) U₀) _)) M₀.cosupp :=
        hLocal.symm ▸ hx
      refine ⟨hCos.symm ▸ hxW, fun z hz => ?_⟩
      have hzW := hCos ▸ hz
      let z₀ : U₀ := ⟨z,hCover hzW⟩
      have H := hxMax.2 z₀ (show z₀ ∈ M₀.cosupp from hCos₀.symm ▸ hzW)
      simpa only [hVal z₀ hzW, hVal x₀ hxW] using H
    · intro hx
      have hxW := hCos ▸ hx.1
      let x₀ : U₀ := ⟨x,hCover hxW⟩
      have hx₀ : x₀ ∈ maxLocus (R.inv M₀ (.refl : BlowupTower (CMfd.of (n := n+1) U₀) _)) M₀.cosupp := by
        refine ⟨hCos₀.symm ▸ hxW, fun z hz => ?_⟩
        have hzW : z.val ∈ W := show z ∈ (Subtype.val : U₀ → X) ⁻¹' W from hCos₀ ▸ hz
        rw [hVal z hzW, hVal x₀ hxW]
        exact hx.2 z.val (hCos.symm ▸ hzW)
      change x₀ ∈ (Subtype.val : U₀ → X) ⁻¹' D
      exact hLocal ▸ hx₀
  exact ⟨trivial, Or.inr (by simpa only [geoTransformAlong_refl] using hCentreWhole)⟩

/-- A genuine cover may replace a full individual window when the retained
common-mark records are literal opens of a single uniform power of the
original input. Their simultaneous value gives both whole-record ties. -/
theorem initial_canonical_of_uniform_power_cover {n : ℕ} {X Y : CMfd.{0} n}
    {I : Type} (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (e : ℕ) (he : 1 ≤ e) (U : I → Opens X)
    (hCover : ∀ x ∈ M.cosupp, ∃ i, x ∈ U i)
    (D : Set X) (hD : D.Nonempty) (m : ValTy n)
    (hCentre : NativeSimultaneousCentre (canonicalInvariant n) U
      (fun i => MarkedIdeal.pullback (Subtype.val : U i → X) (powerMarked M e))
      (.refl : BlowupTower X X) D m)
    (π : Y → X) (hπ : IsBlowupAlong n D π) :
    IsCanonical M ((canonicalInvariant n).inv M) (.step .refl D π hπ) := by
  let R := canonicalInvariant n
  let Q := powerMarked M e
  let v := R.inv Q (.refl : BlowupTower X X)
  have hQ : IsInvDomain n Q := powerMarked_isInvDomain M hM he
  have hCos : Q.cosupp = M.cosupp := powerMarked_cosupp M hM he
  have hLocal (i : I) (z : U i) :
      z ∈ (MarkedIdeal.pullback (Subtype.val : U i → X) Q).cosupp ↔ z.val ∈ M.cosupp := by
    rw [MarkedIdealRestrictOpen.cosupp_pullback_val _
      (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hQ.isWellFormed.isCoherent), hCos]
    rfl
  have hValue (i : I) (z : U i) (hz : z.val ∈ M.cosupp) :
      R.inv (MarkedIdeal.pullback (Subtype.val : U i → X) Q)
        (.refl : BlowupTower (CMfd.of (n := n) (U i)) _) z = v z.val :=
    R.isInvValue.restrictOpen Q hQ (U i) (.refl : BlowupTower X X) trivial z
      (by simpa only [geoTransformAlong_refl, hCos] using hz)
  have hDLevel : ∀ x ∈ D, x ∈ M.cosupp ∧ v x = m := by
    intro x hx
    obtain ⟨i,hi⟩ := hCentre.covered x hx
    let z : U i := ⟨x,hi⟩
    have hTrace := hCentre.trace i
    have hz : z ∈ {z : U i | z ∈ (MarkedIdeal.pullback (Subtype.val : U i → X) Q).cosupp ∧
      R.inv (MarkedIdeal.pullback (Subtype.val : U i → X) Q)
        (.refl : BlowupTower (CMfd.of (n := n) (U i)) _) z = m} := hTrace ▸ hx
    have hMon := (hLocal i z).mp hz.1
    exact ⟨hMon, (hValue i z hMon).symm.trans hz.2⟩
  have hOff : ∀ x ∈ M.cosupp, x ∉ D → v x < m := by
    intro x hx hxD
    obtain ⟨i,hi⟩ := hCover x hx
    let z : U i := ⟨x,hi⟩
    have hz := (hLocal i z).mpr hx
    have hUp := hCentre.upper i z hz
    change R.inv (MarkedIdeal.pullback (Subtype.val : U i → X) Q)
      (.refl : BlowupTower (CMfd.of (n := n) (U i)) _) z ≤ m at hUp
    rw [hValue i z hx] at hUp
    apply lt_of_le_of_ne hUp
    intro hEq
    apply hxD
    have hTrace := hCentre.trace i
    have hMem : z ∈ {z : U i | z ∈ (MarkedIdeal.pullback (Subtype.val : U i → X) Q).cosupp ∧
      R.inv (MarkedIdeal.pullback (Subtype.val : U i → X) Q)
        (.refl : BlowupTower (CMfd.of (n := n) (U i)) _) z = m} := ⟨hz, (hValue i z hx).trans hEq⟩
    exact (show z ∈ (Subtype.val : U i → X) ⁻¹' D from hTrace.symm ▸ hMem)
  have hOrder {x y : X} (hx : x ∈ M.cosupp) (hy : y ∈ M.cosupp) :
      R.inv M (.refl : BlowupTower X X) x < R.inv M (.refl : BlowupTower X X) y ↔ v x < v y :=
    canonical_common_mark_power_lt_iff M M hM hM rfl e he .refl .refl trivial trivial
      (by simpa only [geoTransformAlong_refl] using hx) (by simpa only [geoTransformAlong_refl] using hy)
  obtain ⟨a,ha⟩ := hD
  have hCentreWhole : D = maxLocus (R.inv M (.refl : BlowupTower X X)) M.cosupp := by
    ext x
    constructor
    · intro hx
      have hxLevel := hDLevel x hx
      refine ⟨hxLevel.1, fun y hy => not_lt.mp fun hlt => ?_⟩
      have hv := (hOrder hxLevel.1 hy).mp hlt
      rw [hxLevel.2] at hv
      by_cases hyD : y ∈ D
      · exact (not_lt_of_ge (hDLevel y hyD).2.le) hv
      · exact (not_lt_of_ge (hOff y hy hyD).le) hv
    · intro hx
      by_contra hxD
      have hxSmall := hOff x hx.1 hxD
      have haLevel := hDLevel a ha
      exact (not_lt_of_ge (hx.2 a haLevel.1))
        ((hOrder hx.1 haLevel.1).mpr (haLevel.2.symm ▸ hxSmall))
  exact ⟨trivial, Or.inr (by simpa only [geoTransformAlong_refl] using hCentreWhole)⟩


/-- A uniform-powered native cover only has to cover the attained top
ordinary-order stratum when the common raw mark is that top order. -/
theorem initial_canonical_of_uniform_top_mark_cover {n : ℕ} {X Y : CMfd.{0} (n+1)}
    {I : Type} (W : Set X) (hW : IsComplexAnalyticSubset (n := n+1) W)
    (hInt : interior W = ∅) (q : ℕ) (hq : 1 ≤ q)
    (hUpper : ∀ x : X, ordinaryTraceOrder (X := X) univ (vanishingIdeal (n := n+1) W) x ≤ q)
    (e : ℕ) (he : 1 ≤ e) (U : I → Opens X)
    (hCover : ∀ x : X, ordinaryTraceOrder (X := X) univ (vanishingIdeal (n := n+1) W) x = q →
      ∃ i, x ∈ U i)
    (D : Set X) (hD : D.Nonempty) (m : ValTy (n+1))
    (π : Y → X) (hπ : IsBlowupAlong (n+1) D π) :
    let M : MarkedIdeal (n+1) X := ⟨univ, [], vanishingIdeal (n := n+1) W, 1⟩
    let Q : MarkedIdeal (n+1) X := ⟨univ, [], vanishingIdeal (n := n+1) W, q⟩
    NativeSimultaneousCentre (canonicalInvariant (n+1)) U
      (fun i => MarkedIdeal.pullback (Subtype.val : U i → X) (powerMarked Q e))
      (.refl : BlowupTower X X) D m →
    IsCanonical M ((canonicalInvariant (n+1)).inv M) (.step .refl D π hπ) := by
  intro M Q hCentre
  let R := canonicalInvariant (n+1)
  have hM : IsInvDomain (n+1) M := isInvDomain_boundary hW hInt NormalCrossings.isSNCDivisor_nil
  have hQ : IsInvDomain (n+1) Q :=
    ⟨⟨hM.isWellFormed.isClosedSubmanifold_N,hM.isWellFormed.isCoherent,
      hM.isWellFormed.isSNCDivisor,hM.isWellFormed.isTransverse⟩,
      hM.dimLE,hq,hM.isNonzeroAlongAt⟩
  have hTop (x : X) (hx : x ∈ Q.cosupp) :
      ordinaryTraceOrder (X := X) univ (vanishingIdeal (n := n+1) W) x = q := by
    have h := ordinaryTraceOrder_cosupport_iff (X := X) hM.isWellFormed.isClosedSubmanifold_N
      hM.isWellFormed.isCoherent hM.isNonzeroAlongAt (mem_univ x) q
    exact le_antisymm (hUpper x) (h.mp hx)
  have hCan := initial_canonical_of_uniform_power_cover Q hQ e he U
    (fun x hx => hCover x (hTop x hx)) D hD m hCentre π hπ
  have hMax : D = maxLocus (R.inv Q (.refl : BlowupTower X X)) Q.cosupp := by
    rcases hCan.2 with hEmpty | hMax
    · exact (hD.ne_empty hEmpty).elim
    · exact hMax
  obtain ⟨x,hx⟩ := hD
  have hxQ : x ∈ Q.cosupp := (show x ∈ maxLocus (R.inv Q (.refl : BlowupTower X X)) Q.cosupp from
    hMax ▸ hx).1
  have hCompare := initial_maxLocus_markOne_eq_topMark (X := X) (vanishingIdeal (n := n+1) W)
    hM hq hUpper ⟨x,hTop x hxQ⟩
  exact ⟨trivial, Or.inr (hMax.trans hCompare.symm)⟩


end Hironaka.HironakaG8InitialFullWindowTies
