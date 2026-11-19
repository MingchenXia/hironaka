import Hironaka.Resolution.HironakaG8InitialCommonIdealMaximum
import Hironaka.Resolution.HironakaG8NativeSimultaneousCentre
import Hironaka.Resolution.HironakaG1OriginalUnequalMarkCanonical
import Hironaka.Resolution.HironakaG8LocalRestrictEquiv

/-! Whole original maxima from scalar-aligned native records on independent windows. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace

namespace Hironaka.HironakaG8InitialWeightedCoverTies

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  ResolutionInvariantSpec ResolutionDriver CanonicalCentres HironakaEmbeddedBoundary
  HironakaG8NativeSimultaneousCentre HironakaG8LocalHistory HironakaG11InvBMClass
  HironakaG8LocalPower HironakaActualPowerBoundaryExponents
  HironakaG1OriginalUnequalMarkCanonical HironakaG8InitialCommonIdealMaximum
  HironakaSharpOriginalProductTraceOrder HironakaG8LocalRestrictEquiv MarkedIdealOperationsAlong
open MarkedIdealOperationsAlong.MarkedIdeal (RestrictEquiv)

/-- Distinct coherent records at a common native mark may replace literal
uniform powers. A local weak-test equivalence on each retained window,
with its actual carrier unchanged, preserves cross-window strict order
and therefore the entire original first maximum. -/
theorem initial_canonical_of_weakTest_cover {n : ℕ} {X Y : CMfd.{0} n}
    {I : Type} (M : MarkedIdeal n X) (hM : IsInvDomain n M) (hEmpty : M.E = [])
    (U : I → Opens X) (P : ∀ i, MarkedIdeal n (CMfd.of (n := n) (U i)))
    (hP : ∀ i, IsInvDomain n (P i)) (r : ℕ) (hMark : ∀ i, (P i).d = r)
    (hCompat : ∀ i, let A := MarkedIdeal.pullback (Subtype.val : U i → X) M
      LocWPEquiv A (P i) ∧ A.N = (P i).N)
    (hCover : ∀ x ∈ M.cosupp, ∃ i, x ∈ U i)
    (D : Set X) (hD : D.Nonempty) (m : ValTy n)
    (hCentre : NativeSimultaneousCentre (canonicalInvariant n) U P (.refl : BlowupTower X X) D m)
    (π : Y → X) (hπ : IsBlowupAlong n D π) :
    IsCanonical M ((canonicalInvariant n).inv M) (.step .refl D π hπ) := by
  let R := canonicalInvariant n
  let A := fun i => MarkedIdeal.pullback (Subtype.val : U i → X) M
  have hA (i : I) : IsInvDomain n (A i) := InvDomainTowerAlong.isInvDomain_pullback_val (U i) hM
  have hBoundary (i : I) : (A i).E = [] := by
    change M.E.map _ = []
    rw [hEmpty, List.map_nil]
  have hLocal (i : I) (z : U i) : z ∈ (P i).cosupp ↔ z.val ∈ M.cosupp := by
    rw [← (hCompat i).1.cosupp_eq_base, MarkedIdealRestrictOpen.cosupp_pullback_val _
      (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hM.isWellFormed.isCoherent)]
    rfl
  have hValue (i : I) (z : U i) (hz : z.val ∈ M.cosupp) :
      R.inv (A i) (.refl : BlowupTower (CMfd.of (n := n) (U i)) _) z =
        R.inv M (.refl : BlowupTower X X) z.val :=
    R.isInvValue.restrictOpen M hM (U i) (.refl : BlowupTower X X) trivial z hz
  have hOrder (i j : I) (z : U i) (w : U j) (hz : z.val ∈ M.cosupp) (hw : w.val ∈ M.cosupp) :
      R.inv M (.refl : BlowupTower X X) z.val < R.inv M (.refl : BlowupTower X X) w.val ↔
      R.inv (P i) (.refl : BlowupTower (CMfd.of (n := n) (U i)) _) z <
        R.inv (P j) (.refl : BlowupTower (CMfd.of (n := n) (U j)) _) w := by
    rw [← hValue i z hz, ← hValue j w hw]
    have hzA : z ∈ (A i).cosupp := (hCompat i).1.cosupp_eq_base.symm ▸ (hLocal i z).mpr hz
    have hwA : w ∈ (A j).cosupp := (hCompat j).1.cosupp_eq_base.symm ▸ (hLocal j w).mpr hw
    exact canonicalTwoPairCuts_canonicalInvariant n (A i) (P i) (A j) (P j)
      (hA i) (hP i) (hA j) (hP j)
      (hCompat i).1 (SameCarrierDim.of_N_eq (hCompat i).2) (by simp [hBoundary i])
      (hCompat j).1 (SameCarrierDim.of_N_eq (hCompat j).2) (by simp [hBoundary j])
      rfl ((hMark i).trans (hMark j).symm) trivial trivial trivial trivial
      (.refl : BlowupTower (CMfd.of (n := n) (U i)) _)
      (.refl : BlowupTower (CMfd.of (n := n) (U j)) _) trivial trivial trivial trivial
      z (by simpa only [geoTransformAlong_refl] using hzA)
      w (by simpa only [geoTransformAlong_refl] using hwA)
  have hOn (x : X) (hx : x ∈ D) :
      ∃ (i : I) (z : U i), z.val = x ∧ z.val ∈ M.cosupp ∧
        R.inv (P i) (.refl : BlowupTower (CMfd.of (n := n) (U i)) _) z = m := by
    obtain ⟨i,hi⟩ := hCentre.covered x hx
    let z : U i := ⟨x,hi⟩
    have hTrace := (Set.ext_iff.mp (hCentre.trace i) z).mp hx
    exact ⟨i,z,rfl,(hLocal i z).mp hTrace.1,hTrace.2⟩
  have hOff (x : X) (hx : x ∈ M.cosupp) (hxD : x ∉ D) (i : I) (hi : x ∈ U i) :
      R.inv (P i) (.refl : BlowupTower (CMfd.of (n := n) (U i)) _) ⟨x,hi⟩ < m := by
    let z : U i := ⟨x,hi⟩
    have hz := (hLocal i z).mpr hx
    refine lt_of_le_of_ne (hCentre.upper i z hz) fun hEq => ?_
    exact hxD ((Set.ext_iff.mp (hCentre.trace i) z).mpr ⟨hz,hEq⟩)
  obtain ⟨a,ha⟩ := hD
  have hWhole : D = maxLocus (R.inv M (.refl : BlowupTower X X)) M.cosupp := by
    ext x
    constructor
    · intro hx
      obtain ⟨i,z,rfl,hz,hzVal⟩ := hOn x hx
      refine ⟨hz, fun y hy => not_lt.mp fun hlt => ?_⟩
      obtain ⟨j,hj⟩ := hCover y hy
      let w : U j := ⟨y,hj⟩
      have hRec := (hOrder i j z w hz hy).mp hlt
      rw [hzVal] at hRec
      exact (not_lt_of_ge (hCentre.upper j w ((hLocal j w).mpr hy))) hRec
    · intro hx
      by_contra hxD
      obtain ⟨i,hi⟩ := hCover x hx.1
      obtain ⟨j,w,rfl,hw,hwVal⟩ := hOn a ha
      have hRec := hOff x hx.1 hxD i hi
      rw [← hwVal] at hRec
      exact (not_lt_of_ge (hx.2 w.val hw)) ((hOrder i j ⟨x,hi⟩ w hx.1 hw).mpr hRec)
  exact ⟨trivial, Or.inr (by simpa only [geoTransformAlong_refl] using hWhole)⟩

/-- At the top order, chart-dependent positive powers of the coherent
inputs may verify the required local comparisons. It is enough that the
two powered records have the same restricted ideals, marks and boundary
on the actual chart. -/
theorem initial_canonical_of_chartwise_power_top_cover
    {n : ℕ} {X Y : CMfd.{0} (n+1)} {I : Type}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n+1) W)
    (hInt : interior W = ∅) (q : ℕ) (hq : 1 ≤ q)
    (hUpper : ∀ x : X, ordinaryTraceOrder (X := X) univ (vanishingIdeal (n := n+1) W) x ≤ q)
    (U : I → Opens X)
    (P : ∀ i, MarkedIdeal (n+1) (CMfd.of (n := n+1) (U i)))
    (hP : ∀ i, IsInvDomain (n+1) (P i)) (r : ℕ) (hMark : ∀ i, (P i).d = r)
    (hCover : ∀ x : X, ordinaryTraceOrder (X := X) univ (vanishingIdeal (n := n+1) W) x = q →
      ∃ i, x ∈ U i)
    (D : Set X) (hD : D.Nonempty) (m : ValTy (n+1))
    (hCentre : NativeSimultaneousCentre (canonicalInvariant (n+1)) U P (.refl : BlowupTower X X) D m)
    (π : Y → X) (hπ : IsBlowupAlong (n+1) D π) :
    let M : MarkedIdeal (n+1) X := ⟨univ, [], vanishingIdeal (n := n+1) W, 1⟩
    let Q : MarkedIdeal (n+1) X := ⟨univ, [], vanishingIdeal (n := n+1) W, q⟩
    (∀ i, ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ RestrictEquiv
      (powerMarked (MarkedIdeal.pullback (Subtype.val : U i → X) Q) a) (powerMarked (X := CMfd.of (n := n+1) (U i)) (P i) b)) →
    IsCanonical M ((canonicalInvariant (n+1)).inv M) (.step .refl D π hπ) := by
  intro M Q hPower
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
  have hCompat (i : I) :
      let A := MarkedIdeal.pullback (Subtype.val : U i → X) Q
      LocWPEquiv A (P i) ∧ A.N = (P i).N := by
    let A : MarkedIdeal (n+1) (CMfd.of (n := n+1) (U i)) :=
      MarkedIdeal.pullback (Subtype.val : U i → X) Q
    have hA : IsInvDomain (n+1) A := InvDomainTowerAlong.isInvDomain_pullback_val (U i) hQ
    obtain ⟨a,b,ha,hb,hEq⟩ := hPower i
    change LocWPEquiv A (P i) ∧ A.N = (P i).N
    have hLeft : LocWPEquiv (X := CMfd.of (n := n+1) (U i)) A (powerMarked (X := CMfd.of (n := n+1) (U i)) A a) :=
      locEquiv_powerMarked (X := CMfd.of (n := n+1) (U i)) (κ := Kinds.wp) rfl A hA ha
    have hRight : LocWPEquiv (X := CMfd.of (n := n+1) (U i)) (P i) (powerMarked (X := CMfd.of (n := n+1) (U i)) (P i) b) :=
      locEquiv_powerMarked (X := CMfd.of (n := n+1) (U i)) (κ := Kinds.wp) rfl (P i) (hP i) hb
    have hAD : IsInvDomain (n+1) (powerMarked (X := CMfd.of (n := n+1) (U i)) A a) := powerMarked_isInvDomain (X := CMfd.of (n := n+1) (U i)) A hA ha
    have hPD : IsInvDomain (n+1) (powerMarked (X := CMfd.of (n := n+1) (U i)) (P i) b) := powerMarked_isInvDomain (X := CMfd.of (n := n+1) (U i)) (P i) (hP i) hb
    have hCompare : LocWPEquiv (X := CMfd.of (n := n+1) (U i)) (powerMarked (X := CMfd.of (n := n+1) (U i)) A a) (powerMarked (X := CMfd.of (n := n+1) (U i)) (P i) b) :=
      locWPEquiv_of_restrictEquiv (X := CMfd.of (n := n+1) (U i)) hAD hPD hEq
    exact ⟨hLeft.trans (hCompare.trans hRight.symm), hEq.N_eq⟩
  have hCan := initial_canonical_of_weakTest_cover Q hQ rfl U P hP r hMark hCompat
    (fun x hx => hCover x (hTop x hx)) D hD m hCentre π hπ
  have hMax : D = maxLocus (R.inv Q (.refl : BlowupTower X X)) Q.cosupp := by
    exact hCan.2.resolve_left hD.ne_empty
  obtain ⟨x,hx⟩ := hD
  have hxQ : x ∈ Q.cosupp :=
    (show x ∈ maxLocus (R.inv Q (.refl : BlowupTower X X)) Q.cosupp from hMax ▸ hx).1
  have hCompare := initial_maxLocus_markOne_eq_topMark (X := X) (vanishingIdeal (n := n+1) W)
    hM hq hUpper ⟨x,hTop x hxQ⟩
  exact ⟨trivial, Or.inr (hMax.trans hCompare.symm)⟩


end Hironaka.HironakaG8InitialWeightedCoverTies
