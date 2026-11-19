import Hironaka.Resolution.HironakaG8InitialHSOrdinaryOrder
import Hironaka.Resolution.HironakaG8OriginalSingularPrefix
import Hironaka.Resolution.HironakaHypersurfaceStageCenters
import Hironaka.Resolution.HironakaG8NativePhaseCertificate

/-! The ordinary first-order comparison on the whole initial cosupport. -/
set_option autoImplicit false
open Set TopologicalSpace Classical
open scoped ENat

namespace Hironaka.HironakaG8InitialWholeCosupportOrder

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal GermIdealOrder
  HironakaHolomorphicJetChartInvariance HironakaHypersurfaceStageCenters
  HironakaEmbeddedAnalytic HironakaEmbeddedBoundary HironakaG8NativePhaseCertificate
  HironakaG8InitialHSOrdinaryOrder HironakaSharpOriginalProductTraceOrder
  ResolutionInvariantSpec ResolutionDriver CanonicalCentres
  HironakaG8OriginalSingularPrefix NonmonomialOrderLocal RestrictEmptyTower

/-- A retained singular HS maximum bounds the original ordinary order at
every point of the initial whole cosupport, including its regular points. -/
theorem whole_initial_ordinary_bound_of_singular_HS {n : ℕ} {X : CMfd.{0} n}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W) (hInt : interior W = ∅)
    (c : X) (hc : c ∈ singularSet (n := n) W)
    (hUpper : ∀ x ∈ singularSet (n := n) W,
      toLex (hilbertSamuelAt (vanishingIdeal (n := n) W) x) ≤
        toLex (hilbertSamuelAt (vanishingIdeal (n := n) W) c)) :
    let M : MarkedIdeal n X := ⟨univ, [], vanishingIdeal (n := n) W, 1⟩
    ∀ x ∈ M.cosupp, nmOrd M x ≤ nmOrd M c := by
  intro M x hx
  let I := vanishingIdeal (n := n) W
  have hM := isInvDomain_boundary hW hInt NormalCrossings.isSNCDivisor_nil
  have hCos : M.cosupp = W := cosupp_mk_vanishingIdeal hW.isClosed []
  have hThreshold (z : X) (q : ℕ) :
      z ∈ cosupport n univ I q ↔ q ≤ nmOrd M z :=
    ordinaryTraceOrder_cosupport_iff (X := X) hM.isWellFormed.isClosedSubmanifold_N
      hM.isWellFormed.isCoherent hM.isNonzeroAlongAt (mem_univ z) q
  by_cases hxSing : x ∈ singularSet (n := n) W
  · exact ordinaryTraceOrder_le_of_hilbertSamuelAt_lex_le I hM.isWellFormed.isCoherent
      (fun z => hM.isNonzeroAlongAt z (mem_univ z)) x c (hUpper x hxSing)
  · have hxW : x ∈ W := hCos ▸ hx
    have hReg : ∃ d, RegularAtDim (n := n) W x d := by
      by_contra! hNone
      exact hxSing (mem_singularSet_iff.mpr ⟨hxW, hNone⟩)
    obtain ⟨d, hd⟩ := hReg
    have hdlt : d < n := by
      apply lt_of_le_of_ne hd.1
      rintro rfl
      have hxi := mem_interior_iff_mem_nhds.mpr (EmbeddedFromResolution.mem_nhds_of_regularAtDim_self hd)
      exact (notMem_empty x) (hInt ▸ hxi)
    have hOrder := order_vanishingIdeal_eq_one_of_regularAtDim hdlt hd
    have hxq := (hThreshold x (nmOrd M x)).mpr le_rfl
    have hq := (le_order_iff (𝔞 := I) (fun _ hg => hg.1)).mpr hxq.2
    change ((nmOrd M x : ℕ) : ℕ∞) ≤ order n univ (vanishingIdeal (n := n) W) x at hq
    rw [hOrder] at hq
    have hcW := (mem_singularSet_iff.mp hc).1
    have hcCos : c ∈ M.cosupp := hCos.symm ▸ hcW
    exact (show nmOrd M x ≤ 1 by exact_mod_cast hq).trans ((hThreshold c 1).mp hcCos)

/-- For the literal first centre of a retained HS phase, the exact initial
whole canonicality criterion consists of the two original-value tie
conditions. The label certifies equality of ordinary order on the centre
and bounds the ordinary order on the whole marked cosupport. -/
theorem native_first_canonical_iff_original_ties {n : ℕ} {X Y Z : CMfd.{0} (n+1)}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n+1) W) (hInt : interior W = ∅)
    (H : ℕ → ℕ)
    (D : Set X) (c : X) (hc : c ∈ D) (π : Y → X)
    (hπ : IsBlowupAlong (n+1) D π) (S : BlowupTower Y Z)
    (hPhase : ActualNativePhase W [] H ((BlowupTower.step .refl D π hπ).append S))
    (hUpper : ∀ x ∈ singularSet (n := n+1) W,
      toLex (hilbertSamuelAt (vanishingIdeal (n := n+1) W) x) ≤ toLex H) :
    let M : MarkedIdeal (n+1) X := ⟨univ, [], vanishingIdeal (n := n+1) W, 1⟩
    let v := (canonicalInvariant (n+1)).inv M (.refl : BlowupTower X X)
    IsCanonical M ((canonicalInvariant (n+1)).inv M) (.step .refl D π hπ) ↔
      (∀ x ∈ D, v x = v c) ∧
      (∀ x ∈ M.cosupp, x ∉ D → nmOrd M x = nmOrd M c → v x < v c) := by
  intro M v
  have hDLevel : D ⊆ phaseLevel W H := by
    exact ((centresOver_append_iff _ (.step .refl D π hπ) S).mp hPhase.supports).1.2
  have hDSing : D ⊆ singularSet (n := n+1) W :=
    fun x hx => hPhase.level_subset_singular (hDLevel hx)
  have hCLabel : hilbertSamuelAt (vanishingIdeal (n := n+1) W) c = H := hDLevel hc
  have hOrdUpper := whole_initial_ordinary_bound_of_singular_HS W hW hInt c (hDSing hc)
    (fun x hx => hCLabel.symm ▸ hUpper x hx)
  have hM := isInvDomain_boundary hW hInt NormalCrossings.isSNCDivisor_nil
  have hEqualOrder (x : X) (hx : x ∈ D) : nmOrd M x = nmOrd M c := by
    let A := vanishingIdeal (n := n+1) W
    have hHS : hilbertSamuelAt A x = hilbertSamuelAt A c := (hDLevel hx).trans hCLabel.symm
    have hMono := ordinaryTraceOrder_le_of_hilbertSamuelAt_lex_le A hM.isWellFormed.isCoherent
      (fun z => hM.isNonzeroAlongAt z (mem_univ z))
    exact le_antisymm (hMono x c (congrArg toLex hHS).le) (hMono c x (congrArg toLex hHS).ge)
  have hDsub : D ⊆ (geoTransformAlong M (.refl : BlowupTower X X)).cosupp := by
    rw [geoTransformAlong_refl, show M.cosupp = W from cosupp_mk_vanishingIdeal hW.isClosed []]
    exact fun x hx => (mem_singularSet_iff.mp (hDSing hx)).1
  have hMax := original_maxLocus_iff_first_order_and_ties W [] (.refl : BlowupTower X X) D c hc hDsub
  simp only [geoTransformAlong_refl] at hMax
  constructor
  · intro hCan
    rcases hCan.2 with hEmpty | hCentre
    · exact False.elim (notMem_empty c (hEmpty ▸ hc))
    · have hTies := hMax.mp (by simpa only [geoTransformAlong_refl] using hCentre)
      exact ⟨fun x hx => (hTies.2.1 x hx).2, hTies.2.2⟩
  · rintro ⟨hTie, hOutside⟩
    have hCentre := hMax.mpr ⟨hOrdUpper, fun x hx => ⟨hEqualOrder x hx, hTie x hx⟩, hOutside⟩
    exact ⟨trivial, Or.inr (by simpa only [geoTransformAlong_refl] using hCentre)⟩

end Hironaka.HironakaG8InitialWholeCosupportOrder
