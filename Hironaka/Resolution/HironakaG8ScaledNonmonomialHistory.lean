import Hironaka.Resolution.HironakaG8ScaledExponentHistory
import Hironaka.Resolution.HironakaG8ScaledNonmonomial
import Hironaka.Resolution.HironakaActualProjectedNormalizedOrderDetection
import Hironaka.Resolution.HironakaCoherentTransformExtension

/-! Actual controlled-suffix nonmonomial orders from initial scaled exponents.
Blueprint: `hironaka-g8-scaled-nonmonomial-history.tex`. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8ScaledNonmonomialHistory
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec
  NonmonomialOrderLocal DivisorExponentAlong HironakaG8LocalHistory HironakaG8ProjEquiv
  HironakaG8ScaledExponentHistory HironakaG8ScaledNonmonomial
  HironakaActualProjectedNormalizedOrderDetection HironakaCoherentTransformExtension
  InvDomainTowerAlong MarkedIdealEquivalence.MarkedIdeal
variable {n : ℕ} {X : CMfd.{0} n}

/-- Initial scaled boundary exponent agreement on the cosupport yields
scaled nonmonomial order on every actual common controlled suffix. -/
theorem scaled_nmOrd_of_initial_exponents {k l : ℕ} (hn : 0 < n)
    (P Q : MarkedIdeal n X) (hP : IsInvDomain k P) (hQ : IsInvDomain l Q)
    (hN : Q.N = P.N) (hE : Q.E = P.E) (hL : LocWPEquiv P Q)
    (hInitial : ∀ H ∈ P.E, ∀ y ∈ P.cosupp, y ∈ H →
      Q.d * divExpAlong n P.N P.ideal H y = P.d * divExpAlong n Q.N Q.ideal H y)
    {Y : CMfd.{0} n} (T : BlowupTower X Y) (hT : IsGeoTestTower P T) :
    ∀ y ∈ (geoTransformAlong P T).cosupp,
      Q.d * nmOrd (geoTransformAlong P T) y = P.d * nmOrd (geoTransformAlong Q T) y := by
  let PT := geoTransformAlong P T
  let QT := geoTransformAlong Q T
  have hTQ : IsGeoTestTower Q T := (hL.wEquiv.2 T).1.mp hT
  have hPT := isInvDomain_geoTransformAlong hP T hT
  have hQT := isInvDomain_geoTransformAlong hQ T hTQ
  have hLT := hL.geoTransformAlong T hT
  have hNT : QT.N = PT.N := geoTransformAlong_N_eq_of_N_eq hN T
  have hET : QT.E = PT.E := E_geoTransformAlong_eq hE T
  have hEx := scaled_exponents_of_initial_agreement P Q hP hQ hN hE hL hInitial T hT
  intro y hy
  have hyQ : y ∈ QT.cosupp := hLT.wEquiv.cosupp_eq ▸ hy
  have hOrd := (normalized_ordinary_order_of_projected_wEquiv PT QT hPT hQT y hy hyQ
    hNT hET hLT.projEquiv.projectionTest_wEquiv).2.2
  have hExp : ∀ H ∈ PT.E, y ∈ H →
      QT.d * divExpAlong n PT.N PT.ideal H y = PT.d * divExpAlong n QT.N QT.ideal H y := by
    intro H hH hyH
    simpa [PT,QT,d_geoTransformAlong] using hEx H hH y hy hyH
  have hNm := scaled_nmOrd_of_scaled_data hn PT QT hPT hQT hNT hET (PT.cosupp_subset_N hy) hOrd hExp
  simpa [PT,QT,d_geoTransformAlong] using hNm
end
end Hironaka.HironakaG8ScaledNonmonomialHistory
