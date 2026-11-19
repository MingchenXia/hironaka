import Hironaka.Resolution.HironakaG1OriginalUnequalMarkCanonical
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8CanonicalTwoPairFullCuts
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism ResolutionInvariantSpec CanonicalCentres
  HironakaG8LocalHistory HironakaG11InvBMClass DivisorExponentAlong
  HironakaG1OriginalTwoPairCanonicalCuts HironakaG1OriginalUnequalMarkCanonical

/-- Full native invariant cuts at any bound from first-side canonical
histories, with equal carrier dimensions and the actual scaled exponents. -/
theorem canonical_two_pair_full_cuts {n k : ℕ} (hn : 0<n)
    {X₁ X₂ Y₁ Y₂ : CMfd.{0} n} (P Q : MarkedIdeal n X₁) (R S : MarkedIdeal n X₂)
    (hP : IsInvDomain k P) (hQ : IsInvDomain k Q) (hR : IsInvDomain k R) (hS : IsInvDomain k S)
    (hL₁ : LocWPEquiv P Q) (hDim₁ : SameCarrierDim P Q)
    (hI₁ : ∀ H ∈ P.E, ∀ x ∈ P.cosupp, x ∈ H →
      Q.d * divExpAlong n P.N P.ideal H x = P.d * divExpAlong n Q.N Q.ideal H x)
    (hL₂ : LocWPEquiv R S) (hDim₂ : SameCarrierDim R S)
    (hI₂ : ∀ H ∈ R.E, ∀ x ∈ R.cosupp, x ∈ H →
      S.d * divExpAlong n R.N R.ideal H x = R.d * divExpAlong n S.N S.ideal H x)
    (hMP : P.d=R.d) (hMQ : Q.d=S.d)
    (T₁ : BlowupTower X₁ Y₁) (T₂ : BlowupTower X₂ Y₂)
    (hCanP : IsCanonical P ((invFamily hn k).inv P) T₁)
    (hCanR : IsCanonical R ((invFamily hn k).inv R) T₂)
    (x : Y₁) (y : Y₂) (hx : x ∈ (geoTransformAlong P T₁).cosupp)
    (hy : y ∈ (geoTransformAlong R T₂).cosupp) :
    ((invFamily hn k).inv P T₁ x < (invFamily hn k).inv R T₂ y ↔
     (invFamily hn k).inv Q T₁ x < (invFamily hn k).inv S T₂ y) := by
  have hCanQ := (invFamily_isCanonical_iff_of_local hn P Q hP hQ hL₁ hDim₁ hI₁ T₁).mp hCanP
  have hCanS := (invFamily_isCanonical_iff_of_local hn R S hR hS hL₂ hDim₂ hI₂ T₂).mp hCanR
  exact canonicalTwoPairCuts_invFamily hn k P Q R S hP hQ hR hS hL₁ hDim₁ hI₁ hL₂ hDim₂ hI₂
    hMP hMQ trivial trivial trivial trivial T₁ T₂ hCanP hCanQ hCanR hCanS x hx y hy
end
end Hironaka.HironakaG8CanonicalTwoPairFullCuts
