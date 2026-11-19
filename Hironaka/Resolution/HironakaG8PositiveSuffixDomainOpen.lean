import Hironaka.Resolution.HironakaG8CentreDomainData
import Hironaka.Resolution.HironakaG8PositiveBornDomainOpen
import Hironaka.Resolution.HironakaG11SuffixAllTraceDirectrix

/-! # Positive suffix trace transfer from a common local domain -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8PositiveSuffixDomainOpen
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold HomogenizedGlueingTower NormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen GermIdealOrder DivisorExponentAlong
  HironakaG8LocalHistory HironakaG11InvBMClass HironakaG11InvBMLower HironakaG11SuffixAllTraceDirectrix
open ResolutionInvariantSpec (IsInvDomain)

/-- A common local domain suffices for positive-born all-member transfer. -/
theorem positive_suffix_all_traces_transfer_on_domain_open
    {n : ℕ} (hn : 0 < n) {X Y Z : CMfd.{0} n} (C₀ D₀ : MarkedIdeal n X)
    (hC₀ : C₀.IsWellFormed) (hD₀ : D₀.IsWellFormed) (hdC : 1 ≤ C₀.d) (F : List (Set X))
    (h : LocWPEquiv {C₀ with E := F ++ C₀.E} {D₀ with E := F ++ C₀.E})
    (hE : IsSNCDivisor n (F ++ C₀.E)) (hd : D₀.d = C₀.d) (hdim : SameCarrierDim C₀ D₀)
    {C : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π)
    (hC : C₀.IsAdmissibleCentre C) (hD : D₀.IsAdmissibleCentre C)
    (G : Opens X)
    (hCG : IsInvDomain n (MarkedIdeal.pullback (Subtype.val : G → X) C₀))
    (hDG : IsInvDomain n (MarkedIdeal.pullback (Subtype.val : G → X) D₀))
    (T : BlowupTower Y Z) (hTC : IsGeoTestTower (C₀.geoTransform C π) T)
    (hTD : IsGeoTestTower (D₀.geoTransform C π) T)
    {S : List (Set Z)} (hS : ∀ K ∈ S, IsClosed K) (e : ℕ) {z : Z}
    (hzC : z ∈ strictAlong T (C₀.geoTransform C π).N)
    (hzBorn : z ∈ strictAlong T (π ⁻¹' C))
    (hdiv : IsDivNearAlong n (strictAlong T (C₀.geoTransform C π).N)
      (exceptionalTermBM (n := n) S e) (strictAlong T (π ⁻¹' C)) 1 z)
    (hzG : π (T.proj z) ∈ G)
    (hpos : 0 < divExpAlong n (geoTransformAlong (C₀.geoTransform C π) T).N
      (geoTransformAlong (C₀.geoTransform C π) T).ideal (strictAlong T (π ⁻¹' C)) z)
    (hsource : ∀ K ∈ S, ∃ H : Set X, IsClosedSubmanifold n H ∧
      IsClosedSubmanifold n (geoStrictTransform π C H) ∧
      K = strictAlong T (geoStrictTransform π C H) ∧
      ∀ᶠ x in 𝓝 (π (T.proj z)), x ∈ C → x ∈ H) :
    ∀ᶠ w in 𝓝 z, w ∈ strictAlong T (D₀.geoTransform C π).N →
      w ∈ strictAlong T (π ⁻¹' C) → ∀ K ∈ S, w ∈ K := by
  let P : MarkedIdeal n X := {C₀ with E := F ++ C₀.E}
  let Q : MarkedIdeal n X := {D₀ with E := F ++ C₀.E}
  have hStepC : IsGeoTestTower C₀ (BlowupTower.step (.refl : BlowupTower X X) C π hπ) := ⟨trivial,hC⟩
  have hStepD : IsGeoTestTower D₀ (BlowupTower.step (.refl : BlowupTower X X) C π hπ) := ⟨trivial,hD⟩
  have hDomC : (C₀.geoTransform C π).IsWellFormed :=
    MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hC₀ _ hStepC
  have hDomD : (D₀.geoTransform C π).IsWellFormed :=
    MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hD₀ _ hStepD
  have hBornC : π ⁻¹' C ∈ (C₀.geoTransform C π).E := by
    change π ⁻¹' C ∈ C₀.E.map (geoStrictTransform π C) ++ [π ⁻¹' C]
    simp
  have hBornD : π ⁻¹' C ∈ (D₀.geoTransform C π).E := by
    change π ⁻¹' C ∈ D₀.E.map (geoStrictTransform π C) ++ [π ⁻¹' C]
    simp
  have hhigh := HironakaG8PositiveBornDomainOpen.above_mark_of_positive_born_on_domain_open
    C₀ hC₀ hC hπ T hTC G hCG hzG (by rw [N_geoTransformAlong]; exact hzC) hzBorn hpos
  have hcos : C₀.cosupp = D₀.cosupp := h.cosupp_eq_base
  have hdata := HironakaG8CentreDomainData.centre_data_of_domain_open C₀ D₀ hC₀ hD₀ hcos
    hC.2.1 G hCG hDG hzG hhigh
  exact suffix_all_traces_transfer_of_above_mark hn P Q h hC₀.isClosedSubmanifold_N
    hD₀.isClosedSubmanifold_N hC₀.isCoherent hD₀.isCoherent hE hdC hd hdim hπ
    hC.subset_N hD.subset_N _ _ hDomC hDomD rfl rfl hBornC hBornD T hTC hTD hS e
    hzC hzBorn hdiv hdata hsource

end
end Hironaka.HironakaG8PositiveSuffixDomainOpen
