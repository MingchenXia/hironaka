import Hironaka.Resolution.HironakaG1OriginalUnequalMarkCanonical
import Hironaka.Resolution.HironakaG1CoefficientCarrierClassData

/-! Actual further coefficients AFTER the first full original bar.
Both support gaps and the native normalized exponent law are derived.
No unrecoded-source/bar or padded-source canonicality is asserted.
Blueprint FIRST: hironaka-g1-coefficient-recoding-canonical.tex. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1CoefficientRecodingCanonical
noncomputable section
open Hironaka.HolomorphicIdealSheaves BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec CanonicalCentres
  HomogenizedIdealAlong StepOneValue DivisorExponentAlong ResolutionDriver
  HironakaG8LocalHistory HironakaG11InvBMClass HironakaG8CoefficientBoundaryLocal
  HironakaG8HomStable HironakaActualInitialNonmonomialCoefficientBoundary
  HironakaG8GapNormalizedExponent
  HironakaG1CoefficientBarClassData HironakaG1CoefficientCarrierClassData
  HironakaG1OriginalUnequalMarkCanonical

/-- ENTIRE actual bar and further coefficient records, at their true native
marks, with the INITIAL normalized exponent law derived from BOTH gaps. -/
theorem bar_further_coefficient_data {n k : ℕ} (hn : 0 < n) {X : CMfd.{0} n}
    (P : MarkedIdeal n X) (hP : IsInvDomain k P) :
    let C := barMarked P
    let D := coeffMarkedAlong C
    IsInvDomain k C ∧ IsInvDomain k D ∧ C.N = P.N ∧ D.N = P.N ∧
      C.E = P.E ∧ D.E = P.E ∧ LocWPEquiv C D ∧ SameCarrierDim C D ∧
      HasCosupportGap C ∧ HasCosupportGap D ∧
      (∀ H ∈ C.E, ∀ x ∈ C.cosupp, x ∈ H →
        D.d * divExpAlong n C.N C.ideal H x = C.d * divExpAlong n D.N D.ideal H x) := by
  let C := barMarked P
  let D := coeffMarkedAlong C
  have hH := hom_isInvDomain P hP
  have hC : IsInvDomain k C := coefficient_isInvDomain (homMarkedAlong P) hH
  have hD : IsInvDomain k D := coefficient_isInvDomain C hC
  have hL : LocWPEquiv C D := coefficient_local_any_boundary C hC
  have hDim : SameCarrierDim C D := SameCarrierDim.of_N_eq rfl
  have hGapC : HasCosupportGap C := coefficient_hasCosupportGap (homMarkedAlong P) hH
  have hGapD : HasCosupportGap D := coefficient_hasCosupportGap C hC
  exact ⟨hC,hD,rfl,rfl,rfl,rfl,hL,hDim,hGapC,hGapD,
    normalized_exponents_of_gap_sameCarrierDim hn C D hC hD hL hDim hGapC hGapD⟩

/-- SAME original geometric history; second-side canonicality is derived,
and no equality of the unequal native raw values is claimed. -/
theorem invFamily_isCanonical_bar_coefficient_iff {n k : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (P : MarkedIdeal n X) (hP : IsInvDomain k P)
    (T : BlowupTower X Y) :
    IsCanonical (barMarked P) ((invFamily hn k).inv (barMarked P)) T ↔
      IsCanonical (coeffMarkedAlong (barMarked P))
        ((invFamily hn k).inv (coeffMarkedAlong (barMarked P))) T := by
  obtain ⟨hC,hD,_hCN,_hDN,_hCE,_hDE,hL,hDim,_hGapC,_hGapD,hExp⟩ :=
    bar_further_coefficient_data hn P hP
  exact invFamily_isCanonical_iff_of_local hn (barMarked P) (coeffMarkedAlong (barMarked P))
    hC hD hL hDim hExp T

/-- The ambient original canonical invariant, on the actual whole recodings. -/
theorem canonicalInvariant_isCanonical_bar_coefficient_iff {n : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (P : MarkedIdeal n X) (hP : IsInvDomain n P)
    (T : BlowupTower X Y) :
    IsCanonical (barMarked P) ((canonicalInvariant n).inv (barMarked P)) T ↔
      IsCanonical (coeffMarkedAlong (barMarked P))
        ((canonicalInvariant n).inv (coeffMarkedAlong (barMarked P))) T := by
  obtain ⟨hC,hD,_hCN,_hDN,_hCE,_hDE,hL,hDim,_hGapC,_hGapD,hExp⟩ :=
    bar_further_coefficient_data hn P hP
  exact canonicalInvariant_isCanonical_iff_of_local (barMarked P)
    (coeffMarkedAlong (barMarked P)) hC hD hL hDim hExp T

/-- The actual full maximum centre after the further coefficient recoding,
on the SAME canonical prefix and with the entire old/born boundary. -/
theorem invFamily_maxLocus_bar_coefficient {n k : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (P : MarkedIdeal n X) (hP : IsInvDomain k P)
    (T : BlowupTower X Y)
    (hc : IsCanonical (barMarked P) ((invFamily hn k).inv (barMarked P)) T) :
    maxLocus ((invFamily hn k).inv (barMarked P) T) (geoTransformAlong (barMarked P) T).cosupp =
      maxLocus ((invFamily hn k).inv (coeffMarkedAlong (barMarked P)) T)
        (geoTransformAlong (coeffMarkedAlong (barMarked P)) T).cosupp := by
  let C := barMarked P
  let D := coeffMarkedAlong C
  obtain ⟨hC,hD,_hCN,_hDN,_hCE,_hDE,hL,hDim,_hGapC,_hGapD,hExp⟩ :=
    bar_further_coefficient_data hn P hP
  have hcD := (invFamily_isCanonical_bar_coefficient_iff hn P hP T).mp hc
  have hTest := (invFamily hn k).isInvValue.isGeoTestTower_of_isCanonical hC T hc
  have hCos := (hL.wEquiv.2 T).2 hTest
  have hCuts := canonicalTwoPairCuts_invFamily hn k C D C D hC hD hC hD
    hL hDim hExp hL hDim hExp rfl rfl trivial trivial trivial trivial T T hc hcD hc hcD
  rw [←hCos]
  ext x
  constructor
  · rintro ⟨hx,hMax⟩
    refine ⟨hx,fun y hy => ?_⟩
    exact le_of_not_gt (fun h => not_lt_of_ge (hMax y hy) ((hCuts x hx y hy).mpr h))
  · rintro ⟨hx,hMax⟩
    refine ⟨hx,fun y hy => ?_⟩
    exact le_of_not_gt (fun h => not_lt_of_ge (hMax y hy) ((hCuts x hx y hy).mp h))

/-- The literal ambient canonical maximum centre, with no special-stratum
or maximum-locus nonemptiness assumption. -/
theorem canonicalInvariant_maxLocus_bar_coefficient {n : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (P : MarkedIdeal n X) (hP : IsInvDomain n P)
    (T : BlowupTower X Y)
    (hc : IsCanonical (barMarked P) ((canonicalInvariant n).inv (barMarked P)) T) :
    maxLocus ((canonicalInvariant n).inv (barMarked P) T) (geoTransformAlong (barMarked P) T).cosupp =
      maxLocus ((canonicalInvariant n).inv (coeffMarkedAlong (barMarked P)) T)
        (geoTransformAlong (coeffMarkedAlong (barMarked P)) T).cosupp := by
  cases n with
  | zero => omega
  | succ n => exact invFamily_maxLocus_bar_coefficient (Nat.succ_pos n) P hP T hc

end
end Hironaka.HironakaG1CoefficientRecodingCanonical
