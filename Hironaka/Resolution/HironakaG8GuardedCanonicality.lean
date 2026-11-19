import Hironaka.Resolution.HironakaG1OriginalTwoPairCanonicalCuts
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8GuardedCanonicality
noncomputable section
open Hironaka.HolomorphicIdealSheaves BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism ResolutionInvariantSpec
  HironakaG8LocalHistory HironakaG11InvBMClass HironakaG1OriginalTwoPairCanonicalCuts
  CanonicalCentres ResolutionDriver DivisorExponentAlong

/-- For any guarded two-pair cut contract, two genuine canonical histories
have the same maximal loci whenever the first is a test. -/
theorem maxLocus_eq_of_guarded_pairCuts {n k : ℕ} {Λ : Type} [LinearOrder Λ]
    (C : ∀ {X : CMfd.{0} n}, MarkedIdeal n X → Prop)
    (inv : ∀ {X : CMfd.{0} n}, MarkedIdeal n X → ∀ {Y : CMfd.{0} n}, BlowupTower X Y → Y → Λ)
    (hCuts : TwoPairCanonicalCutsFor C k inv)
    {X Y : CMfd.{0} n} (P Q : MarkedIdeal n X) (hP : IsInvDomain k P) (hQ : IsInvDomain k Q)
    (hCP : C P) (hCQ : C Q) (hL : LocWPEquiv P Q) (hDim : SameCarrierDim P Q)
    (hInitial : ∀ H ∈ P.E, ∀ x ∈ P.cosupp, x ∈ H →
      Q.d * divExpAlong n P.N P.ideal H x = P.d * divExpAlong n Q.N Q.ideal H x)
    (T : BlowupTower X Y) (hT : IsGeoTestTower P T)
    (hcP : IsCanonical P (inv P) T) (hcQ : IsCanonical Q (inv Q) T) :
    maxLocus (inv P T) (geoTransformAlong P T).cosupp =
      maxLocus (inv Q T) (geoTransformAlong Q T).cosupp := by
  have hCos := (hL.wEquiv.2 T).2 hT
  have hLt := hCuts P Q P Q hP hQ hP hQ hL hDim hInitial hL hDim hInitial rfl rfl
    hCP hCQ hCP hCQ T T hcP hcQ hcP hcQ
  rw [← hCos]
  ext x
  constructor
  · rintro ⟨hx, hMax⟩
    refine ⟨hx, fun y hy => ?_⟩
    exact le_of_not_gt (fun h => not_lt_of_ge (hMax y hy) ((hLt x hx y hy).mpr h))
  · rintro ⟨hx, hMax⟩
    refine ⟨hx, fun y hy => ?_⟩
    exact le_of_not_gt (fun h => not_lt_of_ge (hMax y hy) ((hLt x hx y hy).mp h))

/-- The second canonical history follows from the first: a guarded pair-cut
contract and the genuine first-side canonical-to-test theorem suffice. -/
theorem isCanonical_iff_of_guarded_pairCuts {n k : ℕ} {Λ : Type} [LinearOrder Λ]
    (C : ∀ {X : CMfd.{0} n}, MarkedIdeal n X → Prop)
    (inv : ∀ {X : CMfd.{0} n}, MarkedIdeal n X → ∀ {Y : CMfd.{0} n}, BlowupTower X Y → Y → Λ)
    (hCuts : TwoPairCanonicalCutsFor C k inv)
    {X : CMfd.{0} n} (P Q : MarkedIdeal n X) (hP : IsInvDomain k P) (hQ : IsInvDomain k Q)
    (hCP : C P) (hCQ : C Q) (hL : LocWPEquiv P Q) (hDim : SameCarrierDim P Q)
    (hInitial : ∀ H ∈ P.E, ∀ x ∈ P.cosupp, x ∈ H →
      Q.d * divExpAlong n P.N P.ideal H x = P.d * divExpAlong n Q.N Q.ideal H x)
    (hTest : ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), IsCanonical P (inv P) T → IsGeoTestTower P T) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), IsCanonical P (inv P) T ↔ IsCanonical Q (inv Q) T
  | _, .refl => Iff.rfl
  | _, .step T D π hπ => by
      have ih := isCanonical_iff_of_guarded_pairCuts C inv hCuts P Q hP hQ hCP hCQ hL hDim hInitial hTest T
      change (IsCanonical P (inv P) T ∧ (D = ∅ ∨ D = maxLocus (inv P T) (geoTransformAlong P T).cosupp)) ↔
        (IsCanonical Q (inv Q) T ∧ (D = ∅ ∨ D = maxLocus (inv Q T) (geoTransformAlong Q T).cosupp))
      constructor
      · rintro ⟨hcP, hD⟩
        have hcQ := ih.mp hcP
        exact ⟨hcQ, hD.imp id (fun h => h.trans (maxLocus_eq_of_guarded_pairCuts C inv hCuts P Q
          hP hQ hCP hCQ hL hDim hInitial T (hTest T hcP) hcP hcQ))⟩
      · rintro ⟨hcQ, hD⟩
        have hcP := ih.mpr hcQ
        exact ⟨hcP, hD.imp id (fun h => h.trans (maxLocus_eq_of_guarded_pairCuts C inv hCuts P Q
          hP hQ hCP hCQ hL hDim hInitial T (hTest T hcP) hcP hcQ).symm)⟩
end
end Hironaka.HironakaG8GuardedCanonicality
