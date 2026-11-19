import Hironaka.Resolution.HironakaG11InvBMClass
import Hironaka.Resolution.HironakaG8LocalHistory

/-! Ordinary two-pair strict cuts on ACTUAL original canonical histories.
Blueprint FIRST: hironaka-g1-original-two-pair-canonical-cuts.tex.
This is the explicit shared induction contract and genuine constant base;
no successor or unequal-mark canonicality claim is made here. -/
set_option autoImplicit false
namespace Hironaka.HironakaG1OriginalTwoPairCanonicalCuts
noncomputable section
open Hironaka.HolomorphicIdealSheaves BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec HomogenizedIdealAlong HironakaG8LocalHistory HironakaG11InvBMClass
  DivisorExponentAlong

/-- The ordinary two-pair cut property, with only an explicit source guard
distinguishing the all-record and maximal-order forms. The four histories
are genuinely canonical for their actual respective evaluators. -/
def TwoPairCanonicalCutsFor {n : ℕ} {Λ : Type} [LinearOrder Λ]
    (C : ∀ {X : CMfd.{0} n}, MarkedIdeal n X → Prop) (k : ℕ)
    (inv : ∀ {X : CMfd.{0} n}, MarkedIdeal n X → ∀ {Y : CMfd.{0} n}, BlowupTower X Y → Y → Λ) : Prop :=
  ∀ {X₁ X₂ : CMfd.{0} n} (P Q : MarkedIdeal n X₁) (R S : MarkedIdeal n X₂),
    IsInvDomain k P → IsInvDomain k Q → IsInvDomain k R → IsInvDomain k S →
    LocWPEquiv P Q → SameCarrierDim P Q →
    (∀ H ∈ P.E, ∀ x ∈ P.cosupp, x ∈ H →
      Q.d * divExpAlong n P.N P.ideal H x = P.d * divExpAlong n Q.N Q.ideal H x) →
    LocWPEquiv R S → SameCarrierDim R S →
    (∀ H ∈ R.E, ∀ x ∈ R.cosupp, x ∈ H →
      S.d * divExpAlong n R.N R.ideal H x = R.d * divExpAlong n S.N S.ideal H x) →
    P.d = R.d → Q.d = S.d → C P → C Q → C R → C S →
    ∀ {Y₁ Y₂ : CMfd.{0} n} (T₁ : BlowupTower X₁ Y₁) (T₂ : BlowupTower X₂ Y₂),
      IsCanonical P (inv P) T₁ → IsCanonical Q (inv Q) T₁ →
      IsCanonical R (inv R) T₂ → IsCanonical S (inv S) T₂ →
      ∀ x ∈ (geoTransformAlong P T₁).cosupp, ∀ y ∈ (geoTransformAlong R T₂).cosupp,
        (inv P T₁ x < inv R T₂ y ↔ inv Q T₁ x < inv S T₂ y)

/-- The full ordinary-record contract retains all four actual canonical
histories and all actual native class hypotheses. -/
abbrev CanonicalTwoPairCuts {n : ℕ} {Λ : Type} [LinearOrder Λ] (k : ℕ)
    (inv : ∀ {X : CMfd.{0} n}, MarkedIdeal n X → ∀ {Y : CMfd.{0} n}, BlowupTower X Y → Y → Λ) : Prop :=
  TwoPairCanonicalCutsFor (fun {_} _ => True) k inv

/-- The maximal-order contract changes only the ordinary source guard. -/
abbrev CanonicalMaxOrderTwoPairCuts {n : ℕ} {Λ : Type} [LinearOrder Λ] (k : ℕ)
    (inv : ∀ {X : CMfd.{0} n}, MarkedIdeal n X → ∀ {Y : CMfd.{0} n}, BlowupTower X Y → Y → Λ) : Prop :=
  TwoPairCanonicalCutsFor (fun {_} J => IsMaximalOrderAlong J.N J.ideal J.d) k inv

/-- Any actual ordinary cut property specializes to maximal-order sources. -/
theorem CanonicalTwoPairCuts.toMaxOrder {n k : ℕ} {Λ : Type} [LinearOrder Λ]
    {inv : ∀ {X : CMfd.{0} n}, MarkedIdeal n X → ∀ {Y : CMfd.{0} n}, BlowupTower X Y → Y → Λ}
    (h : CanonicalTwoPairCuts k inv) : CanonicalMaxOrderTwoPairCuts k inv := by
  intro X₁ X₂ P Q R S hP hQ hR hS hPQ hDimPQ hExpPQ hRS hDimRS hExpRS hdPR hdQS _ _ _ _
  exact h P Q R S hP hQ hR hS hPQ hDimPQ hExpPQ hRS hDimRS hExpRS hdPR hdQS
    trivial trivial trivial trivial

/-- The constant actual value gives the ordinary cut base at every bound. -/
theorem canonicalTwoPairCuts_constant {n : ℕ} {Λ : Type} [LinearOrder Λ] (k : ℕ) (l : Λ) :
    CanonicalTwoPairCuts (n := n) k (fun {_} _ {_} _ _ => l) := by
  intro X₁ X₂ P Q R S _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Y₁ Y₂ T₁ T₂ _ _ _ _ x _ y _
  exact Iff.rfl

/-- The literal original dimension-zero resolution invariant has the
constant-base contract, with no future numerical premise. -/
theorem canonicalTwoPairCuts_ofDimZero {n : ℕ} {Λ : Type} [LinearOrder Λ] (l : Λ) :
    CanonicalTwoPairCuts (n := n) 0
      (ResolutionInvariantSeq.ResolutionInvariant.ofDimZero.{0,0} (n := n) Λ l).inv :=
  canonicalTwoPairCuts_constant 0 l

end
end Hironaka.HironakaG1OriginalTwoPairCanonicalCuts
