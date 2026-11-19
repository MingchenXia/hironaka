import Hironaka.Resolution.HironakaG4ActualResidualMonomial
import Hironaka.Resolution.HironakaG4BornExponentVector

/-! The selected smooth equation and residual slice yield the actual trace factorization. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff BigOperators
universe u
namespace Hironaka.HironakaG4PreparedResidualTrace
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  NormalCrossings BlowupSNCTransform BlowupFlatCoordinates DivisorExponentAlong MonomialPartAlong
  RestrictedIdealExtension RelativePrincipalizationSpan HironakaG4ActualResidualMonomial
  HironakaG4PreparedCentreCoordinates HironakaSharpOriginalMemberProduct
  HironakaSharpOriginalProductTraceOrder

variable {n : ℕ} {X : CMfd.{u} n}

/-- The actual residual slice equation and selected SNC member produce the
unit-times-born-monomial trace identity. -/
theorem exists_prepared_gamma_trace (hn : 0 < n)
    {N H Z : Set X} {E L : List (Set X)} {J : GermIdeal n X} {x : X}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n E) (hT : IsTransverse n N E)
    (hL : IsSNCDivisor n L) (hHL : H ∈ L) (hx : x ∈ N)
    (hI : (restrictOn n N (vanishingIdeal (n := n) H)).IsCoherent)
    (hnz : ∀ y ∈ N, IsNonzeroAlongAt N (restrictOn n N (vanishingIdeal (n := n) H)) y)
    (hfactor : restrictOn n N (vanishingIdeal (n := n) H) = restrictOn n N
      ((monomialPartAlong n N (restrictOn n N (vanishingIdeal (n := n) H)) E).mul J))
    (hgamma : ¬ (monomialPartAlong n N (restrictOn n N (vanishingIdeal (n := n) H)) E).mem x 1)
    (hJZ : ∀ g, J.mem x g ↔ (vanishingIdeal (n := n) Z).mem x g)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0)
    (k : ℕ) (S : Finset (Fin n)) (t : Fin n) (ht : t ∉ S)
    (hNflat : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x y ∈ Φ.source →
        (y ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ complexCoordinatePlane n k))
    (hNS : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x y ∈ Φ.source →
        (y ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ coordSubspace S))
    (hZflat : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x y ∈ Φ.source →
        (y ∈ Z ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ coordSubspace (S ∪ {t})))
    (σ : Fin E.length → Fin n)
    (hA : ∀ i, x ∈ E.get i → ∀ {y : X}, y ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x y ∈ Φ.source →
        (y ∈ E.get i ↔ Φ.toFun (chartAt (ComplexModel n) x y) (σ i) = 0))
    (hσk : ∀ i, x ∈ E.get i → (σ i).val < k) (hσinj : Set.InjOn σ {i | x ∈ E.get i}) :
    let d : X → ℂ := fun z => ∏ i ∈ Finset.univ.filter (fun i => x ∈ E.get i),
      flatCoord Φ (σ i) z ^ divExpAlong n N (restrictOn n N (vanishingIdeal (n := n) H)) (E.get i) x
    d x = 0 ∧ ∃ (f a : X → ℂ), HolomorphicAt n f x ∧ HolomorphicAt n a x ∧ a x ≠ 0 ∧
      (∀ g, (vanishingIdeal (n := n) H).mem x g ↔ IsInSpanAt (n := n) (· = f) x g) ∧
      ∀ᶠ y in 𝓝 x, y ∈ N → f y = a y * (d y * flatCoord Φ t y) := by
  obtain ⟨f, hf, hF⟩ := exists_originalMember_principal hn hL hHL x
  have hFI : ∀ g, (restrictOn n N (vanishingIdeal (n := n) H)).mem x g ↔
      HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (· = f) x g := by
    intro g
    exact and_congr_right fun _ => restricted_span_iff_principal hf hF g
  have hr : HolomorphicAt n (flatCoord Φ t) x := holomorphicAt_flatCoord Φ t (mem_flatDomain_self Φ)
  have hJ' : ∀ g, J.mem x g ↔ HolomorphicAt n g x ∧
      IsInSpanOnAt (n := n) N (· = flatCoord Φ t) x g := by
    intro g
    exact (hJZ g).trans (vanishingIdeal_coordinate_trace_mem_iff Φ S t ht hsrc h0 hNS hZflat g)
  obtain ⟨hd, a, ha, hax, heq⟩ := actual_gamma_trace_unit_monomial hn hN hE hT hI hnz hx
    hfactor hgamma hf hr hFI hJ' Φ hsrc k hNflat σ hA hσk hσinj
  exact ⟨hd, f, a, hf, ha, hax, hF, heq⟩

end
end Hironaka.HironakaG4PreparedResidualTrace
