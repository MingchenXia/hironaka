import Hironaka.Resolution.HironakaG4UnitResidualTrace
import Hironaka.Resolution.HironakaG4PreparedResidualTrace
import Hironaka.Resolution.HironakaIntrinsicCarrierBoundaryCharts

/-! The actual residual slice gives a free-coordinate trace in the unit case. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4WindowUnitTrace
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  NormalCrossings BlowupFlatCoordinates DivisorExponentAlong MonomialPartAlong
  NonmonomialTransformAlong RestrictedIdealExtension RelativePrincipalizationSpan
  HironakaG4PreparedResidualTrace HironakaIntrinsicCarrierBoundaryCharts
  HironakaG4UnitResidualTrace HironakaG4PreparedCentreCoordinates HironakaSharpOriginalMemberProduct
  HironakaSharpOriginalProductTraceOrder

variable {n : ℕ} {X : CMfd.{u} n}

/-- At a monomial-unit point, the protected slice equation forces the
selected actual old member to have unit times the free slice coordinate as
its trace on the carrier. -/
theorem exists_window_unit_trace (hn : 0 < n)
    {N Haux H : Set X} {F B L : List (Set X)} {x : X}
    (hEF : IsSNCDivisor n (Haux :: F))
    (hTF : IsTransverse n N (Haux :: F))
    (hL : IsSNCDivisor n L) (hHL : H ∈ L) (hxN : x ∈ N) (hxH : x ∈ Haux)
    (hI : (restrictOn n N (vanishingIdeal (n := n) H)).IsCoherent)
    (hnz : IsNonzeroAlongAt N (restrictOn n N (vanishingIdeal (n := n) H)) x)
    (hunit : (monomialPartAlong n N (restrictOn n N (vanishingIdeal (n := n) H)) B).mem x 1)
    (hJZ : ∀ g, (nonmonomialPartAlong n N (restrictOn n N (vanishingIdeal (n := n) H)) B).mem x g ↔
      (vanishingIdeal (n := n) (N ∩ Haux)).mem x g) :
    ∃ (k : ℕ) (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
      (p : Fin (Haux :: F).length → Fin n) (t : Fin n) (f a : X → ℂ),
      Φ.source ⊆ (chartAt (ComplexModel n) x).target ∧ Φ.toFun (chartAt (ComplexModel n) x x) = 0 ∧
      p ⟨0, by simp⟩ = t ∧ t.val < k ∧
      (∀ i, x ∈ (Haux :: F).get i → (p i).val < k) ∧
      Set.InjOn p {i | x ∈ (Haux :: F).get i} ∧
      (∀ z ∈ flatDomain Φ, ∀ i, z ∈ (Haux :: F).get i ↔
        x ∈ (Haux :: F).get i ∧ flatCoord Φ (p i) z = 0) ∧
      (∀ {y : X}, y ∈ (chartAt (ComplexModel n) x).source →
        chartAt (ComplexModel n) x y ∈ Φ.source →
          (y ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ complexCoordinatePlane n k)) ∧
      HolomorphicAt n f x ∧ HolomorphicAt n a x ∧ a x ≠ 0 ∧
      (∀ g, (vanishingIdeal (n := n) H).mem x g ↔ IsInSpanAt (n := n) (· = f) x g) ∧
      ∀ᶠ y in 𝓝 x, y ∈ N → f y = a y * flatCoord Φ t y := by
  obtain ⟨k, hk, Φ, p, hsrc, h0, hlt, hinj, hflat⟩ :=
    exists_centered_full_boundary_chart hn hEF hTF x hxN
  let t : Fin n := p ⟨0, by simp⟩
  have ht : t.val < k := hlt ⟨0, by simp⟩ hxH
  have hNflat : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x y ∈ Φ.source →
        (y ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ complexCoordinatePlane n k) :=
    fun hy hyΦ => (hflat _ ⟨hy, hyΦ⟩).1
  let S : Finset (Fin n) := Finset.univ.filter fun j => k ≤ j.val
  have hNS : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x y ∈ Φ.source →
        (y ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ coordSubspace S) := by
    intro y hy hyΦ
    rw [coordSubspace_eq_complexCoordinatePlane]
    exact hNflat hy hyΦ
  have htS : t ∉ S := by simp [S]; omega
  have hZflat : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x y ∈ Φ.source →
        (y ∈ N ∩ Haux ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ coordSubspace (S ∪ {t})) := by
    intro y hy hyΦ
    have hH := (hflat y ⟨hy, hyΦ⟩).2 ⟨0, by simp⟩
    change y ∈ Haux ↔ x ∈ Haux ∧ flatCoord Φ t y = 0 at hH
    simp only [hxH, true_and] at hH
    rw [mem_inter_iff, hNS hy hyΦ, hH]
    simp [coordSubspace, flatCoord, and_comm]
  obtain ⟨f,hf,hF⟩ := exists_originalMember_principal hn hL hHL x
  have hFI : ∀ g, (restrictOn n N (vanishingIdeal (n := n) H)).mem x g ↔
      HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (· = f) x g := by
    intro g
    exact and_congr_right fun _ => restricted_span_iff_principal hf hF g
  have hr : HolomorphicAt n (flatCoord Φ t) x := holomorphicAt_flatCoord Φ t (mem_flatDomain_self Φ)
  have hJ' : ∀ g, (nonmonomialPartAlong n N (restrictOn n N (vanishingIdeal (n := n) H)) B).mem x g ↔
      HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (· = flatCoord Φ t) x g := by
    intro g
    exact (hJZ g).trans (vanishingIdeal_coordinate_trace_mem_iff Φ S t htS hsrc h0 hNS hZflat g)
  obtain ⟨a,ha,hax,heq⟩ := exists_unit_trace_of_monomial_unit hI hnz hunit hf hr hFI hJ'
  exact ⟨k,Φ,p,t,f,a,hsrc,h0,rfl,ht,hlt,hinj,(fun z hz => (hflat z hz).2),hNflat,hf,ha,hax,hF,heq⟩

end
end Hironaka.HironakaG4WindowUnitTrace
