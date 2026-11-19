import Hironaka.Resolution.HironakaG4PreparedResidualTrace
import Hironaka.Resolution.HironakaIntrinsicCarrierBoundaryCharts
import Hironaka.Blowup.NormalCrossingsComparison

/-! Prepare the actual residual trace directly from a protected slice window. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff BigOperators
universe u
namespace Hironaka.HironakaG4WindowResidualTrace
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  NormalCrossings NormalCrossingsComparison BlowupFlatCoordinates DivisorExponentAlong MonomialPartAlong
  RestrictedIdealExtension HironakaG4PreparedResidualTrace HironakaIntrinsicCarrierBoundaryCharts

variable {n : ℕ} {X : CMfd.{u} n}

/-- The geometric data delivered by a protected slice window construct the
adapted chart and residual trace equation internally. -/
theorem exists_window_gamma_trace (hn : 0 < n)
    {N Haux H : Set X} {F B L : List (Set X)} {J : GermIdeal n X} {x : X}
    (hN : IsClosedSubmanifold n N) (hEF : IsSNCDivisor n (Haux :: F))
    (hTF : IsTransverse n N (Haux :: F)) (hBsub : B.Sublist (Haux :: F))
    (hL : IsSNCDivisor n L) (hHL : H ∈ L) (hxN : x ∈ N) (hxH : x ∈ Haux)
    (hI : (restrictOn n N (vanishingIdeal (n := n) H)).IsCoherent)
    (hnz : ∀ y ∈ N, IsNonzeroAlongAt N (restrictOn n N (vanishingIdeal (n := n) H)) y)
    (hfactor : restrictOn n N (vanishingIdeal (n := n) H) = restrictOn n N
      ((monomialPartAlong n N (restrictOn n N (vanishingIdeal (n := n) H)) B).mul J))
    (hgamma : ¬ (monomialPartAlong n N (restrictOn n N (vanishingIdeal (n := n) H)) B).mem x 1)
    (hJZ : ∀ g, J.mem x g ↔ (vanishingIdeal (n := n) (N ∩ Haux)).mem x g) :
    ∃ (k : ℕ) (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
      (p : Fin (Haux :: F).length → Fin n) (σ : Fin B.length → Fin n)
      (t : Fin n) (f a : X → ℂ),
      Φ.source ⊆ (chartAt (ComplexModel n) x).target ∧ Φ.toFun (chartAt (ComplexModel n) x x) = 0 ∧
      p ⟨0, by simp⟩ = t ∧ t.val < k ∧ (∀ i, x ∈ B.get i → (σ i).val < k) ∧
      (∀ i, x ∈ (Haux :: F).get i → (p i).val < k) ∧
      Set.InjOn p {i | x ∈ (Haux :: F).get i} ∧
      (∀ z ∈ flatDomain Φ, ∀ i, z ∈ (Haux :: F).get i ↔
        x ∈ (Haux :: F).get i ∧ flatCoord Φ (p i) z = 0) ∧
      (∀ {y : X}, y ∈ (chartAt (ComplexModel n) x).source →
        chartAt (ComplexModel n) x y ∈ Φ.source →
          (y ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ complexCoordinatePlane n k)) ∧
      HolomorphicAt n f x ∧ HolomorphicAt n a x ∧ a x ≠ 0 ∧
      (∀ g, (vanishingIdeal (n := n) H).mem x g ↔ IsInSpanAt (n := n) (· = f) x g) ∧
      let d : X → ℂ := fun z => ∏ i ∈ Finset.univ.filter (fun i => x ∈ B.get i),
        flatCoord Φ (σ i) z ^ divExpAlong n N (restrictOn n N (vanishingIdeal (n := n) H)) (B.get i) x
      d x = 0 ∧ ∀ᶠ y in 𝓝 x, y ∈ N → f y = a y * (d y * flatCoord Φ t y) := by
  obtain ⟨k, hk, Φ, p, hsrc, h0, hlt, hinj, hflat⟩ :=
    exists_centered_full_boundary_chart hn hEF hTF x hxN
  let t : Fin n := p ⟨0, by simp⟩
  have ht : t.val < k := hlt ⟨0, by simp⟩ hxH
  obtain ⟨emb, hemb⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hBsub
  let σ : Fin B.length → Fin n := fun i => p (emb i)
  have hB : IsSNCDivisor n B := isSNCDivisor_of_sublist hEF hBsub
  have hBT : IsTransverse n N B := isTransverse_of_forall_mem hTF (fun H hH => hBsub.subset hH)
  have hσk : ∀ i, x ∈ B.get i → (σ i).val < k := by
    intro i hi
    exact hlt (emb i) (by rw [← hemb]; exact hi)
  have hσinj : Set.InjOn σ {i | x ∈ B.get i} := by
    intro i hi j hj hij
    apply emb.injective
    apply hinj ?_ ?_ hij
    · change x ∈ (Haux :: F).get (emb i)
      rw [← hemb]
      exact hi
    · change x ∈ (Haux :: F).get (emb j)
      rw [← hemb]
      exact hj
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
  have hA : ∀ i, x ∈ B.get i → ∀ {y : X}, y ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x y ∈ Φ.source →
        (y ∈ B.get i ↔ Φ.toFun (chartAt (ComplexModel n) x y) (σ i) = 0) := by
    intro i hi y hy hyΦ
    have hh := (hflat y ⟨hy, hyΦ⟩).2 (emb i)
    rw [← hemb] at hh
    simp only [hi, true_and] at hh
    exact hh
  obtain ⟨hd, f, a, hf, ha, hax, hF, heq⟩ := exists_prepared_gamma_trace hn hN hB hBT hL hHL
    hxN hI hnz hfactor hgamma hJZ Φ hsrc h0 k S t htS hNflat hNS hZflat σ hA hσk hσinj
  exact ⟨k, Φ, p, σ, t, f, a, hsrc, h0, rfl, ht, hσk, hlt, hinj,
    (fun z hz => (hflat z hz).2), hNflat, hf, ha, hax, hF, hd, heq⟩

end
end Hironaka.HironakaG4WindowResidualTrace
