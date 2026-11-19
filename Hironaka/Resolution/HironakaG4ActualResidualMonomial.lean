import Hironaka.Resolution.HironakaG4ResidualProductUnit
import Hironaka.Resolution.HironakaG4PreparedCentreCoordinates

/-! Actual born-coordinate monomial in the residual trace factorization. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff BigOperators
universe u
namespace Hironaka.HironakaG4ActualResidualMonomial
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  NormalCrossings BlowupSNCTransform BlowupFlatCoordinates DivisorExponentAlong MonomialPartAlong
  RestrictedIdealExtension RelativePrincipalizationSpan HironakaG4ResidualProductUnit
  HironakaSharpOriginalMemberProduct

variable {n : ℕ} {X : CMfd.{u} n}

/-- At a Gamma point the actual monomial-part generator in a supplied
carrier/born adapted chart vanishes, and the original relative generator is
a holomorphic unit times this monomial and the residual generator. -/
theorem actual_gamma_trace_unit_monomial (hn : 0 < n)
    {N : Set X} {E : List (Set X)} {I J : GermIdeal n X} {x : X}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n E) (hT : IsTransverse n N E)
    (hI : I.IsCoherent) (hnz : ∀ y ∈ N, IsNonzeroAlongAt N I y) (hx : x ∈ N)
    (hfactor : I = restrictOn n N ((monomialPartAlong n N I E).mul J))
    (hgamma : ¬ (monomialPartAlong n N I E).mem x 1)
    {f r : X → ℂ} (hf : HolomorphicAt n f x) (hr : HolomorphicAt n r x)
    (hF : ∀ g, I.mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (· = f) x g)
    (hJ : ∀ g, J.mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (· = r) x g)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target) (k : ℕ)
    (hNflat : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x y ∈ Φ.source →
        (y ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ complexCoordinatePlane n k))
    (σ : Fin E.length → Fin n)
    (hA : ∀ i, x ∈ E.get i → ∀ {y : X}, y ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x y ∈ Φ.source →
        (y ∈ E.get i ↔ Φ.toFun (chartAt (ComplexModel n) x y) (σ i) = 0))
    (hσk : ∀ i, x ∈ E.get i → (σ i).val < k) (hσinj : Set.InjOn σ {i | x ∈ E.get i}) :
    let d : X → ℂ := fun z => ∏ i ∈ Finset.univ.filter (fun i => x ∈ E.get i),
      flatCoord Φ (σ i) z ^ divExpAlong n N I (E.get i) x
    d x = 0 ∧ ∃ a : X → ℂ, HolomorphicAt n a x ∧ a x ≠ 0 ∧
      ∀ᶠ y in 𝓝 x, y ∈ N → f y = a y * (d y * r y) := by
  classical
  let d : X → ℂ := fun z => ∏ i ∈ Finset.univ.filter (fun i => x ∈ E.get i),
    flatCoord Φ (σ i) z ^ divExpAlong n N I (E.get i) x
  have hd : HolomorphicAt n d x := holomorphicAt_generator _ _ (mem_flatDomain_self Φ)
  have hD : ∀ g, (monomialPartAlong n N I E).mem x g ↔
      HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (· = d) x g :=
    (monomialPartAlong_mem_iff hsrc hNflat hA hn hN hE hT hI hnz hx hσk hσinj).self_of_nhds
  have hdx : d x = 0 := by
    by_contra hdx
    apply hgamma
    apply (hD 1).mpr
    refine ⟨holomorphicAt_const 1, isInSpanOnAt_eq_iff.mpr ⟨fun y => (d y)⁻¹,
      holomorphicAt_inv hd hdx, ?_⟩⟩
    filter_upwards [hd.continuousAt.eventually_ne hdx] with y hy _
    exact (inv_mul_cancel₀ hy).symm
  exact ⟨hdx, unit_of_relative_residual_product hf hd hr (hnz x hx) hfactor hF hD hJ⟩

end
end Hironaka.HironakaG4ActualResidualMonomial
