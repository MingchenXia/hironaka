import Hironaka.Invariant.MonomialPartAlong

/-! Relative principal generators of a nonzero ideal differ by a unit. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4RelativeGeneratorUnit
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan DivisorExponentAlong MonomialPartAlong

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- Two relative generators of the same ideal, nonzero along the carrier,
are related on the carrier by a holomorphic unit. -/
theorem exists_unit_of_same_nonzero_relative_generator {N : Set X} {I : GermIdeal n X}
    {x : X} {f m : X → ℂ} (hf : HolomorphicAt n f x) (hm : HolomorphicAt n m x)
    (hnz : IsNonzeroAlongAt N I x)
    (hF : ∀ g, I.mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (· = f) x g)
    (hM : ∀ g, I.mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (· = m) x g) :
    ∃ a : X → ℂ, HolomorphicAt n a x ∧ a x ≠ 0 ∧
      ∀ᶠ y in 𝓝 x, y ∈ N → f y = a y * m y := by
  have hselfF : IsInSpanOnAt (n := n) N (· = f) x f :=
    isInSpanOnAt_eq_iff.mpr ⟨1, holomorphicAt_const 1, Eventually.of_forall fun _ _ => by simp⟩
  have hselfM : IsInSpanOnAt (n := n) N (· = m) x m :=
    isInSpanOnAt_eq_iff.mpr ⟨1, holomorphicAt_const 1, Eventually.of_forall fun _ _ => by simp⟩
  obtain ⟨a, ha, haeq⟩ := isInSpanOnAt_eq_iff.mp ((hM f).mp ((hF f).mpr ⟨hf, hselfF⟩)).2
  obtain ⟨b, hb, hbeq⟩ := isInSpanOnAt_eq_iff.mp ((hF m).mp ((hM m).mpr ⟨hm, hselfM⟩)).2
  have hfreq : ∃ᶠ y in 𝓝 x, y ∈ N ∧ m y ≠ 0 := by
    obtain ⟨g, hg, hfreq⟩ := hnz
    obtain ⟨q, hq, hqeq⟩ := isInSpanOnAt_eq_iff.mp ((hM g).mp hg).2
    refine (hfreq.and_eventually hqeq).mono ?_
    intro y h
    refine ⟨h.1.1, ?_⟩
    intro hzero
    exact h.1.2 (by rw [h.2 h.1.1, hzero, mul_zero])
  refine ⟨a, ha, ?_, haeq⟩
  intro hazero
  have hcont : ContinuousAt (fun y => b y * a y) x := hb.continuousAt.mul ha.continuousAt
  have hne : ∀ᶠ y in 𝓝 x, b y * a y ≠ 1 := hcont.eventually_ne (by simp [hazero])
  have hfalse : ∀ᶠ y in 𝓝 x, ¬ (y ∈ N ∧ m y ≠ 0) := by
    filter_upwards [haeq, hbeq, hne] with y h1 h2 h3 hy
    have heq : m y = (b y * a y) * m y := by
      calc m y = b y * f y := h2 hy.1
           _ = b y * (a y * m y) := by rw [h1 hy.1]
           _ = (b y * a y) * m y := by ring
    have hba : b y * a y = 1 := by
      apply mul_right_cancel₀ hy.2
      simpa using heq.symm
    exact h3 hba
  exact hfreq hfalse

end
end Hironaka.HironakaG4RelativeGeneratorUnit
