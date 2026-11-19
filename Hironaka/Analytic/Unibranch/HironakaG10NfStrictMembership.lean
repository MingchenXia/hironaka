import Hironaka.Resolution.HironakaG10JointStrictTorsion
import Hironaka.Analytic.HolomorphicGermAlgebra

/-!
# H3 (membership): a chart point with proper strict ideal (or proper pivot torsion) lies on the strict transform

Lane G10N5, run 0081, round 3 (field `strict` of `HironakaG10NfFibreModel.FibreModel`, item H3 of
`G10N5/hfib-H3-route.md`).  On a real-open blowup chart:

* `germ_one` — the germ of the constant function `1` is `1`;
* `mem_strict_of_ne_top` — if the whole strict ideal at a point is proper, the point lies on the (closed) strict
  transform (otherwise `1` vanishes on it near the point);
* `mem_strict_of_pivotTorsion_ne_top` — at a point of the local saturation domain, if the exceptional torsion of the
  joint quotient (the fibre product `Y ×_X X'` in the chart) is proper, the point lies on the strict transform
  (`strict_mem_iff_joint_pivot_power`).

No named input.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG10NfStrictMembership

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka HironakaHolomorphicJetRankLoci HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaRealOpenGeometricStrictSaturation HironakaG10RealOpenStrictTorsionKernel HironakaG10JointStrictTorsion
  BlowupStrictSubmanifold

noncomputable section

section Germ

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The germ of the constant function `1` is `1`. -/
theorem germ_one (y : M) (h : HolomorphicAt n (fun _ : M => (1 : ℂ)) y) :
    actualOriginalFunctionGerm y (fun _ => (1 : ℂ)) h = 1 := by
  apply (actualStalkChartEquiv (n := n) y).injective
  rw [actualOriginalFunctionGerm_chart, map_one]
  unfold chartTranslatedGerm translatedGerm
  exact HolGerm.mk_one

/-- The whole vanishing ideal of a closed set at a point off the set is the unit ideal. -/
theorem wholeVanishing_eq_top_of_not_mem {S : Set M} (hS : IsClosed S) {y : M} (hy : y ∉ S) :
    actualWholeSheafStalkIdeal (vanishingIdeal (n := n) S) y = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have h1 : HolomorphicAt n (fun _ : M => (1 : ℂ)) y := holomorphicAt_const 1
  have hmem : (vanishingIdeal (n := n) S).mem y (fun _ => (1 : ℂ)) :=
    ⟨h1, Filter.mem_of_superset (hS.isOpen_compl.mem_nhds hy) fun _ hz hzS => absurd hzS hz⟩
  have := Ideal.subset_span (s := {g | ∃ (f : M → ℂ) (hf : HolomorphicAt n f y),
    (vanishingIdeal (n := n) S).mem y f ∧ g = actualOriginalFunctionGerm y f hf})
    ⟨fun _ => (1 : ℂ), h1, hmem, rfl⟩
  rwa [germ_one] at this

end Germ

variable (d t : ℕ) (j : Fin t) (b : Fin (d+t) → ℂ) (U : Opens (ComplexModel (d+t))) (W : Set U)

theorem isClosed_realOpenStrictTransform : IsClosed (realOpenStrictTransform d t j b U W) :=
  isClosed_closure

/-- **A point with proper whole strict ideal lies on the strict transform.** -/
theorem mem_strict_of_ne_top (y : realOpenChartDomain d t j b U)
    (h : geometricStrictIdeal d t j b U W y ≠ ⊤) : y ∈ realOpenStrictTransform d t j b U W := by
  by_contra hy
  exact h (wholeVanishing_eq_top_of_not_mem (isClosed_realOpenStrictTransform d t j b U W) hy)

variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  (f : realOpenChartDomain d t j b U → Y) (V : Set Y)
  (h0 : (0 : ComplexModel (d+t)) ∈ U) (hW : IsComplexAnalyticSubset (n := d+t) W)
  (hf : Continuous f) (hland : realOpenStrictTransform d t j b U W ⊆ f ⁻¹' V)

include hf hland in
/-- **A point of the local saturation domain whose joint pivot torsion is proper lies on the strict transform.** -/
theorem mem_strict_of_pivotTorsion_ne_top (y : realOpenChartDomain d t j b U)
    (hy : y ∈ localDomain d t j b U W h0 hW)
    (h : pivotTorsion (n := n) d t j b U W f V y ≠ ⊤) : y ∈ realOpenStrictTransform d t j b U W := by
  refine mem_strict_of_ne_top d t j b U W y fun htop => h ?_
  have h1 : (1 : AmbientStalk d t j b U y) ∈ geometricStrictIdeal d t j b U W y := by
    rw [htop]
    trivial
  obtain ⟨m, hm⟩ := (strict_mem_iff_joint_pivot_power (n := n) d t j b U W f V h0 hW hf hland y hy 1).mp h1
  rw [Ideal.eq_top_iff_one]
  refine ⟨⟨_, m, rfl⟩, ?_⟩
  change pivotClass (n := n) d t j b U W f V y ^ m • (1 : JointQuotient (n := n) d t j b U W f V y) = 0
  rw [smul_eq_mul, mul_one, pivotClass, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  simpa using hm

end

end Hironaka.Analytic.Unibranch.HironakaG10NfStrictMembership
