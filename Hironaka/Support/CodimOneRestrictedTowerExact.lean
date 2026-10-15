/- Complete original restricted-equivalence codimension-one tower proof. -/
import Hironaka.Invariant.CodimOnePartCanonical
import Hironaka.MarkedIdeal.MarkedIdealEquivalence
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.CodimOnePartCanonical
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.HomogenizedGlueingTower Hironaka.MarkedIdealRestrictOpen
  Hironaka.CodimOneSupportAlong Hironaka.MarkedIdealBiholomorphism
  Hironaka.MarkedIdealTowerTransport Hironaka.BoundaryCount
  Hironaka.BlowupStrictSubmanifold Hironaka.GermIdealOrder
  Hironaka.MarkedIdealEquivalence
noncomputable section
variable {n : ℕ}
section Regular
variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M'] [IsComplexManifold n M']
omit [IsComplexManifold n M] in
/-- **Membership in the codimension-one part depends only on germs**: of `N` and of the cosupport. -/
theorem mem_codimOnePartAlong_congr {N N' : Set M} {𝔞 𝔟 : GermIdeal n M} {μ ν : ℕ} {x : M}
    (hN : ∀ᶠ y in 𝓝 x, y ∈ N ↔ y ∈ N')
    (hS : ∀ᶠ y in 𝓝 x, y ∈ cosupport n N 𝔞 μ ↔ y ∈ cosupport n N' 𝔟 ν) :
    x ∈ codimOnePartAlong N 𝔞 μ ↔ x ∈ codimOnePartAlong N' 𝔟 ν :=
  mem_codimOnePartAlong_iff_of_eventually hN hS

omit [IsComplexManifold n M] in
/-- **Equal supports have equal codimension-one parts** (the same `N`). -/
theorem codimOnePartAlong_congr {N N' : Set M} {𝔞 𝔟 : GermIdeal n M} {μ ν : ℕ} (hN : N = N')
    (hS : cosupport n N 𝔞 μ = cosupport n N' 𝔟 ν) :
    codimOnePartAlong N 𝔞 μ = codimOnePartAlong N' 𝔟 ν := by
  ext x
  exact mem_codimOnePartAlong_congr (Eventually.of_forall fun _ => by rw [hN])
    (Eventually.of_forall fun _ => by rw [hS])

end Regular
variable {X X' : CMfd.{u} n} {𝔪 : MarkedIdeal n X}
/-- **Restricted-equivalent marked ideals have the same codimension-one part at every stage**
(property (7); closed `N`, coherent ideals). -/
theorem codimOnePartAlong_geoTransformAlong_of_restrictEquiv {𝔫 : MarkedIdeal n X}
    (h : MarkedIdealOperationsAlong.MarkedIdeal.RestrictEquiv 𝔪 𝔫) (hN : IsClosed 𝔪.N)
    (h𝔪 : 𝔪.ideal.IsCoherent) (h𝔫 : 𝔫.ideal.IsCoherent) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) →
      codimOnePartAlong (geoTransformAlong 𝔪 T).N (geoTransformAlong 𝔪 T).ideal (geoTransformAlong 𝔪 T).d =
        codimOnePartAlong (geoTransformAlong 𝔫 T).N (geoTransformAlong 𝔫 T).ideal (geoTransformAlong 𝔫 T).d
  | _, .refl => codimOnePartAlong_congr h.N_eq h.cosupp_eq
  | _, .step T C π hπ => by
      rw [MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.geoTransformAlong_step_eq h hN h𝔪 h𝔫 T C π hπ]

end
end Hironaka.CodimOnePartCanonical
