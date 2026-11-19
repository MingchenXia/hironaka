import Hironaka.Geometry.MonomialBlowupIteration
import Hironaka.Geometry.PolynomialNodeBoundary
import Hironaka.Geometry.SNCIso

/-!
# Actual SNC persistence on finished finite coordinate-prefix charts

For arbitrary finite lists of the two base coordinates, the later original
prefix-centre blowup on a finished chart preserves its actual SNC boundary.
All nonvanishing, original-centre and SNC facts are proved internally.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Hironaka.Geometry.MonomialBlowupIterationSNC

open Algebra.NodeBlowupChart Algebra.MonomialBlowupIteration
open PolynomialNodeBoundary MonomialBlowupIteration

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (K : Type u) [Field K]

/-- Every finite product of the actual base coordinate family is nonzero, including repetitions. -/
theorem coordinateList_nonzero (a : List (Fin 2)) :
    (0 : Base K) ∉ a.map (fun i ↦ (X i : Base K)) := by
  intro h
  obtain ⟨i, _, hi⟩ := List.mem_map.mp h
  exact X_ne_zero i hi

/-- The actual mapped later original prefix centre on its finished coordinate-node chart. -/
def coordinateFinishedCenter (a : List (Fin 2)) (k : Fin 2) (b : List (Fin 2)) (s : Base K) :
    Ideal (Chart K k) := by
  let a' := a.map (fun i ↦ (X i : Base K))
  let b' := b.map (fun i ↦ (X i : Base K))
  let : Fact ((X k : Base K) ≠ 0) := ⟨X_ne_zero k⟩
  let : Fact (b'.prod ≠ 0) := ⟨List.prod_ne_zero (coordinateList_nonzero K b)⟩
  exact (prefixCenter (a' ++ X k :: b').prod (a'.prod * (X k * s))).map
    (finishedPrefixMap a' (X k) b').toRingHom

/-- The exact boundary on this actual native blowup is pulled back by its actual structure map. -/
def coordinateFinishedBoundary (a : List (Fin 2)) (k : Fin 2) (b : List (Fin 2)) (s : Base K) :
    (affineBlowup (coordinateFinishedCenter K a k b s)).IdealSheafData :=
  (chartBoundary K k).comap (affineBlowupStructure (coordinateFinishedCenter K a k b s))

/-- Finite coordinate-prefix iteration preserves the actual SNC boundary on every finished chart. -/
theorem coordinateFinishedBoundary_isStrictNormalCrossings
    (a : List (Fin 2)) (k : Fin 2) (b : List (Fin 2)) (s : Base K) :
    IsStrictNormalCrossings (coordinateFinishedBoundary K a k b s) := by
  let a' := a.map (fun i ↦ (X i : Base K))
  let b' := b.map (fun i ↦ (X i : Base K))
  let : Fact ((X k : Base K) ≠ 0) := ⟨X_ne_zero k⟩
  let : Fact (b'.prod ≠ 0) := ⟨List.prod_ne_zero (coordinateList_nonzero K b)⟩
  let e := finishedPrefixCenterBlowupIso a' (X k : Base K) b' s (coordinateList_nonzero K a)
  change IsStrictNormalCrossings ((chartBoundary K k).comap (affineBlowupStructure
    ((prefixCenter (a' ++ X k :: b').prod (a'.prod * (X k * s))).map
      (finishedPrefixMap a' (X k) b').toRingHom)))
  rw [← finishedPrefixCenterBlowupIso_hom_structure a' (X k : Base K) b' s
    (coordinateList_nonzero K a)]
  exact SNCIso.isStrictNormalCrossings_comap e (chartBoundary K k)
    (chartBoundary_isStrictNormalCrossings K k)

end Hironaka.Geometry.MonomialBlowupIterationSNC
