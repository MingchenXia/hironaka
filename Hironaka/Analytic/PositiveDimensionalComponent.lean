/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.RegularLocusComponent
import Hironaka.Analytic.ClosureDifferenceAnalytic
import Hironaka.Analytic.SingularLocus
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
set_option autoImplicit false

/-!
# Positive-dimensional irreducible components through non-isolated points

* `exists_isOpen_inter_subset_singleton_of_regularAtDim_zero`: a regular point of dimension
  `0` of `A` is isolated in `A` (the flattening sends `A` near the point to `{0}`).
* Take (LS) with connected regular parts at `x`. If all piece dimensions vanished, each piece would meet the
  neighbourhood `Δᵢ` only in `x`, so `x` would be isolated in `A`. Hence some piece has `dᵢ > 0`; for `c` in its
  connected regular part `Gᵢ`, the closure `V` of the connected component `C` of the regular locus through `c` is
  irreducible analytic of dimension `dᵢ`, contains `closure Gᵢ ∋ x`, lies in `A`, and is maximal since `A` agrees
  with `C` near `c`.
-/

open Set Filter
open scoped Topology

namespace Hironaka.PositiveDimensionalComponent

open AnalyticLocalStatement LocalStatementConnected RegularLocusComponent

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

omit [IsComplexManifold n M] in
/-- A regular point of dimension `0` is isolated. -/
theorem exists_isOpen_inter_subset_singleton_of_regularAtDim_zero {A : Set M} {y : M}
    (hy : RegularAtDim (n := n) A y 0) :
    ∃ O : Set M, IsOpen O ∧ y ∈ O ∧ A ∩ O ⊆ {y} := by
  obtain ⟨-, -, Φ, -, hzero, hflat⟩ := hy
  refine ⟨(complexChartAt (n := n) y).val.source ∩
      (complexChartAt (n := n) y).val ⁻¹' Φ.source,
    (complexChartAt (n := n) y).val.continuousOn.isOpen_inter_preimage
      (complexChartAt (n := n) y).val.open_source Φ.isOpen_source,
    ⟨mem_complexChartAt_source y, Φ.center_mem_source⟩, ?_⟩
  rintro z ⟨hzA, hzs, hzΦ⟩
  have hz0 : Φ.toFun ((complexChartAt (n := n) y).val z) = 0 := by
    have hp := (hflat hzs hzΦ).mp hzA
    ext i
    simpa using hp i (Nat.zero_le _)
  have hez : (complexChartAt (n := n) y).val z = (complexChartAt (n := n) y).val y :=
    calc (complexChartAt (n := n) y).val z
        = Φ.invFun (Φ.toFun ((complexChartAt (n := n) y).val z)) := (Φ.left_inv _ hzΦ).symm
      _ = Φ.invFun (Φ.toFun ((complexChartAt (n := n) y).val y)) := by rw [hz0, hzero]
      _ = (complexChartAt (n := n) y).val y := Φ.left_inv _ Φ.center_mem_source
  exact (complexChartAt (n := n) y).val.injOn hzs (mem_complexChartAt_source y) hez

end Hironaka.PositiveDimensionalComponent
