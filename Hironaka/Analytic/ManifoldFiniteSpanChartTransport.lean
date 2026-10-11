/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Coherence.GeneralCoherentIdealColon
import Hironaka.Analytic.LocalHolomorphicFiniteSpanTransport

set_option autoImplicit false

/-! # Full literal manifold finite spans in preferred and adapted holomorphic coordinates -/

open Set Filter
open scoped Topology Manifold

namespace Hironaka.ManifoldFiniteSpanChartTransport

open Hironaka.HolomorphicIdealSheaves

open Hironaka
noncomputable section

/-- The literal original generators, rather than chart-generated substitutes, are retained. -/
theorem isInSpanAt_comp_chartSymm_iff {n s : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {x y : M} (hy : y ∈ (chartAt (ComplexModel n) x).source)
    (G : Fin s → M → ℂ) (F : M → ℂ) :
    IsInSpanAt (n := n) (· ∈ Set.range G) y F ↔
      IsInSpanAt (n := n)
        (· ∈ Set.range fun i z => G i ((chartAt (ComplexModel n) x).symm z))
        ((chartAt (ComplexModel n) x) y) (fun z => F ((chartAt (ComplexModel n) x).symm z)) := by
  let e := chartAt (ComplexModel n) x
  let S : Fin s → ComplexModel n → ℂ := fun i z => G i (e.symm z)
  have hround (i : Fin s) : (fun p => S i (e p)) =ᶠ[𝓝 y] G i :=
    (show ∀ᶠ p in 𝓝 y, p ∈ e.source from e.open_source.mem_nhds hy).mono fun p hp =>
      congrArg (G i) (e.left_inv hp)
  have hbefore : IsInSpanAt (n := n) (· ∈ Set.range G) y F ↔
      IsInSpanAt (n := n) (· ∈ Set.range fun i p => S i (e p)) y F :=
    ⟨CoherentIdealColon.isInSpanAt_range_congr (fun i => (hround i).symm) EventuallyEq.rfl,
      CoherentIdealColon.isInSpanAt_range_congr hround EventuallyEq.rfl⟩
  refine hbefore.trans ((CoherentIdealColon.isInSpanAt_range_comp_chart_iff hy S F).trans ?_)
  rw [CoherentIdealColon.isInSpanAt_range_iff]
  simp only [OkaIdealOperations.InSpanAt, OkaRelationSheaf.HolAt, HolomorphicAt,
    mdifferentiableAt_iff_differentiableAt]
  rfl

/-- Full original finite generation passes through the genuine preferred and adapted charts. -/
theorem isInSpanAt_comp_adapted_iff {n s : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] (x : M)
    (Φ : LocalHolomorphicEquivAt (n := n) ((chartAt (ComplexModel n) x) x))
    (h0 : Φ.toFun ((chartAt (ComplexModel n) x) x) = 0)
    (G : Fin s → M → ℂ) (F : M → ℂ) :
    IsInSpanAt (n := n) (· ∈ Set.range G) x F ↔
      IsInSpanAt (n := n) (· ∈ Set.range fun i z =>
        G i ((chartAt (ComplexModel n) x).symm (Φ.invFun z))) (0 : ComplexModel n)
        (fun z => F ((chartAt (ComplexModel n) x).symm (Φ.invFun z))) := by
  have hchart := isInSpanAt_comp_chartSymm_iff (mem_chart_source (ComplexModel n) x) G F
  have hadapt := LocalHolomorphicFiniteSpanTransport.isInSpanAt_comp_inv_iff Φ
    (fun i z => G i ((chartAt (ComplexModel n) x).symm z))
    (fun z => F ((chartAt (ComplexModel n) x).symm z))
  simpa only [h0] using hchart.trans hadapt

end
end Hironaka.ManifoldFiniteSpanChartTransport
