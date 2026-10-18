/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Support.AnalyticIrreducibleUnivExact
import Hironaka.Analytic.ComponentComplementConnected
import Hironaka.Analytic.AnalyticIrreducibleComponents

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The complement of a proper analytic subset is connected

Source: Grauert--Remmert, *Coherent Analytic Sheaves*, Ch. 9; Demailly, CADG II.
A connected complex manifold is irreducible, so a proper closed analytic subset does not
disconnect it: an analytic set is locally contained in a zero set, whose complement in a ball
is connected because the ambient real codimension is at least two.

`Hironaka.ComponentComplementConnected` proves exactly this statement for the regular component
of an analytic set `A` through a regular point.  Taking `A = univ` — the manifold itself is a
closed irreducible analytic subvariety of dimension `n`
(`AnalyticIrreducibleComponents.regularAtDim_univ`) whose regular points are all of `M` —
specialises it to the complement of `T` in `M`.
-/

open Set

namespace Hironaka.AnalyticComplementConnected



noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- Every point of the manifold is a regular point of `univ`. -/
theorem regularPoints_univ : RegularLocusComponent.regularPoints (n := n) (univ : Set M) = univ :=
  eq_univ_of_forall fun x => ⟨n, AnalyticIrreducibleComponents.regularAtDim_univ x⟩

/-- On a connected manifold the regular component of `univ` is the whole manifold. -/
theorem component_univ [ConnectedSpace M] (c : M) :
    RegularLocusComponent.component (n := n) (univ : Set M) c = univ := by
  rw [RegularLocusComponent.component, regularPoints_univ, connectedComponentIn_univ,
    PreconnectedSpace.connectedComponent_eq_univ]

/-- **The complement of a proper closed analytic subset of a connected complex manifold is
connected.** -/
theorem isPreconnected_compl [ConnectedSpace M] {T : Set M}
    (hT : IsComplexAnalyticSubset (n := n) T) (hTne : T ≠ univ) :
    IsPreconnected (Tᶜ : Set M) := by
  obtain ⟨c⟩ := (inferInstance : Nonempty M)
  have hA : IsComplexAnalyticSubset (n := n) (univ : Set M) :=
    (AnalyticIrreducibleComponents.isComplexAnalyticallyIrreducible_univ (n := n) (M := M)).analytic
  have hc : RegularAtDim (n := n) (univ : Set M) c n :=
    AnalyticIrreducibleComponents.regularAtDim_univ c
  have hK : ¬ RegularLocusComponent.component (n := n) (univ : Set M) c ⊆ T := by
    rw [component_univ]
    exact fun h => hTne (eq_univ_of_univ_subset h)
  have := (ComponentComplementConnected.isPreconnected_component_diff_and_subset_closure
    hA hT hc hK).1
  rw [component_univ] at this
  rwa [Set.compl_eq_univ_sdiff]

end

end Hironaka.AnalyticComplementConnected
