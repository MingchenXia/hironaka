/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.AnalyticSubsetTopology
import Hironaka.Analytic.RegularLocusDense
import Hironaka.Analytic.PureDimension
import Hironaka.Analytic.PositiveDimensionalComponent
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
set_option autoImplicit false

/-!
# Irreducible components of analytic subsets

These are standard (Grauert--Remmert, *Coherent analytic sheaves*, Ch. 9; Demailly, *Complex analytic and
differential geometry*, II.5).

* Proved in `Hironaka.AnalyticSubsetTopology`.
* `regularAtDim_univ`: the manifold itself is a closed irreducible analytic subvariety of dimension `n`.
* (The global irreducible components form a locally finite family of maximal irreducible analytic subsets; the germ
  at a non-isolated point has positive dimension, so some component through it does, and irreducible analytic sets
  are pure-dimensional.) Derived in `Hironaka.PositiveDimensionalComponent` from (LS) with connected regular parts
  and the closures of the connected components of the regular locus.
* `eq_dim_of_regularAtDim`: an irreducible analytic subvariety is pure-dimensional,
  i.e. every regular point has the certified dimension (Chirka, §5.3--5.4).  Derived in
  `Hironaka.PureDimension` from the local statement (LS)
  `AnalyticLocalStatement.exists_localDecomposition`, itself proved from the local
  parametrization theorem (`GermParametrization.exists_localParametrization`).
-/

open Set Filter
open scoped Topology

namespace Hironaka.AnalyticIrreducibleComponents

open Hironaka.BlowupSequences

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

omit [IsComplexManifold n M] in
/-- Every point of the manifold is a regular point of `univ` of dimension `n`. -/
theorem regularAtDim_univ (x : M) : RegularAtDim (n := n) (univ : Set M) x n := by
  set e := (complexChartAt (n := n) x).val
  set p := e x
  refine ⟨le_rfl, mem_univ x, ?_⟩
  let Φ : LocalHolomorphicEquivAt (n := n) p :=
    { source := e.target
      target := (fun w => w + p) ⁻¹' e.target
      isOpen_source := e.open_target
      isOpen_target := e.open_target.preimage (continuous_id.add continuous_const)
      center_mem_source := e.map_source (mem_complexChartAt_source x)
      toFun := fun z => z - p
      invFun := fun w => w + p
      toFun_holomorphic := (differentiable_id.sub_const p).differentiableOn
      invFun_holomorphic := (differentiable_id.add_const p).differentiableOn
      mapsTo_toFun := fun z hz => by simpa using hz
      mapsTo_invFun := fun w hw => hw
      left_inv := fun z _ => by simp
      right_inv := fun w _ => by simp }
  refine ⟨Φ, subset_rfl, sub_self p, ?_⟩
  intro y _ _
  simp only [mem_univ, true_iff]
  intro i hi
  exact absurd i.2 (not_lt.mpr hi)

/-- **Irreducible analytic sets are pure-dimensional.**
At every point where an irreducible analytic subvariety `V` is regular, its dimension is
the certified dimension `dim V`.

Classically the regular locus of an irreducible analytic set is a connected manifold (Chirka, *Complex Analytic
Sets*, §5.3--5.4; Grauert--Remmert, *Coherent analytic sheaves*, Ch. 9, §1--2); equivalently, the closures of the
dimension strata of the regular locus are analytic and irreducibility selects one of them. Derived in
`Hironaka.PureDimension` from the local statement (LS), `AnalyticLocalStatement.exists_localDecomposition`. -/
theorem eq_dim_of_regularAtDim (V : ClosedIrreducibleAnalyticSubvariety n M) {x : M}
    {k : ℕ} (hx : RegularAtDim (n := n) V.carrier x k) : k = V.dim :=
  PureDimension.eq_dim_of_regularAtDim V hx

end

end Hironaka.AnalyticIrreducibleComponents
