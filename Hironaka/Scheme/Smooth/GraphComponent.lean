/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.Smooth.Graph
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# The graph of two coordinate systems: Noetherianity and étale restrictions

* The graph `W = U ×_{𝔸ⁿ} U` is a Noetherian scheme (`isNoetherian_graph`): affine (a fibre
  product of affines) and locally Noetherian (of finite type over `𝔸ⁿ_k`, Mathlib's
  `LocallyOfFiniteType.isLocallyNoetherian`).
* The restriction of an étale morphism to an open subscheme is étale (`etale_ι_comp`).
* The underlying étale neighbourhood pair of a `NbhdPair` has the maps `ψ ≫ U.ι`, `ψ' ≫ U.ι`
  (`NbhdPair.toEtaleNbhdPair_ψ`).

The neighbourhood pair on which two hypersurfaces of maximal contact are compared is the one at
the diagonal point (`GraphDiagonalPair.lean`).
-/

@[expose] public section

namespace AlgebraicGeometry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing TopologicalSpace

universe u

/-- The restriction of an étale morphism to an open subscheme is étale. -/
instance etale_ι_comp {W Y : Scheme.{u}} (V : W.Opens) (ψ : W ⟶ Y) [Etale ψ] :
    Etale (V.ι ≫ ψ) :=
  inferInstance

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) {n : ℕ} {U : X.affineOpens}

namespace EtaleCoordinates

variable {f} (c c' : EtaleCoordinates f n U)

/-- The graph `W = U ×_{𝔸ⁿ} U` is a Noetherian scheme: affine, and of finite type over `𝔸ⁿ_k`
through `ψ_u ≫ φ_u`. -/
theorem isNoetherian_graph : IsNoetherian (c.graph c') := by
  have : IsAffine (U.1 : Scheme.{u}) := U.2
  have : IsLocallyNoetherian (c.graph c') :=
    LocallyOfFiniteType.isLocallyNoetherian (c.graphFst c' ≫ toAffineSpace f U.1 c.v)
  exact ⟨⟩

/-- The underlying étale neighbourhood pair of `p ∈ X` has the maps `ψ ≫ U.ι`, `ψ' ≫ U.ι`. -/
theorem NbhdPair.toEtaleNbhdPair_ψ {p : X} {hpU : p ∈ U.1} (P : c.NbhdPair c' hpU) :
    P.toEtaleNbhdPair.ψ = P.ψ ≫ U.1.ι ∧ P.toEtaleNbhdPair.ψ' = P.ψ' ≫ U.1.ι :=
  ⟨rfl, rfl⟩

end EtaleCoordinates

end AlgebraicGeometry
