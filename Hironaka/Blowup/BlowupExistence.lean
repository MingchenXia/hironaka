import Hironaka.Blowup.BlowupUniqueness
import Hironaka.Blowup.BlowupMonomialCharts
import Hironaka.Blowup.BlowupSpaceUniversal

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Existence of the blowup along a smooth centre

Source: Copy-4, `sec:prelim`; Griffiths--Harris, Chapter 4 §6; Voisin I, §3.3; the construction
follows Demailly, *Complex Analytic and Differential Geometry*, Chapter VII §12.

`exists_isBlowupAlong` below was stated as an OPEN TARGET of the project (human decision I-0157):
every blowup fact in the workspace is conditional on `IsBlowupAlong n C π` being inhabited.  It is
now **PROVED**, with no named input: the witness is Demailly's blowup
`Hironaka.BlowupConstruction.blowupProj : BlowupSpace n C → X`, built in

* `Hironaka.BlowupSpaceTangent` -- the tangent space `T_yC` of the centre (common kernel of the
  differentials of the germs of `𝓘_C`);
* `Hironaka.BlowupSpace` -- the point set `(X \ C) ⊔ P(N_C)` and Demailly's monomial charts `τ̃ⱼ`;
* `Hironaka.BlowupSpaceRatio` -- the quotients `(f/τⱼ)~` are holomorphic in the charts;
* `Hironaka.BlowupSpaceAtlas`, `Hironaka.BlowupSpaceManifold` -- the atlas is holomorphic, the space
  is a Hausdorff, second countable complex manifold and `π` is holomorphic;
* `Hironaka.BlowupSpaceUniversal` -- `π*𝓘_C` is invertible and every holomorphic `g : Z → X` with
  `g*𝓘_C` invertible (test manifolds `Z` of every dimension) lifts uniquely and holomorphically
  (`isBlowupAlong_blowupProj`).

`Hironaka.BlowupUniqueness` shows the object is unique up to a unique isomorphism over `X`, so any
other construction may be compared with this one.
-/

open Set
open scoped Manifold ContDiff

universe u

namespace Hironaka.BlowupExistence

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- **The blowup of a complex manifold along a nowhere-dense closed complex submanifold exists**
(PROVED; formerly the open target of I-0157): Demailly's blowup
`BlowupConstruction.blowupProj : BlowupSpace n C → X`, by
`BlowupConstruction.isBlowupAlong_blowupProj`. -/
theorem exists_isBlowupAlong (C : Set X) (hC : IsClosedSubmanifold n C)
    (hCint : interior C = ∅) :
    ∃ (Z : Type u) (_ : TopologicalSpace Z) (_ : ChartedSpace (ComplexModel n) Z)
      (_ : IsComplexManifold n Z) (π : Z → X), IsBlowupAlong n C π := by
  have : Fact (IsClosedSubmanifold n C) := ⟨hC⟩
  exact ⟨BlowupConstruction.BlowupSpace n C, inferInstance, inferInstance, inferInstance,
    BlowupConstruction.blowupProj n C, BlowupConstruction.isBlowupAlong_blowupProj hCint⟩

end

end Hironaka.BlowupExistence
