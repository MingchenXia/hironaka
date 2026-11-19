/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Hironaka.Geometry.ProperSteinProjectiveCechReesHomogeneousAction
import Hironaka.Geometry.ProperSteinProjectiveCechReesTailDegreeFinite

/-! # Genuine finite EVERY original ideal-power native cohomology

Only the ORIGINAL projective closed embedding, original ideal and Noetherian
original coefficient ring are inputs. The SAME actual Rees-family homology,
entire original degree comparison and original homogeneous action produce
all finiteness hypotheses internally, then the actual original-tail quotient
proves finite every original component. No geometric output is assumed.
-/
open CategoryTheory AlgebraicGeometry
open scoped DirectSum
noncomputable section
universe u
namespace Hironaka.Geometry.ProperSteinProjectiveCech.ReesPowerCohomologyFinite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
variable {R : Type u} [CommRing R] (I : Ideal R)
  {X : Scheme.{u}} {n : ℕ} (i : X ⟶ projectiveSpace R n) [IsClosedImmersion i]

/-- ONLY ORIGINAL projective Noetherian geometry proves finite EVERY original ideal-power native cohomology. -/
theorem projective_powerCech_finite [IsNoetherianRing R] (d p : ℕ) :
    Module.Finite R ((ReesPowerDiagram.powerComplex I (i ≫ projectiveSpaceStructure R n)
      (originalClosedCoordinateOpens i) d).homology p) := by
  let := ReesDegreeHomology.projectiveSeparated i
  let f := i ≫ projectiveSpaceStructure R n
  let U := originalClosedCoordinateOpens i
  let hU := originalClosedCoordinateOpens_isAffine i
  let M : ℕ → Type u := fun j => (ReesPowerDiagram.powerComplex I f U j).homology p
  let := ReesDegreeHomology.reesModule I f U hU p
  let : IsScalarTower R (reesAlgebra I) (⨁ j : ℕ, M j) :=
    ReesDegreeHomology.originalScalarTower I f U hU p
  let : Module.Finite (reesAlgebra I) (⨁ j : ℕ, M j) :=
    ReesDegreeHomology.projective_finite I i p
  apply ReesTailDegreeFinite.degree_finite I M _ d
  intro e a j y
  exact ⟨_, ReesHomogeneousAction.reesModule_homogeneous I f U hU a j p y⟩

end Hironaka.Geometry.ProperSteinProjectiveCech.ReesPowerCohomologyFinite
