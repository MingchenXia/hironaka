/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Analytic.ProperMappingInduction
import Hironaka.Analytic.RemmertSteinGeneral

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Remmert's proper mapping theorem

Blueprint `rem:proper-mapping` (Demailly, *Complex analytic and differential geometry*, II.8.8).
The simultaneous induction closes: `(R_m)` and `(RS_m)` hold for every `m` and all complex
manifolds (`properImageStatement`, `remmertSteinStatement`), and in particular the image of an
analytic subset under a holomorphic map which is proper on it is analytic
(`isComplexAnalyticSubset_image`).

The steps: `ProperMappingInduction` (`(R_0)`, `(R_m) ∧ (RS_{m+1}) ⇒ (R_{m+1})`, the double
induction), `RemmertSteinGeneral` (`(R_{m-1})` in `Type` ⇒ `(RS_m)`), `ProperImageIrreducible`
(Step 1).

Sorry-free.
-/

open Set
open scoped Manifold ContDiff

namespace Hironaka.ProperMappingTheorem

open AnalyticDimensionBasics RemmertStatements

universe u₁ u₂

/-- **`(R_m)` for every `m`.** -/
theorem properImageStatement (m : ℕ) : ProperImageStatement.{u₁, u₂} m :=
  ProperMappingInduction.properImageStatement_of_remmertStein
    (fun m h => RemmertSteinGeneral.remmertSteinStatement_of_properImage (m := m + 1)
      (by rwa [Nat.add_sub_cancel]))
    (fun m h => RemmertSteinGeneral.remmertSteinStatement_of_properImage (m := m + 1)
      (by rwa [Nat.add_sub_cancel])) m

/-- **`(RS_m)` for every `m`**: the Remmert--Stein theorem. -/
theorem remmertSteinStatement (m : ℕ) : RemmertSteinStatement.{u₂} m :=
  RemmertSteinGeneral.remmertSteinStatement_of_properImage (properImageStatement.{0, 0} (m - 1))

/-- **Remmert's proper mapping theorem.**  If `F : X → Y` is holomorphic and `A ⊆ X` is analytic
with `F|_A` proper, then `F(A)` is analytic in `Y`. -/
theorem isComplexAnalyticSubset_image {n k : ℕ} {X : Type u₁} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] {Y : Type u₂} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel k) Y] [IsComplexManifold k Y] {F : X → Y}
    (hF : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel k) ∞ F) {A : Set X}
    (hA : IsComplexAnalyticSubset (n := n) A) (hprop : ProperOn F A) :
    IsComplexAnalyticSubset (n := k) (F '' A) :=
  properImageStatement n hF hA (fun _ _ hy => hy.1) hprop

end Hironaka.ProperMappingTheorem
