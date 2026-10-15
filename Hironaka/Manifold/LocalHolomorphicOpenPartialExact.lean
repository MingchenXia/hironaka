/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Analytic.ComplexAnalyticSubvarieties

/-! Exact original local-coordinate conversion omitted by the initial extraction. -/
set_option autoImplicit false
open Set
open scoped Manifold ContDiff Topology
namespace Hironaka
noncomputable section
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M]

namespace LocalHolomorphicEquivAt

/-- The underlying local biholomorphism is an actual open partial
homeomorphism.  Keeping this conversion explicit lets local analytic
flattenings use the topological covariance theorems for upper-semicontinuous
regularization. -/
def toOpenPartialHomeomorph {p : ComplexModel n}
    (Φ : LocalHolomorphicEquivAt (n := n) p) :
    OpenPartialHomeomorph (ComplexModel n) (ComplexModel n) where
  toFun := Φ.toFun
  invFun := Φ.invFun
  source := Φ.source
  target := Φ.target
  map_source' := Φ.mapsTo_toFun
  map_target' := Φ.mapsTo_invFun
  left_inv' := Φ.left_inv
  right_inv' := Φ.right_inv
  continuousOn_toFun := Φ.toFun_holomorphic.continuousOn
  continuousOn_invFun := Φ.invFun_holomorphic.continuousOn
  open_source := Φ.isOpen_source
  open_target := Φ.isOpen_target

@[simp] theorem coe_toOpenPartialHomeomorph {p : ComplexModel n}
    (Φ : LocalHolomorphicEquivAt (n := n) p) :
    (toOpenPartialHomeomorph Φ : ComplexModel n → ComplexModel n) = Φ.toFun := rfl

@[simp] theorem coe_toOpenPartialHomeomorph_symm {p : ComplexModel n}
    (Φ : LocalHolomorphicEquivAt (n := n) p) :
    ((toOpenPartialHomeomorph Φ).symm : ComplexModel n → ComplexModel n) = Φ.invFun := rfl

end LocalHolomorphicEquivAt

end
end Hironaka
