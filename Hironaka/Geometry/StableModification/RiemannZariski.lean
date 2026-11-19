import Hironaka.Geometry.StableModification.RiemannZariski.Algebraic
import Hironaka.Geometry.StableModification.RiemannZariski.Scheme

/-!
# Riemann–Zariski spaces (Temkin 2010, §3.2)

Umbrella module for the valuation-theoretic Riemann–Zariski spaces used in the stable modification
route:

* `Hironaka.StableModification.RiemannZariski.Algebraic`: the Riemann–Zariski space of a
  field and of a ring mapping to it; basis, `T0`, quasi-compactness (Zariski), the center map, and
  the open embeddings `RZ(B) ⊆ RZ(A)` for `B` of finite type over `A`.
* `Hironaka.StableModification.RiemannZariski.Scheme`: the Riemann–Zariski space
  `RZ_L(S)` of a scheme `S` with respect to `Spec L → S`; the affine description,
  quasi-compactness, uniqueness of extensions for separated `S`, continuity of the center map, the
  open embedding for quasi-modifications (Temkin, Corollary 3.2.7 `openembcor`) and the
  homeomorphism for modifications.
-/
