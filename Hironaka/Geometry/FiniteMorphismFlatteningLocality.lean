import Hironaka.Geometry.FiniteMorphismFlatteningClosure
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Actual open base change of the closed generic-fibre image

The native kernel ideal commutes with an actual open pullback square.
Consequently the native image closed subscheme itself has an actual
Cartesian open-base-change square, with its morphism internally built
from the ideal pullback equation.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Scheme.IdealSheafData

namespace Hironaka.Geometry.FiniteMorphismFlattening

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y U V : Scheme.{u}} (f : X ⟶ Y) (f' : U ⟶ V)
  (iU : U ⟶ X) (iV : V ⟶ Y) [IsOpenImmersion iV] [QuasiCompact f]
  (H : IsPullback f' iU iV f)

include H

/-- The actual native kernel ideal, including nilpotents, commutes with open base change. -/
theorem ker_comap_of_open_isPullback : f.ker.comap iV = f'.ker := by
  ext W
  rw [ideal_comap_of_isOpenImmersion,
    Scheme.ker_ideal_of_isPullback_of_isOpenImmersion f f' iU iV H W]

/-- The actual map of native closed images is induced by their proved kernel equation. -/
def imageOpenMap : f'.image ⟶ f.image :=
  subschemeMap f'.ker f.ker iV
    (le_map_iff_comap_le.mpr (ker_comap_of_open_isPullback f f' iU iV H).le)

/-- The actual map of closed images commutes with the literal closed immersions. -/
@[reassoc (attr := simp)]
theorem imageOpenMap_inclusion :
    imageOpenMap f f' iU iV H ≫ f.imageι = f'.imageι ≫ iV := by
  simp [imageOpenMap, subschemeMap]

/-- The actual native image closed subschemes form a Cartesian open-base-change square. -/
theorem imageOpenMap_isPullback :
    IsPullback f'.imageι (imageOpenMap f f' iU iV H) iV f.imageι := by
  apply isPullback_of_isClosedImmersion
  · exact (imageOpenMap_inclusion f f' iU iV H).symm
  · simpa only [ker_subschemeι] using ker_comap_of_open_isPullback f f' iU iV H

end Hironaka.Geometry.FiniteMorphismFlattening
