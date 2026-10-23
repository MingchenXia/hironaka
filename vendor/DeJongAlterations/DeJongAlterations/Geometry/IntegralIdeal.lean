import DeJongAlterations.Composition
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-!
# Proper closed supports on integral schemes

A proper ideal-sheaf support misses the actual generic point. Consequently
its coordinate ideal is nonzero on every nonempty affine open, as needed
by the native local blowup producers.
-/

open AlgebraicGeometry TopologicalSpace

namespace DeJongAlterations.Geometry.IntegralIdeal

universe u

variable {X : Scheme.{u}} [IsIntegral X]

/-- A proper closed ideal-sheaf support misses the actual generic point. -/
theorem genericPoint_not_mem_support (D : X.IdealSheafData) (hD : D.support ≠ ⊤) :
    genericPoint X ∉ D.support := by
  intro hη
  apply hD
  apply top_le_iff.mp
  intro x hx
  exact (genericPoint_specializes x).mem_closed D.support.isClosed hη

/-- The actual coordinate ideal on every nonempty affine open is nonzero. -/
theorem ideal_ne_bot_of_support_ne_top (D : X.IdealSheafData) (hD : D.support ≠ ⊤)
    (U : X.affineOpens) [Nonempty U.1] : D.ideal U ≠ ⊥ := by
  intro hzero
  have hηU : genericPoint X ∈ U.1 :=
    ((genericPoint_spec X).mem_open_set_iff U.1.isOpen).mpr (by
      simpa using (Set.nonempty_coe_sort.mp (inferInstance : Nonempty U.1)))
  apply genericPoint_not_mem_support D hD
  apply (Scheme.IdealSheafData.mem_support_iff_of_mem (I := D) hηU).mpr
  rw [hzero]
  simp

end DeJongAlterations.Geometry.IntegralIdeal
