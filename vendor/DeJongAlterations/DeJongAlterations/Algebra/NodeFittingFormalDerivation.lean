import DeJongAlterations.Algebra.NodeGeometricCompletionDerivation
import Mathlib.RingTheory.MvPowerSeries.Derivative
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Actual formal hypersurface differentiation into its SAME gradient cokernel

Arbitrary commutative coefficients, arbitrary original formal equation, and all
characteristics. This constructs the actual quotient derivation, not a supplied
differential presentation or algebraic Omega identification for the formal ring.
-/

noncomputable section

namespace DeJongAlterations.Algebra.NodeFittingFormalDerivation

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {R : Type u} [CommRing R]

abbrev Series (R : Type u) [CommRing R] := MvPowerSeries (Fin 2) R
abbrev equationIdeal (F : Series R) : Ideal (Series R) := Ideal.span {F}
abbrev Hypersurface (F : Series R) := Series R ⧸ equationIdeal F
abbrev quotientMap (F : Series R) : Series R →ₐ[R] Hypersurface F :=
  Ideal.Quotient.mkₐ R (equationIdeal F)

/-- The actual native derivatives of the SAME original formal equation. -/
def gradient (F : Series R) : Fin 2 → Hypersurface F :=
  fun i => quotientMap F (MvPowerSeries.pderiv R i F)

/-- The literal one-gradient-column cokernel over the actual formal hypersurface. -/
abbrev GradientModule (F : Series R) :=
  (Fin 2 → Hypersurface F) ⧸ Submodule.span (Hypersurface F) {gradient F}

/-- The literal standard coordinate class, with the SAME original quotient coefficients. -/
def coordinateClass (F : Series R) (i : Fin 2) : GradientModule F :=
  Submodule.Quotient.mk (Pi.single i 1)

/-- Native partial differentiation pushed to the actual coordinate classes. -/
def seriesDerivation (F : Series R) : Derivation R (Series R) (GradientModule F) :=
  (LinearMap.toSpanSingleton (Series R) _ (coordinateClass F 0)).compDer
      (MvPowerSeries.pderiv R 0) +
    (LinearMap.toSpanSingleton (Series R) _ (coordinateClass F 1)).compDer
      (MvPowerSeries.pderiv R 1)

/-- EVERY actual series value is its native partial-derivative vector class. -/
theorem seriesDerivation_apply (F g : Series R) :
    seriesDerivation F g = Submodule.Quotient.mk
      ![quotientMap F (MvPowerSeries.pderiv R 0 g),
        quotientMap F (MvPowerSeries.pderiv R 1 g)] := by
  change quotientMap F (MvPowerSeries.pderiv R 0 g) • coordinateClass F 0 +
      quotientMap F (MvPowerSeries.pderiv R 1 g) • coordinateClass F 1 = _
  rw [coordinateClass, coordinateClass, ← Submodule.Quotient.mk_smul,
    ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add]
  congr 1
  funext i
  fin_cases i <;> simp

/-- The SAME original equation is killed by its ENTIRE actual gradient relation. -/
theorem seriesDerivation_equation (F : Series R) : seriesDerivation F F = 0 := by
  rw [seriesDerivation_apply]
  have hg : ![quotientMap F (MvPowerSeries.pderiv R 0 F),
      quotientMap F (MvPowerSeries.pderiv R 1 F)] = gradient F := by
    funext i
    fin_cases i <;> rfl
  rw [hg, Submodule.Quotient.mk_eq_zero]
  exact Submodule.subset_span (Set.mem_singleton _)

/-- The actual derivation kills the WHOLE original equation ideal internally. -/
theorem seriesDerivation_ideal (F : Series R) (g : Series R) (hg : g ∈ equationIdeal F) :
    seriesDerivation F g = 0 := by
  obtain ⟨h, rfl⟩ := Ideal.mem_span_singleton.mp hg
  rw [Derivation.leibniz, seriesDerivation_equation, smul_zero, add_zero]
  change quotientMap F F • seriesDerivation F h = 0
  rw [show quotientMap F F = 0 from
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton F))]
  exact zero_smul (Hypersurface F) (seriesDerivation F h)

/-- The native quotient linear map, with kernel vanishing proved from the original equation. -/
def quotientDifferential (F : Series R) : Hypersurface F →ₗ[R] GradientModule F :=
  ((equationIdeal F).restrictScalars R).liftQ (seriesDerivation F).toLinearMap
    (fun g hg => seriesDerivation_ideal F g hg)

/-- The actual quotient derivation of the SAME original formal hypersurface. -/
def formalDerivation (F : Series R) : Derivation R (Hypersurface F) (GradientModule F) where
  toLinearMap := quotientDifferential F
  map_one_eq_zero' := by
    change seriesDerivation F 1 = 0
    exact (seriesDerivation F).map_one_eq_zero
  leibniz' x y := by
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective y
    change seriesDerivation F (g * h) =
      quotientMap F g • seriesDerivation F h + quotientMap F h • seriesDerivation F g
    exact (seriesDerivation F).leibniz g h

/-- EVERY actual original formal representative retains its original native gradient. -/
theorem formalDerivation_mk (F g : Series R) :
    formalDerivation F (quotientMap F g) = Submodule.Quotient.mk
      ![quotientMap F (MvPowerSeries.pderiv R 0 g),
        quotientMap F (MvPowerSeries.pderiv R 1 g)] :=
  seriesDerivation_apply F g

/-- BOTH original coordinate derivatives are the literal standard basis classes. -/
theorem formalDerivation_coordinate (F : Series R) (i : Fin 2) :
    formalDerivation F (quotientMap F (MvPowerSeries.X i)) = coordinateClass F i := by
  rw [formalDerivation_mk]
  dsimp only [coordinateClass]
  congr 1
  funext j
  fin_cases i <;> fin_cases j <;> simp

/-- EVERY original coefficient is killed, for the actual native quotient algebra action. -/
theorem formalDerivation_coefficient (F : Series R) (r : R) :
    formalDerivation F (algebraMap R (Hypersurface F) r) = 0 :=
  (formalDerivation F).map_algebraMap r

/-- Actual adic continuity has a uniform one-level loss for EVERY actual ideal. -/
theorem formalDerivation_mem_pow_smul (F : Series R) (J : Ideal (Hypersurface F))
    (n : ℕ) (g : Hypersurface F) (hg : g ∈ J ^ (n + 1)) :
    formalDerivation F g ∈ (J ^ n • ⊤ : Submodule (Hypersurface F) (GradientModule F)) :=
  NodeGeometricCompletionDerivation.differential_mem_pow_smul J (formalDerivation F) n hg

end DeJongAlterations.Algebra.NodeFittingFormalDerivation
