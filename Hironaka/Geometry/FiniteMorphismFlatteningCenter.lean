import Hironaka.Geometry.ModuleFlatteningCenter
import Hironaka.Geometry.FiniteMorphismFlatteningCenterFlatLocus

/-!
# Finite-morphism flattening preserving the entire original prescribed flat open

The original finite algebra internally chooses the same original cleared
maximal-minor ideal used for its actual finite flat generic-fibre closure.
The native blowup is an isomorphism over the entire original flat open,
and its actual intrinsic modification center lies in that open's actual
closed complement. No center, principal ideal or isomorphism certificate
is a premise.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Module

namespace Hironaka.Geometry.FiniteMorphismFlatteningCenter

open Algebra.ModuleFlatteningMinors Algebra.ModuleFlatteningMinorsCoordinates
  Algebra.ModuleFlatteningMinorsChart Algebra.FiniteMorphismFlattening
  FiniteMorphismFlattening

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R A : Type u) [CommRing R] [IsDomain R] [CommRing A] [Algebra R A]

/-- The same internally constructed original maximal-minor blowup makes the
actual native generic-fibre closure finite flat and preserves the WHOLE
original prescribed flat open, with actual intrinsic center containment. -/
theorem exists_finite_flat_transform_preserving_open_of_finitePresentation
    [Module.FinitePresentation R A] (U : (Spec (.of R)).Opens)
    (hflat : Flat (originalMap R A ∣_ U)) :
    ∃ (n r : ℕ) (m : Fin n → A) (V : Matrix (Fin r) (Fin n) R),
      Submodule.span R (Set.range m) = ⊤ ∧ (minorIdeal V).FG ∧ minorIdeal V ≠ ⊥ ∧
      IsProjectiveOver (affineBlowupStructure (minorIdeal V)) ∧
      IsModification (affineBlowupStructure (minorIdeal V)) ∧
      IsFinite (globalTransformMap R A (minorIdeal V)) ∧
      Flat (globalTransformMap R A (minorIdeal V)) ∧
      IsIso (affineBlowupStructure (minorIdeal V) ∣_ U) ∧
      ModificationCenter.center (affineBlowupStructure (minorIdeal V)) ≤ U.compl := by
  obtain ⟨n, r, m, b, s₀, δ, V, hm, hs₀, hδ, hcoord, hminor⟩ :=
    exists_integral_generic_coordinates R A
  have hfg : (minorIdeal V).FG := Submodule.fg_span (Set.finite_range (columnMinor V))
  have hI : minorIdeal V ≠ ⊥ := by
    intro hzero
    have hmem := columnMinor_mem_minorIdeal V s₀
    rw [hzero, Ideal.mem_bot] at hmem
    exact hminor hmem
  have hflatT : Flat (globalTransformMap R A (minorIdeal V)) := by
    apply globalTransformMap_flat_of_minorCharts R A V
    intro s
    obtain ⟨B, hB⟩ := exists_basis_pureTransform_minorChart m hm b δ V hδ hcoord s.val s.property
    let S := affineBlowupFractionChart (minorIdeal V) (columnMinor V s.val)
    let C := B.map (pureTransformLinearEquiv R A S).symm
    let : Module.Free S (pureTransformAlgebra R A S) := Module.Free.of_basis C
    exact chartTransformMap_flat R A S
  have hU := prescribed_flat_open_subset_freeLocus R A U hflat
  exact ⟨n, r, m, V, hm, hfg, hI, affineBlowupStructure_isProjective _ hfg,
    ModuleFlattening.minorBlowup_isModification V hI hfg, inferInstance, hflatT,
    ModuleFlatteningCenter.isIso_restrict_of_subset_freeLocus m hm b δ V hcoord s₀ hminor U hU,
    ModuleFlatteningCenter.center_le_compl_of_subset_freeLocus m hm b δ V hcoord s₀ hminor U hU⟩

/-- The prescribed-flat-open center condition of the finite-morphism case of
de Jong 2.19 over a Noetherian affine integral base, with the actual original
finite algebra and actual native global strict transform. -/
theorem exists_finite_flat_transform_preserving_open
    [IsNoetherianRing R] [Module.Finite R A] (U : (Spec (.of R)).Opens)
    (hflat : Flat (originalMap R A ∣_ U)) :
    ∃ (n r : ℕ) (m : Fin n → A) (V : Matrix (Fin r) (Fin n) R),
      Submodule.span R (Set.range m) = ⊤ ∧ (minorIdeal V).FG ∧ minorIdeal V ≠ ⊥ ∧
      IsProjectiveOver (affineBlowupStructure (minorIdeal V)) ∧
      IsModification (affineBlowupStructure (minorIdeal V)) ∧
      IsFinite (globalTransformMap R A (minorIdeal V)) ∧
      Flat (globalTransformMap R A (minorIdeal V)) ∧
      IsIso (affineBlowupStructure (minorIdeal V) ∣_ U) ∧
      ModificationCenter.center (affineBlowupStructure (minorIdeal V)) ≤ U.compl := by
  let : Module.FinitePresentation R A := Module.finitePresentation_of_finite R A
  exact exists_finite_flat_transform_preserving_open_of_finitePresentation R A U hflat

end Hironaka.Geometry.FiniteMorphismFlatteningCenter
