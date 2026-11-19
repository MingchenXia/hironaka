import Hironaka.Analytic.AnalyticCoherentJacobianStratification

set_option autoImplicit false

/-!
# Reduced hypersurface input for the Jacobian derivative core

For a holomorphic hypersurface generator, the algebraic statement that its
principal germ ideal is reduced is expected to imply that some first derivative
is nonzero on a dense relative-open part of every nonempty local branch.
`HolomorphicGermRing` now supplies a holomorphic local ring, and
`HolomorphicGermReducednessBridge` proves the conditional local implication
from a radical principal germ ideal together with a unit-times-coordinate-power
factorization to a nonzero coordinate derivative.

Accordingly this file names that differential consequence explicitly as
`HasGenericallyNonzeroHypersurfaceDerivative`.  It is not presented as a
definition of algebraic reducedness.  From it we prove the exact usable result:
the derivative core contains no nonempty relatively open hypersurface patch,
and is therefore a proper local core when the branch is nonempty.

The remaining gap is analytic-to-algebraic: the project still has no theorem
that converts the article's reduced local hypersurface presentation into both
the radicality of its concrete principal germ ideal and the required local
unit-times-coordinate-power factorization at the relevant points.  Thus the
generic derivative predicate below remains the exact global input until that
translation is formalized.
-/

open Set

namespace Hironaka.ReducedHypersurfaceJacobianCore

open Hironaka.RegularLocusDense AnalyticLocalStatement

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The explicit differential consequence expected of a nonzero reduced local
hypersurface generator: every nonempty relatively open patch of its zero set
contains a point where a coordinate derivative is nonzero. -/
def HasGenericallyNonzeroHypersurfaceDerivative (S : Set M) (x : M)
    (f : ComplexModel n → ℂ) : Prop :=
  ∀ O : Set M, IsOpen O → (O ∩ S).Nonempty →
    ∃ y ∈ O ∩ S, ∃ j : Fin n,
      fderiv ℂ f ((complexChartAt (n := n) x).val y)
        (AnalyticJacobianSingularCore.coordinateDirection j) ≠ 0

omit [IsComplexManifold n M] in
/-- A point with a nonzero coordinate derivative does not lie in the
corresponding derivative core. -/
theorem not_mem_localHypersurfaceDerivativeCore_of_minor_ne_zero
    {S : Set M} {x y : M} (f : ComplexModel n → ℂ)
    {j : Fin n}
    (hminor : fderiv ℂ f ((complexChartAt (n := n) x).val y)
      (AnalyticJacobianSingularCore.coordinateDirection j) ≠ 0) :
    y ∉ AnalyticCoherentJacobianStratification.localHypersurfaceDerivativeCore
      (n := n) S x f := by
  intro hycore
  change y ∈ S ∧ ∀ k : Fin n,
    fderiv ℂ f ((complexChartAt (n := n) x).val y)
      (AnalyticJacobianSingularCore.coordinateDirection k) = 0 at hycore
  exact hminor (hycore.2 j)

omit [IsComplexManifold n M] in
/-- Under the explicit generically-nonzero derivative input, the derivative
core cannot contain a nonempty relatively open subset of the hypersurface. -/
theorem no_nonempty_relativeOpen_subset_localHypersurfaceDerivativeCore
    {S : Set M} {x : M} {f : ComplexModel n → ℂ}
    (hgen : HasGenericallyNonzeroHypersurfaceDerivative (n := n) S x f)
    {O : Set M} (hO : IsOpen O)
    (hsub : O ∩ S ⊆
      AnalyticCoherentJacobianStratification.localHypersurfaceDerivativeCore
        (n := n) S x f) :
    ¬ (O ∩ S).Nonempty := by
  intro hOS
  obtain ⟨y, hyOS, j, hminor⟩ := hgen O hO hOS
  exact not_mem_localHypersurfaceDerivativeCore_of_minor_ne_zero f hminor
    (hsub hyOS)

omit [IsComplexManifold n M] in
/-- In particular, the derivative core is a strict subset of a nonempty
hypersurface satisfying the explicit generically-nonzero derivative input. -/
theorem localHypersurfaceDerivativeCore_ne_of_genericallyNonzero
    {S : Set M} {x : M} {f : ComplexModel n → ℂ}
    (hgen : HasGenericallyNonzeroHypersurfaceDerivative (n := n) S x f)
    (hS : S.Nonempty) :
    AnalyticCoherentJacobianStratification.localHypersurfaceDerivativeCore
      (n := n) S x f ≠ S := by
  intro hcore
  have hsub : (univ : Set M) ∩ S ⊆
      AnalyticCoherentJacobianStratification.localHypersurfaceDerivativeCore
        (n := n) S x f := by
    simp [hcore]
  have hempty := no_nonempty_relativeOpen_subset_localHypersurfaceDerivativeCore
    hgen isOpen_univ hsub
  exact hempty (by simpa using hS)

/-- The explicit differential input for a one-equation local-decomposition
branch.  It is the exact input needed to make its analytic derivative core
strict; the remaining presentation-to-germ bridge should prove this predicate
for reduced proper hypersurface generators. -/
def HasGenericallyNonzeroLocalPieceHypersurfaceDerivative
    {A : Set M} {p : M} (D : LocalDecomposition (n := n) A p)
    (i : Fin D.count) (hone : D.eqnCount i = 1) : Prop :=
  HasGenericallyNonzeroHypersurfaceDerivative (n := n) (D.piece i) p
    (AnalyticCoherentJacobianStratification.localHypersurfaceEquation (n := n) D i hone)

omit [IsComplexManifold n M] in
/-- The analytic derivative core of a nonempty one-equation branch is proper
once its generator satisfies the explicit generic nonvanishing consequence of
reducedness. -/
theorem localPieceHypersurfaceDerivativeCore_ne_of_genericallyNonzero
    {A : Set M} {p : M} (D : LocalDecomposition (n := n) A p)
    (i : Fin D.count) (hone : D.eqnCount i = 1)
    (hgen : HasGenericallyNonzeroLocalPieceHypersurfaceDerivative (n := n) D i hone)
    (hpiece : (D.piece i).Nonempty) :
    AnalyticCoherentJacobianStratification.localHypersurfaceDerivativeCore
      (n := n) (D.piece i) p
      (AnalyticCoherentJacobianStratification.localHypersurfaceEquation (n := n) D i hone)
      ≠ D.piece i :=
  localHypersurfaceDerivativeCore_ne_of_genericallyNonzero hgen hpiece

omit [IsComplexManifold n M] in
/-- The same input gives the strict local statement directly: no nonempty
relatively open patch of the branch is swallowed by its derivative core. -/
theorem no_nonempty_relativeOpen_subset_localPieceHypersurfaceDerivativeCore
    {A : Set M} {p : M} (D : LocalDecomposition (n := n) A p)
    (i : Fin D.count) (hone : D.eqnCount i = 1)
    (hgen : HasGenericallyNonzeroLocalPieceHypersurfaceDerivative (n := n) D i hone)
    {O : Set M} (hO : IsOpen O)
    (hsub : O ∩ D.piece i ⊆
      AnalyticCoherentJacobianStratification.localHypersurfaceDerivativeCore
        (n := n) (D.piece i) p
        (AnalyticCoherentJacobianStratification.localHypersurfaceEquation (n := n) D i hone)) :
    ¬ (O ∩ D.piece i).Nonempty :=
  no_nonempty_relativeOpen_subset_localHypersurfaceDerivativeCore hgen hO hsub

end

end Hironaka.ReducedHypersurfaceJacobianCore
