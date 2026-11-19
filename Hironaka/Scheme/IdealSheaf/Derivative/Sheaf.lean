/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.RegularSmooth.Stalk
public import Hironaka.Algebra.Derivative.Basic
public import Hironaka.Scheme.IdealSheaf.Defs
import Hironaka.Algebra.Derivative.Localization
import Hironaka.Scheme.BlowUp.InvertibleSheaf
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.Smooth.EtaleCoordinates
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The derivative ideal sheaf `D(I)`

[Kol07, Definition 73]: for a scheme `X` over a field `k` (`f : X ⟶ Spec k`) and an ideal sheaf `I`,
the derivative ideal sheaf `D(I)` has, on each affine open `U`, the derivative
`Ideal.derivative k (I(U))` of the ideal of sections for the `k`-algebra structure
`f.sectionsAlgebra U` (`Hironaka/Algebra/RegularSmooth/SmoothAt.lean`); it is packaged through
Mathlib's `IdealSheafData.ofIdeals`, and the compatibility with restriction to basic opens, for `f`
locally of finite type (derivations extend to localizations, and every derivation of a localization
is locally one of them because `Ω_{Γ(U)/k}` is finitely presented,
`Hironaka/Algebra/Derivative/Localization.lean`), is what identifies `(D(I))(U)` with `D(I(U))`
(`ideal_derivative`). The higher derivatives `Dʳ(I)` iterate (`derivativeIter`), and the stalks
are the derivatives of the stalks: `D(I)_x = D(I_x)` (`stalkIdeal_derivative`,
`stalkIdeal_derivativeIter`). Also here: the `ℚ`-algebra structure `ℚ → k → 𝒪_{X,x}` of a stalk in
characteristic zero (`stalkAlgebraRat`), which the coordinate structures `RegularCoords` need.

Used for Theorem 76 and Theorem 88 on schemes
(`Hironaka/Scheme/BlowUpSequence/TransformDerivative.lean`,
`Hironaka/Scheme/BlowUpSequence/Theorem88Basic.lean`), for maximal contact and tuning
(`Hironaka/Resolution/Algebraic/MaximalContact/Invariant.lean`,
`Hironaka/Resolution/Algebraic/Tuning/Corollary101.lean`), for D-balanced ideals
(`Hironaka/Resolution/Algebraic/Balanced/Basic.lean`) and throughout `Hironaka/Derivative`.
-/

@[expose] public section

namespace AlgebraicGeometry.Scheme.IdealSheafData

open CategoryTheory

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The `ℚ`-algebra structure on a stalk of a scheme over a field `k` of characteristic zero,
`ℚ → k → 𝒪_{X,x}` (through `f.stalkAlgebra x`); not an instance, since it depends on `f`. The
coordinate structures `RegularCoords` and the derivative ideals of `Hironaka/Local` need
`[Algebra ℚ R]`. -/
@[instance_reducible]
noncomputable def _root_.AlgebraicGeometry.Scheme.Hom.stalkAlgebraRat [CharZero k] (x : X) :
    Algebra ℚ (X.presheaf.stalk x) :=
  letI := f.stalkAlgebra x
  ((algebraMap k (X.presheaf.stalk x)).comp (algebraMap ℚ k)).toAlgebra

/-- **The derivative ideal sheaf** `D(I)` of `I` on the `k`-scheme `X` ([Kol07, (73.1)]): on an
affine open `U`, the derivative of `I(U)` for the `k`-algebra structure of `Γ(X, U)` induced by
`f`. -/
noncomputable def derivative (I : X.IdealSheafData) : X.IdealSheafData :=
  ofIdeals fun U => letI := f.sectionsAlgebra U.1; Ideal.derivative k (I.ideal U)

/-- **The higher derivative ideal sheaves** ([Kol07, (73.2)]): `D⁰(I) = I`,
`D^{r+1}(I) = D(Dʳ(I))`. -/
noncomputable def derivativeIter (r : ℕ) (I : X.IdealSheafData) : X.IdealSheafData :=
  (derivative f)^[r] I

@[simp] theorem derivativeIter_zero (I : X.IdealSheafData) : derivativeIter f 0 I = I := rfl

@[simp] theorem derivativeIter_succ (r : ℕ) (I : X.IdealSheafData) :
    derivativeIter f (r + 1) I = derivative f (derivativeIter f r I) :=
  Function.iterate_succ_apply' _ _ _

/-- On every affine open, `(D(I))(U) ⊆ D(I(U))` (Mathlib's `ideal_ofIdeals_le`); equality holds
for `f` locally of finite type (`ideal_derivative`). -/
theorem ideal_derivative_le (I : X.IdealSheafData) (U : X.affineOpens) :
    (derivative f I).ideal U ≤ letI := f.sectionsAlgebra U.1; Ideal.derivative k (I.ideal U) :=
  ideal_ofIdeals_le _ U

/-! ### The gluing, for `f` locally of finite type -/

section FiniteType

variable [LocallyOfFiniteType f]

/-- For `f` locally of finite type, `Γ(X, U)` is a finitely presented `k`-algebra on every affine
`U` (a field is Noetherian), so `Ω_{Γ(X, U)/k}` is finitely presented. -/
theorem finitePresentation_kaehlerDifferential_sections (U : X.affineOpens) :
    letI := f.sectionsAlgebra U.1
    Module.FinitePresentation Γ(X, U.1) (Ω[Γ(X, U.1)⁄k]) := by
  let _ := f.sectionsAlgebra U.1
  have : Algebra.FinitePresentation k Γ(X, U.1) :=
    Algebra.FinitePresentation.of_finiteType.mp (f.finiteType_sectionsAlgebra U.2)
  infer_instance

/-- The family `U ↦ D(I(U))` is compatible with restriction to basic opens: `Γ(X, D(s))` is the
localization of `Γ(X, U)` at `s` (Mathlib's `isLocalization_basicOpen`), `I(D(s)) = I(U)_s`
(`map_ideal_basicOpen`), and `D(I(U)_s) = D(I(U))_s` (`derivative_map`). -/
theorem map_derivative_ideal_basicOpen (I : X.IdealSheafData) (U : X.affineOpens) (s : Γ(X, U)) :
    (letI := f.sectionsAlgebra U.1; Ideal.derivative k (I.ideal U)).map
        (X.presheaf.map (homOfLE <| X.basicOpen_le s).op).hom =
      letI := f.sectionsAlgebra (X.affineBasicOpen s).1
      Ideal.derivative k (I.ideal (X.affineBasicOpen s)) := by
  let _ := f.sectionsAlgebra U.1
  let _ := f.sectionsAlgebra (X.basicOpen s)
  have hloc : IsLocalization.Away s Γ(X, X.basicOpen s) := U.2.isLocalization_basicOpen s
  have hST : IsScalarTower k Γ(X, U.1) Γ(X, X.basicOpen s) := by
    have h := isScalarTower_sectionsAlgebra_restrict f (X.basicOpen_le s)
    exact h
  have hFP := finitePresentation_kaehlerDifferential_sections f U
  rw [← I.map_ideal_basicOpen U s]
  exact (@Ideal.derivative_map k _ _ _ _ _ _ _ _ hST (Submonoid.powers s) hloc hFP (I.ideal U)).symm

/-- For `f` locally of finite type, the derivative ideal sheaf has `(D(I))(U) = D(I(U))` on every
affine open ([Kol07, (73.1)]): the compatible family `U ↦ D(I(U))` is itself an ideal sheaf,
hence the largest one below it. -/
theorem ideal_derivative (I : X.IdealSheafData) (U : X.affineOpens) :
    (derivative f I).ideal U = letI := f.sectionsAlgebra U.1; Ideal.derivative k (I.ideal U) := by
  refine le_antisymm (ideal_derivative_le f I U) ?_
  let J : X.IdealSheafData :=
    { ideal := fun U => letI := f.sectionsAlgebra U.1; Ideal.derivative k (I.ideal U)
      map_ideal_basicOpen := fun U s => map_derivative_ideal_basicOpen f I U s }
  have hJ : J ≤ derivative f I := le_ofIdeals_iff.mpr le_rfl
  exact hJ U

/-! ### Stalks -/

/-- The stalk of `D(I)` at `x` is the derivative of the stalk `I_x` in the `k`-algebra `𝒪_{X,x}`:
on an affine `U ∋ x` the stalk is the localization of `Γ(X, U)` at the prime of `x` (Mathlib's
`isLocalization_stalk`), and `D(I(U))_x = D(I(U)_x)` by `derivative_map`. -/
theorem stalkIdeal_derivative (I : X.IdealSheafData) (x : X) :
    (derivative f I).stalkIdeal x =
      letI := f.stalkAlgebra x; Ideal.derivative k (I.stalkIdeal x) := by
  obtain ⟨U, hxU⟩ := exists_affineOpens_mem x
  let _ := f.sectionsAlgebra U.1
  let _ := f.stalkAlgebra x
  let _ := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have hloc := U.2.isLocalization_stalk ⟨x, hxU⟩
  have hST := f.isScalarTower_sectionsAlgebra_stalk U.1 hxU
  have hFP := finitePresentation_kaehlerDifferential_sections f U
  rw [stalkIdeal_eq_map_germ _ U hxU, stalkIdeal_eq_map_germ I U hxU, ideal_derivative f I U]
  exact (@Ideal.derivative_map k _ _ _ _ _ _ _ _ hST _ hloc hFP (I.ideal U)).symm

/-- `Dʳ(I)_x = Dʳ(I_x)`. -/
theorem stalkIdeal_derivativeIter (r : ℕ) (I : X.IdealSheafData) (x : X) :
    (derivativeIter f r I).stalkIdeal x =
      letI := f.stalkAlgebra x; Ideal.derivativeIter k r (I.stalkIdeal x) := by
  let _ := f.stalkAlgebra x
  induction r with
  | zero => rfl
  | succ r ih => rw [derivativeIter_succ, stalkIdeal_derivative, ih, Ideal.derivativeIter_succ]

end FiniteType

end AlgebraicGeometry.Scheme.IdealSheafData
