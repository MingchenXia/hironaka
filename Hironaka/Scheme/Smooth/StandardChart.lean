/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.Smooth.ChartDefs
public import Hironaka.Algebra.RegularSmooth.Stalk
public import Hironaka.Scheme.BlowUp.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
import Hironaka.Algebra.RegularSmooth.SchemeForms
import Hironaka.Scheme.BlowUp.AffineBlowUp.Universal.Membership
import Hironaka.Scheme.BlowUp.InverseImage
import Hironaka.Scheme.Smooth.Adapted
import Hironaka.Scheme.Smooth.AdaptedCoordinates
import Hironaka.Scheme.Smooth.BlowUpSmooth
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The standard charts of a smooth blow-up: the ideal of the center and the chart coordinates

`E : EtaleCoordinatesAdapted f n r Z x` is a chart of étale coordinates adapted to `Z`,
`J = E.centerIdeal = (v_0, …, v_{r-1}) ⊆ Γ(U)` Kollár's `(x_1, …, x_r)` [Kol07, Definition 60], and
`Γ(U)[J/x_j]` the chart ring of `x_j` (the affine blow-up algebra of Hauser's local blow-up,
[Hau14, Definition 4.16]).

* `Z(U) = J` (`ideal_eq_centerIdeal`), from `Z ∩ U = g⁻¹(L)` (`E.adapted`) and the ideal of the
  coordinate subspace pulled back along the coordinate morphism `g` (`toAffineSpace_appTop_X`).
* Kollár's `x_i = y_i x_j` for `i < r` with `y_i = x_i/x_j` (the coordinates (60.2) of
  [Kol07, Definition 60]; the local parameters at a point of the exceptional divisor in the proof
  of [Wlo05, Lemma 2.6.3]), an identity in `Γ(U)[1/x_j]` (`algebraMap_eq_ratio_mul`).
* `𝒪_{B_ZX,x'}` is a regular local ring of dimension `n − trdeg_k κ(x')` at every point `x'`
  (`isRegularLocalRing_stalk_blowUp`, `ringKrullDim_stalk_blowUp_add_trdeg`), from the smoothness
  of `B_Z X` of relative dimension `n` (`BlowUpSmooth.lean`) with the comparison of regular and
  smooth points (`Hironaka/Algebra/RegularSmooth/`).

Used for the charts and stalks of a smooth blow-up in `ChartIso.lean`,
`Hironaka/Scheme/Snc/ChartSncData.lean`, `Hironaka/Scheme/Snc/ChartStalk.lean` and
`Hironaka/Resolution/Algebraic/Wlo05/EmbeddedChainColon.lean`.
-/

public section

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry

open Scheme.IdealSheafData AlgebraicGeometry affineBlowUpAlgebra

variable {k : Type u} [Field k] {X : Scheme.{u}}

section Coordinates

variable {f : X ⟶ Spec (.of k)} {n r : ℕ} {Z : X.IdealSheafData} {x : X}
  (E : EtaleCoordinatesAdapted f n r Z x) {j : Fin n} (hj : j.val < r)

/-- In the chart of `x_j`, `x_i = y_i x_j` for `i < r`, where `y_i = x_i/x_j` (the coordinates
(60.2) of [Kol07, Definition 60]; the proof of [Wlo05, Lemma 2.6.3]). -/
theorem algebraMap_eq_ratio_mul {i : Fin n} (hi : i.val < r) :
    algebraMap Γ(X, E.U) (affineBlowUpAlgebra E.centerIdeal (E.coord j hj)) (E.v i) =
      ratio E.centerIdeal (E.coord j hj) (E.coord i hi) * algebraMap Γ(X, E.U) _ (E.v j) :=
  (algebraMap_eq_mul_ratio E.centerIdeal (E.coord j hj) (E.coord i hi)).trans (mul_comm _ _)

end Coordinates

section Regular

variable [PerfectField k] (f : X ⟶ Spec (.of k)) (n r : ℕ) [SmoothOfRelativeDimension n f]
  (Z : X.IdealSheafData) [SmoothOfRelativeDimension (n - r) (Z.subschemeι ≫ f)] (hrn : r ≤ n)

include f n r hrn

/-- The local rings of `B_Z X` are regular (`B_Z X` is smooth over `k`). -/
theorem isRegularLocalRing_stalk_blowUp (x' : blowUp Z) :
    IsRegularLocalRing ((blowUp Z).presheaf.stalk x') := by
  have := smooth_blowUpπ_comp f n r Z hrn
  exact isRegularLocalRing_stalk (blowUpπ Z ≫ f) x'

/-- `dim 𝒪_{B_ZX,x'} + trdeg_k κ(x') = n` (`B_Z X` is smooth of relative dimension `n` over `k`;
[Sta, Tag 0A21]). -/
theorem ringKrullDim_stalk_blowUp_add_trdeg (x' : blowUp Z) :
    letI := (blowUpπ Z ≫ f).stalkAlgebra x'
    ringKrullDim ((blowUp Z).presheaf.stalk x') +
      ((Cardinal.toENat (Algebra.trdeg k (ResidueField ((blowUp Z).presheaf.stalk x'))) : ℕ∞) :
        WithBot ℕ∞) = n := by
  have := smoothOfRelativeDimension_blowUpπ_comp f n r Z hrn
  exact Scheme.ringKrullDim_stalk_add_trdeg_residueField_of_smoothOfRelativeDimension
    (blowUpπ Z ≫ f) n x'

end Regular

end AlgebraicGeometry

namespace AlgebraicGeometry

open AlgebraicGeometry affineBlowUpAlgebra

variable {k : Type u} [Field k] {X : Scheme.{u}}

section IdealOfCenter

variable {f : X ⟶ Spec (.of k)} {n r : ℕ} {Z : X.IdealSheafData} {x : X}

/-- The restriction `Γ(X, U) → Γ(U, ⊤)` along `U.ι` is the canonical isomorphism `topIso.inv`. -/
theorem ι_appLE_top_eq_topIso_inv (U : X.Opens) (e : (⊤ : (U : Scheme.{u}).Opens) ≤ U.ι ⁻¹ᵁ U) :
    U.ι.appLE U ⊤ e = U.topIso.inv := by
  rw [Scheme.Opens.ι_appLE]
  simp only [Scheme.Opens.topIso]
  congr 1

/-- On the sections of the chart `U`, the ideal of `Z ∩ U` is `J = (v_0, …, v_{r-1})` (Kollár's
"`Z = (x_1 = ⋯ = x_r = 0)`", [Kol07, Definition 60]): from `Z ∩ U = g⁻¹(L)` and the pull-back of
the coordinate functions along `g` (`toAffineSpace_appTop_X`). -/
theorem ideal_eq_centerIdeal (E : EtaleCoordinatesAdapted f n r Z x) :
    Z.ideal E.U = E.centerIdeal := by
  have e : (⊤ : (E.U.1 : Scheme.{u}).Opens) ≤ E.U.1.ι ⁻¹ᵁ E.U.1 := by
    intro y _
    exact y.2
  have h1 := Z.ideal_comap_of_le E.U.1.ι E.U ⟨⊤, isAffineOpen_top _⟩ e
  have h2 := ideal_comap_specIdealSheaf
    (affineBlowUpAlgebra.coordinateIdeal k {j : Fin n | j.val < r}) (toAffineSpace f E.U.1 E.v)
    ⟨⊤, isAffineOpen_top _⟩
  rw [E.adapted] at h1
  have h3 : (Z.ideal E.U).map (E.U.1.ι.appLE E.U.1 ⊤ e).hom =
      (affineBlowUpAlgebra.coordinateIdeal k {j : Fin n | j.val < r}).map
        (sectionsHom (toAffineSpace f E.U.1 E.v) ⊤) :=
    h1.symm.trans h2
  rw [ι_appLE_top_eq_topIso_inv] at h3
  have key : ∀ i : Fin n, sectionsHom (toAffineSpace f E.U.1 E.v) ⊤ (MvPolynomial.X i) =
      E.U.1.topIso.inv (E.v i) := fun i => by
    change ((toAffineSpace f E.U.1 E.v).appLE ⊤ ⊤ le_top).hom
      ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) k))).inv (MvPolynomial.X i)) = _
    have happ : (toAffineSpace f E.U.1 E.v).appLE ⊤ ⊤ le_top = (toAffineSpace f E.U.1 E.v).app ⊤ :=
      Scheme.Hom.appLE_eq_app _
    rw [happ]
    exact toAffineSpace_app_top_X f E.U.1 E.v i
  have h4 : (affineBlowUpAlgebra.coordinateIdeal k {j : Fin n | j.val < r}).map
      (sectionsHom (toAffineSpace f E.U.1 E.v) ⊤) = E.centerIdeal.map E.U.1.topIso.inv.hom := by
    rw [affineBlowUpAlgebra.coordinateIdeal, Ideal.map_span, EtaleCoordinatesAdapted.centerIdeal,
      Ideal.map_span]
    congr 1
    ext w
    constructor
    · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
      exact ⟨_, ⟨⟨i, hi⟩, rfl⟩, (key i).symm⟩
    · rintro ⟨_, ⟨⟨i, hi⟩, rfl⟩, rfl⟩
      exact ⟨_, ⟨i, hi, rfl⟩, key i⟩
  rw [h4] at h3
  have hbij : Function.Bijective E.U.1.topIso.inv.hom :=
    (ConcreteCategory.bijective_of_isIso E.U.1.topIso.inv)
  have := congrArg (Ideal.comap E.U.1.topIso.inv.hom) h3
  rwa [Ideal.comap_map_of_bijective _ hbij, Ideal.comap_map_of_bijective _ hbij] at this

end IdealOfCenter

end AlgebraicGeometry
