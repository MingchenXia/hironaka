import DeJongAlterations.StableModification.Curves.SemistableOpenTaylor
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Relative plane curves with invertible Hessian have nodal geometric fibres

Let `R` be a ring, `P` an `R`-algebra which is étale over `R[X₀, X₁]`, and `g ∈ P` an element whose
Hessian determinant (`SemistableOpen.hessian`) is a unit of `P`. Then every closed point of every
geometric fibre of `Spec (P/(g)) → Spec R` is a smooth point or an ordinary double point
(`hypersurface_geometricPoint`): for an algebraically closed field `K` with `R → K` and a maximal
ideal `y` of `K ⊗_R P/(g)`, either the maximal ideal of the local ring at `y` is principal, or its
completion is `K[[u, v]]/(uv)`.

The proof base changes `P` to `K ⊗_R P`, étale over `K[X₀, X₁]` (`basePlaneEtale`, via the pushout
square `R[X] → P`, `K[X] → K ⊗_R P` and the stability of étale maps under base change), with the
same partial derivatives (`hessian_baseChange`), and applies the field-level classification of
`SemistableOpenTaylor` at the rational point under `y` (Hilbert's Nullstellensatz).

This is the "nearby fibres" half of the openness of the semi-stable locus (M. Temkin, *Stable
modification of relative curves*, Lemma 5.1(i), T:3282–3292; blueprint `sm-semistable-curves.tex`).
-/

noncomputable section

open IsLocalRing TensorProduct

namespace DeJongAlterations.StableModification.Curves.SemistableOpen

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

/-- **Nullstellensatz**: the residue field of a maximal ideal of a finitely generated algebra over
an algebraically closed field `K` is `K`. -/
theorem algebraMap_quotient_surjective_of_isAlgClosed (K : Type u) [Field K] [IsAlgClosed K]
    (A : Type u) [CommRing A] [Algebra K A] [Algebra.FiniteType K A] (Q : Ideal A) [Q.IsMaximal] :
    Function.Surjective (algebraMap K (A ⧸ Q)) := by
  let := Ideal.Quotient.field Q
  have : Algebra.FiniteType K (A ⧸ Q) :=
    Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  have := finite_of_finite_type_of_isJacobsonRing K (A ⧸ Q)
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral.2

section BaseChange

variable (R : Type u) [CommRing R] (K : Type u) [Field K] [Algebra R K]
  (P : Type u) [CommRing P] [Algebra R P]
  [Algebra (MvPolynomial (Fin 2) R) P] [IsScalarTower R (MvPolynomial (Fin 2) R) P]

/-- The plane structure of the base change: `K[X₀, X₁] → K ⊗_R P`, `Xᵢ ↦ 1 ⊗ uᵢ`. -/
def basePlaneMap : MvPolynomial (Fin 2) K →ₐ[K] K ⊗[R] P :=
  MvPolynomial.aeval fun i => 1 ⊗ₜ coord R P i

/-- The `K[X₀, X₁]`-algebra structure of `K ⊗_R P`. -/
abbrev basePlaneAlgebra : Algebra (MvPolynomial (Fin 2) K) (K ⊗[R] P) :=
  (basePlaneMap R K P).toRingHom.toAlgebra

omit [IsScalarTower R (MvPolynomial (Fin 2) R) P] in
theorem basePlane_isScalarTower :
    letI := basePlaneAlgebra R K P
    IsScalarTower K (MvPolynomial (Fin 2) K) (K ⊗[R] P) := by
  let := basePlaneAlgebra R K P
  exact IsScalarTower.of_algebraMap_eq fun k => ((basePlaneMap R K P).commutes k).symm

omit [IsScalarTower R (MvPolynomial (Fin 2) R) P] in
theorem basePlane_coord (j : Fin 2) :
    letI := basePlaneAlgebra R K P
    coord K (K ⊗[R] P) j = 1 ⊗ₜ coord R P j := by
  let := basePlaneAlgebra R K P
  change basePlaneMap R K P (MvPolynomial.X j) = _
  simp [basePlaneMap]

/-- The base change `K ⊗_R P` as an algebra over `K[X₀, X₁]` (via `basePlaneAlgebra`) and over `P`
(via the right factor); a type synonym, so that these structures do not become instances on
`K ⊗_R P`. -/
def PlaneBaseChange : Type u := K ⊗[R] P

instance : CommRing (PlaneBaseChange R K P) := inferInstanceAs (CommRing (K ⊗[R] P))
instance : Algebra K (PlaneBaseChange R K P) := inferInstanceAs (Algebra K (K ⊗[R] P))
instance : Algebra R (PlaneBaseChange R K P) := inferInstanceAs (Algebra R (K ⊗[R] P))
instance : IsScalarTower R K (PlaneBaseChange R K P) :=
  inferInstanceAs (IsScalarTower R K (K ⊗[R] P))
instance : Algebra (MvPolynomial (Fin 2) K) (PlaneBaseChange R K P) := basePlaneAlgebra R K P
instance : IsScalarTower K (MvPolynomial (Fin 2) K) (PlaneBaseChange R K P) :=
  basePlane_isScalarTower R K P
instance : Algebra P (PlaneBaseChange R K P) :=
  (Algebra.TensorProduct.rightAlgebra : Algebra P (K ⊗[R] P))
instance : Algebra (MvPolynomial (Fin 2) R) (PlaneBaseChange R K P) :=
  ((algebraMap P (PlaneBaseChange R K P)).comp (algebraMap (MvPolynomial (Fin 2) R) P)).toAlgebra
instance : IsScalarTower (MvPolynomial (Fin 2) R) P (PlaneBaseChange R K P) :=
  .of_algebraMap_eq' rfl
instance : IsScalarTower R P (PlaneBaseChange R K P) := .of_algebraMap_eq fun r => by
  change algebraMap R K r ⊗ₜ (1 : P) = (1 : K) ⊗ₜ algebraMap R P r
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
instance : IsScalarTower R (MvPolynomial (Fin 2) R) (PlaneBaseChange R K P) :=
  .of_algebraMap_eq fun r => by
    change algebraMap R (PlaneBaseChange R K P) r = algebraMap P (PlaneBaseChange R K P)
      (algebraMap (MvPolynomial (Fin 2) R) P (algebraMap R _ r))
    rw [← IsScalarTower.algebraMap_apply R (MvPolynomial (Fin 2) R) P r,
      ← IsScalarTower.algebraMap_apply R P (PlaneBaseChange R K P) r]
instance : IsScalarTower R (MvPolynomial (Fin 2) K) (PlaneBaseChange R K P) :=
  .of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R K (MvPolynomial (Fin 2) K),
      ← IsScalarTower.algebraMap_apply K (MvPolynomial (Fin 2) K) (PlaneBaseChange R K P),
      ← IsScalarTower.algebraMap_apply R K (PlaneBaseChange R K P)]

section Pushout

attribute [local instance] MvPolynomial.algebraMvPolynomial

instance : IsScalarTower (MvPolynomial (Fin 2) R) (MvPolynomial (Fin 2) K)
    (PlaneBaseChange R K P) := by
  refine .of_algebraMap_eq fun a => ?_
  change algebraMap P (PlaneBaseChange R K P) (algebraMap _ P a) =
    basePlaneMap R K P (MvPolynomial.map (algebraMap R K) a)
  induction a using MvPolynomial.induction_on with
  | C r =>
    have hc : basePlaneMap R K P (MvPolynomial.C (algebraMap R K r)) =
        algebraMap K (K ⊗[R] P) (algebraMap R K r) := (basePlaneMap R K P).commutes _
    rw [MvPolynomial.map_C, hc]
    change algebraMap P (PlaneBaseChange R K P) (algebraMap (MvPolynomial (Fin 2) R) P
      (algebraMap R (MvPolynomial (Fin 2) R) r)) = _
    rw [← IsScalarTower.algebraMap_apply R (MvPolynomial (Fin 2) R) P r,
      ← IsScalarTower.algebraMap_apply R P (PlaneBaseChange R K P) r]
    exact IsScalarTower.algebraMap_apply R K (PlaneBaseChange R K P) r
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
  | mul_X a i ha =>
    rw [map_mul, map_mul, ha, map_mul, map_mul, MvPolynomial.map_X]
    congr 1
    simp [basePlaneMap, coord]
    rfl

/-- **The base change square is a pushout**: `K ⊗_R P = K[X₀, X₁] ⊗_{R[X₀, X₁]} P`. -/
instance planeBaseChange_isPushout :
    Algebra.IsPushout (MvPolynomial (Fin 2) R) P (MvPolynomial (Fin 2) K)
      (PlaneBaseChange R K P) := by
  have hbig : Algebra.IsPushout R P K (PlaneBaseChange R K P) := TensorProduct.isPushout'
  exact (Algebra.IsPushout.comp_iff R (MvPolynomial (Fin 2) R) K (MvPolynomial (Fin 2) K)
    (T := P) (T' := PlaneBaseChange R K P)).mp hbig

/-- **Base change of a surface étale over the plane.** -/
instance [Algebra.Etale (MvPolynomial (Fin 2) R) P] :
    Algebra.Etale (MvPolynomial (Fin 2) K) (PlaneBaseChange R K P) := by
  have := RingHom.Etale.isStableUnderBaseChange (MvPolynomial (Fin 2) R) P (MvPolynomial (Fin 2) K)
    (PlaneBaseChange R K P) (RingHom.etale_algebraMap.mpr inferInstance)
  exact RingHom.etale_algebraMap.mp this

end Pushout

/-- The inclusion `P → K ⊗_R P`, `p ↦ 1 ⊗ p`. -/
def toPlaneBaseChange : P →ₐ[R] PlaneBaseChange R K P := Algebra.TensorProduct.includeRight

omit [IsScalarTower R (MvPolynomial (Fin 2) R) P] in
theorem toPlaneBaseChange_coord (j : Fin 2) :
    toPlaneBaseChange R K P (coord R P j) = coord K (PlaneBaseChange R K P) j :=
  (basePlane_coord R K P j).symm

/-- **Partial derivatives commute with base change**, hence so does the Hessian. -/
theorem hessian_baseChange [Algebra.Etale (MvPolynomial (Fin 2) R) P] (g : P) :
    hessian K (PlaneBaseChange R K P) (toPlaneBaseChange R K P g) =
      toPlaneBaseChange R K P (hessian R P g) :=
  hessian_map (toPlaneBaseChange R K P) (toPlaneBaseChange_coord R K P) g

end BaseChange

section Points

variable (R : Type u) [CommRing R] (K : Type u) [Field K] [Algebra R K]
  (P : Type u) [CommRing P] [Algebra R P]
  [Algebra (MvPolynomial (Fin 2) R) P] [IsScalarTower R (MvPolynomial (Fin 2) R) P]
  (g : P)

/-- The geometric fibre ring `K ⊗_R P/(g)` of the hypersurface `g = 0` (a type synonym). -/
def HypersurfaceFibre : Type u := K ⊗[R] (P ⧸ Ideal.span {g})

instance : CommRing (HypersurfaceFibre R K P g) :=
  inferInstanceAs (CommRing (K ⊗[R] (P ⧸ Ideal.span {g})))
instance : Algebra K (HypersurfaceFibre R K P g) :=
  inferInstanceAs (Algebra K (K ⊗[R] (P ⧸ Ideal.span {g})))

/-- The base change `K ⊗_R P → K ⊗_R P/(g)` of the quotient map. -/
def baseQuotientMap : PlaneBaseChange R K P →ₐ[K] HypersurfaceFibre R K P g :=
  Algebra.TensorProduct.map (AlgHom.id K K) (Ideal.Quotient.mkₐ R (Ideal.span {g}))

omit [Algebra (MvPolynomial (Fin 2) R) P] [IsScalarTower R (MvPolynomial (Fin 2) R) P] in
theorem baseQuotientMap_surjective : Function.Surjective (baseQuotientMap R K P g) :=
  LinearMap.lTensor_surjective K (Ideal.Quotient.mkₐ_surjective R (Ideal.span {g}))

omit [Algebra (MvPolynomial (Fin 2) R) P] [IsScalarTower R (MvPolynomial (Fin 2) R) P] in
theorem ker_baseQuotientMap :
    RingHom.ker (baseQuotientMap R K P g).toRingHom =
      Ideal.span {toPlaneBaseChange R K P g} := by
  have h := Algebra.TensorProduct.lTensor_ker (A := K)
    (Ideal.Quotient.mkₐ R (Ideal.span {g})) (Ideal.Quotient.mkₐ_surjective R _)
  have hk : RingHom.ker (Ideal.Quotient.mkₐ R (Ideal.span {g})) = Ideal.span {g} := by
    ext a
    simp [RingHom.mem_ker, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
  rw [hk, Ideal.map_span, Set.image_singleton] at h
  exact h

variable [IsAlgClosed K] [Algebra.Etale (MvPolynomial (Fin 2) R) P]

/-- **Geometric points of a relative plane curve with invertible Hessian.** Let `P` be étale over
`R[X₀, X₁]` and `g ∈ P` with `hessian R P g` a unit, `K` an algebraically closed field over `R`,
and `π : K ⊗_R P → T` a surjective `K`-algebra map with kernel `(1 ⊗ g)`. For a maximal ideal `y`
of `T`, the local ring at `y` has principal maximal ideal (a smooth point when it is
one-dimensional), or its completion is the formal node `K[[u, v]]/(uv)`. -/
theorem geometricPoint_of_surjective (hh : IsUnit (hessian R P g)) {T : Type u} [CommRing T]
    [Algebra K T] (π : PlaneBaseChange R K P →ₐ[K] T) (hπ : Function.Surjective π)
    (hker : RingHom.ker π.toRingHom = Ideal.span {toPlaneBaseChange R K P g})
    (y : Ideal T) [y.IsMaximal] :
    (maximalIdeal (Localization.AtPrime y)).spanFinrank ≤ 1 ∨
      Nonempty (AdicCompletion (maximalIdeal (Localization.AtPrime y)) (Localization.AtPrime y) ≃ₐ[K]
        Algebra.NodeGeometricCompletionFormalUV.FormalUV K) := by
  set Q := y.comap π.toRingHom with hQdef
  have : Q.IsMaximal := Ideal.comap_isMaximal_of_surjective π.toRingHom hπ
  have : Algebra.FiniteType K (PlaneBaseChange R K P) :=
    Algebra.FiniteType.trans (S := MvPolynomial (Fin 2) K) inferInstance inferInstance
  have hres := algebraMap_quotient_surjective_of_isAlgClosed K (PlaneBaseChange R K P) Q
  choose c hc using fun j : Fin 2 => hres (Ideal.Quotient.mk Q (coord K (PlaneBaseChange R K P) j))
  have hQ : IsRationalPoint Q c := by
    refine ⟨fun j => ?_, hres⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← hc j, Ideal.Quotient.mk_algebraMap, sub_self]
  have hhQ : hessian K (PlaneBaseChange R K P) (toPlaneBaseChange R K P g) ∉ Q := by
    rw [hessian_baseChange]
    exact fun hmem => (Ideal.IsPrime.ne_top inferInstance)
      (Ideal.eq_top_of_isUnit_mem _ hmem (hh.map _))
  by_cases hd : ∀ i, planeDerivation K (PlaneBaseChange R K P) i (toPlaneBaseChange R K P g) ∈ Q
  · exact Or.inr ⟨hQ.nodeEquiv π y rfl hπ _ hker hd hhQ⟩
  · push Not at hd
    obtain ⟨i, hi⟩ := hd
    exact Or.inl (hQ.spanFinrank_maximalIdeal_le_one π y rfl hπ _ hker i hi)

/-- **Geometric points of a relative plane curve with invertible Hessian**, for the hypersurface
`K ⊗_R P/(g)` itself (`geometricPoint_of_surjective`). -/
theorem hypersurface_geometricPoint (hh : IsUnit (hessian R P g))
    (y : Ideal (HypersurfaceFibre R K P g)) [y.IsMaximal] :
    (maximalIdeal (Localization.AtPrime y)).spanFinrank ≤ 1 ∨
      Nonempty (AdicCompletion (maximalIdeal (Localization.AtPrime y)) (Localization.AtPrime y) ≃ₐ[K]
        Algebra.NodeGeometricCompletionFormalUV.FormalUV K) :=
  geometricPoint_of_surjective R K P g hh (baseQuotientMap R K P g)
    (baseQuotientMap_surjective R K P g) (ker_baseQuotientMap R K P g) y

end Points

end DeJongAlterations.StableModification.Curves.SemistableOpen
