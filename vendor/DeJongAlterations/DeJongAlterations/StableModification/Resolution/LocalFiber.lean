import DeJongAlterations.StableModification.Resolution.LocalModel
import DeJongAlterations.Geometry.NodeCompletedLocalFiberFieldSection
import DeJongAlterations.Geometry.NodeCompletedLocalFiber
import DeJongAlterations.Geometry.SemistableCurve

/-!
# Closed-fibre models from the fibre of a family of curves

Let `f : X → S` be locally of finite type over a locally Noetherian `S`, `x ∈ X`, `s = f(x)`,
`Â = Ô_{S,s}`, `Ĉ = Ô_{X,x}`, and `y ∈ X_s = f⁻¹(s)` the point of the scheme-theoretic fibre over
`x` (Codex's `Geometry.NodeCompletedLocalMap.originalFiberPoint`). The closed fibre `Ĉ/𝔪_Â Ĉ`
of the completed map is the completed local ring `Ô_{X_s,y}` (`closedFiberFiberEquiv`, from
Codex's `closedFiberCompletionEquiv` and `originalFiberCompletedEquiv`). This file shows that this identification is semilinear over
`Â/𝔪_Â ≅ κ(s)`, and transports the fibre models of de Jong 2.21–2.23
(`references/dejong96-alterations/tex/page-0012.tex`):

* `nonempty_splitNode_closedFiber_of_isGeometricOrdinaryDoublePoint`: if `y` is an ordinary double
  point of `X_s` in Codex's sense (`Geometry.IsGeometricOrdinaryDoublePoint`,
  `Ô_{X_s,y} ≃ₐ[κ(s)] κ(s)[[u,v]]/(uv)`), then `Ĉ/𝔪_Â Ĉ ≃ (Â/𝔪_Â)[[u,v]]/(uv)` as
  `Â/𝔪_Â`-algebras, the input of `exists_completed_monomial_normal_form`.
* `nonempty_powerSeries_closedFiber_of_fiber`: if `Ô_{X_s,y} ≃ₐ[κ(s)] κ(s)[[w]]`, then
  `Ĉ/𝔪_Â Ĉ ≃ (Â/𝔪_Â)[[w]]`, the input of `exists_completed_smooth_normal_form`.

When `κ(s)` is algebraically closed (a closed point of a variety over `k = k̄`), the fibre `X_s`
is a geometric fibre, so the semi-stability condition of de Jong 2.21 (Codex's
`IsSemistableCurve.geometricNodes`, applied with `K = κ(s)`) gives the first hypothesis at every
closed non-smooth point; this is de Jong 4.25's remark that at closed points "the situation is
automatically split".
-/

noncomputable section

namespace DeJongAlterations.StableModification.Resolution

open AlgebraicGeometry CategoryTheory IsLocalRing MvPowerSeries
open Geometry.NodeCompletedLocalMap Algebra.NodeFlatPresentation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

section Transport

variable {K L : Type*} [CommRing K] [CommRing L]

/-- A ring isomorphism of coefficients induces one of power series rings. -/
def mvPowerSeriesCongr (σ : Type*) (ψ : K ≃+* L) : MvPowerSeries σ K ≃+* MvPowerSeries σ L :=
  RingEquiv.ofRingHom (MvPowerSeries.map ψ.toRingHom) (MvPowerSeries.map ψ.symm.toRingHom)
    (by rw [← MvPowerSeries.map_comp]; simp)
    (by rw [← MvPowerSeries.map_comp]; simp)

theorem mvPowerSeriesCongr_apply (σ : Type*) (ψ : K ≃+* L) (F : MvPowerSeries σ K) :
    mvPowerSeriesCongr σ ψ F = MvPowerSeries.map ψ.toRingHom F := rfl

/-- A ring isomorphism of coefficients induces one of split node rings `K[[u,v]]/(uv)`. -/
def splitNodeCongr (ψ : K ≃+* L) : SplitNode K ≃+* SplitNode L :=
  Ideal.quotientEquiv _ _ (mvPowerSeriesCongr (Fin 2) ψ) (by
    rw [Ideal.map_span, Set.image_singleton]
    show Ideal.span {X 0 * X 1} = Ideal.span {mvPowerSeriesCongr (Fin 2) ψ (X 0 * X 1)}
    rw [mvPowerSeriesCongr_apply, map_mul, MvPowerSeries.map_X, MvPowerSeries.map_X])

theorem splitNodeCongr_C (ψ : K ≃+* L) (c : K) :
    splitNodeCongr ψ (algebraMap K (SplitNode K) c) = algebraMap L (SplitNode L) (ψ c) := by
  change Ideal.Quotient.mk _ (MvPowerSeries.map ψ.toRingHom (C c)) = _
  rw [MvPowerSeries.map_C]
  rfl

/-- A ring isomorphism of coefficients induces one of power series rings in one variable. -/
def powerSeriesCongr (ψ : K ≃+* L) : PowerSeries K ≃+* PowerSeries L :=
  mvPowerSeriesCongr Unit ψ

theorem powerSeriesCongr_C (ψ : K ≃+* L) (c : K) :
    powerSeriesCongr ψ (algebraMap K (PowerSeries K) c) = algebraMap L (PowerSeries L) (ψ c) := by
  change MvPowerSeries.map ψ.toRingHom (MvPowerSeries.C c) = _
  rw [MvPowerSeries.map_C]
  rfl

/-- Codex's formal `uv` model `K[[u,v]]/(uv)` (a quotient by the image of the polynomial `uv`)
is the split node ring. -/
def formalUVEquivSplitNode (K : Type u) [Field K] :
    Algebra.NodeGeometricCompletionFormalUV.FormalUV K ≃ₐ[K] SplitNode K :=
  Ideal.quotientEquivAlgOfEq K (by
    change Ideal.span {((MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) K) :
      MvPowerSeries (Fin 2) K)} = Ideal.span {X 0 * X 1}
    rw [MvPolynomial.coe_mul, MvPolynomial.coe_X, MvPolynomial.coe_X])

end Transport

variable {X S : Scheme.{u}} (f : X ⟶ S) (x : X)

/-- The residue field of `Ô_{S,s}` is `κ(s)`. -/
def completedResidueEquiv [IsLocallyNoetherian S] :
    CoefficientResidue (S.completedLocalRing (f x)) ≃+* S.residueField (f x) :=
  (Algebra.CompletionRegularityBasics.residueFieldEquiv (S.presheaf.stalk (f x))).symm

theorem completedResidueEquiv_mk [IsLocallyNoetherian S] (a : S.presheaf.stalk (f x)) :
    completedResidueEquiv f x
      (Ideal.Quotient.mk _ (S.toCompletedLocalRing (f x) a)) = residue _ a := by
  show (Algebra.CompletionRegularityBasics.residueFieldEquiv (S.presheaf.stalk (f x))).symm
    (Ideal.Quotient.mk _ (S.toCompletedLocalRing (f x) a)) = residue _ a
  rw [RingEquiv.symm_apply_eq, Algebra.CompletionRegularityBasics.residueFieldEquiv_apply,
    ResidueField.map_residue]
  rfl

theorem exists_completedResidue_eq_mk [IsLocallyNoetherian S]
    (c : CoefficientResidue (S.completedLocalRing (f x))) :
    ∃ a : S.presheaf.stalk (f x), c = Ideal.Quotient.mk _ (S.toCompletedLocalRing (f x) a) := by
  obtain ⟨a, ha⟩ := residue_surjective (completedResidueEquiv f x c)
  refine ⟨a, (completedResidueEquiv f x).injective ?_⟩
  rw [completedResidueEquiv_mk, ha]

variable [LocallyOfFiniteType f] [IsLocallyNoetherian S]

attribute [local instance] completedAlgebra originalFiberResidueAlgebra

local instance completedLocalHom' :
    IsLocalHom (algebraMap (S.completedLocalRing (f x)) (X.completedLocalRing x)) :=
  completedMap_isLocalHom f x

local instance originalFiber_isLocalRing' : IsLocalRing (OriginalFiberRing f x) :=
  originalFiberLocalRing f x

/-- The `κ(s)`-algebra structure of the completed local ring `Ô_{X_s,y}` of the fibre. -/
@[instance_reducible]
def fiberCompletedAlgebra :
    Algebra (S.residueField (f x)) ((f.fiber (f x)).completedLocalRing (originalFiberPoint f x)) :=
  Scheme.completedLocalRingAlgebra (f.fiberToSpecResidueField (f x)) (originalFiberPoint f x)

/-- The completed closed fibre is the completed local ring of the scheme-theoretic fibre:
`Ĉ/𝔪_Â Ĉ ≃ Ô_{X_s,y}` (Codex's `closedFiberCompletionEquiv` and `originalFiberCompletedEquiv`). -/
def closedFiberFiberEquiv :
    ClosedFiber (S.completedLocalRing (f x)) (X.completedLocalRing x) ≃+*
      (f.fiber (f x)).completedLocalRing (originalFiberPoint f x) :=
  (closedFiberCompletionEquiv f x).trans (originalFiberCompletedEquiv f x).symm

/-- The identification `Ĉ/𝔪_Â Ĉ ≃ Ô_{X_s,y}` of the completed closed fibre with the completed
local ring of the scheme-theoretic fibre (`closedFiberFiberEquiv`) carries the
coefficients `Â/𝔪_Â` to `κ(s)` along `completedResidueEquiv`. -/
theorem closedFiberFiberEquiv_algebraMap
    (c : CoefficientResidue (S.completedLocalRing (f x))) :
    letI := fiberCompletedAlgebra f x
    closedFiberFiberEquiv f x
        (algebraMap (CoefficientResidue (S.completedLocalRing (f x)))
          (ClosedFiber (S.completedLocalRing (f x)) (X.completedLocalRing x)) c) =
      algebraMap (S.residueField (f x))
        ((f.fiber (f x)).completedLocalRing (originalFiberPoint f x))
        (completedResidueEquiv f x c) := by
  let := fiberCompletedAlgebra f x
  obtain ⟨a, rfl⟩ := exists_completedResidue_eq_mk f x c
  rw [completedResidueEquiv_mk]
  rw [closedFiberFiberEquiv, RingEquiv.trans_apply, RingEquiv.symm_apply_eq]
  have hR := (originalFiberCompletedAlgEquiv f x).commutes (residue _ a)
  change originalFiberCompletedEquiv f x _ = _ at hR
  rw [hR]
  change closedFiberCompletionEquiv f x
      (Ideal.Quotient.mk _ (completedMap f x (S.toCompletedLocalRing (f x) a))) = _
  rw [completedMap_coefficient, closedFiberCompletionEquiv_coefficient]
  rfl

/-- **Split nodes at points with residue field `κ(s)` (de Jong 2.23, split case; 4.25).** If the
point `y` of the fibre `X_s` over `x` is an ordinary double point,
`Ô_{X_s,y} ≃ₐ[κ(s)] κ(s)[[u,v]]/(uv)`, then the completed closed fibre at `x` is the split node:
`(Â/𝔪_Â)[[u,v]]/(uv) ≃ₐ[Â/𝔪_Â] Ĉ/𝔪_Â Ĉ`. -/
theorem nonempty_splitNode_closedFiber_of_isGeometricOrdinaryDoublePoint
    (hnode : Geometry.IsGeometricOrdinaryDoublePoint (K := S.residueField (f x))
      (f.fiberToSpecResidueField (f x)) (originalFiberPoint f x)) :
    Nonempty (SplitNode (CoefficientResidue (S.completedLocalRing (f x))) ≃ₐ[CoefficientResidue
      (S.completedLocalRing (f x))] ClosedFiber (S.completedLocalRing (f x)) (X.completedLocalRing x)) := by
  let := fiberCompletedAlgebra f x
  obtain ⟨eGeo⟩ := hnode
  let Φ := closedFiberFiberEquiv f x
  let E : SplitNode (CoefficientResidue (S.completedLocalRing (f x))) ≃+*
      ClosedFiber (S.completedLocalRing (f x)) (X.completedLocalRing x) :=
    ((splitNodeCongr (completedResidueEquiv f x)).trans
      ((formalUVEquivSplitNode (S.residueField (f x))).symm.toRingEquiv.trans
        eGeo.symm.toRingEquiv)).trans Φ.symm
  refine ⟨AlgEquiv.ofRingEquiv (f := E) fun c => ?_⟩
  change Φ.symm (eGeo.symm ((formalUVEquivSplitNode (S.residueField (f x))).symm
    (splitNodeCongr (completedResidueEquiv f x) (algebraMap _ _ c)))) = _
  rw [splitNodeCongr_C, AlgEquiv.commutes, AlgEquiv.commutes, RingEquiv.symm_apply_eq]
  exact (closedFiberFiberEquiv_algebraMap f x c).symm

/-- **Smooth points with residue field `κ(s)` (de Jong 4.25 (i)).** If the completed local ring
of the fibre `X_s` at the point over `x` is `κ(s)[[w]]`, then the completed closed fibre at `x` is
`(Â/𝔪_Â)[[w]]`. -/
theorem nonempty_powerSeries_closedFiber_of_fiber
    (hsm : letI := fiberCompletedAlgebra f x
      Nonempty ((f.fiber (f x)).completedLocalRing (originalFiberPoint f x) ≃ₐ[S.residueField (f x)]
        PowerSeries (S.residueField (f x)))) :
    Nonempty (PowerSeries (CoefficientResidue (S.completedLocalRing (f x))) ≃ₐ[CoefficientResidue
      (S.completedLocalRing (f x))] ClosedFiber (S.completedLocalRing (f x)) (X.completedLocalRing x)) := by
  let := fiberCompletedAlgebra f x
  obtain ⟨eGeo⟩ := hsm
  let Φ := closedFiberFiberEquiv f x
  let E : PowerSeries (CoefficientResidue (S.completedLocalRing (f x))) ≃+*
      ClosedFiber (S.completedLocalRing (f x)) (X.completedLocalRing x) :=
    ((powerSeriesCongr (completedResidueEquiv f x)).trans eGeo.symm.toRingEquiv).trans Φ.symm
  refine ⟨AlgEquiv.ofRingEquiv (f := E) fun c => ?_⟩
  change Φ.symm (eGeo.symm (powerSeriesCongr (completedResidueEquiv f x) (algebraMap _ _ c))) = _
  rw [powerSeriesCongr_C, AlgEquiv.commutes, RingEquiv.symm_apply_eq]
  exact (closedFiberFiberEquiv_algebraMap f x c).symm

end DeJongAlterations.StableModification.Resolution
