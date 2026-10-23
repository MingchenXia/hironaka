/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane OM3F)
-/
import DeJongAlterations.StableModification.Projectivity.ValuationSections
import DeJongAlterations.StableModification.Projectivity.StableHypotheses
import DeJongAlterations.StableModification.Valuation.SepClosed
import DeJongAlterations.StableModification.BlowDown.NoClosedExc

/-!
# Projectivity over a valuation ring (`thm:sm-val-proj`)

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`), Theorem 1.1 at the level of a
valuation ring (T:1713–1749: "relative ampleness can be checked separately on each fiber"), in the
form needed for Temkin's §4.5 (the projectivity of the glued semistable model over the normalized
base, PLAN-T5 V1) and for the connectedness of the geometric fibres in the proof of Thm 1.1
(T:1731–1737, OM3D's `exists_geometricPoint_connected`). PLAN-OM3 §3 "V-level (M7)", §5 M7;
ERRATA DJA-O37, DJA-O38. Blueprint `sm-projectivity-valuation.tex` (`thm:sm-pv-proj`, restating
`thm:sm-val-proj` of `sm-projectivity-relative.tex`).

Let `𝒱` be a valuation ring all of whose residue fields `κ(t)`, `t ∈ Spec 𝒱`, are algebraically
closed, `pY : Y ⟶ Spec 𝒱` projective and locally of finite presentation, and `β : X ⟶ Y` locally
relatively projective (OM3A's `LocallyRelativelyProjective`) with `β ≫ pY` a nodal curve. Then `β`
is projective relative to `pY`.

*Proof.* The local-to-global theorem in the valuation case
(`isRelativelyProjective_of_fiberSections_valuation`, lane OM3C): `X` is flat over `𝒱` (nodal),
the fibres of `β` have dimension at most one (`topologicalKrullDim_fiber_le_one`), the closed
points of `Y` lie over the closed point `s` of `Spec 𝒱`, so their residue fields contain the
algebraically closed `κ(s)` and are infinite, and the line bundle `𝒪(∑ P̄ᵢ)` of sections through
closed smooth points of the components of `X_s` has a fibre section at every closed point of `Y`
(`exists_fiberSections`, `ValuationSections.lean`). Only `κ(0)` (through henselianity,
`Valuation.henselianLocalRing_of_isSepClosed`) and `κ(s)` are used.

## Main results

* `isRelativelyProjective_of_henselian`: the theorem for a henselian valuation ring with
  algebraically closed residue field.
* `isRelativelyProjective_of_locallyRelativelyProjective`: the theorem with all residue fields of
  `Spec 𝒱` algebraically closed (no finiteness of `Spec 𝒱`, no flatness of `pY`, no smoothness of
  the generic fibre: ERRATA DJA-O37).
* `valuationProjectivity`: OM3D's named proposition `Projectivity.ValuationProjectivity` (consumed
  by `Projectivity.exists_geometricPoint_connected`).
* `isRelativelyProjective_of_isFractionRing`, `isProjectiveOver_of_isFractionRing`: the theorem
  for a valuation ring with algebraically closed fraction field.
* `isRelativelyProjective_of_valuationSubring`, `isProjectiveOver_of_valuationSubring`: the form
  over `Spec W` for a valuation ring `W` of an algebraically closed field (ERRATA DJA-O38; the form
  used for `Global.ValuationStableExistence`, lane T45E).
* `isRelativelyProjective_comp_specMap_of_locallyRelativelyProjective`: the form relative to
  `Y ⟶ Spec 𝒱 ⟶ Spec k` for a ring map `k → 𝒱` (PLAN-OM3 §4's statement).
-/

universe u

open CategoryTheory Limits AlgebraicGeometry Topology IsLocalRing

namespace DeJongAlterations.StableModification.Projectivity.Valuation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open DeJongAlterations.StableModification.Projectivity

section Henselian

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] [HenselianLocalRing V]
  [IsAlgClosed (ResidueField V)]
  [IsAlgClosed ((Spec (CommRingCat.of V)).residueField (closedPoint V))]

/-- **Projectivity over a henselian valuation ring** (blueprint `thm:sm-pv-proj`, henselian
form): let `V` be a henselian valuation ring with algebraically closed residue field,
`pY : Y ⟶ Spec V` projective and locally of finite presentation, and `β : X ⟶ Y` locally
relatively projective over `pY` with `β ≫ pY` a nodal curve. Then `β` is projective relative to
`pY`. -/
theorem isRelativelyProjective_of_henselian {X Y : Scheme.{u}} (pY : Y ⟶ Spec (.of V))
    (hY : IsProjectiveOver pY) [LocallyOfFinitePresentation pY] (β : X ⟶ Y)
    [DeJong.IsNodalCurve (β ≫ pY)] (hloc : LocallyRelativelyProjective pY β) :
    DeJong.IsRelativelyProjective pY β := by
  have : IsProper β := hloc.isProper
  have : IsProper pY := hY.isProper
  obtain ⟨L, hL⟩ := exists_fiberSections pY β
  refine isRelativelyProjective_of_fiberSections_valuation V pY hY β L hloc
    (fun y _ => topologicalKrullDim_fiber_le_one β pY y) (fun y hy => ?_) hL
  have hys : pY y = closedPoint V := apply_eq_closedPoint_of_isClosed pY hy
  have : IsAlgClosed ((Spec (CommRingCat.of V)).residueField (pY y)) := by
    rw [hys]
    infer_instance
  let φ : (Spec (CommRingCat.of V)).residueField (pY y) →+* Y.residueField y :=
    (pY.residueFieldMap y).hom
  exact Infinite.of_injective φ φ.injective

end Henselian

section Residue

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]

omit [ValuationRing V] in
/-- If the residue field of the generic point of `Spec V` is algebraically closed, so is the
fraction field of `V`. -/
theorem isAlgClosed_fractionRing_of_residueField
    (h : IsAlgClosed (⊥ : PrimeSpectrum V).asIdeal.ResidueField) :
    IsAlgClosed (FractionRing V) := by
  let t : PrimeSpectrum V := ⊥
  have ht : t.asIdeal = ⊥ := rfl
  let e1 : t.asIdeal.ResidueField ≃+* FractionRing (V ⧸ t.asIdeal) :=
    (FractionRing.algEquiv (V ⧸ t.asIdeal) t.asIdeal.ResidueField).symm.toRingEquiv
  let e2 : FractionRing (V ⧸ t.asIdeal) ≃+* FractionRing V :=
    IsFractionRing.ringEquivOfRingEquiv (A := V ⧸ t.asIdeal) (B := V)
      (K := FractionRing (V ⧸ t.asIdeal)) (L := FractionRing V)
      ((Ideal.quotEquivOfEq ht).trans (RingEquiv.quotientBot V))
  exact IsAlgClosed.of_ringEquiv t.asIdeal.ResidueField (FractionRing V) (e1.trans e2)

/-- If the residue field of the closed point of `Spec V` is algebraically closed, so is the
residue field of the local ring `V`. -/
theorem isAlgClosed_residueField_of_closedPoint
    (h : IsAlgClosed (closedPoint V).asIdeal.ResidueField) : IsAlgClosed (ResidueField V) := by
  have hb := Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal V)
  let e : ResidueField V ≃+* (maximalIdeal V).ResidueField := RingEquiv.ofBijective _ hb
  exact IsAlgClosed.of_ringEquiv (closedPoint V).asIdeal.ResidueField (ResidueField V) e.symm

/-- If the residue field of the closed point of `Spec V` is algebraically closed, so is the
scheme-theoretic residue field `κ(s)` of `Spec V` at the closed point. -/
theorem isAlgClosed_schemeResidueField_of_closedPoint
    (h : IsAlgClosed (closedPoint V).asIdeal.ResidueField) :
    IsAlgClosed ((Spec (CommRingCat.of V)).residueField (closedPoint V)) :=
  IsAlgClosed.of_ringEquiv _ _
    (Scheme.Spec.residueFieldIso (CommRingCat.of V) (closedPoint V)).commRingCatIsoToRingEquiv.symm

/-- **Projectivity over a valuation ring** (blueprint `thm:sm-pv-proj`, `thm:sm-val-proj`): let
`V` be a valuation ring all of whose residue fields `κ(t)`, `t ∈ Spec V`, are algebraically
closed, `pY : Y ⟶ Spec V` projective and locally of finite presentation, and `β : X ⟶ Y` locally
relatively projective over `pY` with `β ≫ pY` a nodal curve. Then `β` is projective relative to
`pY`. (Only the generic and the closed point are used; `Spec V` need not be finite, `pY` need not
be flat and the generic fibre of `β ≫ pY` need not be smooth.) -/
theorem isRelativelyProjective_of_locallyRelativelyProjective
    (hres : ∀ t : PrimeSpectrum V, IsAlgClosed t.asIdeal.ResidueField) {X Y : Scheme.{u}}
    (pY : Y ⟶ Spec (.of V)) (hY : IsProjectiveOver pY) [LocallyOfFinitePresentation pY]
    (β : X ⟶ Y) [DeJong.IsNodalCurve (β ≫ pY)] (hloc : LocallyRelativelyProjective pY β) :
    DeJong.IsRelativelyProjective pY β := by
  have : IsAlgClosed (FractionRing V) := isAlgClosed_fractionRing_of_residueField (hres ⊥)
  have : HenselianLocalRing V :=
    DeJongAlterations.StableModification.Valuation.henselianLocalRing_of_isSepClosed V
      (FractionRing V)
  have : IsAlgClosed (ResidueField V) := isAlgClosed_residueField_of_closedPoint (hres _)
  have : IsAlgClosed ((Spec (CommRingCat.of V)).residueField (closedPoint V)) :=
    isAlgClosed_schemeResidueField_of_closedPoint (hres _)
  exact isRelativelyProjective_of_henselian pY hY β hloc

/-- **Projectivity over a valuation ring, relative to a coefficient ring** (PLAN-OM3 §4's form of
`thm:sm-val-proj`): for a ring map `φ : k → V`, `β` is projective relative to
`pY ≫ Spec φ : Y ⟶ Spec k` (Lemma `isRelativelyProjective_comp_specMap_iff`, the change of
coefficient ring). -/
theorem isRelativelyProjective_comp_specMap_of_locallyRelativelyProjective {k : Type u} [CommRing k]
    (φ : k →+* V) (hres : ∀ t : PrimeSpectrum V, IsAlgClosed t.asIdeal.ResidueField)
    {X Y : Scheme.{u}} (pY : Y ⟶ Spec (.of V)) (hY : IsProjectiveOver pY)
    [LocallyOfFinitePresentation pY] (β : X ⟶ Y) [DeJong.IsNodalCurve (β ≫ pY)]
    (hloc : LocallyRelativelyProjective (pY ≫ Spec.map (CommRingCat.ofHom φ)) β) :
    DeJong.IsRelativelyProjective (pY ≫ Spec.map (CommRingCat.ofHom φ)) β := by
  rw [locallyRelativelyProjective_comp_specMap_iff] at hloc
  rw [isRelativelyProjective_comp_specMap_iff]
  exact isRelativelyProjective_of_locallyRelativelyProjective hres pY hY β hloc

end Residue

/-- **OM3D's `ValuationProjectivity`** (blueprint `thm:sm-pv-proj`): the named proposition of
`StableHypotheses.lean` holds. Its hypotheses `Finite (PrimeSpectrum 𝒱)`, `Flat pY` and the
smoothness of the generic fibre are not used. -/
theorem valuationProjectivity : ValuationProjectivity.{u} := by
  intro 𝒱 _ _ _ _ hres X Y pY hY _ _ β _ _ hloc
  exact isRelativelyProjective_of_locallyRelativelyProjective hres pY hY β hloc

section FractionField

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] (K : Type u) [Field K]
  [Algebra V K] [IsFractionRing V K] [IsAlgClosed K]

include K in
/-- **Projectivity over a valuation ring with algebraically closed fraction field** (blueprint
`cor:sm-pv-valuation-subring`): if the fraction field `K` of the valuation ring `V` is
algebraically closed, then for `pY : Y ⟶ Spec V` projective and locally of finite presentation
and `β : X ⟶ Y` locally relatively projective over `pY` with `β ≫ pY` a nodal curve, `β` is
projective relative to `pY` (all residue fields of `V` are algebraically closed,
`BlowDown.NoClosedExc.isAlgClosed_residueField_of_isAlgClosed`). -/
theorem isRelativelyProjective_of_isFractionRing {X Y : Scheme.{u}} (pY : Y ⟶ Spec (.of V))
    (hY : IsProjectiveOver pY) [LocallyOfFinitePresentation pY] (β : X ⟶ Y)
    [DeJong.IsNodalCurve (β ≫ pY)] (hloc : LocallyRelativelyProjective pY β) :
    DeJong.IsRelativelyProjective pY β :=
  isRelativelyProjective_of_locallyRelativelyProjective
    (fun t => BlowDown.NoClosedExc.isAlgClosed_residueField_of_isAlgClosed K t) pY hY β hloc

include K in
/-- In the situation of `isRelativelyProjective_of_isFractionRing`, `X` is projective over
`Spec V`. -/
theorem isProjectiveOver_of_isFractionRing {X Y : Scheme.{u}} (pY : Y ⟶ Spec (.of V))
    (hY : IsProjectiveOver pY) [LocallyOfFinitePresentation pY] (β : X ⟶ Y)
    [DeJong.IsNodalCurve (β ≫ pY)] (hloc : LocallyRelativelyProjective pY β) :
    IsProjectiveOver (β ≫ pY) :=
  (isRelativelyProjective_of_isFractionRing K pY hY β hloc).isProjectiveOver hY

end FractionField

section ValuationSubring

variable {K : Type u} [Field K] [IsAlgClosed K] (W : ValuationSubring K)

/-- **Projectivity over a valuation ring of an algebraically closed field** (blueprint
`cor:sm-pv-valuation-subring`, the form over `Spec W`, ERRATA DJA-O38): for a valuation ring `W`
of an algebraically closed field, `pY : Y ⟶ Spec W` projective and locally of finite
presentation, and `β : X ⟶ Y` locally relatively projective over `pY` with `β ≫ pY` a nodal
curve, `β` is projective relative to `pY`. -/
theorem isRelativelyProjective_of_valuationSubring {X Y : Scheme.{u}} (pY : Y ⟶ Spec (.of W))
    (hY : IsProjectiveOver pY) [LocallyOfFinitePresentation pY] (β : X ⟶ Y)
    [DeJong.IsNodalCurve (β ≫ pY)] (hloc : LocallyRelativelyProjective pY β) :
    DeJong.IsRelativelyProjective pY β :=
  isRelativelyProjective_of_isFractionRing K pY hY β hloc

/-- In the situation of `isRelativelyProjective_of_valuationSubring`, `X` is projective over
`Spec W` (the form `IsProjectiveOver (β ≫ φ)` of `Global.ValuationStableExistence`). -/
theorem isProjectiveOver_of_valuationSubring {X Y : Scheme.{u}} (pY : Y ⟶ Spec (.of W))
    (hY : IsProjectiveOver pY) [LocallyOfFinitePresentation pY] (β : X ⟶ Y)
    [DeJong.IsNodalCurve (β ≫ pY)] (hloc : LocallyRelativelyProjective pY β) :
    IsProjectiveOver (β ≫ pY) :=
  (isRelativelyProjective_of_valuationSubring W pY hY β hloc).isProjectiveOver hY

end ValuationSubring

end

end DeJongAlterations.StableModification.Projectivity.Valuation
