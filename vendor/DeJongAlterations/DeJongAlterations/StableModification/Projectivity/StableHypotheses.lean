/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane OM3D)
-/
import DeJongAlterations.StableModification.Projectivity.Relative
import DeJongAlterations.StableModification.CurvesField.GenusFormula
import DeJongAlterations.StableModification.CurvesField.OmegaDegree

/-!
# The inputs of the projectivity theorem produced by running lanes

The proof of Temkin's Theorem 1.1 in the consumed form (`Global.StableModificationProjectivity`,
M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010),
`references/temkin10-stable-modification/source/semi-stable.tex`, T:1713–1749; PLAN-OM3 §3, §5 M5)
uses lane OM3C's integrated local-to-global theorem
(`Projectivity.isRelativelyProjective_of_fiberSections`, blueprint `thm:sm-ltg`) and two results of
lanes running in parallel. These enter as the plain propositions below (nothing here asserts them),
stated in the planned form (PLAN-OM3 §4, blueprint `sm-projectivity-relative.tex`, brief of lane
OM3E):

* `ValuationProjectivity` (lane OM3C, `thm:sm-val-proj`,
  `Projectivity.Valuation.isRelativelyProjective_of_locallyRelativelyProjective`): over a valuation
  ring of finite height all of whose residue fields are algebraically closed, a locally relatively
  projective `β : X ⟶ Y` onto a flat, finitely presented, projective `Y` with `X` a nodal curve is
  relatively projective (Hensel sections through the contracted components; no stability is
  needed). It is used for the connectedness of the geometric fibres (Temkin's T59 step, PLAN-OM3
  §8 G3): the base change of the stable modification to a valuation ring must be *projective* for
  the connectedness theorem of lane COH3C to apply, and local projectivity over a cover of
  `C ×_S S'` does not give this by itself.
* `PositiveSection` (lane OM3E, `CurvesField/AmplePositive*`, brief: "from componentwise positive
  degree to a good section", fibre form): if on the geometric fibre `X_ā` of `β` over `y` every
  one-dimensional irreducible component `closure {η}` is the image of a finite map `ν : N ⟶ X_ā`
  from an integral normal scheme with `ν (generic point) = η` on which `𝓛` has positive degree
  `χ(ν^* 𝓛) - χ(𝒪_N) > 0`, then some power `𝓛^n|_{X_y}`, `n > 0`, has a section with OM3B's
  properties (non-vanishing at the non-closed points of `X_y`, vanishing at a specialization of
  each): the hypothesis `HasFiberSection β L y` of the local-to-global theorem.

Blueprint: `sm-projectivity-stable.tex`, `def:sm-tsm-inputs`.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry Topology

namespace DeJongAlterations.StableModification.Projectivity

noncomputable section

/-- **Projectivity over a valuation ring** (lane OM3C, `thm:sm-val-proj`, PLAN-OM3 §3 V-level,
§4). Let `𝒱` be a valuation ring of finite height all of whose residue fields are algebraically
closed, `pY : Y ⟶ Spec 𝒱` projective, flat and locally of finite presentation, and `β : X ⟶ Y`
locally relatively projective over `pY` such that `X ⟶ Spec 𝒱` is a nodal curve, smooth over the
generic point. Then `β` is projective relative to `pY`. -/
def ValuationProjectivity : Prop :=
  ∀ (𝒱 : Type u) [CommRing 𝒱] [IsDomain 𝒱] [ValuationRing 𝒱] [Finite (PrimeSpectrum 𝒱)],
    (∀ t : PrimeSpectrum 𝒱, IsAlgClosed t.asIdeal.ResidueField) →
    ∀ ⦃X Y : Scheme.{u}⦄ (pY : Y ⟶ Spec (.of 𝒱)), IsProjectiveOver pY → Flat pY →
      LocallyOfFinitePresentation pY →
      ∀ β : X ⟶ Y, DeJong.IsNodalCurve (β ≫ pY) →
        (∀ x, (β ≫ pY) x = genericPoint (Spec (.of 𝒱)) → DeJong.IsSmoothAt (β ≫ pY) x) →
        LocallyRelativelyProjective pY β → DeJong.IsRelativelyProjective pY β

/-- **From componentwise positive degree to a good section, fibre form** (lane OM3E,
`CurvesField/AmplePositive*`; PLAN-OM3 §5 M3/M5). Let `β : X ⟶ Y`, `y ∈ Y` with infinite residue
field, the fibre `X_y` projective over `κ(y)` of dimension at most one, `L` line-bundle data on `X`,
and `ā : Spec K ⟶ Y` a geometric point over `y` (`K` algebraically closed). Suppose that every
generic point `η` of the geometric fibre `X_ā = X ×_Y Spec K` which is not a closed point (the
one-dimensional components) is the image of the generic point of an integral normal scheme `N`
under a finite morphism `ν : N ⟶ X_ā` such that the degree `χ(ν^* 𝓛) - χ(𝒪_N)` (Čech cohomology
over `K`, the degree notion of lanes OM1D/OM1E) is positive. Then some power `𝓛^n`, `n > 0`, has a
section on `X_y` which does not vanish at the non-closed points of `X_y` and vanishes at a
specialization of each of them (`HasFiberSection β L y`, the fibre hypothesis of the
local-to-global theorem `isRelativelyProjective_of_fiberSections`). -/
def PositiveSection : Prop :=
  ∀ ⦃X Y : Scheme.{u}⦄ (β : X ⟶ Y) (L : LineBundleData X) (y : Y) [Infinite (Y.residueField y)],
    IsProjectiveOver (k := Y.residueField y) (β.fiberToSpecResidueField y) →
    topologicalKrullDim (β.fiber y) ≤ 1 →
    ∀ (K : Type u) [Field K] [IsAlgClosed K] (ā : Spec (.of K) ⟶ Y), (∀ z, ā z = y) →
      (∀ η ∈ genericPoints (pullback (C := Scheme.{u}) β ā),
        ¬ IsClosed ({η} : Set (pullback (C := Scheme.{u}) β ā)) →
        ∃ (N : Scheme.{u}) (ν : N ⟶ pullback (C := Scheme.{u}) β ā) (_ : IsIntegral N)
          (_ : CompactSpace N) (_ : IsAffineHom (pullback.diagonal (terminal.from N))),
          IsNormalScheme N ∧ IsFinite ν ∧ ν (genericPoint N) = η ∧
          0 < CurvesField.DualityScheme.eulerCharOf
                ((L.pullback (ν ≫ pullback.fst β ā)).twist (unitModule N) 1)
                (Cohomology.structureCoeff (ν ≫ pullback.snd β ā)) -
              CurvesField.Genus.eulerChar N (Cohomology.structureCoeff (ν ≫ pullback.snd β ā))) →
      HasFiberSection β L y

end

end DeJongAlterations.StableModification.Projectivity
