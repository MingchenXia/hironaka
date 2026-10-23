/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.BlowDown.StabilityCriterion
import DeJongAlterations.StableModification.Curves.SemistableOpen

/-!
# The stability criterion, local form (Temkin, Lemma 4.4.2)

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, cited `T:<line>`), Lemma 4.4.2
(`stabcritlem`, T:3106–3118) is local at `x`: Temkin shrinks `C` around `x`, compactifies, and
extends `f` trivially, so that `x` is the only point of the modification locus in its fibre
(blueprint `cor:sm-bd-stability-local`, chapter `sm-blow-down-criterion.tex`). The extension
(blueprint `lem:sm-bd-localize`(3)) is **not** constructed here: as allowed by the blueprint, it
is an input. Given

* an open immersion `j : C → C̄` over `V` into a projective normal curve `p̄ : C̄ → Spec V`, and
* a modification `f̄ : C̄' → C̄` (the extension of `f` near `x`) satisfying the hypotheses of
  `stability_criterion_fibre_of_semistableAlong` with `Z(f̄) ∩ C̄_s = {j x}`,

if `x` is a smooth point or an ordinary double point of `C_s` (with the marks condition), the
fibre `f̄_s⁻¹(j x)` is an exceptional `ℙ¹`-tree, and conversely an exceptional tree gives an
ordinary point (`stability_criterion_local`). The fibre `f̄⁻¹(j x)` is identified with `f⁻¹(x)`
through the extension; that identification is part of the (unformalized) extension statement.

The pointwise condition is Temkin's semi-stability at `x` (blueprint `def:sm-bd-semistable-at`,
nodal part): by lane SS2's openness of the semi-stable locus, `x` is a smooth point or an ordinary
double point of the geometric fibre `C_s` iff `C` is a nodal curve over `S` near `x`
(`exists_isNodalCurve_nbhd_iff`).

## Main results

* `isSmoothAt_fiberMap_iff`, `isGeometricOrdinaryDoublePoint_fiberMap_iff`: smooth points and
  ordinary double points of the fibres are local (open immersions over the base).
* `exists_isNodalCurve_nbhd_iff`: nodal near `x` iff smooth or an ordinary double point in
  the fibre.
* `stability_criterion_local`.
-/

namespace DeJongAlterations.StableModification.BlowDown

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace Module
open DeJongAlterations.StableModification.Cohomology
open DeJongAlterations.StableModification.CurvesField
open DeJongAlterations.StableModification.CurvesField.IncidenceGraph
open DeJongAlterations.StableModification.CurvesField.Genus
open Geometry.ModificationCenter (isomorphismOpen center)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

noncomputable section

section OpenImmersion

variable {S C Cb : Scheme.{u}} (j : C ⟶ Cb) [IsOpenImmersion j] (pb : Cb ⟶ S) (s : S)

/-- **Smoothness of the fibre is local**: at a point `y` of the fibre of an open subscheme
`C ⊆ C̄`, `C_s` is smooth iff `C̄_s` is smooth at the image of `y`. -/
theorem isSmoothAt_fiberMap_iff (y : (j ≫ pb).fiber s) :
    DeJong.IsSmoothAt ((j ≫ pb).fiberToSpecResidueField s) y ↔
      DeJong.IsSmoothAt (pb.fiberToSpecResidueField s) (Curves.fiberMap j pb s y) := by
  have : IsOpenImmersion (Curves.fiberMap j pb s) :=
    inferInstanceAs (IsOpenImmersion (Curves.pullbackCompMap j pb _))
  rw [← Curves.fiberMap_fiberToSpecResidueField j pb s]
  exact ⟨fun h => Curves.isSmoothAt_of_isOpenImmersion_comp (Curves.fiberMap j pb s) h,
    fun h => Curves.isSmoothAt_comp (Curves.isSmoothAt_of_smooth _ y) h⟩

/-- **Ordinary double points of the fibre are local**. -/
theorem isGeometricOrdinaryDoublePoint_fiberMap_iff (y : (j ≫ pb).fiber s) :
    Geometry.IsGeometricOrdinaryDoublePoint ((j ≫ pb).fiberToSpecResidueField s) y ↔
      Geometry.IsGeometricOrdinaryDoublePoint (pb.fiberToSpecResidueField s)
        (Curves.fiberMap j pb s y) := by
  have : IsOpenImmersion (Curves.fiberMap j pb s) :=
    inferInstanceAs (IsOpenImmersion (Curves.pullbackCompMap j pb _))
  rw [← Curves.fiberMap_fiberToSpecResidueField j pb s]
  exact ⟨fun h => Curves.isGeometricOrdinaryDoublePoint_of_isOpenImmersion _ _ y h,
    fun h => Curves.isGeometricOrdinaryDoublePoint_of_etale _ _ y h⟩

end OpenImmersion

section SemistableAt

variable {S C : Scheme.{u}} (p : C ⟶ S) [Flat p] [LocallyOfFinitePresentation p] (s : S)

/-- **Semi-stability at a point of a fibre is pointwise** (blueprint `def:sm-bd-semistable-at`,
nodal part; lane SS2's `Curves.SemistableOpen.exists_isNodalCurve_nbhd`): for `κ(s)`
algebraically closed and a closed point `x` of `C_s`, `C → S` is a nodal curve on a neighbourhood
of `x` iff `x` is a smooth point or an ordinary double point of `C_s`. -/
theorem exists_isNodalCurve_nbhd_iff (hpure : Curves.SemistableOpen.PureOneDimensionalFibres p)
    [IsAlgClosed (S.residueField s)] (x : p.fiber s) (hx : IsClosed ({x} : Set (p.fiber s))) :
    (∃ U : C.Opens, p.fiberι s x ∈ U ∧ DeJong.IsNodalCurve (U.ι ≫ p)) ↔
      DeJong.IsSmoothAt (p.fiberToSpecResidueField s) x ∨
        Geometry.IsGeometricOrdinaryDoublePoint (p.fiberToSpecResidueField s) x := by
  constructor
  · rintro ⟨U, hxU, hU⟩
    have : IsOpenImmersion (Curves.fiberMap U.ι p s) :=
      inferInstanceAs (IsOpenImmersion (Curves.pullbackCompMap U.ι p _))
    have hrange : x ∈ Set.range (Curves.fiberMap U.ι p s) := by
      have h := Curves.range_pullbackCompMap U.ι p (S.fromSpecResidueField s)
      change x ∈ Set.range (Curves.pullbackCompMap U.ι p _)
      rw [h]
      change p.fiberι s x ∈ Set.range U.ι
      rw [Scheme.Opens.range_ι]
      exact hxU
    obtain ⟨y, rfl⟩ := hrange
    have hy : IsClosed ({y} : Set ((U.ι ≫ p).fiber s)) := by
      have := hx.preimage (Curves.fiberMap U.ι p s).continuous
      rwa [show (Curves.fiberMap U.ι p s) ⁻¹' {Curves.fiberMap U.ι p s y} = {y} from
        Set.ext fun z => ⟨fun hz => (Curves.fiberMap U.ι p s).isOpenEmbedding.injective hz,
          fun hz => by rw [Set.mem_singleton_iff.1 hz]; rfl⟩] at this
    rcases hU.geometricNodes (↑(S.residueField s)) (S.fromSpecResidueField s) y hy with h | h
    · exact Or.inl ((isSmoothAt_fiberMap_iff U.ι p s y).1 h)
    · exact Or.inr ((isGeometricOrdinaryDoublePoint_fiberMap_iff U.ι p s y).1 h)
  · intro h
    exact Curves.SemistableOpen.exists_isNodalCurve_nbhd p hpure (↑(S.residueField s))
      (S.fromSpecResidueField s) x hx h

end SemistableAt

section Local

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] {C Cb Cb' : Scheme.{u}}
  (j : C ⟶ Cb) [IsOpenImmersion j] (pb : Cb ⟶ Spec (CommRingCat.of V)) (fb : Cb' ⟶ Cb)
  (s : Spec (CommRingCat.of V))

open scoped Classical in
/-- **Temkin's stability criterion, Lemma 4.4.2, local form** (blueprint
`cor:sm-bd-stability-local`), with the extension as an input. Let `j : C → C̄` be an open
immersion over `V` into `p̄ : C̄ → Spec V` and `f̄ : C̄' → C̄` a modification satisfying the
hypotheses of `stability_criterion_fibre_of_semistableAlong` (for the single point `j x` of the
modification locus in `C̄_s`; in Temkin's proof, `f̄` is the trivial extension of `f` near `x`).
If `x` is a smooth point or an ordinary double point of `C_s`, with `m ≤ 1` marks, and a smooth
point if `m = 1`, then `Z̄ = f̄_s⁻¹(j x)` is an exceptional `ℙ¹`-tree (`|∂Z̄| + m ≤ 2`); if `Z̄` is
an exceptional `ℙ¹`-tree, `j x` is an ordinary point of `C̄_s` with at most two branches, `m ≤ 1`,
and one branch if `m = 1`. -/
theorem stability_criterion_local [Finite (PrimeSpectrum V)]
    [Infinite (IsLocalRing.ResidueField V)]
    (hsep : ∀ P : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ P.asIdeal)))
    [IsIntegral Cb] [IsIntegral Cb'] [IsModification fb] [IsProper pb]
    [LocallyOfFinitePresentation pb] [Flat pb] [Flat (fb ≫ pb)] [IsReduced ((fb ≫ pb).fiber s)]
    (hp : IsProjectiveOver pb) (hfp : DeJong.IsRelativelyProjective pb fb)
    (hnormal : IsNormalScheme Cb) (hcurve : ValuationRing.fiberTrdeg pb (genericPoint Cb) ≤ 1)
    (hη : Curves.IsEtaModification fb pb)
    [IsAlgClosed ((Spec (CommRingCat.of V)).residueField s)] [IsReduced (pb.fiber s)]
    (hpure : ∀ W ∈ irreducibleComponents (pb.fiber s), topologicalKrullDim W = 1)
    (x : (j ≫ pb).fiber s)
    (hJ : ∀ y, y = Curves.fiberMap j pb s x ↔ pb.fiberι s y ∈ center fb)
    (G : Finset ((fb ≫ pb).fiber s))
    (hG : (G : Set ((fb ≫ pb).fiber s)) =
      innerPoints (Curves.fiberMap fb pb s) (Curves.fiberMap j pb s x))
    (hdim' : topologicalKrullDim ((fb ≫ pb).fiber s) ≤ 1)
    (hnodal : ∀ y ∈ Curves.fiberMap fb pb s ⁻¹' {Curves.fiberMap j pb s x}, IsClosed {y} →
      DeJong.IsSmoothAt ((fb ≫ pb).fiberToSpecResidueField s) y ∨
        Geometry.IsGeometricOrdinaryDoublePoint ((fb ≫ pb).fiberToSpecResidueField s) y)
    (hg : ∀ v ∈ G, 0 ≤ componentGenus
      (structureCoeff (A := ↑((Spec (CommRingCat.of V)).residueField s))
        ((fb ≫ pb).fiberToSpecResidueField s)) v)
    [Fintype (nodesIn (k := ↑((Spec (CommRingCat.of V)).residueField s))
      ((fb ≫ pb).fiberToSpecResidueField s)
        (Curves.fiberMap fb pb s ⁻¹'
            (({Curves.fiberMap j pb s x} : Finset (pb.fiber s)) : Set (pb.fiber s))))]
    (m : ℕ) :
    ((DeJong.IsSmoothAt ((j ≫ pb).fiberToSpecResidueField s) x ∨
        Geometry.IsGeometricOrdinaryDoublePoint ((j ≫ pb).fiberToSpecResidueField s) x) ∧
        m ≤ 1 ∧ (m = 1 → DeJong.IsSmoothAt ((j ≫ pb).fiberToSpecResidueField s) x) →
      (nodalGraph ((fb ≫ pb).fiberToSpecResidueField s) hdim'
          (Curves.fiberMap fb pb s ⁻¹'
            (({Curves.fiberMap j pb s x} : Finset (pb.fiber s)) : Set (pb.fiber s)))).IsP1Tree
          G ∧
        ((nodalGraph ((fb ≫ pb).fiberToSpecResidueField s) hdim'
          (Curves.fiberMap fb pb s ⁻¹'
            (({Curves.fiberMap j pb s x} : Finset (pb.fiber s)) : Set (pb.fiber s)))).boundary
          G).card + m ≤ 2) ∧
    ((nodalGraph ((fb ≫ pb).fiberToSpecResidueField s) hdim'
          (Curves.fiberMap fb pb s ⁻¹'
            (({Curves.fiberMap j pb s x} : Finset (pb.fiber s)) : Set (pb.fiber s)))).IsP1Tree
          G ∧
        ((nodalGraph ((fb ≫ pb).fiberToSpecResidueField s) hdim'
          (Curves.fiberMap fb pb s ⁻¹'
            (({Curves.fiberMap j pb s x} : Finset (pb.fiber s)) : Set (pb.fiber s)))).boundary
          G).card + m ≤ 2 →
      deltaInvariant (normalizationPointsMap (genericPoints (pb.fiber s)))
          (structureCoeff (A := ↑((Spec (CommRingCat.of V)).residueField s))
            (pb.fiberToSpecResidueField s)) (Curves.fiberMap j pb s x) + 1 =
          Nat.card ↥(normalizationPointsMap (genericPoints (pb.fiber s)) ⁻¹'
            {Curves.fiberMap j pb s x}) ∧
        Nat.card ↥(normalizationPointsMap (genericPoints (pb.fiber s)) ⁻¹'
          {Curves.fiberMap j pb s x}) ≤ 2 ∧ m ≤ 1 ∧
        (m = 1 → Nat.card ↥(normalizationPointsMap (genericPoints (pb.fiber s)) ⁻¹'
          {Curves.fiberMap j pb s x}) = 1)) := by
  have hJ' : ∀ y, y ∈ ({Curves.fiberMap j pb s x} : Finset (pb.fiber s)) ↔
      pb.fiberι s y ∈ center fb := fun y => by
    rw [Finset.mem_singleton]
    exact hJ y
  have hset : (({Curves.fiberMap j pb s x} : Finset (pb.fiber s)) : Set (pb.fiber s)) =
      {Curves.fiberMap j pb s x} := Finset.coe_singleton _
  obtain ⟨-, hA, hB⟩ := stability_criterion_fibre_of_semistableAlong pb fb s hsep hp hfp hnormal
    hcurve hη hpure {Curves.fiberMap j pb s x} hJ' (fun _ => G)
    (fun y hy => by rw [Finset.mem_singleton.1 hy]; exact hG) hdim' (by rw [hset]; exact hnodal)
    (fun _ _ => hg) (fun _ => m)
  have hmem : Curves.fiberMap j pb s x ∈ ({Curves.fiberMap j pb s x} : Finset (pb.fiber s)) :=
    Finset.mem_singleton_self _
  refine ⟨fun hss => hA (fun y hy => ?_) _ hmem, fun hexc => hB (fun y hy => ?_) _ hmem⟩
  · rw [Finset.mem_singleton.1 hy]
    obtain ⟨h1, h2, h3⟩ := hss
    refine ⟨?_, h2, fun h => (isSmoothAt_fiberMap_iff j pb s x).1 (h3 h)⟩
    rcases h1 with h | h
    · exact Or.inl ((isSmoothAt_fiberMap_iff j pb s x).1 h)
    · exact Or.inr ((isGeometricOrdinaryDoublePoint_fiberMap_iff j pb s x).1 h)
  · exact hexc

end Local

end

end DeJongAlterations.StableModification.BlowDown
