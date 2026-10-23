/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.BlowDown.ContractionMarks

/-!
# Iterated exceptional blow-downs (Temkin, Prop. 4.4.6; PLAN-T5 node B5)

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, cited `T:<line>`),
Prop. 4.4.6 (`blowdownprop`, T:3188–3229): if `(C, D)` admits a semi-stable modification
`(C', D')` then it admits a stable one, by successively blowing down exceptional components of
the closed fibre ("this process must stop because we can perform at most `|Γ₀(C')|`
contractions", T:3192–3194), Lemma 4.4.4 (`emptylem`) giving stability once no exceptional
component lies over a closed point.

In the de Jong route all curves are projective over the valuation ring `V` of finite height and
the closed points lie over the closed point `s₀`, so `E₀` is the set of exceptional components of
the closed fibre (PLAN-T5 §7 "T44B", blueprint `sm-blow-down-global.tex`). We fix
`φ : C → Spec V` and marks `D ⊆ C` and call a *semi-stable stage* (`IsSemistableStage`) an
η-modification `β : Y → C` with `Y` integral and normal, `(Y, D_Y)` a semi-stable pair for the
transported marks `D_Y = genericMarksClosure β φ D η` and `Y` projective over `V`. An *exceptional
component of the closed fibre* (`IsClosedExceptional`) is a component `Z` of `Y_{s₀}` contracted by
`β`, of nonnegative genus, with `{Z}` a `ℙ¹`-tree of the incidence graph of `Y_{s₀}` and
`|∂Z| + |D_Y ∩ Z| ≤ 2` (Temkin's App. B, combinatorially).

* `ContractingMorphismExists` (**not proved here**): Temkin's construction T:3203–3226 of a
  morphism `h̄ : Y → P = ℙ¹_C` over `C` contracting exactly `Z` among the components of `Y_{s₀}`
  (sections through the other components, `L = 𝒪(m ∑ P̄ᵢ)`, the corrected vanishing T10, the lift
  of `h_s` by base change over `V`). It needs the invertible sheaf `𝒪_Y(m ∑ P̄ᵢ)` of the Cartier
  divisor of the sections, the vanishing of blueprint `cor:sm-temkin-blowdown-vanishing` (not
  formalized), sections through smooth points of the closed fibre and the base-change lift of
  `h_s`, and is taken as a hypothesis.
* `exists_blowDown_stage`: one exceptional blow-down `Y → Y'' = Nor_Y(h̄(Y))` is a semi-stable
  stage with one component less in the closed fibre (Lemma 4.4.5:
  `isNodalCurve_of_contractsExactlyAt` and, for the marks, `isSemistablePair_blowDown`;
  `ContractionStein.lean`; `ncard_genericPoints_closedFibre`).
* `exists_stage_not_hasClosedExceptional`: iteration (induction on the number of components of
  the closed fibre).
* `exists_dominated_stage_not_hasClosedExceptional`: **Prop. 4.4.6 without Lemma 4.4.4**: every
  semi-stable stage dominates a semi-stable stage whose closed fibre has no exceptional component.
  With Lemma 4.4.4 (lane T44A3) this is PLAN-T5's `BlowDownStable`,
  `exists_isStableModification_of_isSemistableStage` in `StableComb.lean`.
-/

namespace DeJongAlterations.StableModification.BlowDown

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open DeJongAlterations.StableModification.Cohomology
open DeJongAlterations.StableModification.CurvesField
open DeJongAlterations.StableModification.CurvesField.IncidenceGraph
open DeJongAlterations.StableModification.CurvesField.Genus
open Geometry.ModificationCenter (isomorphismOpen center)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

universe u

noncomputable section

section Definitions

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] {C : Scheme.{u}}
  (φ : C ⟶ Spec (CommRingCat.of V)) (D : C.IdealSheafData)

local notation "s₀" => IsLocalRing.closedPoint V

/-- A **semi-stable stage** over `(C, D)` (Temkin's semi-stable modification `(C', D') → (C, D)`,
T:3158–3160, in the projective setting of the de Jong route): `β : Y → C` is an η-modification,
`Y` is integral and normal, `(Y, D_Y)` is a semi-stable pair for the transported marks
`D_Y = genericMarksClosure β φ D η`, and `Y` is projective over `V`. -/
structure IsSemistableStage {Y : Scheme.{u}} (β : Y ⟶ C) : Prop where
  isIntegral : IsIntegral Y
  isNormalScheme : IsNormalScheme Y
  isEtaModification : Curves.IsEtaModification β φ
  isSemistablePair : DeJong.IsSemistablePair (β ≫ φ)
    (Curves.genericMarksClosure β φ D (genericPoint (Spec (CommRingCat.of V))))
  isProjectiveOver : IsProjectiveOver (β ≫ φ)

/-- The number of points of the transported marks of `Y` on the closure of a point `Z` of the
closed fibre (Temkin's `|D'_s ∩ Z|`). -/
def marksOnClosure {Y : Scheme.{u}} (β : Y ⟶ C) (Z : (β ≫ φ).fiber s₀) : ℕ :=
  (closure {(β ≫ φ).fiberι s₀ Z} ∩
    ((Curves.genericMarksClosure β φ D (genericPoint (Spec (CommRingCat.of V)))).support :
      Set Y)).ncard

open scoped Classical in
/-- An **exceptional component of the closed fibre** (Temkin's `Z ∈ E₀`, T:3158–3160, in the
combinatorial form of App. B used by the stability criterion): a generic point `Z` of the closed
fibre `Y_{s₀}` whose closure is contracted to a point by `β`, of nonnegative genus, such that `{Z}`
is a `ℙ¹`-tree of the incidence graph of `Y_{s₀}` along `Z` (genus `0`, no double point of its
own) with `|∂Z| + |D_Y ∩ Z| ≤ 2`. -/
def IsClosedExceptional {Y : Scheme.{u}} (β : Y ⟶ C) (hn : DeJong.IsNodalCurve (β ≫ φ))
    (hpr : IsProper (β ≫ φ)) (Z : (β ≫ φ).fiber s₀) : Prop :=
  haveI := hn
  haveI := hpr
  Z ∈ genericPoints ((β ≫ φ).fiber s₀) ∧
    (β '' closure {(β ≫ φ).fiberι s₀ Z}).Subsingleton ∧
    0 ≤ componentGenus
      (structureCoeff (A := ↑((Spec (CommRingCat.of V)).residueField (IsLocalRing.closedPoint V)))
        ((β ≫ φ).fiberToSpecResidueField s₀)) Z ∧
    ∀ [Fintype (nodesIn ((β ≫ φ).fiberToSpecResidueField s₀) (closure {Z}))],
      (nodalGraph ((β ≫ φ).fiberToSpecResidueField s₀)
          (topologicalKrullDim_fiber_le_one_of_nodal (β ≫ φ) s₀) (closure {Z})).IsP1Tree
          {Z} ∧
        ((nodalGraph ((β ≫ φ).fiberToSpecResidueField s₀)
          (topologicalKrullDim_fiber_le_one_of_nodal (β ≫ φ) s₀)
          (closure {Z})).boundary {Z}).card + marksOnClosure φ D β Z ≤ 2

/-- The closed fibre of `Y` has an exceptional component. -/
def HasClosedExceptional {Y : Scheme.{u}} (β : Y ⟶ C) : Prop :=
  ∃ (hn : DeJong.IsNodalCurve (β ≫ φ)) (hpr : IsProper (β ≫ φ)) (Z : (β ≫ φ).fiber s₀),
    IsClosedExceptional φ D β hn hpr Z

/-- **Temkin's contracting morphism** (Prop. 4.4.6, T:3203–3226; blueprint
`lem:sm-bdg-contracting`, **not formalized**): for a semi-stable stage `β : Y → C` and an
exceptional component `Z` of its closed fibre there are `π : P → C` with `P` separated, of finite
presentation and projective over `V` (Temkin: `P = ℙ¹_C`) and `g : Y → P` over `C` contracting
exactly `Z` among the components of `Y_{s₀}` (Temkin's `h̄ = (f, h)`, `h` a lift of a section
`h_s ∈ H⁰(Y_{s₀}, 𝒪(m ∑ pᵢ))` not vanishing at the `pᵢ`). -/
def ContractingMorphismExists : Prop :=
  ∀ (Y : Scheme.{u}) (β : Y ⟶ C), IsSemistableStage φ D β →
    ∀ (hn : DeJong.IsNodalCurve (β ≫ φ)) (hpr : IsProper (β ≫ φ)) (Z : (β ≫ φ).fiber s₀),
      IsClosedExceptional φ D β hn hpr Z →
      ∃ (P : Scheme.{u}) (π : P ⟶ C) (g : Y ⟶ P), g ≫ π = β ∧ IsSeparated (π ≫ φ) ∧
        LocallyOfFinitePresentation (π ≫ φ) ∧ IsProjectiveOver (π ≫ φ) ∧
        ContractsExactlyAt (β ≫ φ) g Z

end Definitions

section Iteration

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] {C : Scheme.{u}}
  (φ : C ⟶ Spec (CommRingCat.of V)) (D : C.IdealSheafData)

local notation "s₀" => IsLocalRing.closedPoint V

/-- **Iteration** (Temkin T:3190–3194): if every semi-stable stage with an exceptional component
of the closed fibre dominates a semi-stable stage with fewer components of the closed fibre, then
every semi-stable stage dominates one without exceptional components of the closed fibre
(induction on the number of components). -/
theorem exists_stage_not_hasClosedExceptional
    (hstep : ∀ (Y : Scheme.{u}) (β : Y ⟶ C), IsSemistableStage φ D β → HasClosedExceptional φ D β →
      ∃ (Y'' : Scheme.{u}) (β'' : Y'' ⟶ C) (b : Y ⟶ Y''), IsSemistableStage φ D β'' ∧
        b ≫ β'' = β ∧
        (genericPoints ((β'' ≫ φ).fiber s₀)).ncard < (genericPoints ((β ≫ φ).fiber s₀)).ncard)
    (Y : Scheme.{u}) (β : Y ⟶ C) (hY : IsSemistableStage φ D β) :
    ∃ (Y'' : Scheme.{u}) (β'' : Y'' ⟶ C) (b : Y ⟶ Y''), IsSemistableStage φ D β'' ∧
      b ≫ β'' = β ∧ ¬ HasClosedExceptional φ D β'' := by
  suffices h : ∀ n : ℕ, ∀ (Y : Scheme.{u}) (β : Y ⟶ C), IsSemistableStage φ D β →
      (genericPoints ((β ≫ φ).fiber s₀)).ncard = n →
      ∃ (Y'' : Scheme.{u}) (β'' : Y'' ⟶ C) (b : Y ⟶ Y''), IsSemistableStage φ D β'' ∧
        b ≫ β'' = β ∧ ¬ HasClosedExceptional φ D β'' from h _ Y β hY rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Y β hY hn
    by_cases hE : HasClosedExceptional φ D β
    · obtain ⟨Y'', β'', b, hY'', hb, hlt⟩ := hstep Y β hY hE
      obtain ⟨Y₃, β₃, b₃, hY₃, hb₃, hE₃⟩ := ih _ (hn ▸ hlt) Y'' β'' hY'' rfl
      refine ⟨Y₃, β₃, b ≫ b₃, hY₃, ?_, hE₃⟩
      rw [Category.assoc, hb₃, hb]
    · exact ⟨Y, β, 𝟙 Y, hY, Category.id_comp β, hE⟩

end Iteration

section Step

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] [Finite (PrimeSpectrum V)]
  [Infinite (IsLocalRing.ResidueField V)] {C : Scheme.{u}}
  (φ : C ⟶ Spec (CommRingCat.of V)) (D : C.IdealSheafData)
  [IsAlgClosed ((Spec (CommRingCat.of V)).residueField (IsLocalRing.closedPoint V))]
  [IsIntegral C] [IsSeparated φ] [Flat φ] [HenselianLocalRing V]

local notation "s₀" => IsLocalRing.closedPoint V

/-- **The generic point maps to the generic point under an η-modification**, which induces an
isomorphism of the local rings there. -/
theorem genericPoint_isIso_stalkMap_of_isEtaModification {Y : Scheme.{u}} [IsIntegral Y]
    (β : Y ⟶ C) (hβ : Curves.IsEtaModification β φ) :
    β (genericPoint Y) = genericPoint C ∧ IsIso (β.stalkMap (genericPoint Y)) := by
  have hiso := isIso_restrict_genericOpen φ β hβ
  set U := φ ⁻¹ᵁ genericOpen V
  obtain ⟨c, hc⟩ := genericPoint_mem_range_of_flat φ
  have hcU : c ∈ U := by
    change φ c ∈ ({_} : Set _)
    rw [hc]
    rfl
  have : IsDominant β := by
    refine ⟨?_⟩
    rw [DenseRange, dense_iff_closure_eq]
    refine Set.eq_univ_of_univ_subset ?_
    rw [← (genericPoint_spec C).def]
    refine closure_mono (Set.singleton_subset_iff.2 ?_)
    have hgU : genericPoint C ∈ U :=
      ((genericPoint_spec C).mem_open_set_iff U.isOpen).2 ⟨c, trivial, hcU⟩
    exact exists_eq_of_isIso_morphismRestrict β U hgU
  have hgen : β (genericPoint Y) = genericPoint C := genericPoint_map_of_isDominant β
  refine ⟨hgen, ?_⟩
  refine isIso_stalkMap_of_isIso_morphismRestrict β U (genericPoint Y) ?_
  rw [hgen]
  exact ((genericPoint_spec C).mem_open_set_iff U.isOpen).2 ⟨c, trivial, hcU⟩

/-- **The relative dimension of a stage**: `trdeg (K(Y)/K) ≤ 1` (lane T42's
`fiberTrdeg_le_one_of_isGenericIso`). -/
theorem fiberTrdeg_le_one_of_isEtaModification {Y : Scheme.{u}} [IsIntegral Y] (β : Y ⟶ C)
    (hβ : Curves.IsEtaModification β φ) (hdimC : ValuationRing.fiberTrdeg φ (genericPoint C) ≤ 1) :
    ValuationRing.fiberTrdeg (β ≫ φ) (genericPoint Y) ≤ 1 := by
  obtain ⟨hgen, hiso⟩ := genericPoint_isIso_stalkMap_of_isEtaModification φ β hβ
  exact ValCurves.fiberTrdeg_le_one_of_isGenericIso φ hdimC β hgen (genericPoint Y)

/-- **One exceptional blow-down** (Temkin Prop. 4.4.6, T:3195–3229, with Lemma 4.4.5): a
semi-stable stage `β : Y → C` whose closed fibre has an exceptional component `Z` dominates a
semi-stable stage `β'' : Y'' → C` (`Y'' = Nor_Y(h̄(Y))` for Temkin's contracting morphism `h̄`,
`ContractingMorphismExists`), whose closed fibre has one component less. The marks of `Y''` are
handled by `isSemistablePair_blowDown` (`V` henselian). -/
theorem exists_blowDown_stage
    (hsep : ∀ P : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ P.asIdeal)))
    (hdimC : ValuationRing.fiberTrdeg φ (genericPoint C) ≤ 1)
    (hcontract : ContractingMorphismExists φ D)
    (Y : Scheme.{u}) (β : Y ⟶ C) (hY : IsSemistableStage φ D β)
    (hE : HasClosedExceptional φ D β) :
    ∃ (Y'' : Scheme.{u}) (β'' : Y'' ⟶ C) (b : Y ⟶ Y''), IsSemistableStage φ D β'' ∧
      b ≫ β'' = β ∧
      (genericPoints ((β'' ≫ φ).fiber s₀)).ncard < (genericPoints ((β ≫ φ).fiber s₀)).ncard := by
  obtain ⟨hn, hpr, Z, hZ⟩ := hE
  have := hY.isIntegral
  obtain ⟨P, π, g, hg, hsepP, hlfp, hP, hcg⟩ := hcontract Y β hY hn hpr Z hZ
  have hYp := hY.isProjectiveOver
  have hβη := hY.isEtaModification
  have := hY.isSemistablePair.nodal
  have : IsProper g := by
    have : IsProper (g ≫ π ≫ φ) := by
      rw [← Category.assoc, hg]
      infer_instance
    exact IsProper.of_comp g (π ≫ φ)
  have hb : g.toNormalization ≫ g.fromNormalization ≫ π = β := toNormalization_comp_eq φ π g β hg
  have hP'' : IsProjectiveOver ((g.fromNormalization ≫ π) ≫ φ) :=
    isProjectiveOver_blowDown φ π g β hP hg hYp
  have : Flat ((g.fromNormalization ≫ π) ≫ φ) := flat_blowDown φ π g β hg hYp
  have : LocallyOfFinitePresentation ((g.fromNormalization ≫ π) ≫ φ) :=
    locallyOfFinitePresentation_blowDown φ π g β hg hYp
  have : IsProper ((g.fromNormalization ≫ π) ≫ φ) := hP''.isProper
  have hbp := isRelativelyProjective_blowDown φ π g β hg hYp
  have hmod : IsModification g.toNormalization := isModification_blowDown φ π g β hg hβη
  have hbη := isEtaModification_blowDown φ π g β hg hYp hβη
  have hβ''η := isEtaModification_blowDown_base φ π g β hP hg hYp hβη
  have hnormal : IsNormalScheme g.normalization := isNormalScheme_normalization g hY.isNormalScheme
  have hcurve := fiberTrdeg_le_one_of_isEtaModification φ (g.fromNormalization ≫ π) hβ''η hdimC
  have hq : g.toNormalization ≫ (g.fromNormalization ≫ π) ≫ φ = β ≫ φ := by
    rw [← Category.assoc, hb]
  have hcb : ContractsExactlyAt (β ≫ φ) g.toNormalization Z := fun w hw =>
    (image_closure_subsingleton_toNormalization_iff φ π g β hg hYp _).trans (hcg w hw)
  have hZ' := hZ
  obtain ⟨hZg, hZc, hgZ, htree⟩ := hZ
  let := (finite_nodesIn ((β ≫ φ).fiberToSpecResidueField s₀)
    (topologicalKrullDim_fiber_le_one_of_nodal (β ≫ φ) s₀)
    (isProjectiveOver_fiberToSpecResidueField (β ≫ φ) s₀ hYp) (closure {Z})).fintype
  obtain ⟨htr, hcard⟩ := htree
  obtain ⟨hnod, hm, hsm⟩ := isNodalCurve_of_contractsExactlyAt hsep ((g.fromNormalization ≫ π) ≫ φ)
    g.toNormalization (β ≫ φ) hq hP'' hbp hnormal hcurve hbη hZg hcb hgZ
    (marksOnClosure φ D β Z) htr hcard
  -- the marks (Lemma 4.4.5, marks part)
  have : IsAlgClosed (IsLocalRing.ResidueField V) :=
    IsAlgClosed.of_ringEquiv _ _ (residueFieldClosedPointEquiv (V := V)).symm
  set x' := g.toNormalization ((β ≫ φ).fiberι s₀ Z) with hx'def
  have hx' : ((g.fromNormalization ≫ π) ≫ φ) x' = IsLocalRing.closedPoint V := by
    rw [hx'def, ← Scheme.Hom.comp_apply, hq]
    exact apply_fiberι (β ≫ φ) s₀ Z
  have hcen := specializes_contractedPoint_of_mem_center ((g.fromNormalization ≫ π) ≫ φ)
    g.toNormalization (β ≫ φ) hq hnormal hcurve hZg hcb
  have hpre := preimage_contractedPoint_eq_closure hsep ((g.fromNormalization ≫ π) ≫ φ)
    g.toNormalization (β ≫ φ) hq hP'' hbp hnormal hcurve hbη hZg hcb hgZ
  set DY := Curves.genericMarksClosure β φ D (genericPoint (Spec (CommRingCat.of V))) with hDY
  have hetDY := hY.isSemistablePair.etale
  have hfinM : (closure {(β ≫ φ).fiberι s₀ Z} ∩ (DY.support : Set Y)).Finite := by
    have : QuasiCompact (DY.subschemeι ≫ β ≫ φ) := inferInstance
    have hfin := (DY.subschemeι ≫ β ≫ φ).finite_preimage_singleton (IsLocalRing.closedPoint V)
    refine (hfin.image DY.subschemeι).subset ?_
    rintro y ⟨hyZ, hyD⟩
    rw [← Scheme.IdealSheafData.range_subschemeι] at hyD
    obtain ⟨e, rfl⟩ := hyD
    refine ⟨e, ?_, rfl⟩
    rw [closure_fiberι_singleton] at hyZ
    obtain ⟨t, -, ht⟩ := hyZ
    change (β ≫ φ) (DY.subschemeι e) = _
    rw [← ht]
    exact apply_fiberι (β ≫ φ) s₀ t
  have hmarks : (g.toNormalization ⁻¹' {x'} ∩ (DY.support : Set Y)).Subsingleton := by
    rw [hpre]
    exact (Set.ncard_le_one hfinM).1 hm
  have hsmooth : (∃ d, d ∈ g.toNormalization ⁻¹' {x'} ∩ (DY.support : Set Y)) →
      DeJong.IsSmoothAt ((g.fromNormalization ≫ π) ≫ φ) x' := by
    rintro ⟨d, hd⟩
    rw [hpre] at hd
    have hm1 : marksOnClosure φ D β Z = 1 :=
      le_antisymm hm ((Set.ncard_pos hfinM).2 ⟨d, hd⟩)
    have hxs : x' ∈ Set.range (((g.fromNormalization ≫ π) ≫ φ).fiberι s₀) := by
      rw [Scheme.Hom.range_fiberι]
      exact hx'
    obtain ⟨y, hy⟩ := hxs
    have hsy := hsm hm1 y hy
    have hsy' : y ∈ (((g.fromNormalization ≫ π) ≫ φ).fiberToSpecResidueField s₀).smoothLocus :=
      (DeJong.isSmoothAt_iff_mem_smoothLocus _ y).1 hsy
    have hpb := Omega.preimage_smoothLocus_eq_of_isNodalCurve ((g.fromNormalization ≫ π) ≫ φ)
      ↑((Spec (CommRingCat.of V)).residueField (IsLocalRing.closedPoint V))
      ((Spec (CommRingCat.of V)).fromSpecResidueField (IsLocalRing.closedPoint V))
    have : y ∈ pullback.fst ((g.fromNormalization ≫ π) ≫ φ)
        ((Spec (CommRingCat.of V)).fromSpecResidueField (IsLocalRing.closedPoint V)) ⁻¹ᵁ
        ((g.fromNormalization ≫ π) ≫ φ).smoothLocus := by
      rw [hpb]
      exact hsy'
    rw [DeJong.isSmoothAt_iff_mem_smoothLocus, ← hy]
    exact this
  have hYb : DeJong.IsSemistablePair (g.toNormalization ≫ (g.fromNormalization ≫ π) ≫ φ) DY := by
    rw [hq]
    exact hY.isSemistablePair
  have hfib := hbη.isIso_fiberMap
  have hD'' : Curves.genericMarksClosure (g.fromNormalization ≫ π) φ D
      (genericPoint (Spec (CommRingCat.of V))) = (DY.subschemeι ≫ g.toNormalization).ker := by
    rw [genericMarksClosure_eq_ker_comp φ D g.toNormalization (g.fromNormalization ≫ π), hb]
  have hss := isSemistablePair_blowDown ((g.fromNormalization ≫ π) ≫ φ) g.toNormalization DY
    hnod hYb hD'' x' hx' hcen hmarks hsmooth
  refine ⟨g.normalization, g.fromNormalization ≫ π, g.toNormalization,
    ⟨inferInstance, hnormal, hβ''η, hss, hP''⟩, hb, ?_⟩
  have hcount := ncard_genericPoints_closedFibre_of_eq ((g.fromNormalization ≫ π) ≫ φ)
    g.toNormalization (β ≫ φ) hq hnormal hcurve hbη hZg hcb
  omega

/-- **Temkin's Proposition 4.4.6 without Lemma 4.4.4** (blueprint `prop:sm-bdg-blowdown`): every
semi-stable stage `β : Y → C` (a projective semi-stable η-modification with the transported
marks) dominates a semi-stable stage `β'' : Y'' → C`, `b ≫ β'' = β`, whose closed fibre has no
exceptional component, given Temkin's contracting morphisms (`ContractingMorphismExists`).
Together with Lemma 4.4.4 in the form "no
exceptional component over `s₀` ⇒ stable and numerically stable" (lane T44A3) this is PLAN-T5's
`BlowDownStable` (`exists_isStableModification_of_isSemistableStage`). -/
theorem exists_dominated_stage_not_hasClosedExceptional
    (hsep : ∀ P : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ P.asIdeal)))
    (hdimC : ValuationRing.fiberTrdeg φ (genericPoint C) ≤ 1)
    (hcontract : ContractingMorphismExists φ D)
    (Y : Scheme.{u}) (β : Y ⟶ C) (hY : IsSemistableStage φ D β) :
    ∃ (Y'' : Scheme.{u}) (β'' : Y'' ⟶ C) (b : Y ⟶ Y''), IsSemistableStage φ D β'' ∧
      b ≫ β'' = β ∧ ¬ HasClosedExceptional φ D β'' :=
  exists_stage_not_hasClosedExceptional φ D
    (exists_blowDown_stage φ D hsep hdimC hcontract) Y β hY

end Step

end

end DeJongAlterations.StableModification.BlowDown
