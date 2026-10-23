/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane T45F)
-/
import DeJongAlterations.StableModification.Gluing.UniquenessValSetup
import DeJongAlterations.StableModification.BlowDown.DominationStable
import DeJongAlterations.StableModification.BlowDown.ComponentGenus
import DeJongAlterations.StableModification.Global.StatementsBaseChange

/-!
# Numerical stability gives the combinatorial stability of Corollary 4.4.3

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, cited `T:<line>`), stability
(T:1687–1690) in the numerical form of `PLAN-T5.md` §1.3 (lane T5G's
`Global.NumericallyStableFibre`: every contracted component `Z` with `p_a(Z_red) = 0` carries at
least three special points) and in the combinatorial form used by lane T44D's Corollary 4.4.3 (1)
(`BlowDown.Domination.FibreStable`: no component contracted to a point of the base is exceptional
in the incidence data of the fibre, i.e. of genus `0`, without double point of its own, with at
most two marks and double points).

`fibreStable_of_numericallyStableFibre`: **the numerical form implies the combinatorial form**
(the comparison left open in `rem:sm-dom-not-proved`, chapter `sm-blow-down-domination.tex`). Let
`w` be an exceptional component of `Cs_s` in the combinatorial sense. Then

* `Z = closure {w}` is contracted to a point: its image in `N_s` lies over the modification locus
  of `fs`, whose points are closed in `N_s` (`BlowDown.isClosed_singleton_of_mem_center`, `N`
  normal);
* `p_a(Z_red) = g(w) = 0`: every double point of `Cs_s` on `Z` lies on another component (`{w}` is
  a tree, so it has no inner double point), so `BlowDown.ComponentGenus.nodalComponentGenus`
  applies; `g(w) ≥ 0` (`ExcSpecialize.componentGenus_nonneg`) and its truncation is `0`;
* the special points of `Z` are the marks on `Z` (each a point `τᵢ(s)` with `w` the unique
  component through it, `Domination.eq_of_mem_closure_of_isSmoothAt`) and the non-smooth points of
  `Z` (closed double points other than `w`, boundary double points of `{w}`), at most two.

So `Z` violates numerical stability. The numerical stability is taken in the form
`NumericallyStableFibre fs p D' a` relative to the base `N` (with `a = Spec κ(s) → Spec V`);
`numericallyStableFibre_comp` transports it from the base `C` along `ν : N → C`.

Blueprint: `sm-gluing-uniqueness.tex`, `lem:sm-gu-numerical-combinatorial`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace DeJongAlterations.StableModification.Gluing.UniquenessVal

open _root_.DeJongAlterations.StableModification.ValuationRing (fiberTrdeg)
open DeJong (IsNodalCurve IsSmoothAt)
open Cohomology (structureCoeff)
open CurvesField CurvesField.Genus CurvesField.IncidenceGraph
open BlowDown.Domination (FibreStable stContractedLocus withMarks)
open BlowDown.ClosureComponent (closureScheme closureι)
open Geometry.ModificationCenter (center)

set_option backward.isDefEq.respectTransparency false

section Transport

variable {N C C' S : Scheme.{u}}

/-- **Numerical stability relative to a finite base change of the target**: numerical stability of
`(f ≫ ν, φ)` gives that of `(f, ν ≫ φ)` (the contracted components for `f` are contracted for
`f ≫ ν`). -/
theorem numericallyStableFibre_comp (f : C' ⟶ N) (ν : N ⟶ C) (φ : C ⟶ S)
    (D' : C'.IdealSheafData) {K : Type u} [Field K] (a : Spec (.of K) ⟶ S)
    (h : Global.NumericallyStableFibre (f ≫ ν) φ D' a) :
    Global.NumericallyStableFibre f (ν ≫ φ) D' a := by
  refine Global.NumericallyStableFibre.of_iso
    (pullback.congrHom (Category.assoc f ν φ).symm rfl) (Curves.pullbackCompMap ν φ a) ?_ ?_ ?_ h
  · simp [pullback.congrHom]
  · apply pullback.hom_ext <;> simp [pullback.congrHom, Curves.pullbackCompMap]
  · intro y
    have e : (pullback.congrHom (Category.assoc f ν φ).symm rfl).hom ≫
        pullback.fst ((f ≫ ν) ≫ φ) a = pullback.fst (f ≫ ν ≫ φ) a := by
      simp [pullback.congrHom]
    rw [← Scheme.Hom.comp_apply, e]

end Transport

section Bridge

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
  {N Cs : Scheme.{u}} (p : N ⟶ Spec (.of V)) (fs : Cs ⟶ N) {ι : Type*} [Fintype ι]
  (τ : ι → (Spec (.of V) ⟶ Cs)) (s : Spec (.of V))

local notation "q" => Scheme.Hom.fiberToSpecResidueField (fs ≫ p) s

open scoped Classical in
/-- **Numerical stability gives the combinatorial stability `FibreStable`** of lane T44D (the
comparison of `rem:sm-dom-not-proved`). Let `p : N → Spec V` with `N` integral and normal of
relative dimension at most one, `fs : Cs → N` a modification with `Cs` nodal and projective over
`V`, marks `D'` through smooth points whose points over `s` are the points `τ i s`, and
`κ(s)` algebraically closed. If the fibre over `Spec κ(s)` is numerically stable relative to `N`,
then no component of `Cs_s` contracted to a point of `N` is exceptional. -/
theorem fibreStable_of_numericallyStableFibre [IsIntegral N] [IsIntegral Cs] [IsModification fs]
    [IsSeparated p] [IsProper (fs ≫ p)] [IsNodalCurve (fs ≫ p)]
    [IsAlgClosed ((Spec (.of V)).residueField s)]
    (hnormal : IsNormalScheme N) (hcurve : fiberTrdeg p (genericPoint N) ≤ 1)
    (hp : IsProjectiveOver (fs ≫ p)) (D' : Cs.IdealSheafData)
    (hsm : ∀ x ∈ (D'.support : Set Cs), IsSmoothAt (fs ≫ p) x)
    (hD : ∀ y : (fs ≫ p).fiber s, (fs ≫ p).fiberι s y ∈ (D'.support : Set Cs) →
      ∃ i, τ i s = (fs ≫ p).fiberι s y)
    (hns : Global.NumericallyStableFibre fs p D' ((Spec (.of V)).fromSpecResidueField s)) :
    FibreStable p fs s τ := by
  intro hdim _ mk hmk w hexc
  have : IsAlgClosed (IsLocalRing.ResidueField ((Spec (CommRingCat.of V)).presheaf.stalk s)) :=
    ‹IsAlgClosed ((Spec (CommRingCat.of V)).residueField s)›
  have hpq : IsProjectiveOver q := BlowDown.isProjectiveOver_fiberToSpecResidueField (fs ≫ p) s hp
  have hpure := BlowDown.Domination.pure_fiber_of_isNodalCurve (fs ≫ p) s
  have hnodal : ∀ y : (fs ≫ p).fiber s, IsClosed ({y} : Set _) →
      IsSmoothAt q y ∨ Geometry.IsGeometricOrdinaryDoublePoint q y :=
    fun y hy => BlowDown.Domination.nodes_fiber_of_isNodalCurve (fs ≫ p) s y hy
  have hZc : IsClosed (stContractedLocus p fs s) :=
    ((center fs).isClosed.preimage (p.fiberι s).continuous).preimage
      (Curves.fiberMap fs p s).continuous
  let _ : Fintype (nodesIn q (closure {w})) :=
    (BlowDown.Domination.finite_nodesIn q hdim hpq _).fintype
  obtain ⟨hwZ, hwg, ⟨⟨-, htree⟩, hgen⟩, hcard⟩ :=
    (BlowDown.Domination.isExceptional_withMarks_iff q hdim hZc mk).mp hexc
  -- no double point of its own
  have hinner : (nodalGraph q hdim (closure {w})).inner {w} = ∅ := by
    rw [Finset.card_singleton, Nat.add_eq_right, Finset.card_eq_zero] at htree
    exact htree
  have hother : ∀ y ∈ closure {w}, IsClosed ({y} : Set ((fs ≫ p).fiber s)) →
      Geometry.IsGeometricOrdinaryDoublePoint q y →
      ∃ w' ∈ genericPoints ((fs ≫ p).fiber s), w' ≠ w ∧ y ∈ closure {w'} := by
    intro y hyw hyc hyo
    by_contra hno
    push Not at hno
    have hyg : y ∉ genericPoints ((fs ≫ p).fiber s) := BlowDown.not_mem_genericPoints_of_isClosed hpure hyc
    let e : nodesIn q (closure {w}) := ⟨y, hyw, hyc, hyg, hyo⟩
    have he : e ∈ (nodalGraph q hdim (closure {w})).inner {w} := by
      rw [mem_inner]
      intro v hv
      rw [mem_nodalGraph_ends] at hv
      rw [Finset.mem_singleton]
      by_contra hvw
      exact hno v hv.1 hvw hv.2
    rw [hinner] at he
    exact Finset.notMem_empty _ he
  -- the genus
  have hw0 : componentGenus (structureCoeff q) w = 0 := by
    have h0 := hgen w (Finset.mem_singleton_self w)
    rw [nodalGraph_genus, Int.toNat_eq_zero] at h0
    have hpt : ∃ y ∈ closure ({w} : Set ((fs ≫ p).fiber s)), y ≠ w := by
      by_contra hno
      push Not at hno
      have hcl : IsClosed ({w} : Set ((fs ≫ p).fiber s)) := by
        have : closure ({w} : Set ((fs ≫ p).fiber s)) = {w} :=
          Set.Subset.antisymm (fun y hy => hno y hy) subset_closure
        rw [← this]
        exact isClosed_closure
      exact BlowDown.not_mem_genericPoints_of_isClosed hpure hcl hwg
    have h1 := BlowDown.ExcSpecialize.componentGenus_nonneg q hpq hdim hpt
    omega
  have hpa : arithmeticGenus (closureScheme w) (structureCoeff (closureι w ≫ q)) = 0 := by
    rw [BlowDown.ComponentGenus.nodalComponentGenus _ _ _ hdim hpq hnodal w hwg hother, hw0]
  -- `closure {w}` is contracted
  have hxc : IsClosed ({Curves.fiberMap fs p s w} : Set (p.fiber s)) :=
    BlowDown.isClosed_singleton_of_mem_center p fs s hnormal hcurve _ hwZ
  have hcon : (Curves.pullbackCompMap fs p ((Spec (.of V)).fromSpecResidueField s) ''
      closure {w}).Subsingleton := by
    rintro _ ⟨z, hz, rfl⟩ _ ⟨z', hz', rfl⟩
    change Curves.fiberMap fs p s z = Curves.fiberMap fs p s z'
    rw [BlowDown.eq_of_mem_closure_of_isClosed _ hxc hz, BlowDown.eq_of_mem_closure_of_isClosed _ hxc hz']
  -- the instances of numerical stability
  have hZ : closure {w} ∈ irreducibleComponents ((fs ≫ p).fiber s) := hwg
  have : CompactSpace (Scheme.IdealSheafData.vanishingIdeal
      ⟨closure {w}, isClosed_of_mem_irreducibleComponents _ hZ⟩).subscheme :=
    BlowDown.ClosureComponent.compactSpace_closureScheme w
  have : IsSeparated (terminal.from (Scheme.IdealSheafData.vanishingIdeal
      ⟨closure {w}, isClosed_of_mem_irreducibleComponents _ hZ⟩).subscheme) := by
    have e : closureι w ≫ q ≫ terminal.from _ = terminal.from (closureScheme w) :=
      terminal.hom_ext _ _
    have : IsSeparated (terminal.from (closureScheme w)) := by rw [← e]; infer_instance
    exact this
  have h3 := hns (closure {w}) hZ hcon hpa
  -- at most two special points
  have hwsm : IsSmoothAt q w :=
    BlowDown.NoClosedExc.isSmoothAt_of_mem_genericPoints q hdim hpq hpure hnodal hwg
  choose yi hyi hyc using fun i => (hmk i).2
  let Mk := Finset.univ.filter fun i => mk i = w
  let B := (nodalGraph q hdim (closure {w})).boundary {w}
  have hsub : closure {w} ∩ Global.specialPoints fs p D' ((Spec (.of V)).fromSpecResidueField s) ⊆
      (yi '' (Mk : Set ι)) ∪ (Subtype.val '' (B : Set (nodesIn q (closure {w})))) := by
    rintro y ⟨hyw, hys⟩
    rcases hys with hyD | hyns
    · -- a mark
      left
      obtain ⟨i, hi⟩ := hD y hyD
      have hyi' : yi i = y := (fs ≫ p).fiberι s |>.isEmbedding.injective (by rw [hyi i, hi])
      refine ⟨i, ?_, hyi'⟩
      have hysm : IsSmoothAt q y :=
        BlowDown.Domination.isSmoothAt_fiber_of_isSmoothAt (fs ≫ p) s (hsm _ hyD)
      have h1 : y ∈ closure {mk i} := hyi' ▸ hyc i
      simp only [Mk, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
      exact BlowDown.Domination.eq_of_mem_closure_of_isSmoothAt q hdim hysm (hmk i).1 hwg h1 hyw
    · -- a double point
      right
      have hyw' : y ≠ w := fun h => hyns (h ▸ hwsm)
      have hyg : y ∉ genericPoints ((fs ≫ p).fiber s) := fun hg =>
        hyw' (eq_of_mem_closure_of_mem_genericPoints hg hyw).symm
      have hyc' := isClosed_singleton_of_not_mem_genericPoints hdim hyg
      have hyo := (hnodal y hyc').resolve_left hyns
      let e : nodesIn q (closure {w}) := ⟨y, hyw, hyc', hyg, hyo⟩
      refine ⟨e, ?_, rfl⟩
      obtain ⟨w', hw'g, hw'w, hyw'c⟩ := hother y hyw hyc' hyo
      rw [Finset.mem_coe, mem_boundary]
      refine ⟨⟨w, (mem_nodalGraph_ends q hdim e w).2 ⟨hwg, hyw⟩, Finset.mem_singleton_self w⟩,
        ⟨w', (mem_nodalGraph_ends q hdim e w').2 ⟨hw'g, hyw'c⟩, ?_⟩⟩
      rw [Finset.mem_singleton]
      exact hw'w
  have hle : (closure {w} ∩ Global.specialPoints fs p D'
      ((Spec (.of V)).fromSpecResidueField s)).encard ≤ 2 := by
    refine (Set.encard_le_encard hsub).trans ((Set.encard_union_le _ _).trans ?_)
    refine (add_le_add (Set.encard_image_le _ _) (Set.encard_image_le _ _)).trans ?_
    rw [Set.encard_coe_eq_coe_finsetCard, Set.encard_coe_eq_coe_finsetCard]
    exact_mod_cast hcard
  have : (3 : ℕ∞) ≤ 2 := h3.trans hle
  exact absurd this (by decide)

end Bridge

end DeJongAlterations.StableModification.Gluing.UniquenessVal
