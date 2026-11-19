import Hironaka.Analytic.Unibranch.HironakaG11CompatibleAnalyticCover

/-!
# Iterating glued singular-centre steps (goal G11, route step 5)

The global G11 sequence is obtained by iterating glued blowup steps
(`HironakaG11CompatibleAnalyticCover.LocalSmoothCentres.exists_singularCentreBlowup`). This file
proves the iteration and termination mechanics, with LOCAL termination data only:

* `towerComp`: the composites `X k ⟶ X 0` of a tower `p k : X (k+1) ⟶ X k`; for a tower of
  singular-centre modifications they are singular-centre modifications
  (`isSingularCentreModification_towerComp`), and regularity over a subset of `X 0`, once reached,
  persists (`preimage_subset_regular_mono`).
* **Local termination on compact spaces** (`exists_isSmooth_of_local_termination`): if every point
  of the compact base `X 0` has a neighbourhood over which some stage of the tower is regular,
  some stage is smooth, and the composite is a resolution by singular-centre blowups
  (`hasSingularCentreResolution_of_local_termination`, with the whole endpoint in
  `exists_endpoint_of_local_termination`). Local termination is also necessary
  (`local_termination_of_isSmooth`).
* **Local termination measures** (`exists_regular_of_local_measure`,
  `exists_isSmooth_of_local_measure`): a measure with values in a well-founded order, attached to a
  neighbourhood of each point, which strictly drops at every stage at which singular points remain
  over that neighbourhood (e.g. the maximum of a resolution invariant over the fibre) forces local,
  hence global, termination.
* Glued stages (`IsGluedCentreStage`): a blowup along the glued centre of a compatible family of
  local smooth centres with closed glued centre in the singular locus; every glued stage is a
  singular-centre step, and one exists for every such family (`exists_isGluedCentreStage`).
* Towers from a step rule (`TowerStep`, `towerOfRule`), and the inductive form of a glued history
  (`HasGluedCentreHistory`): a space which is smooth, or has a compatible family as above all of
  whose blowups again have glued histories, has a resolution by singular-centre blowups
  (`HasGluedCentreHistory.hasSingularCentreResolution`); `hasGluedCentreHistory_of_measure` builds
  such histories by well-founded recursion on a measure.

CAUTION: the step hypothesis of `hasGluedCentreHistory_of_measure`, if assumed for the class of ALL
compact spaces, is equivalent to G11 itself; it is a combinator for a class on which the step is
PROVED (from the canonical invariant), never an input. Nothing here proves or assumes G11.
Blueprint: `hironaka-g11-resume-compatible-centres.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG11GluedCentreIteration

open Hironaka HironakaIntrinsicComplexAnalyticRegularLocus
  SourceReducedComplexSpace SmoothCentreModification OriginalIntrinsicSingularLocus
  HironakaG11SingularCentreModification HironakaG11CompatibleAnalyticCover

noncomputable section

/-! ### Towers and their composites -/

section Tower

variable {X : ℕ → SourceReducedComplexSpace} (p : ∀ k, X (k + 1) ⟶ X k)

/-- The composite `X k ⟶ X 0` of the first `k` maps of a tower. -/
def towerComp : ∀ k, X k ⟶ X 0
  | 0 => 𝟙 (X 0)
  | k + 1 => p k ≫ towerComp k

theorem towerComp_zero : towerComp p 0 = 𝟙 (X 0) := rfl

theorem towerComp_succ (k : ℕ) : towerComp p (k + 1) = p k ≫ towerComp p k := rfl

theorem towerComp_succ_apply (k : ℕ) (y : (X (k + 1)).obj.left) :
    (towerComp p (k + 1)).hom.left.base y =
      (towerComp p k).hom.left.base ((p k).hom.left.base y) := rfl

variable {p}

/-- The composites of a tower of singular-centre modifications are singular-centre
modifications. -/
theorem isSingularCentreModification_towerComp
    (hp : ∀ k, IsSingularCentreModification (p k)) :
    ∀ k, IsSingularCentreModification (towerComp p k)
  | 0 => .id (X 0)
  | k + 1 => (hp k).comp (isSingularCentreModification_towerComp hp k)

/-- One more stage keeps the points over `U` regular. -/
theorem preimage_subset_regular_succ (hp : ∀ k, IsSingularCentreModification (p k))
    {U : Set (X 0).obj.left} {N : ℕ}
    (hN : (towerComp p N).hom.left.base ⁻¹' U ⊆ intrinsicRegularLocus (X N).obj) :
    (towerComp p (N + 1)).hom.left.base ⁻¹' U ⊆ intrinsicRegularLocus (X (N + 1)).obj := by
  intro y hy
  have hy' : (p N).hom.left.base y ∈ (towerComp p N).hom.left.base ⁻¹' U := by
    change (towerComp p (N + 1)).hom.left.base y ∈ U
    exact hy
  exact (hp N).preimage_intrinsicRegularLocus_subset (hN hy')

/-- **Regularity over a subset of the base persists along the tower.** -/
theorem preimage_subset_regular_mono (hp : ∀ k, IsSingularCentreModification (p k))
    {U : Set (X 0).obj.left} {N : ℕ}
    (hN : (towerComp p N).hom.left.base ⁻¹' U ⊆ intrinsicRegularLocus (X N).obj)
    {M : ℕ} (hNM : N ≤ M) :
    (towerComp p M).hom.left.base ⁻¹' U ⊆ intrinsicRegularLocus (X M).obj := by
  induction M, hNM using Nat.le_induction with
  | base => exact hN
  | succ M _ ih => exact preimage_subset_regular_succ hp ih

/-- **Local termination implies global termination on a compact base.** If every point of the
compact space `X 0` has a neighbourhood over which some stage of a tower of singular-centre
modifications is regular, then some stage is smooth. -/
theorem exists_isSmooth_of_local_termination [CompactSpace (X 0).obj.left]
    (hp : ∀ k, IsSingularCentreModification (p k))
    (hloc : ∀ x : (X 0).obj.left, ∃ U ∈ 𝓝 x, ∃ N : ℕ,
      (towerComp p N).hom.left.base ⁻¹' U ⊆ intrinsicRegularLocus (X N).obj) :
    ∃ N : ℕ, (X N).IsSmooth := by
  choose U hU N hN using hloc
  obtain ⟨t, -, ht⟩ := (isCompact_univ : IsCompact (univ : Set (X 0).obj.left)).elim_nhds_subcover
    U (fun x _ => hU x)
  refine ⟨t.sup N, ?_⟩
  rw [isSmooth_iff_intrinsicSingularLocus_eq_empty]
  refine eq_empty_iff_forall_notMem.mpr fun y hy => hy ?_
  obtain ⟨x, hxt, hx⟩ := mem_iUnion₂.mp (ht (mem_univ ((towerComp p (t.sup N)).hom.left.base y)))
  exact preimage_subset_regular_mono hp (hN x) (Finset.le_sup hxt) hx

/-- Local termination is also necessary: at a smooth stage, the whole base is a neighbourhood
over which that stage is regular. -/
theorem local_termination_of_isSmooth {N : ℕ} (hN : (X N).IsSmooth) (x : (X 0).obj.left) :
    ∃ U ∈ 𝓝 x, ∃ M : ℕ,
      (towerComp p M).hom.left.base ⁻¹' U ⊆ intrinsicRegularLocus (X M).obj :=
  ⟨univ, Filter.univ_mem, N, fun y _ => hN y⟩

/-- **The G11 conclusion from local termination.** -/
theorem hasSingularCentreResolution_of_local_termination [CompactSpace (X 0).obj.left]
    (hp : ∀ k, IsSingularCentreModification (p k))
    (hloc : ∀ x : (X 0).obj.left, ∃ U ∈ 𝓝 x, ∃ N : ℕ,
      (towerComp p N).hom.left.base ⁻¹' U ⊆ intrinsicRegularLocus (X N).obj) :
    HasSingularCentreResolution (X 0) := by
  obtain ⟨N, hN⟩ := exists_isSmooth_of_local_termination hp hloc
  exact ⟨X N, towerComp p N, isSingularCentreModification_towerComp hp N, hN⟩

/-- The whole G11 endpoint from local termination: a stage `N` whose composite is a
singular-centre modification and a resolution, an isomorphism over the original regular locus,
with compact smooth source. -/
theorem exists_endpoint_of_local_termination [CompactSpace (X 0).obj.left]
    (hp : ∀ k, IsSingularCentreModification (p k))
    (hloc : ∀ x : (X 0).obj.left, ∃ U ∈ 𝓝 x, ∃ N : ℕ,
      (towerComp p N).hom.left.base ⁻¹' U ⊆ intrinsicRegularLocus (X N).obj) :
    ∃ N : ℕ, IsSingularCentreModification (towerComp p N) ∧ (X N).IsSmooth ∧
      IsResolution (towerComp p N) ∧ Function.Surjective (towerComp p N).hom.left.base ∧
      IsIsoOver (towerComp p N) (intrinsicRegularLocus (X 0).obj) ∧
      CompactSpace (X N).obj.left := by
  obtain ⟨N, hN⟩ := exists_isSmooth_of_local_termination hp hloc
  have hm := isSingularCentreModification_towerComp hp N
  exact ⟨N, hm, hN, hm.isResolution hN, hm.surjective, hm.isIsoOver_intrinsicRegularLocus,
    hm.source_compact⟩

/-- **A local termination measure forces local termination.** If a measure with values in a
well-founded order strictly drops at every stage at which singular points remain over `U`, some
stage is regular over `U`. -/
theorem exists_regular_of_local_measure {α : Type*} [Preorder α] [WellFoundedLT α]
    (U : Set (X 0).obj.left) (ν : ℕ → α)
    (hν : ∀ k, ¬(towerComp p k).hom.left.base ⁻¹' U ⊆ intrinsicRegularLocus (X k).obj →
      ν (k + 1) < ν k) :
    ∃ N : ℕ, (towerComp p N).hom.left.base ⁻¹' U ⊆ intrinsicRegularLocus (X N).obj := by
  by_contra hcon
  obtain ⟨n, hn⟩ := WellFounded.not_rel_apply_succ (r := (· < ·)) ν
  exact hn (hν n fun h => hcon ⟨n, h⟩)

/-- **Termination from local measures on a compact base.** -/
theorem exists_isSmooth_of_local_measure {α : Type*} [Preorder α] [WellFoundedLT α]
    [CompactSpace (X 0).obj.left] (hp : ∀ k, IsSingularCentreModification (p k))
    (hmeas : ∀ x : (X 0).obj.left, ∃ U ∈ 𝓝 x, ∃ ν : ℕ → α, ∀ k,
      ¬(towerComp p k).hom.left.base ⁻¹' U ⊆ intrinsicRegularLocus (X k).obj →
        ν (k + 1) < ν k) :
    ∃ N : ℕ, (X N).IsSmooth := by
  apply exists_isSmooth_of_local_termination hp
  intro x
  obtain ⟨U, hU, ν, hν⟩ := hmeas x
  exact ⟨U, hU, exists_regular_of_local_measure U ν hν⟩

theorem hasSingularCentreResolution_of_local_measure {α : Type*} [Preorder α] [WellFoundedLT α]
    [CompactSpace (X 0).obj.left] (hp : ∀ k, IsSingularCentreModification (p k))
    (hmeas : ∀ x : (X 0).obj.left, ∃ U ∈ 𝓝 x, ∃ ν : ℕ → α, ∀ k,
      ¬(towerComp p k).hom.left.base ⁻¹' U ⊆ intrinsicRegularLocus (X k).obj →
        ν (k + 1) < ν k) :
    HasSingularCentreResolution (X 0) := by
  obtain ⟨N, hN⟩ := exists_isSmooth_of_local_measure hp hmeas
  exact ⟨X N, towerComp p N, isSingularCentreModification_towerComp hp N, hN⟩

end Tower

/-! ### Glued stages -/

/-- A **glued stage**: a blowup along the glued centre of a compatible family of local smooth
centres whose glued centre is closed and contained in the singular locus. -/
def IsGluedCentreStage {X Y : SourceReducedComplexSpace} (p : Y ⟶ X) : Prop :=
  ∃ (ι : Type) (F : LocalSmoothCentres X ι), F.Compatible ∧ IsClosed F.support ∧
    F.support ⊆ intrinsicSingularLocus X.obj ∧
    ∃ (S : SourceReducedComplexSpace) (i : S ⟶ X),
      range i.hom.left.base = F.support ∧ IsSmoothCentreBlowup p i

theorem IsGluedCentreStage.isSingularCentreStep {X Y : SourceReducedComplexSpace} {p : Y ⟶ X}
    (h : IsGluedCentreStage p) : IsSingularCentreStep p := by
  obtain ⟨_, F, _, _, hsing, S, i, hi, hp⟩ := h
  exact F.isSingularCentreStep_of_blowup hsing p i hi hp

theorem IsGluedCentreStage.isSingularCentreModification {X Y : SourceReducedComplexSpace}
    {p : Y ⟶ X} (h : IsGluedCentreStage p) : IsSingularCentreModification p :=
  h.isSingularCentreStep.isSingularCentreModification

/-- Every compatible family with closed glued centre in the singular locus has a glued stage. -/
theorem exists_isGluedCentreStage {X : SourceReducedComplexSpace} {ι : Type}
    (F : LocalSmoothCentres X ι) (hc : F.Compatible) (hcl : IsClosed F.support)
    (hsing : F.support ⊆ intrinsicSingularLocus X.obj) :
    ∃ (Y : SourceReducedComplexSpace) (p : Y ⟶ X), IsGluedCentreStage p ∧ IsIsoOver p F.supportᶜ := by
  obtain ⟨hS, Y, p, hblow, -, -, -, hiso⟩ := F.exists_singularCentreBlowup hc hcl hsing
  exact ⟨Y, p, ⟨ι, F, hc, hcl, hsing, _, OriginalAnalyticClosedSubspace.inclusion X F.support hS,
    OriginalAnalyticClosedSubspace.inclusion_range X F.support hS, hblow⟩, hiso⟩

/-- A tower whose stages are glued stages or singular-centre modifications (e.g. identities once
the space is smooth) is a tower of singular-centre modifications. -/
theorem isSingularCentreModification_of_glued_or {X Y : SourceReducedComplexSpace} {p : Y ⟶ X}
    (h : IsGluedCentreStage p ∨ IsSingularCentreModification p) : IsSingularCentreModification p :=
  h.elim IsGluedCentreStage.isSingularCentreModification id

/-! ### Towers from a step rule -/

/-- One step of a tower inside a class `P` of spaces: the next space, again in `P`, with a
singular-centre modification onto the current one. -/
structure TowerStep (P : SourceReducedComplexSpace → Prop) (X : SourceReducedComplexSpace) where
  /-- The next space. -/
  next : SourceReducedComplexSpace
  /-- The modification onto the current space. -/
  map : next ⟶ X
  isSingularCentreModification : IsSingularCentreModification map
  mem : P next

namespace TowerStep

variable {P : SourceReducedComplexSpace → Prop}

/-- The identity step (used once the space is smooth). -/
def refl {X : SourceReducedComplexSpace} (hX : P X) : TowerStep P X :=
  ⟨X, 𝟙 X, .id X, hX⟩

/-- The glued step from a compatible family of local smooth centres, provided every blowup along
its glued centre stays in the class. -/
def ofGlued {X : SourceReducedComplexSpace} {ι : Type} (F : LocalSmoothCentres X ι)
    (hc : F.Compatible) (hcl : IsClosed F.support)
    (hsing : F.support ⊆ intrinsicSingularLocus X.obj)
    (hP : ∀ {Y : SourceReducedComplexSpace} (p : Y ⟶ X), IsGluedCentreStage p → P Y) :
    TowerStep P X :=
  let h := exists_isGluedCentreStage F hc hcl hsing
  ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.1.isSingularCentreModification,
    hP _ h.choose_spec.choose_spec.1⟩

theorem ofGlued_isGluedCentreStage {X : SourceReducedComplexSpace} {ι : Type}
    (F : LocalSmoothCentres X ι) (hc : F.Compatible) (hcl : IsClosed F.support)
    (hsing : F.support ⊆ intrinsicSingularLocus X.obj)
    (hP : ∀ {Y : SourceReducedComplexSpace} (p : Y ⟶ X), IsGluedCentreStage p → P Y) :
    IsGluedCentreStage (ofGlued F hc hcl hsing hP).map :=
  (exists_isGluedCentreStage F hc hcl hsing).choose_spec.choose_spec.1

end TowerStep

/-- The tower generated by a step rule from a space in the class. -/
def towerOfRule (P : SourceReducedComplexSpace → Prop)
    (rule : ∀ X, P X → TowerStep P X) (X₀ : SourceReducedComplexSpace) (h₀ : P X₀) :
    ℕ → {X : SourceReducedComplexSpace // P X}
  | 0 => ⟨X₀, h₀⟩
  | k + 1 =>
    let s := towerOfRule P rule X₀ h₀ k
    ⟨(rule s.1 s.2).next, (rule s.1 s.2).mem⟩

/-- The spaces of the tower generated by a step rule. -/
abbrev towerOfRuleSpace (P : SourceReducedComplexSpace → Prop)
    (rule : ∀ X, P X → TowerStep P X) (X₀ : SourceReducedComplexSpace) (h₀ : P X₀) (k : ℕ) :
    SourceReducedComplexSpace :=
  (towerOfRule P rule X₀ h₀ k).1

/-- The maps of the tower generated by a step rule. -/
def towerOfRuleMap (P : SourceReducedComplexSpace → Prop)
    (rule : ∀ X, P X → TowerStep P X) (X₀ : SourceReducedComplexSpace) (h₀ : P X₀) (k : ℕ) :
    towerOfRuleSpace P rule X₀ h₀ (k + 1) ⟶ towerOfRuleSpace P rule X₀ h₀ k :=
  (rule (towerOfRule P rule X₀ h₀ k).1 (towerOfRule P rule X₀ h₀ k).2).map

theorem towerOfRuleSpace_zero (P : SourceReducedComplexSpace → Prop)
    (rule : ∀ X, P X → TowerStep P X) (X₀ : SourceReducedComplexSpace) (h₀ : P X₀) :
    towerOfRuleSpace P rule X₀ h₀ 0 = X₀ := rfl

theorem towerOfRuleMap_isSingularCentreModification (P : SourceReducedComplexSpace → Prop)
    (rule : ∀ X, P X → TowerStep P X) (X₀ : SourceReducedComplexSpace) (h₀ : P X₀) (k : ℕ) :
    IsSingularCentreModification (towerOfRuleMap P rule X₀ h₀ k) :=
  (rule (towerOfRule P rule X₀ h₀ k).1 (towerOfRule P rule X₀ h₀ k).2).isSingularCentreModification

/-- **Resolution from a step rule with local termination.** The base of the generated tower is
`X₀`; if the generated tower terminates locally over the compact space `X₀`, then `X₀` has a
resolution by singular-centre blowups. -/
theorem hasSingularCentreResolution_of_rule (P : SourceReducedComplexSpace → Prop)
    (rule : ∀ X, P X → TowerStep P X) (X₀ : SourceReducedComplexSpace) (h₀ : P X₀)
    [CompactSpace X₀.obj.left]
    (hloc : ∀ x : X₀.obj.left, ∃ U ∈ 𝓝 x, ∃ N : ℕ,
      (towerComp (X := towerOfRuleSpace P rule X₀ h₀) (towerOfRuleMap P rule X₀ h₀) N).hom.left.base
        ⁻¹' U ⊆ intrinsicRegularLocus (towerOfRuleSpace P rule X₀ h₀ N).obj) :
    HasSingularCentreResolution X₀ := by
  have : CompactSpace (towerOfRuleSpace P rule X₀ h₀ 0).obj.left := ‹CompactSpace X₀.obj.left›
  exact hasSingularCentreResolution_of_local_termination (X := towerOfRuleSpace P rule X₀ h₀)
    (towerOfRuleMap_isSingularCentreModification P rule X₀ h₀) hloc

/-! ### Glued histories (inductive form) -/

/-- A **glued history**: the space is smooth, or it carries a compatible family of local smooth
centres with closed glued centre in the singular locus such that EVERY blowup along the glued
centre again has a glued history. The induction is well-founded by construction. -/
inductive HasGluedCentreHistory : SourceReducedComplexSpace → Prop
  | smooth {X : SourceReducedComplexSpace} (hX : X.IsSmooth) : HasGluedCentreHistory X
  | step {X : SourceReducedComplexSpace} {ι : Type} (F : LocalSmoothCentres X ι)
      (hc : F.Compatible) (hcl : IsClosed F.support)
      (hsing : F.support ⊆ intrinsicSingularLocus X.obj)
      (next : ∀ (Y S : SourceReducedComplexSpace) (p : Y ⟶ X) (i : S ⟶ X),
        range i.hom.left.base = F.support → IsSmoothCentreBlowup p i → HasGluedCentreHistory Y) :
      HasGluedCentreHistory X

/-- **A glued history gives a resolution by singular-centre blowups.** -/
theorem HasGluedCentreHistory.hasSingularCentreResolution {X : SourceReducedComplexSpace}
    (h : HasGluedCentreHistory X) : HasSingularCentreResolution X := by
  induction h with
  | smooth hX => exact hasSingularCentreResolution_of_isSmooth hX
  | step F hc hcl hsing _ ih =>
    obtain ⟨hS, Y, p, hblow, -, hmod, -, -⟩ := F.exists_singularCentreBlowup hc hcl hsing
    exact (ih Y _ p _ (OriginalAnalyticClosedSubspace.inclusion_range _ F.support hS) hblow).of_comp
      hmod

/-- **Glued histories by well-founded recursion on a measure.** On a class `P` in which every
non-smooth space carries a compatible family (closed glued centre in the singular locus) all of
whose blowups stay in `P` with strictly smaller measure, every space has a glued history.
(CAUTION: for `P` = all compact spaces the step hypothesis is equivalent to G11; this is a
combinator for classes on which the step is proved.) -/
theorem hasGluedCentreHistory_of_measure {α : Type*} [Preorder α] [WellFoundedLT α]
    (P : SourceReducedComplexSpace → Prop) (μ : SourceReducedComplexSpace → α)
    (hstep : ∀ X, P X → ¬X.IsSmooth →
      ∃ (ι : Type) (F : LocalSmoothCentres X ι), F.Compatible ∧ IsClosed F.support ∧
        F.support ⊆ intrinsicSingularLocus X.obj ∧
        ∀ (Y S : SourceReducedComplexSpace) (p : Y ⟶ X) (i : S ⟶ X),
          range i.hom.left.base = F.support → IsSmoothCentreBlowup p i → P Y ∧ μ Y < μ X)
    (X : SourceReducedComplexSpace) (hX : P X) : HasGluedCentreHistory X := by
  induction X using (InvImage.wf μ wellFounded_lt).induction with
  | _ X ih =>
    by_cases hsm : X.IsSmooth
    · exact .smooth hsm
    · obtain ⟨ι, F, hc, hcl, hsing, hnext⟩ := hstep X hX hsm
      refine .step F hc hcl hsing fun Y S p i hi hp => ?_
      obtain ⟨hPY, hμ⟩ := hnext Y S p i hi hp
      exact ih Y hμ hPY

end

end Hironaka.Analytic.Unibranch.HironakaG11GluedCentreIteration
