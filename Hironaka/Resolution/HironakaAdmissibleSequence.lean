/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaEmbeddedExceptional
import Hironaka.Analytic.MonomialCaseLocal
import Hironaka.Analytic.AnalyticSubsetTopology
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Blowup.ExceptionalLocus
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.SingularLocus
import Hironaka.Blowup.BlowupExceptionalDivisor
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.Invariant.CanonicalCentres
import Hironaka.Coherence.CartanIrreducible
import Hironaka.Invariant.CodimOneAdmissibleAlong
import Hironaka.Invariant.DivisorExponentAlong
import Hironaka.Resolution.EmbeddedFromResolution
import Hironaka.Resolution.FactorizationDomain
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.MarkedIdeal.GiraudAlong
import Hironaka.Resolution.HironakaEmbeddedResolutionLocal
import Hironaka.Resolution.HironakaFromSeqInvariant
import Hironaka.Resolution.HironakaLocalPrincipalization
import Hironaka.Resolution.HironakaPrincipalization
import Hironaka.Invariant.InvDomainTowerAlong
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Blowup.NormalCrossings
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.Invariant.ResolutionDriver
import Hironaka.Invariant.ResolutionInvariantDriver
import Hironaka.Invariant.ResolutionInvariantSeq
import Hironaka.Invariant.ResolutionInvariantSpec
import Hironaka.Invariant.RestrictEmptyTower
import Hironaka.Invariant.SmoothCentreLocus
import Hironaka.MarkedIdeal.TransformOffCentre
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Admissible blowup sequences; principalization and embedded resolution with a compact singular set (Hironaka)

Sources: Bierstone--Milman 1997 (`bierstone-milman97-invent-math`), Theorems 1.6 and 1.10 (admissible blowups, the
centres over `Sing X`, quasi-compactness only where the centres live); Kollár 2007, "Principalization II/III"
(normal crossings of the centres with the accumulated divisor); Włodarczyk 2005 (`wlodarczyk05-hironaka`).

**Admissible blowup sequences.** `IsAdmissibleBlowupSequence n X E₀ F Y f E`: a finite composition `f: Y → X` of
blowups whose every centre `C` (at a stage `f_j: Y_j → X` with accumulated divisor `E_j`) is a smooth centre having
only normal crossings with `E_j` and lying over `F`; after the blowup `π` along `C` the divisor is `(closure (π⁻¹ (H
\ C)))_{H ∈ E_j} ++ [π⁻¹ C]`, starting from `E₀`. It is what composing resolutions needs, and it records the two
properties of the canonical resolution that the previous public statements did not export.

**Compact support.** The canonical process needs a compact *cosupport*, not a compact base: the compact-cosupport
driver of `MonomialCaseLocal` applies to the canonical invariant
(`exists_isGeoResolution_isCanonical_of_isCompact`). Hence principalization on any complex manifold when only `Z(𝔞)`
is compact, and embedded resolution when only `V` is compact, with the sequence admissible, the centres over `Z(𝔞)`
(resp. over `V_sing`), and `Exc f = ⋃ E = f⁻¹(V_sing)`. The compact forms are the special case of a compact `X`.

## Main results

* `IsAdmissibleBlowupSequence` with `.isBlowupSequence`, `.mono`, `isAdmissibleBlowupSequence_proj` (multiple test blow-ups
  are admissible), `centresOver_compl_of_centresAvoid`, `centresOver_cosupp`;
* `exists_isGeoResolution_isCanonical_of_isCompact`: a resolution invariant with well-ordered values resolves every marked
  ideal of its domain with compact cosupport, on any complex manifold, by a canonical segment;
* `exists_tower_embedded_of_isCanonical`: the first-centre argument from any canonical resolution of `(X, X, ∅, 𝓘_W, 1)`;
* **`exists_principalization_of_isCompact`**, **`exists_embeddedResolution_of_isCompact`** and the compact-base corollaries
  `exists_principalization_admissible`, `exists_embeddedResolution_admissible`;
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaAdmissibleSequence

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.NormalCrossings Hironaka.RestrictEmptyTower Hironaka.DivisorExponentAlong Hironaka.BlowupTowerTransforms
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open Hironaka.ResolutionDriver (maxLocus IsCanonicalSegment)
open Hironaka.EmbeddedFromResolution (EmbeddingFields regularOpen regularAtDim_of_mem_regularOpen exists_first_centre mem_cosupp_iff_of_centresAvoid isInvDomain_vanishingIdeal_of_dim_lt isClosedConnectedSubmanifold_of_dim_eq)
open Hironaka.HironakaEmbeddedResolutionLocal (strictTransform_of_centresAvoid mem_maxLocus_iff_of_centresAvoid_of_pureDim exceptionalDivisor_facts_of_centresAvoid subset_closure_inter_regularOpen)

noncomputable section

variable {n : ℕ}

/-! ### Admissible blowup sequences -/

/-- **An admissible blowup sequence** of `(X, E₀)` with centres over `F ⊆ X`: a finite composition `f : Y → X` of blowups
with smooth centres, together with the divisor `E` on `Y` it accumulates, such that every centre `C`, at a stage `Y_j` with
`f_j : Y_j → X` and accumulated divisor `E_j`, has only normal crossings with `E_j` and lies over `F`.  After the blowup
`π : Z → Y_j` along `C` the accumulated divisor is formed by the strict transforms `closure (π⁻¹ (H \ C))` of the members
`H ∈ E_j` followed by the exceptional preimage `π⁻¹ C`; the sequence starts from `E₀`. -/
inductive IsAdmissibleBlowupSequence (n : ℕ) (X : Type u) [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] (E₀ : List (Set X)) (F : Set X) :
    (Y : Type u) → [TopologicalSpace Y] → [ChartedSpace (ComplexModel n) Y] → [IsComplexManifold n Y] →
      (Y → X) → List (Set Y) → Prop
  | refl : IsAdmissibleBlowupSequence n X E₀ F X id E₀
  | step {Y Z : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
      [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
      (f : Y → X) (E : List (Set Y)) (C : Set Y) (π : Z → Y) :
      IsAdmissibleBlowupSequence n X E₀ F Y f E → IsBlowupAlong n C π → HasNormalCrossings n C E →
      C ⊆ f ⁻¹' F →
      IsAdmissibleBlowupSequence n X E₀ F Z (f ∘ π) (E.map (fun H => closure (π ⁻¹' (H \ C))) ++ [π ⁻¹' C])

section API

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {E₀ : List (Set X)} {F : Set X}

/-- An admissible blowup sequence is a blowup sequence. -/
theorem IsAdmissibleBlowupSequence.isBlowupSequence {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] {f : Y → X} {E : List (Set Y)}
    (h : IsAdmissibleBlowupSequence n X E₀ F Y f E) : IsBlowupSequence n X Y f := by
  induction h with
  | refl => exact IsBlowupSequence.refl
  | step f E C π _ hπ _ _ ih => exact IsBlowupSequence.step f C π ih hπ

/-- Admissibility with centres over `F` gives admissibility with centres over any `F' ⊇ F`. -/
theorem IsAdmissibleBlowupSequence.mono {F' : Set X} (hFF' : F ⊆ F') {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] {f : Y → X} {E : List (Set Y)}
    (h : IsAdmissibleBlowupSequence n X E₀ F Y f E) : IsAdmissibleBlowupSequence n X E₀ F' Y f E := by
  induction h with
  | refl => exact IsAdmissibleBlowupSequence.refl
  | step f E C π _ hπ hnc hCF ih =>
      exact IsAdmissibleBlowupSequence.step f E C π ih hπ hnc fun y hy => hFF' (hCF hy)

end API

section Tower

variable {X : CMfd.{u} n}

/-- **A multiple test blow-up is an admissible blowup sequence** (for the transformed divisor, from the divisor of the marked
ideal): each centre is an admissible centre of the transform so far, so it has only normal crossings with its divisor; if the
centres lie over `F`, so does the sequence. -/
theorem isAdmissibleBlowupSequence_proj (𝔪 : MarkedIdeal n X) (F : Set X) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower 𝔪 T → CentresOver F T →
      IsAdmissibleBlowupSequence n X 𝔪.E F Y T.proj (geoTransformAlong 𝔪 T).E
  | _, .refl, _, _ => IsAdmissibleBlowupSequence.refl
  | _, .step T C π hπ, hTt, hTF => by
      obtain ⟨hTt', hC⟩ : IsGeoTestTower 𝔪 T ∧ (geoTransformAlong 𝔪 T).IsAdmissibleCentre C := hTt
      obtain ⟨hTF', hCF⟩ : CentresOver F T ∧ C ⊆ T.proj ⁻¹' F := hTF
      exact IsAdmissibleBlowupSequence.step T.proj _ C π (isAdmissibleBlowupSequence_proj 𝔪 F T hTt' hTF') hπ hC.2.2
        hCF

/-- Centres missing the preimages of an open set lie over its complement. -/
theorem centresOver_compl_of_centresAvoid (U : Opens X) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), CentresAvoid U T → CentresOver ((U : Set X)ᶜ) T
  | _, .refl, _ => trivial
  | _, .step T C π hπ, hT => by
      obtain ⟨hT', hd⟩ : CentresAvoid U T ∧ Disjoint C (T.proj ⁻¹' (U : Set X)) := hT
      exact ⟨centresOver_compl_of_centresAvoid U T hT', fun c hc hcU => Set.disjoint_left.mp hd hc hcU⟩

/-- **The centres of a multiple test blow-up lie over the original cosupport** (`N` a closed submanifold, `𝔞` coherent). -/
theorem centresOver_cosupp (𝔪 : MarkedIdeal n X) (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower 𝔪 T → CentresOver 𝔪.cosupp T
  | _, .refl, _ => trivial
  | _, .step T C π hπ, hTt => by
      obtain ⟨hTt', hC⟩ : IsGeoTestTower 𝔪 T ∧ (geoTransformAlong 𝔪 T).IsAdmissibleCentre C := hTt
      exact ⟨centresOver_cosupp 𝔪 hN h𝔞 T hTt',
        hC.2.1.trans (TransformOffCentre.cosupp_geoTransformAlong_subset 𝔪 hN h𝔞 T hTt')⟩

end Tower

/-! ### The canonical resolution with a compact cosupport -/

section Driver

variable {Λ : Type v} [LinearOrder Λ] [WellFoundedLT Λ] {k : ℕ}

/-- **A resolution invariant with well-ordered values resolves every marked ideal of its domain with compact cosupport,
on any complex manifold, by a canonical segment**: the compact-cosupport driver
`MonomialCaseLocal.exists_isGeoResolution_of_wellFounded_invariant_of_isCompact` applied to the invariant, whose
properties (1)-(3) give the admissibility of the maximum locus, its upper semicontinuity and the drop of the
maximum. -/
theorem exists_isGeoResolution_isCanonical_of_isCompact (R : ResolutionInvariantSeq.ResolutionInvariant.{u, v} n k Λ)
    {X : CMfd.{u} n} {𝔪 : MarkedIdeal n X} (h : IsInvDomain k 𝔪) (hK : IsCompact 𝔪.cosupp) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y), IsCanonical 𝔪 (R.inv 𝔪) T ∧ IsGeoResolution 𝔪 T := by
  have hcanseg : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonicalSegment 𝔪 (R.inv 𝔪) T →
      IsCanonical 𝔪 (R.inv 𝔪) T := fun T hT =>
    ResolutionInvariantDriver.isCanonical_of_isCanonicalSegment (R.inv 𝔪) T hT
  obtain ⟨Y, T, hseg, hres⟩ :=
    MonomialCaseLocal.exists_isGeoResolution_of_wellFounded_invariant_of_isCompact 𝔪 (R.inv 𝔪)
      (fun T _ hT => MonomialCaseLocal.isCompact_cosupp_geoTransformAlong h.isWellFormed.isClosedSubmanifold_N
        h.isWellFormed.isCoherent hK T hT)
      (fun T hseg _ => R.isInvValue.usc 𝔪 h T (hcanseg T hseg))
      (fun T hseg hT _ => ⟨R.isInvValue.isAdmissibleCentre_maxLocus h T (hcanseg T hseg) hT,
        ResolutionInvariantDriver.interior_maxLocus_eq_empty h T hT _⟩)
      (fun {Y} T hseg hT x₀ hx₀ {Z} π hπ z hz => by
        have hcan := hcanseg T hseg
        have hdomT := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hT
        have hzS : π z ∈ (geoTransformAlong 𝔪 T).cosupp :=
          TransformOffCentre.cosupp_geoTransform_subset_preimage _ hdomT.isWellFormed.isClosedSubmanifold_N.1
            (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
              hdomT.isWellFormed.isCoherent hg) hπ (fun p hp => hp.1) hz
        obtain ⟨hdrop, heq⟩ := R.isInvValue.decrease 𝔪 h T _ π hπ hcan ⟨x₀, hx₀⟩ rfl z hz
        by_cases hzC : π z ∈ maxLocus (R.inv 𝔪 T) (geoTransformAlong 𝔪 T).cosupp
        · exact (hdrop hzC).trans_le (hx₀.2 _ hzS)
        · rw [heq hzC]
          exact lt_of_le_of_ne (hx₀.2 _ hzS) fun hval => hzC ⟨hzS, fun p hp => (hx₀.2 p hp).trans hval.ge⟩)
  exact ⟨Y, T, hcanseg T hseg, hres⟩

end Driver

/-! ### The first-centre argument from a canonical resolution -/

section Embedded

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ]
  {inv : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ}

/-- **Embedded resolution from a canonical resolution of `(X, X, ∅, 𝓘_W, 1)`** (any complex manifold `X`, a value function with
the properties `EmbeddingFields`): let `W` be analytic, `O ⊆ X` open, `W` regular of dimension `d` at each point of `W ∩ O` and
`W ⊆ closure (W ∩ O)`.  From a canonical segment of `(X, X, ∅, 𝓘_W, 1)` with empty final cosupport, the part before the first
centre meeting the preimage of `O` (or the whole segment, when no centre meets it and then `W = ∅`) is a multiple test blow-up
whose centres miss the preimages of `O` and whose strict transform of `W` is a closed submanifold, regular of dimension `d` at
each of its points, with only normal crossings with the transformed divisor. -/
theorem exists_tower_embedded_of_isCanonical (hF : EmbeddingFields n k inv) {X : CMfd.{u} n} {W : Set X}
    (hWa : IsComplexAnalyticSubset (n := n) W) (O : Opens X) {d : ℕ}
    (hreg : ∀ x ∈ W, x ∈ O → RegularAtDim (n := n) W x d) (hdense : W ⊆ closure (W ∩ O))
    (hdom : IsInvDomain k (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X))
    {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀)
    (hcan₀ : IsCanonical (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X)
      (inv (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X)) T₀)
    (hres₀ : IsGeoResolution (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T₀) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsGeoTestTower (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T ∧ CentresAvoid O T ∧
      IsClosedSubmanifold n (strictTransform n T.proj W) ∧
      (∀ x ∈ strictTransform n T.proj W, RegularAtDim (n := n) (strictTransform n T.proj W) x d) ∧
      HasNormalCrossings n (strictTransform n T.proj W)
        (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T).E := by
  have hTt₀ := hres₀.1
  by_cases hA : CentresAvoid O T₀
  · -- every centre misses `O`: then `W` is empty
    have hWO : ∀ x ∈ W, x ∉ O := fun x hxW hxO => by
      obtain ⟨y, rfl⟩ := HironakaLocalPrincipalization.IsBlowupSequence.surjective T₀.isBlowupSequence x
      have hy := (mem_cosupp_iff_of_centresAvoid hWa.isClosed hdom O T₀ hTt₀ hA hxO).mpr hxW
      rw [hres₀.2] at hy
      exact hy
    have hW0 : W = ∅ := by
      refine eq_empty_iff_forall_notMem.mpr fun x hx => ?_
      have h := hdense hx
      rw [show W ∩ (O : Set X) = ∅ from eq_empty_iff_forall_notMem.mpr fun y hy => hWO y hy.1 hy.2,
        closure_empty] at h
      exact h
    have hS0 : strictTransform n T₀.proj W = ∅ := by
      rw [hW0]
      simp [strictTransform]
    refine ⟨Y₀, T₀, hTt₀, hA, ?_, ?_, ?_⟩
    · rw [hS0]
      exact ⟨isClosed_empty, fun x hx => absurd hx (notMem_empty x)⟩
    · rw [hS0]
      exact fun x hx => absurd hx (notMem_empty x)
    · rw [hS0]
      exact fun x hx => absurd hx (notMem_empty x)
  · -- the first centre meeting `O`
    obtain ⟨Y', T', -, -, h1, h2, c, hc, hcU⟩ := exists_first_centre _ _ O T₀ hcan₀ hA
    have hTt' := hF.isGeoTestTower_of_isCanonical hdom T' h1
    have hadm := hF.isAdmissibleCentre_maxLocus hdom T' h1 hTt'
    have hCV := fun y (hy : T'.proj y ∈ O) =>
      mem_maxLocus_iff_of_centresAvoid_of_pureDim hF hWa.isClosed O (d := d)
        (fun x hx => hreg x hx x.2) hdom T' h1 h2 hc hcU hy
    obtain ⟨hSC, hev, hreg'⟩ := strictTransform_of_centresAvoid hWa O hreg hdense T' h2 hadm.1 hCV
    refine ⟨Y', T', hTt', h2, ⟨isClosed_closure, fun x hx => ⟨d, hreg' x hx⟩⟩, hreg', ?_⟩
    exact CodimOneAdmissibleAlong.hasNormalCrossings_of_forall_eventually fun x hx =>
      ⟨_, hSC hx, hev x hx, hadm.2.2⟩

end Embedded

/-! ### Principalization with a compact zero locus -/

section Principalization

/-- **`IsNonzeroAlongAt univ` in elementary terms**: some germ of `𝔞_x` does not vanish identically near `x`. -/
theorem isNonzeroAlongAt_univ_iff_exists {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    {𝔞 : GermIdeal n M} {x : M} :
    IsNonzeroAlongAt univ 𝔞 x ↔ ∃ g, 𝔞.mem x g ∧ ∃ᶠ y in 𝓝 x, g y ≠ 0 := by
  simp [IsNonzeroAlongAt]

/-- **The cosupport of `(X, X, ∅, 𝔞, 1)` is the zero locus of `𝔞`** (coherent `𝔞`). -/
theorem cosupp_univ_one {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    {𝔞 : GermIdeal n X} (h𝔞 : 𝔞.IsCoherent) :
    (⟨univ, [], 𝔞, 1⟩ : MarkedIdeal n X).cosupp = 𝔞.zeroLocus := by
  show GermIdealOrder.cosupport n univ 𝔞 1 = 𝔞.zeroLocus
  rw [GermIdealOrder.cosupport_one (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg),
    univ_inter]

/-- **Principalization with a compact zero locus** (Hironaka; `hir:principalization-compact-support`): let `X` be any complex
manifold and `𝔞` a coherent ideal sheaf on `X`, nonzero at every point, whose zero locus `Z(𝔞)` is compact.  There are an
admissible blowup sequence `f : X' → X` (from the empty divisor, with centres over `Z(𝔞)`) with accumulated divisor `E`, and an
effective divisor `D` on `X'`, such that `f^*𝔞 = 𝒪(-D)`, `E` has simple normal crossings, `supp D = ⋃ E = f⁻¹ Z(𝔞)`, and `f` is
an isomorphism over `X \ Z(𝔞)`. -/
theorem exists_principalization_of_isCompact {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] {𝔞 : GermIdeal n X} (h𝔞 : 𝔞.IsCoherent) (hne : ∀ x, IsNonzeroAlongAt univ 𝔞 x)
    (hZ : IsCompact 𝔞.zeroLocus) :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : ChartedSpace (ComplexModel n) X')
      (_ : IsComplexManifold n X') (f : X' → X) (D : EffectiveDivisor n X') (E : List (Set X')),
      IsAdmissibleBlowupSequence n X [] 𝔞.zeroLocus X' f E ∧
      GermIdeal.pullback (m := n) f 𝔞 = D.ideal ∧
      IsSNCDivisor n E ∧
      D.support = ⋃ H ∈ E, H ∧
      D.support = f ⁻¹' 𝔞.zeroLocus ∧
      IsIsomorphismOver n f 𝔞.zeroLocusᶜ := by
  set 𝔪 : MarkedIdeal n (CMfd.of (n := n) X) := ⟨univ, [], 𝔞, 1⟩ with h𝔪
  have hdom : IsInvDomain n 𝔪 := HironakaPrincipalization.isInvDomain_univ (M := CMfd.of (n := n) X) h𝔞 hne
  have hcos : 𝔪.cosupp = 𝔞.zeroLocus := cosupp_univ_one (X := CMfd.of (n := n) X) h𝔞
  obtain ⟨Y, T, -, hres⟩ := exists_isGeoResolution_isCanonical_of_isCompact
    (CanonicalCentres.canonicalInvariant.{u} n) hdom (by rw [hcos]; exact hZ)
  have hpb : GermIdeal.pullback (m := n) T.proj 𝔞 = (BlowupTowerTransforms.exceptionalDivisor T).ideal :=
    pullback_eq_exceptionalDivisor_of_isGeoResolution 𝔪 rfl h𝔞 rfl T hres
  have hsuppZ : (BlowupTowerTransforms.exceptionalDivisor T).support = T.proj ⁻¹' 𝔞.zeroLocus := by
    rw [EffectiveDivisor.support, ← hpb, BlowupExceptionalDivisor.zeroLocus_pullback T.contMDiff_proj h𝔞]
  have hadm := isAdmissibleBlowupSequence_proj 𝔪 _ T hres.1
    (centresOver_cosupp 𝔪 hdom.isWellFormed.isClosedSubmanifold_N h𝔞 T hres.1)
  rw [hcos] at hadm
  refine ⟨Y, inferInstance, inferInstance, inferInstance, T.proj, BlowupTowerTransforms.exceptionalDivisor T, _, hadm,
    hpb, (InvDomainTowerAlong.isInvDomain_geoTransformAlong hdom T hres.1).isWellFormed.isSNCDivisor,
    HironakaPrincipalization.support_exceptionalDivisor_eq_biUnion 𝔪 rfl T, hsuppZ, ?_⟩
  refine HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset T.isBlowupSequence ?_
  rintro x ⟨z, hz, rfl⟩
  have hz' := HironakaPrincipalization.exceptionalLocus_subset_support T hz
  rw [hsuppZ] at hz'
  exact hz'

/-- **Principalization, admissible form** (compact `X`). -/
theorem exists_principalization_admissible {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] [CompactSpace X] {𝔞 : GermIdeal n X} (h𝔞 : 𝔞.IsCoherent)
    (hne : ∀ x, IsNonzeroAlongAt univ 𝔞 x) :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : ChartedSpace (ComplexModel n) X')
      (_ : IsComplexManifold n X') (f : X' → X) (D : EffectiveDivisor n X') (E : List (Set X')),
      IsAdmissibleBlowupSequence n X [] 𝔞.zeroLocus X' f E ∧
      GermIdeal.pullback (m := n) f 𝔞 = D.ideal ∧
      IsSNCDivisor n E ∧
      D.support = ⋃ H ∈ E, H ∧
      D.support = f ⁻¹' 𝔞.zeroLocus ∧
      IsIsomorphismOver n f 𝔞.zeroLocusᶜ := by
  have hdom := HironakaPrincipalization.isInvDomain_univ (M := CMfd.of (n := n) X) h𝔞 hne
  have hclosed : IsClosed 𝔞.zeroLocus := by
    rw [← cosupp_univ_one (X := CMfd.of (n := n) X) h𝔞]
    exact GiraudAlong.isClosed_cosupport_along hdom.isWellFormed.isCoherent hdom.isWellFormed.isClosedSubmanifold_N _
  exact exists_principalization_of_isCompact h𝔞 hne hclosed.isCompact

end Principalization

/-! ### Embedded resolution of a compact subvariety -/

section EmbeddedResolution

/-- **Embedded resolution of a compact subvariety, tower form** (`dim V < n`, `𝓘_V` coherent, `V` compact; `X` any complex
manifold): a multiple test blow-up `T` of `(X, X, ∅, 𝓘_V, 1)` whose centres miss the preimages of `X \ V_sing` and whose strict
transform of `V` is a closed submanifold, regular of dimension `dim V` at each of its points, with only normal crossings with
the transformed divisor. -/
theorem exists_tower_embeddedResolution_of_isCompact {X : CMfd.{u} n} (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hV : V.dim < n) (hcoh : (vanishingIdeal (n := n) V.carrier).IsCoherent) (hK : IsCompact V.carrier) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsGeoTestTower (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X) T ∧
      CentresAvoid (regularOpen V) T ∧
      IsClosedSubmanifold n (strictTransform n T.proj V.carrier) ∧
      (∀ x ∈ strictTransform n T.proj V.carrier,
        RegularAtDim (n := n) (strictTransform n T.proj V.carrier) x V.dim) ∧
      HasNormalCrossings n (strictTransform n T.proj V.carrier)
        (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X) T).E := by
  have hdom : IsInvDomain n (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X) :=
    isInvDomain_vanishingIdeal_of_dim_lt le_rfl V hV hcoh
  have hcos : (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X).cosupp = V.carrier :=
    SmoothCentreLocus.cosupp_vanishingIdeal V.isClosed_carrier (subset_univ _)
  obtain ⟨Y₀, T₀, hcan₀, hres₀⟩ := exists_isGeoResolution_isCanonical_of_isCompact
    (CanonicalCentres.canonicalInvariant.{u} n) hdom (by rw [hcos]; exact hK)
  exact exists_tower_embedded_of_isCanonical
    (HironakaFromSeqInvariant.embeddingFields_of_seq (CanonicalCentres.canonicalInvariant.{u} n))
    V.analytic (regularOpen V) (fun x hxV hxO => regularAtDim_of_mem_regularOpen hxV hxO)
    (subset_closure_inter_regularOpen V) hdom T₀ hcan₀ hres₀

/-- **Embedded resolution of a compact subvariety** (Hironaka; `hir:embedded-resolution-compact-support`): let `X` be any
complex manifold and `V ⊆ X` a compact irreducible analytic subvariety.  There are an admissible blowup sequence `f : X' → X`
(from the empty divisor, with centres over `V_sing`) with accumulated divisor `E` such that `E` has simple normal crossings,
`Exc f = ⋃ E = f⁻¹(V_sing)`, `f` is an isomorphism over `X \ V_sing`, the strict transform of `V` is a closed connected
submanifold of dimension `dim V`, and it has only normal crossings with `E`. -/
theorem exists_embeddedResolution_of_isCompact {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] (V : ClosedIrreducibleAnalyticSubvariety n X) (hK : IsCompact V.carrier) :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : ChartedSpace (ComplexModel n) X')
      (_ : IsComplexManifold n X') (f : X' → X) (E : List (Set X')),
      IsAdmissibleBlowupSequence n X [] (singularLocus V) X' f E ∧
      IsSNCDivisor n E ∧
      exceptionalLocus n f = ⋃ H ∈ E, H ∧
      (⋃ H ∈ E, H) = f ⁻¹' singularLocus V ∧
      IsIsomorphismOver n f (singularLocus V)ᶜ ∧
      IsClosedConnectedSubmanifold n (strictTransform n f V.carrier) V.dim ∧
      HasNormalCrossings n (strictTransform n f V.carrier) E := by
  rcases V.dim_le.lt_or_eq with h | h
  · obtain ⟨Y, T, hTt, hT, -, hreg, hnc⟩ :=
      exists_tower_embeddedResolution_of_isCompact (X := CMfd.of (n := n) X) V h
        (CartanIrreducible.cartanCoherence V.carrier V.irreducible_carrier.analytic) hK
    have hdom : IsInvDomain n (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ :
        MarkedIdeal n (CMfd.of (n := n) X)) :=
      isInvDomain_vanishingIdeal_of_dim_lt le_rfl V h
        (CartanIrreducible.cartanCoherence V.carrier V.irreducible_carrier.analytic)
    obtain ⟨hsnc, hsupp, hexc, hsing⟩ := exceptionalDivisor_facts_of_centresAvoid hdom rfl (regularOpen V) T hTt hT
    have hsing' : (BlowupTowerTransforms.exceptionalDivisor T).support ⊆ T.proj ⁻¹' singularLocus V := fun z hz =>
      not_not.mp (hsing hz)
    have hExcS : T.proj '' exceptionalLocus n T.proj ⊆ singularLocus V := by
      rintro x ⟨z, hz, rfl⟩
      exact hsing' (hexc hz)
    have hsub := HironakaEmbeddedExceptional.preimage_singularLocus_subset_exceptionalLocus T.contMDiff_proj V hreg
    have hadm := isAdmissibleBlowupSequence_proj _ ((regularOpen V : Set (CMfd.of (n := n) X))ᶜ) T hTt
      (centresOver_compl_of_centresAvoid (regularOpen V) T hT)
    rw [show ((regularOpen V : Set (CMfd.of (n := n) X))ᶜ) = singularLocus V from compl_compl _] at hadm
    refine ⟨Y, inferInstance, inferInstance, inferInstance, T.proj, _, hadm, hsnc, ?_, ?_,
      HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset T.isBlowupSequence hExcS,
      ⟨isClosed_closure,
        HironakaEmbeddedResolutionLocal.isConnected_strictTransform_of_isBlowupSequence T.isBlowupSequence V hExcS,
        hreg⟩, hnc⟩
    · rw [← hsupp]
      exact Subset.antisymm hexc (hsing'.trans hsub)
    · rw [← hsupp]
      exact Subset.antisymm hsing' (hsub.trans hexc)
  · have hV := isClosedConnectedSubmanifold_of_dim_eq V h
    have hst : strictTransform n (id : X → X) V.carrier = V.carrier := by
      simp [strictTransform, exceptionalLocus_id, V.isClosed_carrier.closure_eq]
    have hsing0 : singularLocus V = ∅ := by
      refine eq_empty_iff_forall_notMem.mpr fun x hx => hx.2 ?_
      show RegularAtDim (n := n) V.carrier x V.dim
      rw [h]
      exact hV.2.2 x hx.1
    refine ⟨X, inferInstance, inferInstance, inferInstance, id, [], IsAdmissibleBlowupSequence.refl, isSNCDivisor_nil,
      ?_, ?_, HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset
        IsBlowupSequence.refl (by simp [exceptionalLocus_id]), ?_, ?_⟩
    · simp [exceptionalLocus_id]
    · simp [hsing0]
    · rw [hst, h]
      exact hV
    · rw [hst]
      exact hasNormalCrossings_nil_of_isClosedSubmanifold
        (FactorizationDomain.isClosedSubmanifold_of_isClosedConnectedSubmanifold hV)

/-- **Embedded resolution, admissible form** (compact `X`; the admissibility of the sequence and the centres over
`V_sing` exported). -/
theorem exists_embeddedResolution_admissible {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] [CompactSpace X] (V : ClosedIrreducibleAnalyticSubvariety n X) :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : ChartedSpace (ComplexModel n) X')
      (_ : IsComplexManifold n X') (f : X' → X) (E : List (Set X')),
      IsAdmissibleBlowupSequence n X [] (singularLocus V) X' f E ∧
      IsSNCDivisor n E ∧
      exceptionalLocus n f = ⋃ H ∈ E, H ∧
      (⋃ H ∈ E, H) = f ⁻¹' singularLocus V ∧
      IsIsomorphismOver n f (singularLocus V)ᶜ ∧
      IsClosedConnectedSubmanifold n (strictTransform n f V.carrier) V.dim ∧
      HasNormalCrossings n (strictTransform n f V.carrier) E :=
  exists_embeddedResolution_of_isCompact V V.isClosed_carrier.isCompact

end EmbeddedResolution

end

end Hironaka.HironakaAdmissibleSequence
