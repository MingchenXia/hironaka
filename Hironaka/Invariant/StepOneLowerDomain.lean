/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.StepOneValue
import Hironaka.Invariant.ContactStageInvDomain
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.Invariant.BoundaryCount
import Hironaka.Invariant.CodimOnePartCanonical
import Hironaka.MarkedIdeal.CodimOneSupportAlong
import Hironaka.Invariant.ContactIndependenceAlong
import Hironaka.MarkedIdeal.DerivativeIdealAlongTransform
import Hironaka.Invariant.DivisorExponentAlong
import Hironaka.MarkedIdeal.HomogenizedGlueingTower
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.Invariant.InvDomainMemberRestriction
import Hironaka.Invariant.InvDomainTowerAlong
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOpenBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Invariant.MaximalOrderStepOneB
import Hironaka.Invariant.MemberInterLocusAlong
import Hironaka.Blowup.NormalCrossings
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.Invariant.ResolutionInvariantSpec
import Hironaka.Invariant.StepOneRegime
import Hironaka.MarkedIdeal.TangentDirectionAlong
import Hironaka.MarkedIdeal.TransformOffCentre
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The masks and the domain of the lower marked ideals of Step 1

Source: Włodarczyk 2005 (arXiv `hiron.tex`), proof of Proposition `pr:resol`, Step 1ab (the restriction
`J̄_{|H^s_α}`, after the intersections contained in the support are blown up) and Step 1bb (the restriction
`J̄_{p|V(u)_p}` to the strict transform of a hypersurface of maximal contact, after the codimension-one components
are blown up).

Let `𝔍` be well formed with `d ≥ 1`, of maximal order along `N`, `dim N ≤ k`, and `T₀` a multiple test blow-up of
`J̄ = 𝓒_N(𝓗_N(𝔍))`.  At a point `y₀` of the cosupport of `J̄_{T₀}` which is not special (`StepOneValue.IsSpecial`), of level `s`:

* `mem_maskA` (`s ≥ 1`): `y₀` lies in its mask -- the original members are closed and, on the open set of the points
  on no original member missing `y₀` (where the level is at most `s`), the level-`s` member locus is closed
  (`MemberInterLocusAlong.isAdmissibleCentre_memberInterLocus_level` for the restricted marked ideal);
* `isInvDomain_lowerMarked_succ` (`s ≥ 1`): the lower marked ideal (`memberRestrict` restricted to the mask) lies in
  `IsInvDomain (k - 1)`
* `mem_maskB` (`s = 0`): `y₀` lies in its mask -- a tangent direction exists at the base point (maximal order), the original
  members are closed, and the codimension-one part `Z₁` of `J̄_{T₀}` is closed (maximal order is kept along the tower);
* `isInvDomain_lowerMarked_zero` (`s = 0`): the lower marked ideal (`contactMarked` on the mask) lies in
  `IsInvDomain (k - 1)` (`ContactStageInvDomain.isInvDomain_stage_coeffHom_of_le`);
* `mem_lowerMask_and_isInvDomain`: both, for every level.

The tools on `J̄` and along towers: `isWellFormed_barMarked`, `isMaximalOrderAlong_barMarked`, `cosupp_barMarked`,
`isMaximalOrderAlong_geoTransformAlong`, `proj_mem_cosupp_of_mem_cosupp`, `isClosed_of_mem_origMembers`,
`tangentChoice_spec`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.StepOneLowerDomain

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.HomogenizedIdealAlong Hironaka.MaximalOrderStepOneB Hironaka.StepOneRegime Hironaka.StepOneValue Hironaka.BoundaryCount Hironaka.CodimOneSupportAlong Hironaka.MemberInterLocusAlong Hironaka.InvDomainMemberRestriction Hironaka.TangentDirectionAlong Hironaka.MarkedIdealBiholomorphism Hironaka.MarkedIdealRestrictOpen Hironaka.GermIdealOrder
open Hironaka.ResolutionInvariantSpec (IsInvDomain DimLE)

noncomputable section

variable {n : ℕ}

/-! ### `J̄` and the tower -/

section Bar

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X)

/-- **`J̄ = 𝓒_N(𝓗_N(𝔍))` is well formed** when `𝔍` is (same submanifold and divisor, coherent ideal). -/
theorem isWellFormed_barMarked (h𝔍 : 𝔍.IsWellFormed) : (barMarked 𝔍).IsWellFormed :=
  ⟨h𝔍.isClosedSubmanifold_N, isCoherent_barMarked 𝔍 h𝔍.isClosedSubmanifold_N h𝔍.isCoherent, h𝔍.isSNCDivisor,
    h𝔍.isTransverse⟩

/-- **`J̄` has maximal order along `N`** when `𝔍` has (`d ≥ 1`). -/
theorem isMaximalOrderAlong_barMarked (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) :
    IsMaximalOrderAlong (barMarked 𝔍).N (barMarked 𝔍).ideal (barMarked 𝔍).d := by
  have hhol : ∀ x g, 𝔍.ideal.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔍.isCoherent hg
  have hholH : ∀ x g, (homMarkedAlong 𝔍).ideal.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
      (isCoherent_homMarkedAlong h𝔍.isCoherent h𝔍.isClosedSubmanifold_N) hg
  exact IsMaximalOrderAlong.coeffMarkedAlong (𝔪 := homMarkedAlong 𝔍) h𝔍.isClosedSubmanifold_N.2 hholH hd
    (IsMaximalOrderAlong.homogenizedIdealAlong hhol hd hmax)

/-- **The cosupport of `J̄` is that of `𝔍`** (`d ≥ 1`). -/
theorem cosupp_barMarked (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) : (barMarked 𝔍).cosupp = 𝔍.cosupp := by
  have hhol : ∀ x g, 𝔍.ideal.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔍.isCoherent hg
  have hholH : ∀ x g, (homMarkedAlong 𝔍).ideal.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
      (isCoherent_homMarkedAlong h𝔍.isCoherent h𝔍.isClosedSubmanifold_N) hg
  rw [cosupp_coeffMarkedAlong (𝔪 := homMarkedAlong 𝔍) h𝔍.isClosedSubmanifold_N.2 hholH hd,
    cosupp_homMarkedAlong hhol hd]

/-- The original members at every stage are closed. -/
theorem isClosed_of_mem_origMembers (hE : ∀ H ∈ 𝔍.E, IsClosed H) {Y : CMfd.{u} n} (T : BlowupTower X Y) :
    ∀ H ∈ origMembers 𝔍 T, IsClosed H :=
  isClosed_of_mem_take_E_geoTransformAlong (barMarked 𝔍) hE T

end Bar

section Tower

variable {X : CMfd.{u} n}

/-- **Maximal order is kept along a multiple test blow-up** (`DerivativeIdealAlongTransform.isMaximalOrderAlong_geoTransform`
at each step). -/
theorem isMaximalOrderAlong_geoTransformAlong {𝔪 : MarkedIdeal n X} (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : 𝔪.ideal.IsCoherent) (hmax : IsMaximalOrderAlong 𝔪.N 𝔪.ideal 𝔪.d) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower 𝔪 T →
      IsMaximalOrderAlong (geoTransformAlong 𝔪 T).N (geoTransformAlong 𝔪 T).ideal (geoTransformAlong 𝔪 T).d
  | _, .refl, _ => hmax
  | _, .step T C π hπ, hT => by
      obtain ⟨hTT, hC⟩ := (isGeoTestTower_step_iff 𝔪 T C π hπ).mp hT
      obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 T hTT
      have ih := isMaximalOrderAlong_geoTransformAlong hN h𝔞 hmax T hTT
      rw [geoTransformAlong_step, geoTransform_d]
      exact DerivativeIdealAlongTransform.isMaximalOrderAlong_geoTransform (geoTransformAlong 𝔪 T) hNT hcT hC hπ ih

/-- **The images of the points of the cosupport lie in the cosupport** along a multiple test blow-up (over the centre, the
centre lies in the cosupport; off it, `TransformOffCentre.mem_cosupp_geoTransform_iff`). -/
theorem proj_mem_cosupp_of_mem_cosupp {𝔪 : MarkedIdeal n X} (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : 𝔪.ideal.IsCoherent) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower 𝔪 T → ∀ {z : Y},
      z ∈ (geoTransformAlong 𝔪 T).cosupp → T.proj z ∈ 𝔪.cosupp
  | _, .refl, _, _, hz => hz
  | _, .step T C π hπ, hT, z, hz => by
      obtain ⟨hTT, hC⟩ := (isGeoTestTower_step_iff 𝔪 T C π hπ).mp hT
      obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 T hTT
      refine proj_mem_cosupp_of_mem_cosupp hN h𝔞 T hTT ?_
      by_cases hzC : π z ∈ C
      · exact hC.2.1 hzC
      · exact (TransformOffCentre.mem_cosupp_geoTransform_iff (geoTransformAlong 𝔪 T) hNT.1
          (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcT hg) hπ hzC).mp hz

end Tower

/-! ### The chosen tangent direction -/

section Tangent

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X)

/-- **The chosen tangent direction** contains the base point and is a tangent direction, when there is one. -/
theorem tangentChoice_spec {x : X}
    (h : ∃ (U : Set X) (w : X → ℂ), x ∈ U ∧ IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U w) :
    x ∈ (tangentChoice 𝔍 x).1 ∧
      IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d (tangentChoice 𝔍 x).1 (tangentChoice 𝔍 x).2 := by
  classical
  rw [tangentChoice, dif_pos h]
  exact h.choose_spec.choose_spec

/-- **At the image in `X` of a point of the cosupport along a multiple test blow-up of `J̄` a tangent direction exists**
(maximal order). -/
theorem exists_tangent_of_mem_cosupp (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower (barMarked 𝔍) T) {y : Y} (hy : y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp) :
    ∃ (U : Set X) (w : X → ℂ), T.proj y ∈ U ∧ IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U w := by
  have hx : T.proj y ∈ (barMarked 𝔍).cosupp :=
    proj_mem_cosupp_of_mem_cosupp (𝔪 := barMarked 𝔍) h𝔍.isClosedSubmanifold_N
      (isCoherent_barMarked 𝔍 h𝔍.isClosedSubmanifold_N h𝔍.isCoherent) T hT hy
  rw [cosupp_barMarked 𝔍 h𝔍 hd] at hx
  exact exists_isTangentDirectionAlong_of_isMaximalOrderAlong h𝔍.isCoherent h𝔍.isClosedSubmanifold_N hd hmax hx

end Tangent

/-! ### Step 1bb -/

section StepOneB

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X) (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d)
  (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀)
  (hT₀ : IsGeoTestTower (barMarked 𝔍) T₀) {y₀ : Y₀}

include h𝔍 hd hmax hT₀ in
/-- **Step 1bb: the point lies in its mask** -- over the open set of the chosen tangent direction, on no original member
(level `0`, closed members), off `Z₁` (closed, by maximal order). -/
theorem mem_maskB (hy₀ : y₀ ∈ (geoTransformAlong (barMarked 𝔍) T₀).cosupp) (hl : level 𝔍 T₀ y₀ = 0)
    (hZ : y₀ ∉ codimOnePartAlong (geoTransformAlong (barMarked 𝔍) T₀).N (geoTransformAlong (barMarked 𝔍) T₀).ideal
      (geoTransformAlong (barMarked 𝔍) T₀).d) : y₀ ∈ maskB 𝔍 T₀ y₀ := by
  classical
  obtain ⟨hxU, hU⟩ := tangentChoice_spec 𝔍 (exists_tangent_of_mem_cosupp 𝔍 h𝔍 hd hmax T₀ hT₀ hy₀)
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJ.isClosedSubmanifold_N
    hJ.isCoherent T₀ hT₀
  have hmaxT := isMaximalOrderAlong_geoTransformAlong hJ.isClosedSubmanifold_N hJ.isCoherent
    (isMaximalOrderAlong_barMarked 𝔍 h𝔍 hd hmax) T₀ hT₀
  have hdT : 1 ≤ (geoTransformAlong (barMarked 𝔍) T₀).d := by
    rw [d_geoTransformAlong]
    exact ContactIndependenceAlong.one_le_coeffMarkedAlong_d _
  have hZc := isClosed_codimOnePartAlong hcT hNT hdT hmaxT
  have hEc := isClosed_of_mem_origMembers 𝔍 (fun H hH => h𝔍.isSNCDivisor.1 H hH) T₀
  -- an open neighbourhood of `y₀` inside the defining set
  set O : Set Y₀ := T₀.proj ⁻¹' (tangentChoice 𝔍 (T₀.proj y₀)).1 ∩
    (⋂ H ∈ {H | H ∈ origMembers 𝔍 T₀}, Hᶜ) ∩
    (codimOnePartAlong (geoTransformAlong (barMarked 𝔍) T₀).N (geoTransformAlong (barMarked 𝔍) T₀).ideal
      (geoTransformAlong (barMarked 𝔍) T₀).d)ᶜ with hOdef
  have hO : IsOpen O :=
    ((hU.isOpen.preimage T₀.contMDiff_proj.continuous).inter
      ((List.finite_toSet (origMembers 𝔍 T₀)).isOpen_biInter fun H hH => (hEc H hH).isOpen_compl)).inter
      hZc.isOpen_compl
  have hyO : y₀ ∈ O := by
    refine ⟨⟨hxU, ?_⟩, hZ⟩
    simp only [mem_iInter]
    intro H hH hyH
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hH
    have hpos : 0 < boundaryCount (origMembers 𝔍 T₀) y₀ :=
      Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyH⟩⟩
    have : boundaryCount (origMembers 𝔍 T₀) y₀ = 0 := hl
    omega
  show y₀ ∈ interior _
  refine interior_maximal ?_ hO hyO
  intro z hz
  refine ⟨hz.1.1, fun H hH hzH => ?_, hz.2⟩
  have h2 := hz.1.2
  simp only [mem_iInter] at h2
  exact h2 H hH hzH

include h𝔍 hd hmax hT₀ in
/-- **Step 1bb: the lower marked ideal lies in the domain** of the inductive invariant (`dim N ≤ k`):
`isInvDomain_stage_coeffHom_of_le` on the mask, which lies over the open set of the tangent direction and misses
`Z₁`. -/
theorem isInvDomain_lowerMarked_zero {k : ℕ} (hk : DimLE n 𝔍.N k)
    (hy₀ : y₀ ∈ (geoTransformAlong (barMarked 𝔍) T₀).cosupp) :
    IsInvDomain (k - 1) (lowerMarked 𝔍 0 T₀ y₀) := by
  obtain ⟨hxU, hU⟩ := tangentChoice_spec 𝔍 (exists_tangent_of_mem_cosupp 𝔍 h𝔍 hd hmax T₀ hT₀ hy₀)
  have hT₀' := isGeoTestTower_stepOneMarked_of_coeffHom 𝔍 T₀ hT₀
  have hdrop := geoTransformAlong_coeffHom_dropE 𝔍 T₀
  have hsub : ((maskB 𝔍 T₀ y₀ : Opens Y₀) : Set Y₀) ⊆
      openPreimage T₀ ⟨(tangentChoice 𝔍 (T₀.proj y₀)).1, hU.isOpen⟩ := fun z hz => (interior_subset hz).1
  have hZ : ∀ y ∈ maskB 𝔍 T₀ y₀, y ∈ HomogenizedGlueingTower.strictAlong T₀ (𝔍.N ∩ {x | (tangentChoice 𝔍 (T₀.proj y₀)).2 x = 0}) →
      y ∉ codimOnePartAlong (geoTransformAlong (stepOneMarked 𝔍.N 𝔍.ideal 𝔍.d) T₀).N
        (geoTransformAlong (stepOneMarked 𝔍.N 𝔍.ideal 𝔍.d) T₀).ideal
        (geoTransformAlong (stepOneMarked 𝔍.N 𝔍.ideal 𝔍.d) T₀).d := by
    intro y hy _
    rw [hdrop]
    exact (interior_subset hy).2.2
  exact ContactStageInvDomain.isInvDomain_stage_coeffHom_of_le h𝔍.isCoherent h𝔍.isClosedSubmanifold_N hd hk
    ⟨(tangentChoice 𝔍 (T₀.proj y₀)).1, hU.isOpen⟩ hU T₀ hT₀' (maskB 𝔍 T₀ y₀) hsub hZ

end StepOneB

/-! ### Step 1ab -/

section StepOneA

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X) (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
  {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (hT₀ : IsGeoTestTower (barMarked 𝔍) T₀) {y₀ : Y₀}

include h𝔍 hd hn hT₀ in
/-- **Step 1ab: the point lies in its mask**: on the open set `V` of the points on no original member missing `y₀`, the
level is at most that of `y₀`, so the level-`s` member locus of the restriction of `J̄_{T₀}` to `V` is an admissible
centre, in particular closed; `y₀` is not in it. -/
theorem mem_maskA (hl : 1 ≤ level 𝔍 T₀ y₀) (hsp : ¬ IsSpecial 𝔍 T₀ y₀) : y₀ ∈ maskA 𝔍 T₀ y₀ := by
  classical
  set 𝔪 := geoTransformAlong (barMarked 𝔍) T₀ with h𝔪def
  set E₀ := origMembers 𝔍 T₀ with hE₀def
  set s := level 𝔍 T₀ y₀ with hsdef
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  have h𝔪 : 𝔪.IsWellFormed := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hJ T₀ hT₀
  have hd𝔪 : 1 ≤ 𝔪.d := by
    rw [h𝔪def, d_geoTransformAlong]
    exact ContactIndependenceAlong.one_le_coeffMarkedAlong_d _
  have hEc : ∀ H ∈ E₀, IsClosed H := isClosed_of_mem_origMembers 𝔍 (fun H hH => h𝔍.isSNCDivisor.1 H hH) T₀
  obtain ⟨V, hyV, hV⟩ := exists_opens_forall_mem_imp hEc y₀
  have hhol : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔪.isCoherent hg
  -- the restriction to `V`
  set 𝔪V := MarkedIdeal.pullback (Subtype.val : V → Y₀) 𝔪 with h𝔪Vdef
  have h𝔪V : 𝔪V.IsWellFormed := IsWellFormed.pullback_val h𝔪 V
  set E₀V := E₀.map ((Subtype.val : V → Y₀) ⁻¹' ·) with hE₀Vdef
  have hsubl : E₀V.Sublist 𝔪V.E := (List.take_sublist _ _).map _
  have hcount : ∀ p : V, boundaryCount E₀V p = boundaryCount E₀ (p : Y₀) := fun p =>
    CodimOnePartCanonical.boundaryCount_map_preimage _ _ p
  have hle : ∀ p : V, boundaryCount E₀ (p : Y₀) ≤ s := fun p => by
    show (Finset.univ.filter fun i : Fin E₀.length => (p : Y₀) ∈ E₀.get i).card ≤
      (Finset.univ.filter fun i : Fin E₀.length => y₀ ∈ E₀.get i).card
    exact Finset.card_le_card fun i hi => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact hV p p.2 _ (List.get_mem _ _) hi
  have hadm := isAdmissibleCentre_memberInterLocus_level 𝔪V h𝔪V hd𝔪 hn hsubl s
    (fun p _ => (hcount p).trans_le (hle p))
  have hC : IsClosed (memberInterLocus 𝔪V.N E₀V 𝔪V.cosupp ∩ {p | boundaryCount E₀V p = s}) := hadm.1.1
  have hcos : 𝔪V.cosupp = (Subtype.val : V → Y₀) ⁻¹' 𝔪.cosupp := cosupp_pullback_val 𝔪 hhol V
  have hmem : ∀ p : V, p ∈ memberInterLocus 𝔪V.N E₀V 𝔪V.cosupp ∩ {p | boundaryCount E₀V p = s} ↔
      ((p : Y₀) ∈ memberInterLocus 𝔪.N E₀ 𝔪.cosupp ∧ boundaryCount E₀ (p : Y₀) = s) := fun p => by
    show (p ∈ memberInterLocus 𝔪V.N E₀V 𝔪V.cosupp ∧ boundaryCount E₀V p = s) ↔ _
    rw [hcount p, hcos]
    exact and_congr (mem_memberInterLocus_preimage_iff Subtype.val
      (V.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq p) 𝔪.N E₀ 𝔪.cosupp) Iff.rfl
  -- the open neighbourhood `O = V ∖ L_s` of `y₀`
  set O : Set Y₀ := (Subtype.val : V → Y₀) ''
    (memberInterLocus 𝔪V.N E₀V 𝔪V.cosupp ∩ {p | boundaryCount E₀V p = s})ᶜ with hOdef
  have hO : IsOpen O := V.isOpen.isOpenMap_subtype_val _ hC.isOpen_compl
  have hyO : y₀ ∈ O := by
    refine ⟨⟨y₀, hyV⟩, fun h => hsp (Or.inr ⟨hl, ?_⟩), rfl⟩
    exact ((hmem ⟨y₀, hyV⟩).mp h).1
  show y₀ ∈ interior _
  refine interior_maximal ?_ hO hyO
  rintro z ⟨p, hp, rfl⟩
  refine ⟨hV p p.2, fun ⟨hlev, hspz⟩ => hp ((hmem p).mpr ⟨?_, hlev⟩)⟩
  rcases hspz with ⟨h0, -⟩ | ⟨-, hL⟩
  · exact absurd (h0 ▸ hlev : (0 : ℕ) = s) (by omega)
  · exact hL

include h𝔍 hd hn hT₀ in
/-- **Step 1ab: the lower marked ideal lies in the domain** of the inductive invariant (`dim N ≤ k`, level `s + 1 ≥
1`): `memberRestrict` at the original members through `y₀`, restricted to the mask, whose points lie on exactly
those members and are not special of that level. -/
theorem isInvDomain_lowerMarked_succ {k s : ℕ} (hk : DimLE n 𝔍.N k) (hl : level 𝔍 T₀ y₀ = s + 1) :
    IsInvDomain (k - 1) (lowerMarked 𝔍 (s + 1) T₀ y₀) := by
  set 𝔪 := geoTransformAlong (barMarked 𝔍) T₀ with h𝔪def
  set E₀ := origMembers 𝔍 T₀ with hE₀def
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  have h𝔪 : 𝔪.IsWellFormed := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hJ T₀ hT₀
  have hd𝔪 : 1 ≤ 𝔪.d := by
    rw [h𝔪def, d_geoTransformAlong]
    exact ContactIndependenceAlong.one_le_coeffMarkedAlong_d _
  have hk𝔪 : DimLE n 𝔪.N k :=
    InvDomainTowerAlong.dimLE_geoTransformAlong hJ.isClosedSubmanifold_N hJ.isCoherent hk T₀ hT₀
  have hE₀ : ∀ H ∈ E₀, H ∈ 𝔪.E := fun H hH => List.mem_of_mem_take hH
  have hy : 1 ≤ boundaryCount E₀ y₀ := by
    have : boundaryCount E₀ y₀ = s + 1 := hl
    omega
  have hU : ∀ z ∈ maskA 𝔍 T₀ y₀, ∀ H ∈ E₀, z ∈ H → y₀ ∈ H := fun z hz => (interior_subset hz).1
  refine isInvDomain_pullback_val_of_forall (isWellFormed_memberRestrict hn h𝔪 _)
    (dimLE_memberRestrict hn h𝔪 (membersThrough_nonempty hE₀ hy) hk𝔪) (one_le_memberRestrict_d 𝔪 _)
    (maskA 𝔍 T₀ y₀) ?_
  rintro z ⟨hzN, hzS⟩ hzU
  have hzS' : z ∈ {w | ∀ H ∈ E₀, y₀ ∈ H → w ∈ H} := memberInter_membersThrough hE₀ y₀ ▸ hzS
  have hiff : ∀ H ∈ E₀, y₀ ∈ H ↔ z ∈ H := fun H hH =>
    ⟨fun hyH => hzS' H hH hyH, fun hzH => hU z hzU H hH hzH⟩
  have hset : memberInter 𝔪.E (membersThrough 𝔪.E E₀ y₀) = {w | ∀ H ∈ E₀, z ∈ H → w ∈ H} := by
    rw [memberInter_membersThrough hE₀ y₀]
    ext w
    exact forall_congr' fun H => forall_congr' fun hH => by rw [hiff H hH]
  refine isNonzeroAlongAt_memberRestrict h𝔪.isClosedSubmanifold_N h𝔪.isCoherent hd𝔪 E₀ _ hzN
    (Eventually.of_forall fun w => by rw [hset]; exact Iff.rfl) fun hzL => ?_
  have hlev : level 𝔍 T₀ z = level 𝔍 T₀ y₀ := (boundaryCount_eq_of_forall_iff hiff).symm
  exact (interior_subset hzU).2 ⟨hlev, Or.inr ⟨by rw [hlev, hl]; omega, hzL⟩⟩

end StepOneA

/-! ### Both steps -/

section Both

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X)

/-- **The mask and domain clauses of `LowerData`**: for `𝔍` well formed with `d ≥ 1`, of maximal order along `N` with
`dim N ≤ k` (`0 < n`), along a multiple test blow-up `T₀` of `J̄`, at a point `y₀` of the cosupport in the regime of its level
`s` (not special), `y₀` lies in its mask and the lower marked ideal lies in `IsInvDomain (k - 1)`. -/
theorem mem_lowerMask_and_isInvDomain (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) {k : ℕ} (hk : DimLE n 𝔍.N k) {Y₀ : CMfd.{u} n}
    (T₀ : BlowupTower X Y₀) (hT₀ : IsGeoTestTower (barMarked 𝔍) T₀) {y₀ : Y₀}
    (hy₀ : y₀ ∈ (geoTransformAlong (barMarked 𝔍) T₀).cosupp) {s : ℕ} (hreg : stepRegime 𝔍 s T₀ y₀) :
    y₀ ∈ lowerMask 𝔍 s T₀ y₀ ∧ IsInvDomain (k - 1) (lowerMarked 𝔍 s T₀ y₀) := by
  obtain ⟨hl, hsp⟩ := hreg
  match s, hl with
  | 0, hl =>
    refine ⟨mem_maskB 𝔍 h𝔍 hd hmax T₀ hT₀ hy₀ hl fun hZ => hsp (Or.inl ⟨hl, hZ⟩),
      isInvDomain_lowerMarked_zero 𝔍 h𝔍 hd hmax T₀ hT₀ hk hy₀⟩
  | s + 1, hl =>
    exact ⟨mem_maskA 𝔍 h𝔍 hd hn T₀ hT₀ (by omega) hsp, isInvDomain_lowerMarked_succ 𝔍 h𝔍 hd hn T₀ hT₀ hk hl⟩

end Both

end

end Hironaka.StepOneLowerDomain
