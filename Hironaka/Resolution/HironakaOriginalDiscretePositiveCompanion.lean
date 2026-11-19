/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalGeneralControlledCompositeResidual
import Hironaka.Resolution.HironakaOriginalDiscretePreparationFirstEntry
import Hironaka.Invariant.NonmonomialOrderTail

/-! Actual positive companions on a SAME noncanonical discrete preparation
step. Original inputs construct the true window and companion test; earlier
frozen full ORIGINAL history comparison remains a separate obligation. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalDiscretePositiveCompanion
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen BlowupRestrictOpen
  NonmonomialOrderLocal NonmonomialOrderTail CompanionRebase CompanionReductionAlong CompanionOpen
  InvDomainCompanion MonomialPartAlong NonmonomialTransformAlong
  MarkedIdealOperationsAlong RestrictedIdealExtension DivisorExponentAlong
  HomogenizedIdealAlong GermIdealOrder
open HironakaOriginalSmoothCurveWholeTupleBadBlowup HironakaOneDimensionalCanonicalSuperlevels
  CanonicalCentres
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n k : ℕ} {X Y Z : CMfd.{u} n}

/-- ONLY actual domain/discrete admissibility/positive actual point order give
one true singleton order-mask window and actual maximal-order companion. -/
theorem exists_discrete_positive_companion_window (hn : 0<n)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    {C : Set X} (hC : M.IsAdmissibleCentre C) (hd : IsDiscrete C)
    {c : X} (hc : c ∈ C) (hq : 1 ≤ nmOrd M c) :
    ∃ U : Opens X,c ∈ U ∧ (U : Set X) ∩ C={c} ∧
      let J : MarkedIdeal n (CMfd.of (n := n) U) := MarkedIdeal.pullback (Subtype.val : U → X) M
      let O := companionOf n J (nmOrd M c)
      (∀ x ∈ J.cosupp,x ∉ ordGe J (nmOrd M c+1)) ∧ IsInvDomain k O ∧
      IsMaximalOrderAlong O.N O.ideal O.d ∧ O.IsAdmissibleCentre ((Subtype.val : U → X) ⁻¹' C) := by
  obtain ⟨U0,hU0,htrace⟩ := (isDiscrete_iff_forall_mem_exists_isOpen.mp hd) c hc
  have hcU0 : c ∈ U0 := ((Set.ext_iff.mp htrace c).mpr (mem_singleton c)).1
  have hcn : c ∈ M.N := hC.subset_N hc
  have hcNot : c ∉ ordGe M (nmOrd M c+1) := by
    intro h
    have hle := (mem_ordGe_iff hM.isWellFormed hM.isNonzeroAlongAt hcn _).mp h
    omega
  let U : Opens X := ⟨U0 ∩ (ordGe M (nmOrd M c+1))ᶜ,
    hU0.inter (isClosed_ordGe hn hM.isWellFormed hM.isNonzeroAlongAt _).isOpen_compl⟩
  have hcU : c ∈ U := ⟨hcU0,hcNot⟩
  have hTrace : (U : Set X) ∩ C={c} := by
    apply Set.ext
    intro x
    constructor
    · rintro ⟨hxU,hxC⟩
      exact (Set.ext_iff.mp htrace x).mp ⟨hxU.1,hxC⟩
    · intro hx
      have heq : x=c := mem_singleton_iff.mp hx
      subst x
      exact ⟨hcU,hc⟩
  let J : MarkedIdeal n (CMfd.of (n := n) U) := MarkedIdeal.pullback (Subtype.val : U → X) M
  let O := companionOf n J (nmOrd M c)
  have hJ : IsInvDomain k J := InvDomainTowerAlong.isInvDomain_pullback_val U hM
  have hBound : ∀ x ∈ J.cosupp,x ∉ ordGe J (nmOrd M c+1) := by
    intro x _hx hh
    exact x.property.2 ((mem_ordGe_pullback_val_iff hn hM.isWellFormed hM.isNonzeroAlongAt U _ x).mp hh)
  have hDom : IsInvDomain k O := isInvDomain_companionAlong hn hJ hq
  have hMax : IsMaximalOrderAlong O.N O.ideal O.d := by
    simpa only [O,companionOf,companionAlong_N] using
      isMaximalOrderAlong_companionOf hn hJ.isWellFormed hJ.isNonzeroAlongAt hBound
  have hCU : J.IsAdmissibleCentre ((Subtype.val : U → X) ⁻¹' C) := IsAdmissibleCentre.pullback_val
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent hg) hC U
  have hAdm : O.IsAdmissibleCentre ((Subtype.val : U → X) ⁻¹' C) := by
    refine ⟨hCU.1,?_,?_⟩
    · obtain ⟨_ht,_hn,_hb,hcos⟩ := companionOf_reduction hn hJ.isWellFormed hJ.isNonzeroAlongAt hq hBound .refl trivial
      intro x hxC
      have hxc : (x : X)=c := mem_singleton_iff.mp ((Set.ext_iff.mp hTrace x).mp ⟨x.property,hxC⟩)
      have hxOrd : x ∈ ordGe J (nmOrd M c) :=
        (mem_ordGe_pullback_val_iff hn hM.isWellFormed hM.isNonzeroAlongAt U _ x).mpr
          ((mem_ordGe_iff hM.isWellFormed hM.isNonzeroAlongAt (hC.subset_N hxC) _).mpr (by rw [hxc]))
      change x ∈ (geoTransformAlong O .refl).cosupp
      rw [hcos]
      exact ⟨hxOrd,hCU.2.1 hxC⟩
    · simpa only [O,companionOf,companionAlong_E] using hCU.2.2
  exact ⟨U,hcU,hTrace,hBound,hDom,hMax,hAdm⟩


/-- The literal restriction of the GIVEN actual blowup is internally a true
positive-companion test step, with BOTH actual current order-level directions. -/
theorem exists_discrete_positive_same_blowup_companion_test (hn : 0<n)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    {C : Set X} (hC : M.IsAdmissibleCentre C) (hd : IsDiscrete C)
    {c : X} (hc : c ∈ C) (hq : 1 ≤ nmOrd M c)
    {π : Y → X} (hπ : IsBlowupAlong n C π) :
    ∃ U : Opens X,c ∈ U ∧ (U : Set X) ∩ C={c} ∧
      let J : MarkedIdeal n (CMfd.of (n := n) U) := MarkedIdeal.pullback (Subtype.val : U → X) M
      let O := companionOf n J (nmOrd M c)
      let V : Opens Y := ⟨π ⁻¹' (U : Set X),U.isOpen.preimage hπ.contMDiff.continuous⟩
      let ρ : V → U := fun y => ⟨π y,y.property⟩
      let D : Set U := (Subtype.val : U → X) ⁻¹' C
      IsInvDomain k O ∧ IsMaximalOrderAlong O.N O.ideal O.d ∧
        ∃ hρ : IsBlowupAlong n D ρ,
          IsGeoTestTower O (BlowupTower.step (X := CMfd.of (n := n) U) (Y := CMfd.of (n := n) U) (Z := CMfd.of (n := n) V) .refl D ρ hρ) ∧
          IsInvDomain k (O.geoTransform D ρ) ∧
          (O.geoTransform D ρ).cosupp=ordGe (M := CMfd.of (n := n) V) (J.geoTransform D ρ) (nmOrd M c) ∩ (J.geoTransform D ρ).cosupp := by
  obtain ⟨U,hcU,hTrace,hBound,hDom,hMax,hAdm⟩ :=
    exists_discrete_positive_companion_window hn M hM hC hd hc hq
  let J : MarkedIdeal n (CMfd.of (n := n) U) := MarkedIdeal.pullback (Subtype.val : U → X) M
  let O := companionOf n J (nmOrd M c)
  let V : Opens Y := ⟨π ⁻¹' (U : Set X),U.isOpen.preimage hπ.contMDiff.continuous⟩
  let ρ : V → U := fun y => ⟨π y,y.property⟩
  let D : Set U := (Subtype.val : U → X) ⁻¹' C
  have hρ : IsBlowupAlong n D ρ := isBlowupAlong_restrict hπ U V.isOpen
  have ht : IsGeoTestTower O (BlowupTower.step (X := CMfd.of (n := n) U) (Y := CMfd.of (n := n) U) (Z := CMfd.of (n := n) V) .refl D ρ hρ) := ⟨trivial,hAdm⟩
  have hPost := InvDomainTowerAlong.isInvDomain_geoTransformAlong hDom (BlowupTower.step (X := CMfd.of (n := n) U) (Y := CMfd.of (n := n) U) (Z := CMfd.of (n := n) V) .refl D ρ hρ) ht
  have hJ : IsInvDomain k J := InvDomainTowerAlong.isInvDomain_pullback_val U hM
  have hcos := cosupp_companionOf_geoTransformAlong hn hJ hq hBound (BlowupTower.step (X := CMfd.of (n := n) U) (Y := CMfd.of (n := n) U) (Z := CMfd.of (n := n) V) .refl D ρ hρ) ht
  exact ⟨U,hcU,hTrace,hDom,hMax,hρ,ht,hPost,hcos⟩

/-- ONLY original domain and ANY actual original prefix internally supply the
real current domain before producing the SAME next-map positive companion. -/
theorem original_test_prefix_discrete_positive_companion_step (hn : 0<n)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    {C : Set Y} (hC : (geoTransformAlong M T).IsAdmissibleCentre C) (hd : IsDiscrete C)
    {c : Y} (hc : c ∈ C) (hq : 1 ≤ nmOrd (geoTransformAlong M T) c)
    {π : Z → Y} (hπ : IsBlowupAlong n C π) :
    ∃ U : Opens Y,c ∈ U ∧ (U : Set Y) ∩ C={c} ∧
      let J : MarkedIdeal n (CMfd.of (n := n) U) :=
        MarkedIdeal.pullback (Subtype.val : U → Y) (geoTransformAlong M T)
      let O := companionOf n J (nmOrd (geoTransformAlong M T) c)
      let V : Opens Z := ⟨π ⁻¹' (U : Set Y),U.isOpen.preimage hπ.contMDiff.continuous⟩
      let ρ : V → U := fun y => ⟨π y,y.property⟩
      let D : Set U := (Subtype.val : U → Y) ⁻¹' C
      IsInvDomain k O ∧ IsMaximalOrderAlong O.N O.ideal O.d ∧
        ∃ hρ : IsBlowupAlong n D ρ,
          IsGeoTestTower O (BlowupTower.step (X := CMfd.of (n := n) U) (Y := CMfd.of (n := n) U) (Z := CMfd.of (n := n) V) .refl D ρ hρ) ∧
          IsInvDomain k (O.geoTransform D ρ) ∧
          (O.geoTransform D ρ).cosupp=
            ordGe (M := CMfd.of (n := n) V) (J.geoTransform D ρ) (nmOrd (geoTransformAlong M T) c) ∩ (J.geoTransform D ρ).cosupp := by
  exact exists_discrete_positive_same_blowup_companion_test hn (geoTransformAlong M T)
    (InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hT) hC hd hc hq hπ


end
end Hironaka.HironakaOriginalDiscretePositiveCompanion
