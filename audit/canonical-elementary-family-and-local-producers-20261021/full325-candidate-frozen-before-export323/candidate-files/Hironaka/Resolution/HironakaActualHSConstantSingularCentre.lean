/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualCompactIntrinsicHSMaximum
import Hironaka.Resolution.HironakaActualHSSingularOriginalPrefix
import Hironaka.Resolution.HironakaActualBlowupOffCentreIntrinsicHS

/-! Original-only actual all-order HS-constant singular centres, before any exceptional nonincrease claim. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualHSConstantSingularCentre
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaHolomorphicJetChartInvariance AnalyticDimensionBasics
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings SimultaneousNormalCrossings
  BlowupTowers BlowupTowerTransforms ResolutionDriver
  HironakaActualCompactIntrinsicHSMaximum HironakaActualReferenceHSSingularCentre
  HironakaActualHSSingularOriginalPrefix HironakaActualBlowupOffCentreIntrinsicHS
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ}

/-- ONLY original nonsmooth pure geometry internally chooses a genuine singular whole-HS maximum and ENTIRE constant locus. -/
theorem exists_actual_original_singular_constant_maximal_hs_locus {X : CMfd.{u} n} {W : Set X}
    (hW : IsComplexAnalyticSubset (n := n) W) (hK : IsCompact W) {d : ℕ} (hd : d < n)
    (hpure : IsPureDim (n := n) W d) (hns : ¬ IsClosedSubmanifold n W) :
    ∃ a ∈ W \ regularLocus (n := n) W d,
      (∀ x ∈ W \ regularLocus (n := n) W d, ¬ Pi.Lex (· < ·) (· < ·)
        (hilbertSamuelAt (vanishingIdeal (n := n) W) a) (hilbertSamuelAt (vanishingIdeal (n := n) W) x)) ∧
      (actualReferenceHSLocus (vanishingIdeal (n := n) W) a).Nonempty ∧
      IsComplexAnalyticSubset (n := n) (actualReferenceHSLocus (vanishingIdeal (n := n) W) a) ∧
      IsCompact (actualReferenceHSLocus (vanishingIdeal (n := n) W) a) ∧
      actualReferenceHSLocus (vanishingIdeal (n := n) W) a ⊆ W \ regularLocus (n := n) W d ∧
      ∀ x ∈ actualReferenceHSLocus (vanishingIdeal (n := n) W) a, ∀ i,
        hilbertSamuelAt (vanishingIdeal (n := n) W) x i =
          hilbertSamuelAt (vanishingIdeal (n := n) W) a i := by
  have hne : (W \ regularLocus (n := n) W d).Nonempty := by
    by_contra hempty
    apply hns
    refine ⟨hW.isClosed,fun x hx => ⟨d,?_⟩⟩
    by_contra hr
    exact hempty ⟨x,hx,hr⟩
  have hs := isComplexAnalyticSubset_actualCurrentSingular hW hd.le hpure
  have hSk := hK.of_isClosed_subset hs.isClosed sdiff_subset
  obtain ⟨a,ha,hmax,hconst⟩ := exists_actual_original_compact_hs_maximum
    (vanishingIdeal (n := n) W) (CartanIrreducible.cartanCoherence W hW) hSk hne
  obtain ⟨hneA,haA,hkA,hsub⟩ := actualReferenceHSLocus_current_geometry hW hK hd.le hpure ha
  exact ⟨a,ha,hmax,hneA,haA,hkA,hsub,fun x hx => (hconst x (hsub hx)).mp hx⟩

/-- The SAME auxiliary canonical centre is genuinely NC with EVERY original member and has EVERY original HS order constant. -/
theorem exists_actual_original_hs_constant_singular_auxiliary_canonical_centre
    {X : CMfd.{u} n} {W : Set X}
    (hW : IsComplexAnalyticSubset (n := n) W) (hK : IsCompact W) {d : ℕ} (hd : d < n)
    (hpure : IsPureDim (n := n) W d) (hns : ¬ IsClosedSubmanifold n W)
    {E : List (Set X)} (hE : IsSNCDivisor n E) :
    ∃ (a : X) (C : Set X), a ∈ W \ regularLocus (n := n) W d ∧ C.Nonempty ∧
      C ⊆ actualReferenceHSLocus (vanishingIdeal (n := n) W) a ∧
      C ⊆ W \ regularLocus (n := n) W d ∧
      (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X).IsAdmissibleCentre C ∧
      (∀ x ∈ C, ∀ i, hilbertSamuelAt (vanishingIdeal (n := n) W) x i =
        hilbertSamuelAt (vanishingIdeal (n := n) W) a i) ∧
      C = maxLocus ((CanonicalCentres.canonicalInvariant n).inv
        (actualReferenceHSMarked (n := n) W E a) (.refl : BlowupTower X X))
        (actualReferenceHSMarked (n := n) W E a).cosupp := by
  obtain ⟨a,ha,_hmax,hneA,_haA,hkA,hsub,hconst⟩ :=
    exists_actual_original_singular_constant_maximal_hs_locus hW hK hd hpure hns
  let M := actualReferenceHSMarked (n := n) W E a
  let R := CanonicalCentres.canonicalInvariant.{u} n
  have hdom : IsInvDomain n M := actualReferenceHSMarked_isInvDomain hW hd hpure hE ha
  have hcos : M.cosupp = actualReferenceHSLocus (vanishingIdeal (n := n) W) a :=
    actualReferenceHSMarked_cosupp hW E a
  have husc := R.isInvValue.usc M hdom (.refl : BlowupTower X X) trivial
  rw [geoTransformAlong_refl] at husc
  obtain ⟨c,hc,hmax⟩ := husc.exists_isMaxOn (hcos.symm ▸ hkA) (hcos.symm ▸ hneA)
  let C := maxLocus (R.inv M (.refl : BlowupTower X X)) M.cosupp
  have hadm := R.isInvValue.isAdmissibleCentre_maxLocus hdom (.refl : BlowupTower X X) trivial trivial
  rw [geoTransformAlong_refl] at hadm
  have hCA : C ⊆ actualReferenceHSLocus (vanishingIdeal (n := n) W) a := hcos ▸ hadm.2.1
  have hCS := hCA.trans hsub
  have hemb : (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X).IsAdmissibleCentre C := by
    refine ⟨hadm.1,?_,hadm.2.2⟩
    rw [HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal hW.isClosed E]
    exact fun _ hx => (hCS hx).1
  exact ⟨a,C,ha,⟨c,hc,hmax⟩,hCA,hCS,hemb,(fun x hx => hconst x (hCA hx)),rfl⟩

/-- That SAME real original HS-constant singular centre has a genuine proper blowup, full regular-open inverse and actual HS complement comparison. -/
theorem exists_actual_original_hs_constant_singular_centre_proper_blowup
    {X : CMfd.{u} n} {W : Set X}
    (hW : IsComplexAnalyticSubset (n := n) W) (hK : IsCompact W) {d : ℕ} (hd : d < n)
    (hpure : IsPureDim (n := n) W d) (hns : ¬ IsClosedSubmanifold n W)
    {E : List (Set X)} (hE : IsSNCDivisor n E) :
    ∃ (a : X) (C : Set X) (Y : CMfd.{u} n) (π : Y → X),
      a ∈ W \ regularLocus (n := n) W d ∧ C.Nonempty ∧
      C ⊆ W \ regularLocus (n := n) W d ∧
      (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X).IsAdmissibleCentre C ∧
      (∀ x ∈ C, ∀ i, hilbertSamuelAt (vanishingIdeal (n := n) W) x i =
        hilbertSamuelAt (vanishingIdeal (n := n) W) a i) ∧
      IsBlowupAlong n C π ∧ IsProperMap π ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π ∧
      IsIsomorphismOver n π (W \ regularLocus (n := n) W d)ᶜ ∧
      IsSNCDivisor n (E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]) ∧
      (∀ y : Y, π y ∉ C → ∀ i,
        hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n π W)) y i =
          hilbertSamuelAt (vanishingIdeal (n := n) W) (π y) i) ∧
      C = maxLocus ((CanonicalCentres.canonicalInvariant n).inv
        (actualReferenceHSMarked (n := n) W E a) (.refl : BlowupTower X X))
        (actualReferenceHSMarked (n := n) W E a).cosupp := by
  obtain ⟨a,C,ha,hCne,_hCA,hCS,hCadm,hconst,hCeq⟩ :=
    exists_actual_original_hs_constant_singular_auxiliary_canonical_centre hW hK hd hpure hns hE
  have hint : interior C = ∅ := eq_empty_of_subset_empty
    ((interior_mono (fun _ hx => (hCS hx).1)).trans (currentPure_interior_empty hd hpure).subset)
  obtain ⟨Y,π,hπ⟩ := ResolutionDriver.exists_blowup C hCadm.1 hint
  have hGsub : (W \ regularLocus (n := n) W d)ᶜ ⊆ Cᶜ :=
    fun _ hx hC => hx (hCS hC)
  have hisoC := BlowupIsomorphismOff.isIsomorphismOver_compl_of_isBlowupAlong hπ
  have hiso : IsIsomorphismOver n π (W \ regularLocus (n := n) W d)ᶜ := by
    refine ⟨⟨fun _ hz => hz,?_,?_⟩,hisoC.2.mono_left (preimage_mono hGsub)⟩
    · exact hisoC.1.2.1.mono (preimage_mono hGsub)
    · intro x hx
      obtain ⟨y,_hy,hπy⟩ := hisoC.1.2.2 (hGsub hx)
      exact ⟨y,by change π y ∈ (W \ regularLocus (n := n) W d)ᶜ; rwa [hπy],hπy⟩
  have hMwell : (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X).IsWellFormed :=
    ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ,CartanIrreducible.cartanCoherence W hW,
      hE,isTransverse_univ_of_isSNCDivisor hE⟩
  have hE' := (GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre
    hMwell hCadm hπ).isSNCDivisor
  exact ⟨a,C,Y,π,ha,hCne,hCS,hCadm,hconst,hπ,
    HironakaLocalPrincipalization.isProperMap_of_isBlowupAlong hπ,hπ.contMDiff,hiso,hE',
    fun y hy i => hilbertSamuelAt_actual_strict_blowup_off_centre hπ hW y hy i,hCeq⟩

end
end Hironaka.HironakaActualHSConstantSingularCentre
