import Hironaka.Resolution.HironakaG8CaseTAmbientStageOrder
import Hironaka.Resolution.HironakaG8CaseTActualAmbient

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8CaseTActualHistory

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.MarkedIdealBiholomorphism Hironaka.MarkedIdealRestrictOpen
  Hironaka.DivisorExponentAlong Hironaka.HomogenizedIdealAlong
  Hironaka.MarkedIdealOperationsAlong
  Hironaka.MarkedIdealOperationsAlong.MarkedIdeal
  Hironaka.ContactEquivalenceAlong Hironaka.TangentDirectionAlong
  Hironaka.NormalCrossings Hironaka.GermIdealOrder
  Hironaka.StepOneValue Hironaka.HironakaG11InvBMMask
  Hironaka.HironakaG11InvBMLower Hironaka.HironakaG11InvBMStage
  Hironaka.HironakaG8LocalHistory Hironaka.HironakaG8LocalContact
  Hironaka.HironakaG8DomainExponents Hironaka.CoefficientIdealRestriction
  Hironaka.CoefficientIdealAlongRestrictionTower Hironaka.RestrictedIdealWeight
  Hironaka.BlowupStrictSubmanifold
open Hironaka.HironakaStepOneZeroContactRemainderGlueing (isNonzeroAlongAt_pullback_val_iff)
open Hironaka.MarkedIdealEquivalence.MarkedIdeal (WEquiv)
open Hironaka.ResolutionInvariantSpec (IsInvDomain)
open Hironaka.HironakaG11InvBMClass (SameCarrierDim ExpAgree)
open Hironaka.HironakaG8MixedEquiv (isAdmissibleCentre_congr)
open Hironaka.HironakaG8ClassStep (LowerPairs)
open Hironaka.RestrictedIdealExtension (sumIdeal)
open Hironaka.HironakaG8ClassStepResidual (LowerExpResidual)

noncomputable section

universe u

variable {n : ℕ}


open HironakaG8ClassStepHistory HironakaG8CaseTAmbientStageOrder HironakaG8CaseTActualAmbient

variable {X : CMfd.{0} n}

private theorem contact_facts {𝔍 : MarkedIdeal n X} (h𝔍 : 𝔍.IsWellFormed) {U : Set X} {w : X → ℂ}
    (hw : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U w) (W : Opens X) (hWU : (W : Set X) ⊆ U) :
    (MarkedIdeal.pullback (Subtype.val : W → X) (withN (coeffEmptyBM 𝔍) (𝔍.N ∩ {x | w x = 0}))).IsWellFormed ∧
      ∀ x ∈ (Subtype.val : W → X) ⁻¹' (𝔍.N ∩ {y | w y = 0}), ∃ k,
        RegularAtDim (n := n) ((Subtype.val : W → X) ⁻¹' 𝔍.N) x k ∧
        RegularAtDim (n := n) ((Subtype.val : W → X) ⁻¹' (𝔍.N ∩ {y | w y = 0})) x (k - 1) := by
  have hN := h𝔍.isClosedSubmanifold_N
  have h𝔞 := h𝔍.isCoherent
  have hhol := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent h𝔞
  have hval : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val : W → X) := contMDiff_subtype_val
  have hwW := IsTangentDirectionAlong.mono_open hw W.isOpen hWU
  have hNU : IsClosedSubmanifold n (MarkedIdeal.pullback (Subtype.val : W → X) (emptyBoundary 𝔍)).N :=
    BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN W
  have hcU : (MarkedIdeal.pullback (Subtype.val : W → X) (emptyBoundary 𝔍)).ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback hval h𝔞
  have hwU := isTangentDirectionAlong_pullback_val W hhol hwW
  have h1 := isClosedSubmanifold_contact_along (X := CMfd.of (n := n) W)
    (𝔪 := MarkedIdeal.pullback (Subtype.val : W → X) (emptyBoundary 𝔍)) hNU hcU hwU
  rw [preimage_val_contact_eq W] at h1
  have hwfc := isWellFormed_coeffEmptyBM h𝔍
  have hcohA := GermIdealPullbackCalculus.isCoherent_pullback hval hwfc.isCoherent
  refine ⟨⟨h1, hcohA, isSNCDivisor_nil, isTransverse_nil_of_isClosedSubmanifold h1⟩, fun x hx => ?_⟩
  have hx' : x ∈ (MarkedIdeal.pullback (Subtype.val : W → X) (emptyBoundary 𝔍)).N ∩
      {x : W | (w ∘ Subtype.val) x = 0} ∩ univ := by
    rw [preimage_val_contact_eq W]; exact hx
  obtain ⟨k, hk, hk'⟩ := IsTangentDirectionAlong.regularAtDim_contact
    (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcU) hNU hwU hx'
  rw [preimage_val_contact_eq W] at hk'
  exact ⟨k, hk, hk'⟩


/-- The actual transformed contact coefficient ideals have the same born
exponents below their marks, without assuming a universal order-comparison
principle. This specializes the history proof to its actual ambient carriers. -/
theorem expAgreeBelowAt_contactCoeffBM_actual
    {k k' : ℕ} {A B : MarkedIdeal n X}
    (hA : IsInvDomain k A) (hB : IsInvDomain k' B) (h : LocWPEquiv A B) (hd : A.d = B.d) (hE : A.E = B.E)
    (hdim : SameCarrierDim A B) {UA UB : Set X} {uA uB : X → ℂ}
    (huA : IsTangentDirectionAlong A.N A.ideal A.d UA uA) (huB : IsTangentDirectionAlong B.N B.ideal B.d UB uB)
    (W : Opens X) (hWA : (W : Set X) ⊆ UA) (hWB : (W : Set X) ⊆ UB) {Y₀ : CMfd.{0} n} (T₀ : BlowupTower X Y₀)
    (hTA : IsGeoTestTower A T₀) {p : Y₀} (hpW : p ∈ openPreimage T₀ W)
    (hpA : IsNonzeroAlongAt (contactCoeffBM A uA T₀).N (contactCoeffBM A uA T₀).ideal p)
    (hpB : IsNonzeroAlongAt (contactCoeffBM B uB T₀).N (contactCoeffBM B uB T₀).ideal p) :
    ExpAgreeBelowAt (contactCoeffBM A uA T₀) (contactCoeffBM B uB T₀) p := by
  have hTB : IsGeoTestTower B T₀ := ((LocEquiv.wEquiv h).2 T₀).1.mp hTA
  have hwAW : IsTangentDirectionAlong A.N A.ideal A.d (W : Set X) uA := IsTangentDirectionAlong.mono_open huA W.isOpen hWA
  have hwBW : IsTangentDirectionAlong B.N B.ideal B.d (W : Set X) uB := IsTangentDirectionAlong.mono_open huB W.isOpen hWB
  obtain ⟨hwfP, hregA⟩ := contact_facts hA.isWellFormed huA W hWA
  obtain ⟨hwfQ, hregB⟩ := contact_facts hB.isWellFormed huB W hWB
  set P := MarkedIdeal.pullback (Subtype.val : W → X) (withN (coeffEmptyBM A) (A.N ∩ {x | uA x = 0})) with hPdef
  set Q := MarkedIdeal.pullback (Subtype.val : W → X) (withN (coeffEmptyBM B) (B.N ∩ {x | uB x = 0})) with hQdef
  set F := (MarkedIdeal.pullback (Subtype.val : W → X) A).E with hFdef
  -- `𝒞_W(A_∅) ≈ A_∅|_W`, `𝒞_W(B_∅) ≈ B_∅|_W`, then add the original members
  have hcA : LocWPEquiv (X := CMfd.of (n := n) W) (MarkedIdeal.pullback (Subtype.val : W → X) (emptyBoundary A)) P :=
    locWPEquiv_contact_open_along (emptyBoundary A) hA.isWellFormed.isClosedSubmanifold_N hA.isWellFormed.isCoherent
      hA.one_le_d W hwAW
  have hcB : LocWPEquiv (X := CMfd.of (n := n) W) (MarkedIdeal.pullback (Subtype.val : W → X) (emptyBoundary B)) Q :=
    locWPEquiv_contact_open_along (emptyBoundary B) hB.isWellFormed.isClosedSubmanifold_N hB.isWellFormed.isCoherent
      hB.one_le_d W hwBW
  have hcAF := HironakaG8ClassStepCut.locEquiv_addE rfl hcA F
  have hcBF := HironakaG8ClassStepCut.locEquiv_addE rfl hcB F
  have hAW : ({ MarkedIdeal.pullback (Subtype.val : W → X) (emptyBoundary A) with
      E := F ++ (MarkedIdeal.pullback (Subtype.val : W → X) (emptyBoundary A)).E } : MarkedIdeal n W) =
      MarkedIdeal.pullback (Subtype.val : W → X) A := by
    show ({ MarkedIdeal.pullback (Subtype.val : W → X) (emptyBoundary A) with E := F ++ [] } : MarkedIdeal n W) = _
    rw [List.append_nil]
    rfl
  have hBW : ({ MarkedIdeal.pullback (Subtype.val : W → X) (emptyBoundary B) with
      E := F ++ (MarkedIdeal.pullback (Subtype.val : W → X) (emptyBoundary B)).E } : MarkedIdeal n W) =
      MarkedIdeal.pullback (Subtype.val : W → X) B := by
    show ({ MarkedIdeal.pullback (Subtype.val : W → X) (emptyBoundary B) with E := F ++ [] } : MarkedIdeal n W) = _
    rw [List.append_nil, hFdef]
    show ({ MarkedIdeal.pullback (Subtype.val : W → X) (emptyBoundary B) with E := A.E.map _ } : MarkedIdeal n W) = _
    rw [hE]
    rfl
  rw [hAW] at hcAF
  rw [hBW] at hcBF
  have hrest := LocEquiv.restrict h W
  have hL : LocWPEquiv (X := CMfd.of (n := n) W) { P with E := F ++ P.E } { Q with E := F ++ P.E } :=
    hcAF.symm.trans (hrest.trans hcBF)
  -- the data of the base pair
  have hsnc : IsSNCDivisor n (F ++ P.E) := by
    show IsSNCDivisor n (F ++ [])
    rw [List.append_nil]
    exact (IsWellFormed.pullback_val hA.isWellFormed W).isSNCDivisor
  have hdP : 1 ≤ P.d := ContactIndependenceAlong.one_le_coeffMarkedAlong_d (emptyBoundary A)
  have hdd : Q.d = P.d := by
    show (coeffEmptyBM B).d = (coeffEmptyBM A).d
    rw [coeffEmptyBM_d, coeffEmptyBM_d, hd]
  have hEQ : Q.E = P.E := rfl
  have hcosPQ : P.cosupp = Q.cosupp := hL.cosupp_eq_base
  have hdimPQ : SameCarrierDim (X := CMfd.of (n := n) W) P Q := by
    intro x hx j
    have hxA0 : x ∈ (MarkedIdeal.pullback (Subtype.val : W → X) (emptyBoundary A)).cosupp := hcA.cosupp_eq_base ▸ hx
    have hxA : (x : X) ∈ A.cosupp := by
      have h1 := cosupp_pullback_val (emptyBoundary A)
        (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hA.isWellFormed.isCoherent) W
      rw [h1] at hxA0
      exact hxA0
    have hxB := hcosPQ ▸ hx
    obtain ⟨kA, hkA, hkSA⟩ := hregA x (MarkedIdeal.cosupp_subset_N _ hx)
    obtain ⟨kB, hkB, hkSB⟩ := hregB x (MarkedIdeal.cosupp_subset_N _ hxB)
    have hkA' : RegularAtDim (n := n) A.N (x : X) kA := AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mp hkA
    have hkB' : RegularAtDim (n := n) B.N (x : X) kB := AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mp hkB
    have hkk : kA = kB := RegularPointDimension.eq_of_regularAtDim ((hdim (x : X) hxA kA).mp hkA') hkB'
    show RegularAtDim (n := n) ((Subtype.val : W → X) ⁻¹' (A.N ∩ {y | uA y = 0})) x j ↔
      RegularAtDim (n := n) ((Subtype.val : W → X) ⁻¹' (B.N ∩ {y | uB y = 0})) x j
    constructor
    · intro hj
      rw [← RegularPointDimension.eq_of_regularAtDim hkSA hj, hkk]; exact hkSB
    · intro hj
      rw [← RegularPointDimension.eq_of_regularAtDim hkSB hj, ← hkk]; exact hkSA
  have hgeomA := actual_contact_ambient A hA.isWellFormed hA.one_le_d W hwAW
    (BlowupTower.refl : BlowupTower X X) (by simp [IsGeoTestTower])
  have hgeomB := actual_contact_ambient B hB.isWellFormed hB.one_le_d W hwBW
    (BlowupTower.refl : BlowupTower X X) (by simp [IsGeoTestTower])
  change P.IsWellFormed ∧ (MarkedIdeal.pullback (Subtype.val : W → X) A).IsWellFormed ∧
    P.N ⊆ (MarkedIdeal.pullback (Subtype.val : W → X) A).N ∧
    (∀ x ∈ P.N, ∃ m, RegularAtDim (n := n) (MarkedIdeal.pullback (Subtype.val : W → X) A).N x (m+1) ∧
      RegularAtDim (n := n) P.N x m) at hgeomA
  change Q.IsWellFormed ∧ (MarkedIdeal.pullback (Subtype.val : W → X) B).IsWellFormed ∧
    Q.N ⊆ (MarkedIdeal.pullback (Subtype.val : W → X) B).N ∧
    (∀ x ∈ Q.N, ∃ m, RegularAtDim (n := n) (MarkedIdeal.pullback (Subtype.val : W → X) B).N x (m+1) ∧
      RegularAtDim (n := n) Q.N x m) at hgeomB
  -- the restricted tower
  obtain ⟨-, hRE⟩ := restrictEquiv_stage_contactCoeffBM hA.isWellFormed hA.one_le_d W hwAW T₀ hTA
  obtain ⟨-, hRE'⟩ := restrictEquiv_stage_contactCoeffBM hB.isWellFormed hB.one_le_d W hwBW T₀ hTB
  have hTF : IsGeoTestTower (X := CMfd.of (n := n) W) { P with E := F ++ P.E } (restrict W T₀) :=
    (hcAF.wEquiv.2 _).1.mp (isGeoTestTower_restrict W hA.isWellFormed.isClosedSubmanifold_N hA.isWellFormed.isCoherent
      T₀ hTA)
  -- coherence of the two transformed coefficient ideals
  have hTc := HironakaG11InvBMStage.isGeoTestTower_coeffEmptyBM hA.isWellFormed hA.one_le_d _
    (HironakaG11InvBMStage.isGeoTestTower_emptyBoundary A _ hTA)
  have hTcB := HironakaG11InvBMStage.isGeoTestTower_coeffEmptyBM hB.isWellFormed hB.one_le_d _
    (HironakaG11InvBMStage.isGeoTestTower_emptyBoundary B _ hTB)
  have hwfc := isWellFormed_coeffEmptyBM hA.isWellFormed
  have hwfcB := isWellFormed_coeffEmptyBM hB.isWellFormed
  obtain ⟨-, hcL⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hwfc.isClosedSubmanifold_N hwfc.isCoherent
    T₀ hTc
  obtain ⟨-, hcL'⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hwfcB.isClosedSubmanifold_N
    hwfcB.isCoherent T₀ hTcB
  have hholL : ∀ x g, (contactCoeffBM A uA T₀).ideal.mem x g → HolomorphicAt n g x := hol_of_isCoherent hcL
  have hholL' : ∀ x g, (contactCoeffBM B uB T₀).ideal.mem x g → HolomorphicAt n g x := hol_of_isCoherent hcL'
  -- localize at `p`
  rw [← expAgreeBelowAt_pullback_val_iff hholL hholL' (openPreimage T₀ W) ⟨p, hpW⟩]
  intro H hH hy hyH
  have hyA := hRE.cosupp_eq ▸ hy
  have hyAN := MarkedIdeal.cosupp_subset_N _ hyA
  have hcosT : (geoTransformAlong (X := CMfd.of (n := n) W) P (restrict W T₀)).cosupp =
      (geoTransformAlong (X := CMfd.of (n := n) W) Q (restrict W T₀)).cosupp := by
    rw [← cosupp_geoTransformAlong_addE (X := CMfd.of (n := n) W) P F, (hL.wEquiv.2 _).2 hTF]
    exact cosupp_geoTransformAlong_addE (X := CMfd.of (n := n) W) Q F _
  have hyBN := MarkedIdeal.cosupp_subset_N _ (hcosT ▸ hyA)
  have nzA := (isNonzeroAlongAt_iff_of_restrictEquiv hRE hyAN).mpr
    ((isNonzeroAlongAt_pullback_val_iff hcL (openPreimage T₀ W) ⟨p, hpW⟩).mpr hpA)
  have nzB := (isNonzeroAlongAt_iff_of_restrictEquiv hRE' hyBN).mpr
    ((isNonzeroAlongAt_pullback_val_iff hcL' (openPreimage T₀ W) ⟨p, hpW⟩).mpr hpB)
  have hstagegeom := actual_contact_ambient A hA.isWellFormed hA.one_le_d W hwAW T₀ hTA
  have hstageN : (⟨p, hpW⟩ : openPreimage T₀ W) ∈
      (MarkedIdeal.pullback (Subtype.val : openPreimage T₀ W → Y₀) (contactCoeffBM A uA T₀)).N :=
    MarkedIdeal.cosupp_subset_N _ hy
  obtain ⟨m, hm, _⟩ := hstagegeom.2.2.2 _ hstageN
  have hn : 0 < n := by have := hm.1; omega
  have hkey := expAgreeBelowAt_geoTransformAlong_of_addE (X := CMfd.of (n := n) W) F hwfP hwfQ hdP hdd hEQ hL.wEquiv
    (fun T hT y hy hyP hyQ => ordAgreeBelowAt_stage_of_ambient_carriers hn P Q
      (MarkedIdeal.pullback (Subtype.val : W → X) A) (MarkedIdeal.pullback (Subtype.val : W → X) B)
      F hwfP hwfQ hgeomA.2.1 hgeomB.2.1 hgeomA.2.2.1 hgeomB.2.2.1 hcAF.symm hcBF.symm
      hgeomA.2.2.2 hgeomB.2.2.2 hdP hdd hEQ hL hsnc hdimPQ T hT y hy hyP hyQ)
    (fun x _ _ _ H hH => absurd hH List.not_mem_nil) (restrict W T₀) hTF _ hyA nzA nzB
  exact expAgreeBelowAt_of_restrictEquiv hRE hRE' hkey H hH hy hyH


end
end Hironaka.HironakaG8CaseTActualHistory
