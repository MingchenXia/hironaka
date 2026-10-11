/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Coherence.GeneralCoherentIdealColon
import Hironaka.Invariant.StepOneBarMarkedCarrierBoundary
import Hironaka.Resolution.HironakaCurveAnalyticPredicates
import Hironaka.Coherence.CoherentIdealColon

set_option autoImplicit false

/-!
# True coherent controlled transforms across actual order-mask boundaries

General coherent colon internally removes the restricted-inclusion requirement
for actual controlled ideal coherence. Actual smooth carrier geometry and real
strict-transform accumulation preserve nonzero along without candidate-testness.
The globally formed actual companion and homogenized coefficient companion
remain in the genuine invariant domain along the original true tail. Exact
marked-ideal equalities identify their mask pullbacks with the literal restricted
transforms used by the actual invariant. Global maximal order and General2
threshold descent are not asserted.
Blueprint: `hironaka-coherent-transform-extension.tex`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaCoherentTransformExtension

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  RestrictedIdealExtension RestrictedIdealQuotient GermIdealPullbackCalculus
  DivisorExponentAlong GermIdealOrder MarkedIdealRestrictOpen
  BlowupStrictSubmanifold MarkedIdealBiholomorphism

open Hironaka
noncomputable section

universe u
variable {n : ℕ}

section Ambient

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The actual colonAlong is coherent by the actual general coherent-colon
producer, without a restricted-inclusion or invertible-quotient hypothesis. -/
theorem isCoherent_colonAlong_without_inclusion {N : Set M} {I L : GermIdeal n M}
    (hI : I.IsCoherent) (hN : (vanishingIdeal (n := n) N).IsCoherent) (hL : L.IsCoherent) :
    (colonAlong n N I L).IsCoherent :=
  CoherentIdealColon.isCoherent_colon_of_isCoherent (isCoherent_restrictOn hI hN) hL

end Ambient

section Step

variable {X Y : CMfd.{u} n} {C : Set X} {π : Y → X}

/-- Coherence of the actual globally defined controlled ideal follows from
actual smooth carrier and centre geometry, without candidate admissibility. -/
theorem isCoherent_geoTransform_ideal_without_inclusion (𝔪 : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n 𝔪.N) (hI : 𝔪.ideal.IsCoherent)
    (hπ : IsBlowupAlong n C π) (hCN : C ⊆ 𝔪.N) :
    (𝔪.geoTransform C π).ideal.IsCoherent := by
  have hN' := BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ hN hCN
  have hC := BlowupExceptionalDivisor.isCoherent_vanishingIdeal_centre hπ
  exact isCoherent_colonAlong_without_inclusion (isCoherent_pullback hπ.contMDiff hI)
    (VanishingIdealCoherent.isCoherent_vanishingIdeal hN')
    (isCoherent_idealPow (isCoherent_pullback hπ.contMDiff hC) 𝔪.d)

/-- Actual coherence and genuine accumulation from outside the literal
centre internally preserve the nonzero-along property of the actual transform. -/
theorem isNonzeroAlongAt_geoTransform_without_admissibility (𝔪 : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n 𝔪.N) (hI : 𝔪.ideal.IsCoherent)
    (hπ : IsBlowupAlong n C π) (hCN : C ⊆ 𝔪.N)
    (hnz : ∀ x ∈ 𝔪.N, IsNonzeroAlongAt 𝔪.N 𝔪.ideal x) :
    ∀ y ∈ (𝔪.geoTransform C π).N,
      IsNonzeroAlongAt (𝔪.geoTransform C π).N (𝔪.geoTransform C π).ideal y := by
  have hoff : ∀ y ∈ (𝔪.geoTransform C π).N, π y ∉ C →
      IsNonzeroAlongAt (𝔪.geoTransform C π).N (𝔪.geoTransform C π).ideal y := fun y hy hyC =>
    InvDomainTowerAlong.isNonzeroAlongAt_geoTransform_of_notMem hπ 𝔪 hI hyC
      (hnz (π y) (geoStrictTransform_subset_preimage hπ.contMDiff.continuous hN.1 hy))
  intro y hy
  by_cases hyC : π y ∈ C
  · by_contra hcon
    have hcoh := isCoherent_geoTransform_ideal_without_inclusion 𝔪 hN hI hπ hCN
    have hev := CodimOnePartTowerAlong.eventually_forall_eq_zero_of_not_isNonzeroAlongAt hcoh hcon
    have hfreq : ∃ᶠ z in 𝓝 y, z ∈ π ⁻¹' (𝔪.N \ C) := mem_closure_iff_frequently.mp hy
    obtain ⟨z, hz, hzev⟩ := (hfreq.and_eventually hev).exists
    have hzN' : z ∈ (𝔪.geoTransform C π).N := subset_closure hz
    obtain ⟨g, hg, hgfreq⟩ := hoff z hzN' hz.2
    obtain ⟨w, ⟨hwN, hgw⟩, hw⟩ := (hgfreq.and_eventually (hzev g hg)).exists
    exact hgw (hw hwN)
  · exact hoff y hy hyC

end Step

section Tower

variable {X : CMfd.{u} n} {𝔪 𝔍 : MarkedIdeal n X}

/-- Actual transformed carriers depend on the literal geometry and initial
carrier, so candidates with the same initial carrier retain identical carriers. -/
theorem geoTransformAlong_N_eq_of_N_eq (hN : 𝔍.N = 𝔪.N) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      (geoTransformAlong 𝔍 T).N = (geoTransformAlong 𝔪 T).N
  | _, .refl => hN
  | _, .step T C π hπ => by
    change geoStrictTransform π C (geoTransformAlong 𝔍 T).N =
      geoStrictTransform π C (geoTransformAlong 𝔪 T).N
    rw [geoTransformAlong_N_eq_of_N_eq hN T]


/-- Actual boundary transforms also depend only on the literal geometry. -/
theorem geoTransformAlong_E_eq_of_E_eq (hE : 𝔍.E = 𝔪.E) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      (geoTransformAlong 𝔍 T).E = (geoTransformAlong 𝔪 T).E
  | _, .refl => hE
  | _, .step T C π hπ => by
    change (geoTransformAlong 𝔍 T).E.map (geoStrictTransform π C) ++ [π ⁻¹' C] =
      (geoTransformAlong 𝔪 T).E.map (geoStrictTransform π C) ++ [π ⁻¹' C]
    rw [geoTransformAlong_E_eq_of_E_eq hE T]

/-- A genuine actual template test tower supplies carrier geometry for the
candidate's true global controlled ideal, without candidate-test assumptions. -/
theorem isClosedSubmanifold_and_isCoherent_geoTransformAlong_sameCarrier
    (hN : IsClosedSubmanifold n 𝔍.N) (hI : 𝔍.ideal.IsCoherent) (hEq : 𝔍.N = 𝔪.N) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower 𝔪 T →
      IsClosedSubmanifold n (geoTransformAlong 𝔍 T).N ∧
        (geoTransformAlong 𝔍 T).ideal.IsCoherent
  | _, .refl, _ => ⟨hN, hI⟩
  | _, .step T C π hπ, hT => by
    obtain ⟨hTT, hC⟩ := hT
    obtain ⟨hNT, hIT⟩ := isClosedSubmanifold_and_isCoherent_geoTransformAlong_sameCarrier hN hI hEq T hTT
    have hCN : C ⊆ (geoTransformAlong 𝔍 T).N := by
      rw [geoTransformAlong_N_eq_of_N_eq hEq T]
      exact hC.subset_N
    exact ⟨BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ hNT hCN,
      isCoherent_geoTransform_ideal_without_inclusion _ hNT hIT hπ hCN⟩

/-- The actual candidate's true global controlled ideal remains nonzero
along the genuine common strict carrier at every literal tower stage. -/
theorem isNonzeroAlongAt_geoTransformAlong_sameCarrier
    (hN : IsClosedSubmanifold n 𝔍.N) (hI : 𝔍.ideal.IsCoherent) (hEq : 𝔍.N = 𝔪.N)
    (hnz : ∀ x ∈ 𝔍.N, IsNonzeroAlongAt 𝔍.N 𝔍.ideal x) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower 𝔪 T →
      ∀ y ∈ (geoTransformAlong 𝔍 T).N,
        IsNonzeroAlongAt (geoTransformAlong 𝔍 T).N (geoTransformAlong 𝔍 T).ideal y
  | _, .refl, _ => hnz
  | _, .step T C π hπ, hT => by
    obtain ⟨hTT, hC⟩ := hT
    obtain ⟨hNT, hIT⟩ := isClosedSubmanifold_and_isCoherent_geoTransformAlong_sameCarrier hN hI hEq T hTT
    have hCN : C ⊆ (geoTransformAlong 𝔍 T).N := by
      rw [geoTransformAlong_N_eq_of_N_eq hEq T]
      exact hC.subset_N
    exact isNonzeroAlongAt_geoTransform_without_admissibility _ hNT hIT hπ hCN
      (isNonzeroAlongAt_geoTransformAlong_sameCarrier hN hI hEq hnz T hTT)

/-- The actual entire candidate controlled transform restricts exactly,
with its true ideal, carrier, boundary and mark, along the literal open tower. -/
theorem geoTransformAlong_restrict_sameCarrier
    (hN : IsClosedSubmanifold n 𝔍.N) (hI : 𝔍.ideal.IsCoherent) (hEq : 𝔍.N = 𝔪.N)
    (U : TopologicalSpace.Opens X) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower 𝔪 T →
      geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) (restrict U T) =
        MarkedIdeal.pullback (Subtype.val : openPreimage T U → Y) (geoTransformAlong 𝔍 T)
  | _, .refl, _ => rfl
  | _, .step T C π hπ, hT => by
    obtain ⟨hTT, hC⟩ := hT
    obtain ⟨hNT, hIT⟩ := isClosedSubmanifold_and_isCoherent_geoTransformAlong_sameCarrier hN hI hEq T hTT
    have hCN : C ⊆ (geoTransformAlong 𝔍 T).N := by
      rw [geoTransformAlong_N_eq_of_N_eq hEq T]
      exact hC.subset_N
    have ih := geoTransformAlong_restrict_sameCarrier hN hI hEq U T hTT
    change (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) (restrict U T)).geoTransform
      ((↑) ⁻¹' C : Set (openPreimage T U)) _ = _
    rw [ih]
    exact geoTransform_pullback_val hIT hπ
      (isCoherent_geoTransform_ideal_without_inclusion _ hNT hIT hπ hCN)
      (openPreimage T U) _



/-- The actual common carrier and boundary supply all genuine domain fields
for the candidate's entire transform; candidate-testness is unnecessary. -/
theorem isInvDomain_geoTransformAlong_sameCarrier {k : ℕ}
    (hJ : ResolutionInvariantSpec.IsInvDomain k 𝔍) (hm : 𝔪.IsWellFormed)
    (hN : 𝔍.N = 𝔪.N) (hE : 𝔍.E = 𝔪.E)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) :
    ResolutionInvariantSpec.IsInvDomain k (geoTransformAlong 𝔍 T) := by
  obtain ⟨hNT, hIT⟩ := isClosedSubmanifold_and_isCoherent_geoTransformAlong_sameCarrier
    hJ.isWellFormed.isClosedSubmanifold_N hJ.isWellFormed.isCoherent hN T hT
  have hNm : ResolutionInvariantSpec.DimLE n 𝔪.N k := by
    rw [← hN]
    exact hJ.dimLE
  have hNTeq := geoTransformAlong_N_eq_of_N_eq hN T
  have hETeq := geoTransformAlong_E_eq_of_E_eq hE T
  have hwfT := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hm T hT
  refine ⟨⟨hNT, hIT, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hETeq]
    exact hwfT.isSNCDivisor
  · rw [hNTeq, hETeq]
    exact hwfT.isTransverse
  · rw [hNTeq]
    exact InvDomainTowerAlong.dimLE_geoTransformAlong hm.isClosedSubmanifold_N hm.isCoherent hNm T hT
  · rw [d_geoTransformAlong]
    exact hJ.one_le_d
  · exact isNonzeroAlongAt_geoTransformAlong_sameCarrier hJ.isWellFormed.isClosedSubmanifold_N
      hJ.isWellFormed.isCoherent hN hJ.isNonzeroAlongAt T hT

end Tower

section ActualCompanion

open CompanionRebase CompanionReductionAlong InvDomainCompanion GeneralValue
  StepOneValue StepOneLowerDomain HomogenizedIdealAlong ContactStageKept
  IdealWeightPowers
variable {k : ℕ} {X Y₀ Y : CMfd.{u} n}


/-- The actual index-zero coefficient summand contains a genuine power of
an original nonzero germ, internally preserving nonzero along the carrier. -/
theorem isNonzeroAlongAt_barMarked (𝔍 : MarkedIdeal n X) (hI : 𝔍.ideal.IsCoherent)
    (hd : 1 ≤ 𝔍.d) (hnz : ∀ x ∈ 𝔍.N, IsNonzeroAlongAt 𝔍.N 𝔍.ideal x) :
    ∀ x ∈ (barMarked 𝔍).N, IsNonzeroAlongAt (barMarked 𝔍).N (barMarked 𝔍).ideal x := by
  intro x hx
  obtain ⟨g, hg, hfreq⟩ := hnz x hx
  have hhol : ∀ y f, 𝔍.ideal.mem y f → HolomorphicAt n f y :=
    fun _ _ hf => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hf
  let H := homMarkedAlong 𝔍
  have hgH : H.ideal.mem x g := le_homogenizedIdealAlong hhol hd x g hg
  let e := CoefficientIdeal.sumExp (fun j => (derivMarkedAlong H j).d) H.d 0
  have hpow : (idealPow (derivMarkedAlong H 0).ideal e).mem x (fun z => g z ^ e) :=
    OrderMultiplicativity.pow_mem_idealPow hgH (hhol x g hg) e
  have hmem : (barMarked 𝔍).ideal.mem x (fun z => g z ^ e) :=
    (InvertibleIdealQuotient.isInSpanAt_self
      (S := fun f => ∃ i, i < H.d ∧ (idealPow (derivMarkedAlong H i).ideal
        (CoefficientIdeal.sumExp (fun j => (derivMarkedAlong H j).d) H.d i)).mem x f)
      ⟨0, hd, hpow⟩ (holomorphicAt_of_mem_idealPow hpow) : IsInSpanAt (n := n) _ x _)
  exact ⟨fun z => g z ^ e, hmem, hfreq.mono fun z hz => ⟨hz.1, pow_ne_zero e hz.2⟩⟩

/-- Actual coefficient-of-homogenization retains every real domain field. -/
theorem isInvDomain_barMarked (𝔍 : MarkedIdeal n X) (h : ResolutionInvariantSpec.IsInvDomain k 𝔍) :
    ResolutionInvariantSpec.IsInvDomain k (barMarked 𝔍) :=
  ⟨isWellFormed_barMarked 𝔍 h.isWellFormed, h.dimLE,
    ContactIndependenceAlong.one_le_coeffMarkedAlong_d _,
    isNonzeroAlongAt_barMarked 𝔍 h.isWellFormed.isCoherent h.one_le_d h.isNonzeroAlongAt⟩

/-- The actual globally formed companion stays in the genuine invariant
domain along the original true tail, and its exact mask pullback is the
literal transformed companion used by the constructed general value. -/
theorem coherent_nonzero_companion_transform_and_mask_identity (hn : 0 < n)
    (𝔪 : MarkedIdeal n X) (h : ResolutionInvariantSpec.IsInvDomain k 𝔪)
    (o : ℕ) (ho : 1 ≤ o) (T₀ : BlowupTower X Y₀) (hT₀ : IsGeoTestTower 𝔪 T₀)
    (T₁ : BlowupTower Y₀ Y) (hT₁ : IsGeoTestTower (geoTransformAlong 𝔪 T₀) T₁) :
    ResolutionInvariantSpec.IsInvDomain k
        (geoTransformAlong (companionOf n (geoTransformAlong 𝔪 T₀) o) T₁) ∧
      geoTransformAlong (compAt 𝔪 o T₀) (restrict (NonmonomialOrderTail.ordMask (geoTransformAlong 𝔪 T₀) o) T₁) =
        MarkedIdeal.pullback
          (Subtype.val : openPreimage T₁ (NonmonomialOrderTail.ordMask (geoTransformAlong 𝔪 T₀) o) → Y)
          (geoTransformAlong (companionOf n (geoTransformAlong 𝔪 T₀) o) T₁) := by
  have hd₀ := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T₀ hT₀
  have hK := isInvDomain_companionAlong hn hd₀ ho
  have hKN : (companionOf n (geoTransformAlong 𝔪 T₀) o).N = (geoTransformAlong 𝔪 T₀).N := by
    simp only [companionOf, companionAlong_N]
  have hKE : (companionOf n (geoTransformAlong 𝔪 T₀) o).E = (geoTransformAlong 𝔪 T₀).E := by
    simp only [companionOf, companionAlong_E]
  obtain ⟨hNT, hIT⟩ := isClosedSubmanifold_and_isCoherent_geoTransformAlong_sameCarrier
    hK.isWellFormed.isClosedSubmanifold_N hK.isWellFormed.isCoherent hKN T₁ hT₁
  have hNTeq := geoTransformAlong_N_eq_of_N_eq hKN T₁
  have hETeq := geoTransformAlong_E_eq_of_E_eq hKE T₁
  have hdT := InvDomainTowerAlong.isInvDomain_geoTransformAlong hd₀ T₁ hT₁
  refine ⟨⟨⟨hNT, hIT, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
  · rw [hETeq]
    exact hdT.isWellFormed.isSNCDivisor
  · rw [hNTeq, hETeq]
    exact hdT.isWellFormed.isTransverse
  · rw [hNTeq]
    exact hdT.dimLE
  · rw [d_geoTransformAlong]
    exact hK.one_le_d
  · exact isNonzeroAlongAt_geoTransformAlong_sameCarrier hK.isWellFormed.isClosedSubmanifold_N
      hK.isWellFormed.isCoherent hKN hK.isNonzeroAlongAt T₁ hT₁
  · have hmask : compAt 𝔪 o T₀ = MarkedIdeal.pullback
        (Subtype.val : NonmonomialOrderTail.ordMask (geoTransformAlong 𝔪 T₀) o → Y₀)
        (companionOf n (geoTransformAlong 𝔪 T₀) o) :=
      (pullback_val_companionOf hn hd₀.isWellFormed hd₀.isNonzeroAlongAt _ o).symm
    rw [hmask]
    exact geoTransformAlong_restrict_sameCarrier hK.isWellFormed.isClosedSubmanifold_N
      hK.isWellFormed.isCoherent hKN _ T₁ hT₁

/-- The actual entire coefficient-of-homogenized companion ideal is coherent;
its marked-ideal restriction equals the literal masked coefficient transform. -/
theorem coherent_coefficient_transform_and_mask_identity (hn : 0 < n)
    (𝔪 : MarkedIdeal n X) (h : ResolutionInvariantSpec.IsInvDomain k 𝔪)
    (o : ℕ) (ho : 1 ≤ o) (T₀ : BlowupTower X Y₀) (hT₀ : IsGeoTestTower 𝔪 T₀)
    (T₁ : BlowupTower Y₀ Y) (hT₁ : IsGeoTestTower (geoTransformAlong 𝔪 T₀) T₁) :
    ResolutionInvariantSpec.IsInvDomain k
        (geoTransformAlong (barMarked (companionOf n (geoTransformAlong 𝔪 T₀) o)) T₁) ∧
      geoTransformAlong (barMarked (compAt 𝔪 o T₀))
          (restrict (NonmonomialOrderTail.ordMask (geoTransformAlong 𝔪 T₀) o) T₁) =
        MarkedIdeal.pullback
          (Subtype.val : openPreimage T₁ (NonmonomialOrderTail.ordMask (geoTransformAlong 𝔪 T₀) o) → Y)
          (geoTransformAlong (barMarked (companionOf n (geoTransformAlong 𝔪 T₀) o)) T₁) := by
  have hd₀ := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T₀ hT₀
  have hK := isInvDomain_companionAlong hn hd₀ ho
  have hBD := isInvDomain_barMarked _ hK
  have hBN : (barMarked (companionOf n (geoTransformAlong 𝔪 T₀) o)).N =
      (geoTransformAlong 𝔪 T₀).N := by simp only [barMarked_N, companionOf, companionAlong_N]
  have hBE : (barMarked (companionOf n (geoTransformAlong 𝔪 T₀) o)).E =
      (geoTransformAlong 𝔪 T₀).E := by simp only [barMarked_E, companionOf, companionAlong_E]
  refine ⟨isInvDomain_geoTransformAlong_sameCarrier hBD hd₀.isWellFormed hBN hBE T₁ hT₁, ?_⟩
  have hmask : compAt 𝔪 o T₀ = MarkedIdeal.pullback
      (Subtype.val : NonmonomialOrderTail.ordMask (geoTransformAlong 𝔪 T₀) o → Y₀)
      (companionOf n (geoTransformAlong 𝔪 T₀) o) :=
    (pullback_val_companionOf hn hd₀.isWellFormed hd₀.isNonzeroAlongAt _ o).symm
  have hbar : barMarked (X := CMfd.of (n := n) (NonmonomialOrderTail.ordMask (geoTransformAlong 𝔪 T₀) o)) (MarkedIdeal.pullback
      (Subtype.val : NonmonomialOrderTail.ordMask (geoTransformAlong 𝔪 T₀) o → Y₀)
      (companionOf n (geoTransformAlong 𝔪 T₀) o)) =
      MarkedIdeal.pullback
        (Subtype.val : NonmonomialOrderTail.ordMask (geoTransformAlong 𝔪 T₀) o → Y₀)
        (barMarked (X := Y₀) (companionOf n (geoTransformAlong 𝔪 T₀) o)) :=
    barMarked_pullback_val _ hK.isWellFormed.isCoherent hK.isWellFormed.isClosedSubmanifold_N hK.one_le_d
  rw [hmask, hbar]
  exact geoTransformAlong_restrict_sameCarrier hBD.isWellFormed.isClosedSubmanifold_N
    hBD.isWellFormed.isCoherent hBN _ T₁ hT₁

end ActualCompanion
end
end Hironaka.HironakaCoherentTransformExtension
