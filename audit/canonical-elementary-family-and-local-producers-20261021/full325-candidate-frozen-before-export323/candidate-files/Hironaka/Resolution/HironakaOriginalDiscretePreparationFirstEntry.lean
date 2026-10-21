/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalSmoothCurveWholeTupleBadBlowup
/-! Genuine SAME-original first-coordinate comparison after discrete preparation.
No canonical continuation or full higher-history comparison is inferred. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalDiscretePreparationFirstEntry
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms CanonicalCentres
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen BlowupRestrictOpen NonmonomialOrderLocal NonmonomialOrderCanonical
  HironakaOriginalSmoothCurveWholeTupleBadBlowup HironakaOneDimensionalCanonicalSuperlevels
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n : ℕ} {X Y Z : CMfd.{u} n}

private theorem generic_actual_constant_order_bound (hn : 0<n) {k : ℕ}
    (m : MarkedIdeal n X) (h : IsInvDomain k m) {C : Set X} (hC : m.IsAdmissibleCentre C)
    {π : Y → X} (hπ : IsBlowupAlong n C π) (q : ℕ)
    (hlevel : ∀ c ∈ C,nmOrd m c=q) (z : Y) (hz : z ∈ (m.geoTransform C π).cosupp)
    (hzC : π z ∈ C) : nmOrd (m.geoTransform C π) z≤q :=
  nmOrd_geoTransform_le_of_level hn (Y := X) (Z := Y) (𝔫 := m) h hC hπ hlevel hz hzC

private theorem nmOrd_actual_order_window_bound (hn : 0<n) {k : ℕ}
    (m : MarkedIdeal n X) (h : IsInvDomain k m) {C : Set X} (hC : m.IsAdmissibleCentre C)
    {π : Y → X} (hπ : IsBlowupAlong n C π) (z : Y) (hz : z ∈ (m.geoTransform C π).cosupp)
    (hzC : π z ∈ C) (q : ℕ) (O : Opens X) (hcO : π z ∈ O)
    (hlevelBase : ∀ c ∈ C,c ∈ O → nmOrd m c=q) : nmOrd (m.geoTransform C π) z≤q := by
  have hpost : IsInvDomain k (m.geoTransform C π) := by
    as_aux_lemma => exact InvDomainTowerAlong.isInvDomain_geoTransformAlong h (.step .refl C π hπ) ⟨trivial,hC⟩
  have hV : IsOpen (π ⁻¹' (O : Set X)) := O.isOpen.preimage hπ.contMDiff.continuous
  let V : Opens Y := ⟨π ⁻¹' (O : Set X),hV⟩
  let r : V → O := fun p => ⟨π p,p.property⟩
  let mU : MarkedIdeal n (CMfd.of (n := n) O) := MarkedIdeal.pullback (Subtype.val : O → X) m
  have hUdom : IsInvDomain k mU := InvDomainTowerAlong.isInvDomain_pullback_val O h
  have hCU : mU.IsAdmissibleCentre ((↑) ⁻¹' C : Set O) := IsAdmissibleCentre.pullback_val
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h.isWellFormed.isCoherent hg) hC O
  have hr : IsBlowupAlong n ((↑) ⁻¹' C : Set O) r := isBlowupAlong_restrict hπ O hV
  have heq : mU.geoTransform ((↑) ⁻¹' C : Set O) r =
      MarkedIdeal.pullback (Subtype.val : V → Y) (m.geoTransform C π) := by
    exact geoTransform_pullback_val h.isWellFormed.isCoherent hπ hpost.isWellFormed.isCoherent O hV
  let p : V := ⟨z,hcO⟩
  have hzU : p ∈ (mU.geoTransform ((↑) ⁻¹' C : Set O) r).cosupp := by
    rw [heq,cosupp_pullback_val _ (fun _ _ hg =>
      RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hpost.isWellFormed.isCoherent hg)]
    exact hz
  have hlevel : ∀ c ∈ ((↑) ⁻¹' C : Set O),nmOrd (M := CMfd.of (n := n) O) mU c=q := by
    intro c hc
    rw [nmOrd_pullback_val hn h.isWellFormed h.isNonzeroAlongAt O c]
    exact hlevelBase c hc c.property
  have hzCU : r p ∈ ((↑) ⁻¹' C : Set O) := hzC
  have hp : (p : Y)=z := rfl
  clear_value mU r p V
  have h0 := @generic_actual_constant_order_bound n (CMfd.of (n := n) O) (CMfd.of (n := n) V) hn
  have h1 := @h0 k mU hUdom
  have h2 := @h1 ((↑) ⁻¹' C : Set O) hCU r hr
  have h3 := h2 q hlevel
  have hle := h3 p hzU hzCU
  rw [heq,nmOrd_pullback_val hn hpost.isWellFormed hpost.isNonzeroAlongAt V p] at hle
  simpa only [hp] using hle

/-- A TRUE discrete centre internally supplies the actual local constant-order
restriction needed for nonincrease, with no global order/max/canonical input. -/
theorem nmOrd_discrete_admissible_blowup_nonincrease (hn : 0<n) {k : ℕ}
    (m : MarkedIdeal n X) (h : IsInvDomain k m) {C : Set X} (hC : m.IsAdmissibleCentre C)
    (hdis : IsDiscrete C) {π : Y → X} (hπ : IsBlowupAlong n C π)
    (z : Y) (hz : z ∈ (m.geoTransform C π).cosupp) :
    π z ∈ m.cosupp ∧ nmOrd (m.geoTransform C π) z≤nmOrd m (π z) ∧
      (π z ∉ C → nmOrd (m.geoTransform C π) z=nmOrd m (π z)) := by
  have hoff : π z ∉ C → nmOrd (m.geoTransform C π) z=nmOrd m (π z) :=
    fun hzC => nmOrd_geoTransform_of_notMem hn h hC hπ hzC
  by_cases hzC : π z ∈ C
  · obtain ⟨U,hUo,hUC⟩ := (isDiscrete_iff_forall_mem_exists_isOpen.mp hdis) (π z) hzC
    have hcU : π z ∈ U := ((Set.ext_iff.mp hUC (π z)).mpr (mem_singleton (π z))).1
    have hlevel : ∀ c ∈ C,c ∈ U → nmOrd m c=nmOrd m (π z) := by
      intro c hc hcU
      have hec : c=π z := mem_singleton_iff.mp (hUC ▸ (show c ∈ U ∩ C from ⟨hcU,hc⟩))
      rw [hec]
    exact ⟨hC.2.1 hzC,nmOrd_actual_order_window_bound hn m h hC hπ z hz hzC
      (nmOrd m (π z)) ⟨U,hUo⟩ hcU hlevel,hoff⟩
  · have hcos := (TransformOffCentre.mem_cosupp_geoTransform_iff m h.isWellFormed.isClosedSubmanifold_N.1
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h.isWellFormed.isCoherent hg)
      hπ hzC).mp hz
    exact ⟨hcos,(hoff hzC).le,hoff⟩

/-- The actual successor original FULL first coordinate is its actual current
nonmonomial order for EVERY tower, without canonical or lower-data assumptions. -/
theorem original_successor_first_entry_eq_nmOrd (hn : 0<n) (k : ℕ)
    (m : MarkedIdeal n X) (T : BlowupTower X Y) (y : Y) :
    (ofLex ((invFamily hn (k+1)).inv m T y)).1=nmOrd (geoTransformAlong m T) y := rfl

/-- A REAL arbitrary ORIGINAL test prefix and discrete admissible next centre
supply an actual SAME-original successor first-coordinate comparison. -/
theorem original_discrete_test_step_first_entry_nonincrease (hn : 0<n) (k : ℕ)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+1) m) (T : BlowupTower X Y)
    (hT : IsGeoTestTower m T) {C : Set Y} (hC : (geoTransformAlong m T).IsAdmissibleCentre C)
    (hdis : IsDiscrete C) {π : Z → Y} (hπ : IsBlowupAlong n C π)
    (z : Z) (hz : z ∈ (geoTransformAlong m (.step T C π hπ)).cosupp) :
    π z ∈ (geoTransformAlong m T).cosupp ∧
      (ofLex ((invFamily hn (k+1)).inv m (.step T C π hπ) z)).1≤
        (ofLex ((invFamily hn (k+1)).inv m T (π z))).1 ∧
      (π z ∉ C → (ofLex ((invFamily hn (k+1)).inv m (.step T C π hπ) z)).1=
        (ofLex ((invFamily hn (k+1)).inv m T (π z))).1) := by
  simpa only [original_successor_first_entry_eq_nmOrd,geoTransformAlong_step] using
    nmOrd_discrete_admissible_blowup_nonincrease hn (geoTransformAlong m T)
      (InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hT) hC hdis hπ z hz

/-- ONLY original curve inputs construct the actual GLOBAL whole-bad blowup,
SAME-original post-domain/good inverse and REAL original first-entry comparison. -/
theorem exists_original_curve_whole_bad_first_entry_preparation
    {t : ℕ} {X Y : CMfd.{u} (1+t)} (k : ℕ)
    (m : MarkedIdeal (1+t) X) (h : IsInvDomain (k+1) m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily (by omega : 0<1+t) (k+1)).inv m) T)
    {S : Set Y} (hS : IsComplexAnalyticSubset (n := 1+t) S)
    (hreg : ∀ x ∈ S,RegularAtDim (n := 1+t) S x 1) (hSP : S ⊆ (geoTransformAlong m T).cosupp)
    {ι : Type*} [Fintype ι] (A : ι → GermIdeal (1+t) Y) (hA : ∀ i,(A i).IsCoherent) :
    let C := actualOriginalCurveWholeBad (k+1) m T A S
    ∃ (Z : CMfd.{u} (1+t)) (π : Z → Y) (hπ : IsBlowupAlong (1+t) C π),
      IsGeoTestTower m (.step T C π hπ) ∧ IsInvDomain (k+1) (geoTransformAlong m (.step T C π hπ)) ∧
      IsProperMap π ∧ IsIsomorphismOver (1+t) π Cᶜ ∧
      ∀ z ∈ (geoTransformAlong m (.step T C π hπ)).cosupp,
        π z ∈ (geoTransformAlong m T).cosupp ∧
        (ofLex ((invFamily (by omega : 0<1+t) (k+1)).inv m (.step T C π hπ) z)).1≤
          (ofLex ((invFamily (by omega : 0<1+t) (k+1)).inv m T (π z))).1 ∧
        (π z ∉ C → (ofLex ((invFamily (by omega : 0<1+t) (k+1)).inv m (.step T C π hπ) z)).1=
          (ofLex ((invFamily (by omega : 0<1+t) (k+1)).inv m T (π z))).1) := by
  dsimp only
  obtain ⟨hCa,hdC,hCadm,_hregC,_hlocal⟩ :=
    original_smooth_curve_whole_tuple_bad_admissible (k+1) m h T hc hS hreg hSP A hA
  obtain ⟨Z,π,hπ,hstep,hpost,hproper,_hholo,hiso,_hSNC⟩ :=
    exists_original_smooth_curve_whole_tuple_bad_blowup (k+1) m h T hc hS hreg hSP A hA
  have ht := (invFamily (by omega : 0<1+t) (k+1)).isInvValue.isGeoTestTower_of_isCanonical h T hc
  refine ⟨Z,π,hπ,hstep,hpost,hproper,hiso,?_⟩
  intro z hz
  exact original_discrete_test_step_first_entry_nonincrease (by omega : 0<1+t) k m h T ht hCadm
    (isDiscrete_of_analytic_dimLE_zero hCa hdC) hπ z hz

end
end Hironaka.HironakaOriginalDiscretePreparationFirstEntry
