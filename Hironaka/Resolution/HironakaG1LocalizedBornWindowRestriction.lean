import Hironaka.Resolution.HironakaG1LocalizedLaterBornCanonical
import Hironaka.Resolution.HironakaG8LocalTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG1LocalizedBornWindowRestriction
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  ResolutionInvariantSpec CanonicalCentres HomogenizedIdealAlong CoefficientIdealRestriction
  TangentDirectionAlong ContactEquivalenceAlong StepOneValue StepOneLowerDomain BoundaryCount
  InvDomainMemberRestriction InvDomainTowerAlong
  HironakaG8LocalHistory HironakaG8LocalTransport HironakaG1RecursiveMemberValueTransport
  HironakaG1BornSelectedCompanionCanonical HironakaG1LocalizedLaterBornCanonical
  HironakaActualOpenTangentDescent DivisorExponentAlong RelativePrincipalizationSpan

private theorem domain_on_smaller {n q : ℕ} {X : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : M.ideal.IsCoherent) {V W : Opens X} (hWV : W ≤ V)
    (hV : IsInvDomain q (MarkedIdeal.pullback (Subtype.val : V → X) M)) :
    IsInvDomain q (MarkedIdeal.pullback (Subtype.val : W → X) M) := by
  have h := isInvDomain_pullback_val (MaxLocusLocal.nestedOpens V W) hV
  have h' := isInvDomain_pullback (MaxLocusLocal.nestedOpensDiffeo (n := n) hWV).symm h
  rwa [MaxLocusLocal.pullback_symm_nestedOpensDiffeo hM hWV] at h'

/-- The entire born contact pair on a specified window of the actual masks. -/
abbrev LocalizedBornWindowData {n k l : ℕ} (hn : 0 < n) {X : CMfd.{0} n}
    (J R : MarkedIdeal n X) (a : X) (u : X → ℂ) (W : Opens X) : Prop :=
  let I : BlowupTower X X := .refl
  let A := CMfd.of (n := n) W
  let K := positiveMemberOn J I a W
  let S := positiveMemberOn R I a W
  let Cut := withN (coeffMarkedAlong K) (K.N ∩ {z : W | u z.val = 0})
  IsInvDomain (k - 1) K ∧
  IsTangentDirectionAlong K.N K.ideal K.d univ (u ∘ (Subtype.val : W → X)) ∧
  Cut.N = S.N ∧ Cut.E = S.E ∧ LocWPEquiv (X := A) Cut S ∧
  K.d = (coeffMarkedAlong (barMarked J)).d ∧
  S.d = (coeffMarkedAlong (barMarked R)).d ∧
  Cut.d = (coeffMarkedAlong K).d ∧
  IsInvDomain (l - 1) Cut ∧ IsInvDomain (l - 1) S ∧
  (∀ F ∈ Cut.E, ∀ z ∈ Cut.cosupp, z ∈ F →
    S.d * divExpAlong n Cut.N Cut.ideal F z =
      Cut.d * divExpAlong n S.N S.ideal F z) ∧
  ∀ {Y : CMfd.{0} n} (T : BlowupTower A Y),
    IsCanonical Cut ((invFamily hn (l - 1)).inv Cut) T ↔
      IsCanonical S ((invFamily hn (l - 1)).inv S) T

set_option maxHeartbeats 1500000 in
/-- Same literal coefficient definition before or after restriction of the
selected record. The normal, original mark and ordered slots all pull back. -/
theorem selected_bare_contact_pullback_val {n : ℕ} {X : CMfd.{0} n}
    (K : MarkedIdeal n X) (hK : K.IsWellFormed) (hd : 1 ≤ K.d) (u : X → ℂ)
    (W : Opens X) :
    let A := CMfd.of (n := n) W
    let L := MarkedIdeal.pullback (M' := A) (Subtype.val : W → X) K
    MarkedIdeal.pullback (M' := A) (Subtype.val : W → X)
      (withN (coeffMarkedAlong K) (K.N ∩ {z | u z = 0})) =
      withN (coeffMarkedAlong L) (L.N ∩ {z : W | u z.val = 0}) := by
  intro A L
  change withN (MarkedIdeal.pullback (Subtype.val : W → X) (coeffMarkedAlong K))
    (L.N ∩ {z : W | u z.val = 0}) = _
  rw [pullback_val_coeffMarkedAlong W K hK.isCoherent hK.isClosedSubmanifold_N hd]

set_option maxHeartbeats 1900000 in
/-- Restrict the actual next-born contact and supported pair to any smaller
common window. The coefficient contact is pulled back as a whole record,
so no boundary member or recursive mark is changed in the comparison. -/
theorem localized_born_window_data_restrict {n k l : ℕ} (hn : 0 < n) {X : CMfd.{0} n}
    (J R : MarkedIdeal n X) (hJ : IsInvDomain k J) (hR : IsInvDomain l R)
    (a : X) (u : X → ℂ) {V W : Opens X} (hWV : W ≤ V)
    (hV : LocalizedBornWindowData (k := k) (l := l) hn J R a u V) :
    LocalizedBornWindowData (k := k) (l := l) hn J R a u W := by
  let H : BlowupTower X X := .refl
  let B := barMarked J
  let Br := barMarked R
  let I := membersThrough B.E (origMembers J H) a
  let Ir := membersThrough Br.E (origMembers R H) a
  let K₀ := memberRestrict B I
  let S₀ := memberRestrict Br Ir
  let Cut₀ := withN (coeffMarkedAlong K₀) (K₀.N ∩ {z | u z = 0})
  have hB := HironakaCoherentTransformExtension.isInvDomain_barMarked J hJ
  have hBr := HironakaCoherentTransformExtension.isInvDomain_barMarked R hR
  have hK₀ : K₀.IsWellFormed := isWellFormed_memberRestrict hn hB.isWellFormed I
  have hS₀ : S₀.IsWellFormed := isWellFormed_memberRestrict hn hBr.isWellFormed Ir
  have hdK₀ : 1 ≤ K₀.d := one_le_memberRestrict_d B I
  have hCut₀ : Cut₀.ideal.IsCoherent :=
    isCoherent_coeffMarkedAlong hK₀.isCoherent hK₀.isClosedSubmanifold_N
  let Kv := positiveMemberOn J H a V
  let Sv := positiveMemberOn R H a V
  let Cv := withN (coeffMarkedAlong Kv) (Kv.N ∩ {z : V | u z.val = 0})
  let Kw := positiveMemberOn J H a W
  let Sw := positiveMemberOn R H a W
  let Cw := withN (coeffMarkedAlong Kw) (Kw.N ∩ {z : W | u z.val = 0})
  have hCv : MarkedIdeal.pullback (Subtype.val : V → X) Cut₀ = Cv :=
    selected_bare_contact_pullback_val K₀ hK₀ hdK₀ u V
  have hCw : MarkedIdeal.pullback (Subtype.val : W → X) Cut₀ = Cw :=
    selected_bare_contact_pullback_val K₀ hK₀ hdK₀ u W
  obtain ⟨hKv, hTanV, hNv, _, hClassV, _, _, _, hDCv, _, _, _⟩ := hV
  have hKw : IsInvDomain (k - 1) Kw := domain_on_smaller K₀ hK₀.isCoherent hWV hKv
  have hDCw : IsInvDomain (l - 1) Cw := by
    rw [← hCw]
    exact domain_on_smaller Cut₀ hCut₀ hWV (hCv.symm ▸ hDCv)
  have hNw : Cw.N = Sw.N := by
    ext z
    have hz := Set.ext_iff.mp hNv (⟨z.val, hWV z.property⟩ : V)
    exact hz
  have hClassBase : LocWPEquiv (X := CMfd.of (n := n) V)
      (MarkedIdeal.pullback (Subtype.val : V → X) Cut₀)
      (MarkedIdeal.pullback (Subtype.val : V → X) S₀) := hCv.symm ▸ hClassV
  have hClassW : LocWPEquiv (X := CMfd.of (n := n) W) Cw Sw := by
    rw [← hCw]
    exact locWPEquiv_restrict_of_le hCut₀ hS₀.isCoherent hWV hClassBase
  have hDown := isTangentDirectionAlong_of_open_pullback K₀.N hK₀.isClosedSubmanifold_N
    K₀.ideal hK₀.isCoherent K₀.d V univ u hTanV
  have hImage : (Subtype.val : V → X) '' (univ : Set V) = (V : Set X) := by
    ext z
    exact ⟨fun ⟨w, _, he⟩ => he ▸ w.property, fun hz => ⟨⟨z, hz⟩, trivial, rfl⟩⟩
  rw [hImage] at hDown
  have hTanW := isTangentDirectionAlong_pullback_val W
    (fun _ _ hf => GermIdeal.IsCoherent.holomorphicAt_mem hK₀.isCoherent hf)
      ⟨W.isOpen, fun x hx => hDown.mem x (hWV hx), fun x hx => hDown.multiplicity_one x (hWV hx)⟩
  obtain ⟨hDC, hDS, hExp, hCan⟩ := born_selected_contact_canonical_of_domain hn J R hR a W u
    hKw hNw hClassW (Or.inl hDCw)
  exact ⟨hKw, hTanW, hNw, hClassW.wEquiv.1, hClassW, rfl, rfl, rfl, hDC, hDS, hExp, hCan⟩


/-- Any independently constructed geometry window through the same split
anchor contains a common subwindow carrying the entire born contact pair. -/
theorem localized_born_witness_inside {n k l : ℕ} (hn : 0 < n) {X : CMfd.{0} n}
    (J R : MarkedIdeal n X) (hJ : IsInvDomain k J) (hR : IsInvDomain l R)
    (a : X) (u : X → ℂ) (U : Opens X) (haU : a ∈ U)
    (hWitness : LocalizedBornWitness (k := k) (l := l) hn J R a u) :
    let I : BlowupTower X X := .refl
    ∃ W : Opens X, a ∈ W ∧ W ≤ U ∧ W ≤ maskA J I a ∧ W ≤ maskA R I a ∧
      LocalizedBornWindowData (k := k) (l := l) hn J R a u W := by
  intro I
  obtain ⟨V, haV, hVJ, hVR, hData⟩ := hWitness
  let W := U ⊓ V
  have hWV : W ≤ V := inf_le_right
  exact ⟨W, ⟨haU, haV⟩, inf_le_left, le_trans hWV hVJ, le_trans hWV hVR,
    localized_born_window_data_restrict hn J R hJ hR a u hWV hData⟩

end
end Hironaka.HironakaG1LocalizedBornWindowRestriction
