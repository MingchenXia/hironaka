import Hironaka.Resolution.HironakaOriginalNCMarkedStratumNaturality
import Hironaka.Resolution.HironakaOriginalNCMarkedStratumStepDrop
import Hironaka.Resolution.HironakaEmbeddedBoundary

/-!
# Homogeneity of the actual prescribed-H NEW value over a good open

The literal open preimage of H is empty, and every retained E member
restricts to an empty member of the SAME-length list. Actual empty
steps, actual smooth-centre biholomorphisms and NEW open/given-iso
value fields prove the comparison. No empty chronology is deleted;
no old ambient coefficient value or H-free invariant is substituted.

Mathematics and complete real API precede source in
work/hironaka-g9-general-nc-embedded-producers-20261024/.
SOURCE ONLY: no Lean/kernel/Blueprint acceptance is asserted.
-/

set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaOriginalNCMarkedStratumGoodOpen
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  HironakaEmbeddedBoundary HironakaNormalCrossingsBoundaryTransform
  HironakaNormalCrossingsOpenRestrictionSeparation
  HironakaOriginalNCMarkedStratumHistoryValue HironakaOriginalNCMarkedStratumCanonicalHistory
  HironakaOriginalNCMarkedStratumNaturality HironakaOriginalNCMarkedStratumStepDrop
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open ResolutionInvariantExt (IsEmptyTower)

variable {n : ℕ}

/-- Literal empty steps retain the SAME prescribed-H value and original
native cosupport at their actual base images; no years are erased. -/
private theorem value_empty_tower {X : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsEmptyTower T →
      ∀ y ∈ (geoTransformAlong M T).cosupp,
        T.proj y ∈ M.cosupp ∧
          markedStratumHistoryValue M H T y =
            markedStratumHistoryValue M H (BlowupTower.refl : BlowupTower X X) (T.proj y)
  | _, .refl, _, y, hy => ⟨hy, rfl⟩
  | _, .step T C π hπ, he, y, hy => by
      have hWhole := he
      obtain ⟨hT, hC⟩ : IsEmptyTower T ∧ C = ∅ := he
      have hiff := SmoothCentreInvariant.mem_cosupp_geoTransformAlong_of_isEmptyTower M
        hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent (.step T C π hπ) hWhole y
      have hπy : π y ∈ (geoTransformAlong M T).cosupp :=
        (SmoothCentreInvariant.mem_cosupp_geoTransformAlong_of_isEmptyTower M
          hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent T hT (π y)).mpr (hiff.mp hy)
      have hCan := ResolutionInvariantExt.isCanonical_of_isEmptyTower M
        (markedStratumHistoryValue M H) T hT
      have hStep := markedStratum_history_value_empty_step M hM h T C π hπ hC hCan y hy
      obtain ⟨hm, hv⟩ := value_empty_tower M hM h T hT (π y) hπy
      exact ⟨hm, hStep.trans hv⟩

/-- Genuine smooth-centre biholomorphisms compare the reflexive NEW values
with literal empty H and an unchanged full list of empty E members. -/
private theorem value_refl_empty_carrier_equal {X : CMfd.{u} n}
    {Z : Set X} {E : List (Set X)} (hE : ∀ A ∈ E, A = ∅)
    (hZ : IsClosedSubmanifold n Z)
    (hM : IsInvDomain n (⟨univ, E, vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X))
    (h : IsBoundaryAdaptedCarrier (n := n) (∅ : Set X) E)
    {x x' : X} {d : ℕ} (hx : RegularAtDim (n := n) Z x d) (hx' : RegularAtDim (n := n) Z x' d) :
    markedStratumHistoryValue (⟨univ, E, vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X) ∅
        (BlowupTower.refl : BlowupTower X X) x' =
      markedStratumHistoryValue (⟨univ, E, vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X) ∅
        (BlowupTower.refl : BlowupTower X X) x := by
  let M : MarkedIdeal n X := ⟨univ, E, vanishingIdeal (n := n) Z, 1⟩
  have hcos : M.cosupp = Z := cosupp_mk_vanishingIdeal hZ.1 E
  obtain ⟨U₁, U₂, Φ, hxU, hx'U, hΦx, _hΦW, hpb⟩ := SmoothCentreHomogeneity.exists_smoothCentre_iso hx hx' 1
  have hpb' := pullback_pullback_val_mk_of_forall_eq_empty hE Φ hpb
  have hhol := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hM.isWellFormed.isCoherent
  have h1 := markedStratum_history_value_restrictOpen M hM h U₁ BlowupTower.refl trivial ⟨x, hxU⟩
    (by show x ∈ M.cosupp; rw [hcos]; exact hx.2.1)
  have h2 := markedStratum_history_value_restrictOpen M hM h U₂ BlowupTower.refl trivial ⟨x', hx'U⟩
    (by show x' ∈ M.cosupp; rw [hcos]; exact hx'.2.1)
  simp only [preimage_empty] at h1 h2
  have hM₂ := InvDomainTowerAlong.isInvDomain_pullback_val U₂ hM
  have h₂ := boundaryAdapted_open U₂ h
  simp only [preimage_empty] at h₂
  have hc₂ : Φ ⟨x, hxU⟩ ∈
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U₂ → X) M)
        (BlowupTower.refl : BlowupTower (CMfd.of (n := n) U₂) (CMfd.of (n := n) U₂))).cosupp := by
    show Φ ⟨x, hxU⟩ ∈ (MarkedIdeal.pullback (Subtype.val : U₂ → X) M).cosupp
    rw [MarkedIdealRestrictOpen.cosupp_pullback_val M hhol U₂, hcos]
    change ((Φ ⟨x, hxU⟩ : U₂) : X) ∈ Z
    rw [hΦx]
    exact hx'.2.1
  have h3 := markedStratum_history_value_towerIso
    (MarkedIdeal.pullback (Subtype.val : U₂ → X) M) hM₂ h₂ Φ BlowupTower.refl BlowupTower.refl Φ
    IsTowerIso.refl trivial ⟨x, hxU⟩ hc₂
  rw [preimage_empty, hpb'] at h3
  have hΦx' : Φ ⟨x, hxU⟩ = ⟨x', hx'U⟩ := Subtype.ext hΦx
  rw [hΦx'] at h3
  exact h2.symm.trans (h3.symm.trans h1)

/-- On the actual good open, every surviving point of a GIVEN raw canonical
history with empty restricted centres has the same NEW value. The SAME
prescribed H and all equal-length empty boundary labels are transported. -/
theorem markedStratum_value_eq_over_good_open {X : CMfd.{u} n}
    {W : Set X} {E : List (Set X)}
    (hM : IsInvDomain n (⟨univ, E, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X))
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H E)
    (U : Opens X) (hHU : Disjoint H (U : Set X)) (hEU : ∀ A ∈ E, Disjoint A (U : Set X))
    (hZ : IsClosedSubmanifold n ((Subtype.val : U → X) ⁻¹' W)) {d : ℕ}
    (hpure : ∀ x ∈ (Subtype.val : U → X) ⁻¹' W,
      RegularAtDim (n := n) ((Subtype.val : U → X) ⁻¹' W) x d)
    {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hCan : IsCanonical (⟨univ, E, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X)
      (markedStratumHistoryValue (⟨univ, E, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) H) T)
    (hEmpty : IsEmptyTower (restrict U T)) {p p' : openPreimage T U}
    (hp : (p : Y) ∈ (geoTransformAlong (⟨univ, E, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T).cosupp)
    (hp' : (p' : Y) ∈ (geoTransformAlong (⟨univ, E, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T).cosupp) :
    markedStratumHistoryValue (⟨univ, E, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) H T p' =
      markedStratumHistoryValue (⟨univ, E, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) H T p := by
  let M : MarkedIdeal n X := ⟨univ, E, vanishingIdeal (n := n) W, 1⟩
  have h1 := markedStratum_history_value_restrictOpen M hM h U T hCan p hp
  have h2 := markedStratum_history_value_restrictOpen M hM h U T hCan p' hp'
  have hMU := InvDomainTowerAlong.isInvDomain_pullback_val U hM
  have hPair := boundaryAdapted_open U h
  have hH0 : (Subtype.val : U → X) ⁻¹' H = ∅ :=
    (RestrictEmptyTower.preimage_val_eq_empty_iff U H).mpr hHU
  have hTest := (markedStratum_canonical_history_joint_interpretation M hM h T hCan).1
  have hc := ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict
    hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent U T hTest
  have hq : p ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) M) (restrict U T)).cosupp := by
    rw [hc]
    exact hp
  have hq' : p' ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) M) (restrict U T)).cosupp := by
    rw [hc]
    exact hp'
  rw [pullback_val_mk_vanishingIdeal U E W] at h1 h2 hMU hq hq'
  rw [hH0] at h1 h2 hPair
  have hE0 : ∀ A ∈ E.map ((Subtype.val : U → X) ⁻¹' ·), A = ∅ := by
    intro A hA
    obtain ⟨A₀, hA₀, rfl⟩ := List.mem_map.mp hA
    exact (RestrictEmptyTower.preimage_val_eq_empty_iff U A₀).mpr (hEU A₀ hA₀)
  obtain ⟨hm, hv⟩ := value_empty_tower _ hMU hPair (restrict U T) hEmpty p hq
  obtain ⟨hm', hv'⟩ := value_empty_tower _ hMU hPair (restrict U T) hEmpty p' hq'
  rw [cosupp_mk_vanishingIdeal hZ.1] at hm hm'
  rw [← h1, ← h2, hv, hv']
  exact value_refl_empty_carrier_equal hE0 hZ hMU hPair (hpure _ hm) (hpure _ hm')

end
end Hironaka.HironakaOriginalNCMarkedStratumGoodOpen
