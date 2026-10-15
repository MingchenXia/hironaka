/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualControlledRelativePrincipal

/-! Genuine original-mark ALL-boundary controlled nonmonomial residual equals
actual next chronological full product. Earlier-original-history comparison,
modified decrease and sharp termination remain OPEN. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualControlledAccumulatedResidual
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualControlledRelativePrincipal HironakaSharpActualControlledRelativeSaturation
  HironakaSharpActualTotalAccumulatedResidual HironakaSharpActualProductRelativeStrict
  HironakaSharpActualFiniteProductResidual HironakaSharpActualFiniteMemberProduct
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualChronologicalNoOldFactor
  HironakaSharpActualChronologicalStrictStep HironakaSharpOriginalFirstMemberExceptionalFactor
  RelativePrincipalizationSpan RestrictedIdealExtension RestrictedIdealQuotient
  MonomialPartAlong DivisorExponentAlong NormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal
  IdealWeightPowers MemberTraceIdealAlong GermIdealOrder BlowupSNCTransform BlowupStrictSubmanifold
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Actual finite denominator testing places EVERY genuine normalized TOTAL
germ in the SAME original-mark controlled ideal. -/
theorem actual_total_le_controlled (M : MarkedIdeal n X)
    {C : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π) :
    (nextTotalMarked M.N M.ideal C π).ideal.Le (M.geoTransform C π).ideal := by
  have hAcoh := GermIdealPullbackCalculus.isCoherent_idealPow
    (GermIdealPullbackCalculus.isCoherent_pullback hπ.contMDiff
      (BlowupExceptionalDivisor.isCoherent_vanishingIdeal_centre hπ)) M.d
  intro y g hg
  have hTot := geoTransform_zeroMark_ideal_eq_restricted_total (⟨M.N,[],M.ideal,0⟩ : MarkedIdeal n X) rfl C π
  change (nextTotalMarked M.N M.ideal C π).ideal=_ at hTot
  rw [hTot] at hg
  exact ⟨hg.1,fun a ha => restrictOn_mul_left
    (RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hAcoh ha) hg⟩

/-- Genuine OLD TOTAL witnesses retain exclusion in the actual controlled ideal;
ONLY old exponents vanish before the WHOLE full/new monomial dictionary. -/
theorem controlled_accumulated_monomial_eq_new (M : MarkedIdeal n X) (hw : M.IsWellFormed)
    {C : Set X} (hC : M.IsAdmissibleCentre C) {π : Y → X} (hπ : IsBlowupAlong n C π)
    (hnd : ∀ x ∈ M.N,∀ i : Fin M.E.length,x ∈ M.E.get i → ∃ a,M.ideal.mem x a ∧
      ¬IsInSpanOnAt (n := n) M.N ((vanishingIdeal (n := n) (M.E.get i)).mem x) x a) :
    monomialPartAlong n (M.geoTransform C π).N (M.geoTransform C π).ideal (M.geoTransform C π).E=
      monomialPartAlong n (M.geoTransform C π).N (M.geoTransform C π).ideal [π ⁻¹' C] := by
  let N := M.N
  let E := M.E
  let I := M.ideal
  have hN := hw.isClosedSubmanifold_N
  have hE := hw.isSNCDivisor
  have hT := hw.isTransverse
  have hI := hw.isCoherent
  have hCN := hC.subset_N
  have hNC := hC.2.2
  have hwNew := GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hw hC hπ
  let E' := E.map (geoStrictTransform π C) ++ [π ⁻¹' C]
  have hzero : ∀ y ∈ (M.geoTransform C π).N,∀ j : Fin E.length,y ∈ geoStrictTransform π C (E.get j) →
      divExpAlong n (M.geoTransform C π).N (M.geoTransform C π).ideal (geoStrictTransform π C (E.get j)) y=0 := by
    intro y hy j hyj
    let idx : Fin E'.length := ⟨j.val,by simpa only [E',List.length_append,List.length_map,List.length_singleton] using Nat.lt_succ_of_lt j.isLt⟩
    have hget : E'.get idx=geoStrictTransform π C (E.get j) := by
      rw [get_map_append_singleton]
      change (if h : j.val<E.length then geoStrictTransform π C (E.get ⟨j.val,h⟩) else π ⁻¹' C)=_
      rw [dif_pos j.isLt]
    have hnd' : ∀ z ∈ (M.geoTransform C π).N,z ∈ E'.get idx → ∃ a,(M.geoTransform C π).ideal.mem z a ∧
        ¬IsInSpanOnAt (n := n) (M.geoTransform C π).N ((vanishingIdeal (n := n) (E'.get idx)).mem z) z a := by
      rw [hget]
      intro z hz hzi
      obtain ⟨a,ha,hna⟩ := nextTotal_old_strict_member_not_factor hN hE hT hI hπ hCN hNC hnd hz j hzi
      exact ⟨a,actual_total_le_controlled M hπ z a ha,hna⟩
    have hz := fixed_member_no_factor_divExpAlong_zero hwNew.isSNCDivisor hwNew.isTransverse hwNew.isCoherent idx hnd' hy
    change y ∈ E'.get idx → divExpAlong n (M.geoTransform C π).N (M.geoTransform C π).ideal (E'.get idx) y=0 at hz
    rw [hget] at hz
    exact hz hyj
  let last : Fin E'.length := ⟨E.length,by simp [E']⟩
  have hlast : E'.get last=π ⁻¹' C := by
    rw [get_map_append_singleton]
    change (if h : E.length<E.length then geoStrictTransform π C (E.get ⟨E.length,h⟩) else π ⁻¹' C)=_
    rw [dif_neg (Nat.lt_irrefl _)]
  ext y g
  change (monomialPartAlong n (M.geoTransform C π).N (M.geoTransform C π).ideal E').mem y g ↔
    (monomialPartAlong n (M.geoTransform C π).N (M.geoTransform C π).ideal [π ⁻¹' C]).mem y g
  constructor
  · intro hg
    refine ⟨hg.1,?_⟩
    intro i hyN hyi
    have hi : i=(0 : Fin [π ⁻¹' C].length) := by
      apply Fin.ext
      have hh := i.isLt
      simp only [List.length_singleton] at hh
      change i.val=0
      omega
    subst i
    have hh := hg.2 last hyN
    rw [hlast] at hh
    exact hh hyi
  · intro hg
    refine ⟨hg.1,?_⟩
    intro i hyN hyi
    have hget := get_map_append_singleton E (geoStrictTransform π C) (π ⁻¹' C) i
    by_cases hi : i.val<E.length
    · rw [dif_pos hi] at hget
      rw [hget,hzero y hyN ⟨i.val,hi⟩ (hget ▸ hyi),idealPow_zero]
      exact IsInSpanAt.restrict (InvertibleIdealQuotient.isInSpanAt_self hg.1 hg.1)
    · rw [dif_neg hi] at hget
      rw [hget]
      exact hg.2 (0 : Fin [π ⁻¹' C].length) hyN (hget ▸ hyi)

/-- True controlled principal/nonzero geometry precedes singleton saturation/Nm,
then the real ALL-boundary positive-mark residual/STRICT identity follows. -/
theorem controlled_all_accumulated_nonmonomial_eq_nextStrict (hn : 0 < n)
    (M : MarkedIdeal n X) (hw : M.IsWellFormed)
    (hnz : ∀ x ∈ M.N,IsNonzeroAlongAt M.N M.ideal x)
    (hp : ∀ x ∈ M.N,∃ f : X → ℂ,HolomorphicAt n f x ∧ ∀ g,M.ideal.mem x g ↔
      HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) M.N (·=f) x g)
    {C : Set X} (hC : M.IsAdmissibleCentre C) {π : Y → X} (hπ : IsBlowupAlong n C π)
    (hnd : ∀ x ∈ M.N,∀ i : Fin M.E.length,x ∈ M.E.get i → ∃ a,M.ideal.mem x a ∧
      ¬IsInSpanOnAt (n := n) M.N ((vanishingIdeal (n := n) (M.E.get i)).mem x) x a) :
    nonmonomialPartAlong n (M.geoTransform C π).N (M.geoTransform C π).ideal (M.geoTransform C π).E=
      nextRelativeStrict M.N M.ideal C π := by
  have hwQ := GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hw hC hπ
  have hnzQ := HironakaCoherentTransformExtension.isNonzeroAlongAt_geoTransform_without_admissibility
    M hw.isClosedSubmanifold_N hw.isCoherent hπ hC.subset_N hnz
  have hprQ : ∀ y ∈ (M.geoTransform C π).N,∃ f : Y → ℂ,HolomorphicAt n f y ∧
      ∀ g,(M.geoTransform C π).ideal.mem y g ↔ HolomorphicAt n g y ∧
        IsInSpanOnAt (n := n) (M.geoTransform C π).N (·=f) y g := by
    intro y hy
    obtain ⟨f,hf,hgen⟩ := actual_admissible_geoTransform_relative_principal M hw.isClosedSubmanifold_N hw.isCoherent hp hC hπ y hy
    exact ⟨f,((hgen f).mp hf).1,hgen⟩
  have hSat := (HironakaSharpOriginalFirstMemberWholeFactor.actual_single_exceptional_saturation_eq_residual hn
    hwQ.isClosedSubmanifold_N (isSNCDivisor_preimage_centre hπ)
    (isTransverse_preimage_centre hπ hw.isClosedSubmanifold_N hC.subset_N) hwQ.isCoherent hnzQ hprQ).1
  have hM := controlled_accumulated_monomial_eq_new M hw hC hπ hnd
  calc
    nonmonomialPartAlong n (M.geoTransform C π).N (M.geoTransform C π).ideal (M.geoTransform C π).E=
        nonmonomialPartAlong n (M.geoTransform C π).N (M.geoTransform C π).ideal [π ⁻¹' C] := by
      change InvertibleIdealQuotient.colon _ (monomialPartAlong n _ _ _)=InvertibleIdealQuotient.colon _ (monomialPartAlong n _ _ _)
      rw [hM]
    _ = HironakaSharpOriginalFirstMemberRelativeStrict.relativeExceptionalSaturation
        (M.geoTransform C π).N (M.geoTransform C π).ideal (π ⁻¹' C) := hSat.symm
    _ = nextRelativeStrict M.N M.ideal C π := geoTransform_relativeExceptionalSaturation_eq hn M hπ

/-- ONLY original chronological inputs internally supply the positive-mark
current full product and every real ALL-boundary residual premise. -/
theorem original_current_product_controlled_residual_eq_next_product (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    {Z : CMfd.{u} n} (T : BlowupTower X Z) (ht : IsGeoTestTower (geometricTemplate W []) T)
    {C : Set Z} {π : Y → Z} (hπ : IsBlowupAlong n C π)
    (hC : (⟨(geoTransformAlong (geometricTemplate W []) T).N,(geoTransformAlong (geometricTemplate W []) T).E,
      chronologicalMemberProduct W E T,1⟩ : MarkedIdeal n Z).IsAdmissibleCentre C) :
    let M : MarkedIdeal n Z := ⟨(geoTransformAlong (geometricTemplate W []) T).N,
      (geoTransformAlong (geometricTemplate W []) T).E,chronologicalMemberProduct W E T,1⟩
    nonmonomialPartAlong n (M.geoTransform C π).N (M.geoTransform C π).ideal (M.geoTransform C π).E=
      chronologicalMemberProduct W E (.step T C π hπ) := by
  have hw : (geometricTemplate W []).IsWellFormed :=
    ⟨hW,isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hwA := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw T ht
  obtain ⟨hc,hnz,hpr,_hord⟩ := original_chronological_full_product_actual_geometry hn hW hE hdense T ht
  have hnd := original_chronological_product_no_exceptional_factor hn hW hE hdense T ht
  let M : MarkedIdeal n Z := ⟨(geoTransformAlong (geometricTemplate W []) T).N,
    (geoTransformAlong (geometricTemplate W []) T).E,chronologicalMemberProduct W E T,1⟩
  have hwM : M.IsWellFormed := ⟨hwA.isClosedSubmanifold_N,hc,hwA.isSNCDivisor,hwA.isTransverse⟩
  exact (controlled_all_accumulated_nonmonomial_eq_nextStrict hn M hwM hnz hpr hC hπ hnd).trans
      (original_next_chronological_product_eq_full_relative_strict hn hW hE hdense T ht hπ hC.subset_N)

end
end Hironaka.HironakaSharpActualControlledAccumulatedResidual
