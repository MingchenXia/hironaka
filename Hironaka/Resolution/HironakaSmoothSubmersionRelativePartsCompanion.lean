/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionFiniteIdealIntersections
import Hironaka.Resolution.HironakaSmoothSubmersionRelativeControlledTower
import Hironaka.Invariant.MonomialPartAlong
import Hironaka.Resolution.HironakaSmoothSubmersionRelativeMonomial
import Hironaka.Invariant.NonmonomialOrderTail
import Hironaka.Invariant.CompanionRebase
set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionRelativePartsCompanion
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaSmoothSubmersionGermIdealColon HironakaSmoothSubmersionFiniteIdealIntersections
  HironakaSmoothSubmersionRelativeControlledTower HironakaSmoothSubmersionCoefficientIdeals
  HironakaSmoothSubmersionRelativeGeometry HironakaSmoothSubmersionRelativeMonomial
  HironakaSmoothSubmersionRelativeRestriction HironakaSmoothSubmersionRelativeOrder
  HironakaSmoothSubmersionComposition HironakaSmoothSubmersionProjectionIdealColon
  HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  GermIdealPullbackCalculus RestrictedIdealExtension RestrictedIdealQuotient
  IdealWeightPowers MonomialPartAlong MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings DivisorExponentAlong BlowupTowers
noncomputable section
local instance instDecidable_partsCompanion : ∀ p : Prop, Decidable p := Classical.propDecidable
variable {n m : ℕ} {X : CMfd.{u} n} {Y : CMfd.{u} m}
  {N : Set X} {E : List (Set X)} {I : GermIdeal n X} {f : Y → X}

theorem adaptedIdeal_monomialPartAlong
    (hn : 0 < n) (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n E)
    (hT : IsTransverse n N E) (hI : I.IsCoherent)
    (hne : ∀ y ∈ N, IsNonzeroAlongAt N I y) (x : X)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0) :
    adaptedIdeal (monomialPartAlong n N I E) x Φ h0 =
      ⨅ i : Fin E.length, if x ∈ N ∧ x ∈ E.get i then
        adaptedIdeal (restrictOn n N (idealPow (vanishingIdeal (n := n) (E.get i))
          (divExpAlong n N I (E.get i) x))) x Φ h0 else ⊤ := by
  classical
  have hmon := isCoherent_monomialPartAlong hn hN hE hT hI hne
  have hp (i : Fin E.length) := isCoherent_restrictOn_of_isClosedSubmanifold
    (isCoherent_idealPow (VanishingIdealCoherent.isCoherent_vanishingIdeal
      (MonomialPart.isClosedSubmanifold_get hn hE i))
      (divExpAlong n N I (E.get i) x)) hN
  ext g
  obtain ⟨F,hF,rfl⟩ := exists_original_adapted_representative x Φ h0 g
  rw [mem_adaptedIdeal_iff _ hmon,Submodule.mem_iInf]
  constructor
  · intro h i
    by_cases hi : x ∈ N ∧ x ∈ E.get i
    · rw [if_pos hi,mem_adaptedIdeal_iff _ (hp i)]
      exact ⟨hF,h.2 i hi.1 hi.2⟩
    · rw [if_neg hi]
      exact Submodule.mem_top
  · intro h
    refine ⟨hF,?_⟩
    intro i hxN hxi
    have hh := h i
    rw [if_pos (show x ∈ N ∧ x ∈ E.get i from ⟨hxN,hxi⟩),
      mem_adaptedIdeal_iff _ (hp i)] at hh
    exact hh.2

theorem pullback_restricted_vanishing_power
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hN : IsClosedSubmanifold n N) {H : Set X} (hH : IsClosedSubmanifold n H) (e : ℕ) :
    GermIdeal.pullback (m := m) f (restrictOn n N (idealPow (vanishingIdeal (n := n) H) e)) =
      restrictOn m (f ⁻¹' N) (idealPow (vanishingIdeal (n := m) (f ⁻¹' H)) e) := by
  rw [pullback_restrictOn_eq hf
    (isCoherent_idealPow (VanishingIdealCoherent.isCoherent_vanishingIdeal hH) e) hN,
    pullback_idealPow hf.contMDiff (VanishingIdealCoherent.isCoherent_vanishingIdeal hH),
    pullback_vanishingIdeal_submersion hf hH]

theorem pullback_monomialPartAlong_add {t : ℕ} {Y : CMfd.{u} (n+t)} {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel (n+t)) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hn : 0 < n) (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n E)
    (hT : IsTransverse n N E) (hI : I.IsCoherent)
    (hne : ∀ y ∈ N, IsNonzeroAlongAt N I y) :
    GermIdeal.pullback (m := n+t) f (monomialPartAlong n N I E) =
      monomialPartAlong (n+t) (f ⁻¹' N) (GermIdeal.pullback (m := n+t) f I)
        (E.map (f ⁻¹' ·)) := by
  have hmon := isCoherent_monomialPartAlong hn hN hE hT hI hne
  have hn' : 0 < n+t := by omega
  have hNp := isClosedSubmanifold_preimage_submersion hf hN
  have hEp := HironakaSmoothSubmersionNormalCrossings.isSNCDivisor_preimage_submersion hf E hE
  have hTp := isTransverse_preimage_submersion hf hT
  have hIp := isCoherent_pullback hf.contMDiff hI
  have hnep : ∀ y ∈ f ⁻¹' N,
      IsNonzeroAlongAt (f ⁻¹' N) (GermIdeal.pullback (m := n+t) f I) y :=
    fun y hy => isNonzeroAlongAt_preimage_submersion hf hI (hne (f y) hy)
  have hmonp := isCoherent_monomialPartAlong hn' hNp hEp hTp hIp hnep
  have hpb := isCoherent_pullback hf.contMDiff hmon
  ext y F
  by_cases hF : HolomorphicAt (n+t) F y
  · have heq : adaptedIdeal (GermIdeal.pullback (m := n+t) f (monomialPartAlong n N I E)) y
        (actualSourceCoordinates hf y) (actualSourceCoordinates_zero hf y) =
        adaptedIdeal (monomialPartAlong (n+t) (f ⁻¹' N)
          (GermIdeal.pullback (m := n+t) f I) (E.map (f ⁻¹' ·))) y
          (actualSourceCoordinates hf y) (actualSourceCoordinates_zero hf y) := by
      rw [adaptedIdeal_actual_pullback hf _ hmon y,
        adaptedIdeal_monomialPartAlong hn hN hE hT hI hne,
        projection_map_iInf_eq]
      have hsource := adaptedIdeal_monomialPartAlong hn' hNp hEp hTp hIp hnep y
        (actualSourceCoordinates hf y) (actualSourceCoordinates_zero hf y)
      simp only [List.get_eq_getElem,List.getElem_map,
        divExpAlong_preimage_eq hf hI] at hsource
      rw [hsource]
      let e : Fin E.length ≃ Fin (E.map (f ⁻¹' ·)).length := finCongr (by simp)
      rw [← e.iInf_comp]
      apply iInf_congr
      intro i
      change Ideal.map (tangentPullback n t).toRingHom
        (if f y ∈ N ∧ f y ∈ E.get i then
          adaptedIdeal (restrictOn n N (idealPow (vanishingIdeal (n := n) (E.get i))
            (divExpAlong n N I (E.get i) (f y)))) (f y)
            (centeredCoordinates (f y)) (centeredCoordinates_zero (f y)) else ⊤) =
        if y ∈ f ⁻¹' N ∧ y ∈ f ⁻¹' E.get i then
          adaptedIdeal (restrictOn (n+t) (f ⁻¹' N)
            (idealPow (vanishingIdeal (n := n+t) (f ⁻¹' E.get i))
              (divExpAlong n N I (E.get i) (f y)))) y
            (actualSourceCoordinates hf y) (actualSourceCoordinates_zero hf y) else ⊤
      by_cases hi : f y ∈ N ∧ f y ∈ E.get i
      · simp only [mem_preimage] at *
        rw [if_pos hi,if_pos hi]
        have hpower := pullback_restricted_vanishing_power hf hN
          (MonomialPart.isClosedSubmanifold_get hn hE i)
          (divExpAlong n N I (E.get i) (f y))
        rw [← hpower,adaptedIdeal_actual_pullback hf _
          (isCoherent_restrictOn_of_isClosedSubmanifold
            (isCoherent_idealPow (VanishingIdealCoherent.isCoherent_vanishingIdeal
              (MonomialPart.isClosedSubmanifold_get hn hE i)) _) hN)]
      · simp only [mem_preimage] at *
        rw [if_neg hi,if_neg hi,Ideal.map_top]
    have h₁ := mem_adaptedIdeal_iff _ hpb y (actualSourceCoordinates hf y)
      (actualSourceCoordinates_zero hf y) F hF
    have h₂ := mem_adaptedIdeal_iff _ hmonp y (actualSourceCoordinates hf y)
      (actualSourceCoordinates_zero hf y) F hF
    rw [heq] at h₁
    exact h₁.symm.trans h₂
  · constructor
    · intro hm
      exact (hF (holomorphicAt_of_mem_coherent _ hpb hm)).elim
    · intro hm
      exact (hF (holomorphicAt_of_mem_coherent _ hmonp hm)).elim

theorem pullback_monomialPartAlong
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hn : 0 < n) (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n E)
    (hT : IsTransverse n N E) (hI : I.IsCoherent)
    (hne : ∀ y ∈ N, IsNonzeroAlongAt N I y) :
    GermIdeal.pullback (m := m) f (monomialPartAlong n N I E) =
      monomialPartAlong m (f ⁻¹' N) (GermIdeal.pullback (m := m) f I) (E.map (f ⁻¹' ·)) := by
  by_cases hY : Nonempty Y
  · obtain ⟨y⟩ := hY
    obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le
      (HironakaSmoothSubmersionMonomialOrdering.dimension_le_of_submersionAt (hf.isSubmersionAt y))
    exact pullback_monomialPartAlong_add hf hn hN hE hT hI hne
  · have : IsEmpty Y := not_nonempty_iff.mp hY
    ext y F
    exact (IsEmpty.false y).elim

theorem pullback_nonmonomialPartAlong
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hn : 0 < n) (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n E)
    (hT : IsTransverse n N E) (hI : I.IsCoherent)
    (hne : ∀ y ∈ N, IsNonzeroAlongAt N I y) :
    GermIdeal.pullback (m := m) f (nonmonomialPartAlong n N I E) =
      nonmonomialPartAlong m (f ⁻¹' N) (GermIdeal.pullback (m := m) f I) (E.map (f ⁻¹' ·)) := by
  unfold nonmonomialPartAlong
  rw [pullback_colonAlong_eq hf hI (isCoherent_monomialPartAlong hn hN hE hT hI hne) hN,
    pullback_monomialPartAlong hf hn hN hE hT hI hne]

theorem ordGe_markedPullback
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hn : 0 < n) (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (hne : ∀ y ∈ M.N, IsNonzeroAlongAt M.N M.ideal y) (q : ℕ) :
    NonmonomialOrderLocal.ordGe (markedPullback (m := m) f M) q =
      f ⁻¹' NonmonomialOrderLocal.ordGe M q := by
  change GermIdealOrder.cosupport m (f ⁻¹' M.N)
    (nonmonomialPartAlong m (f ⁻¹' M.N) (GermIdeal.pullback (m := m) f M.ideal)
      (M.E.map (f ⁻¹' ·))) q = _
  rw [← pullback_nonmonomialPartAlong hf hn hM.isClosedSubmanifold_N
    hM.isSNCDivisor hM.isTransverse hM.isCoherent hne]
  exact cosupport_preimage_eq hf
    (isCoherent_nonmonomialPartAlong hn hM.isClosedSubmanifold_N
      hM.isSNCDivisor hM.isTransverse hM.isCoherent hne) M.N q

theorem nmOrd_markedPullback
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hn : 0 < n) (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (hne : ∀ y ∈ M.N, IsNonzeroAlongAt M.N M.ideal y) (y : Y) :
    NonmonomialOrderLocal.nmOrd (markedPullback (m := m) f M) y =
      NonmonomialOrderLocal.nmOrd M (f y) := by
  unfold NonmonomialOrderLocal.nmOrd
  congr 1
  ext q
  change (y ∉ NonmonomialOrderLocal.ordGe (markedPullback (m := m) f M) (q+1)) ↔
    (f y ∉ NonmonomialOrderLocal.ordGe M (q+1))
  rw [ordGe_markedPullback hf hn M hM hne]
  rfl

theorem ordMask_markedPullback
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hn : 0 < n) (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (hne : ∀ y ∈ M.N, IsNonzeroAlongAt M.N M.ideal y) (q : ℕ) :
    (NonmonomialOrderTail.ordMask (markedPullback (m := m) f M) q : Set Y) =
      f ⁻¹' (NonmonomialOrderTail.ordMask M q : Set X) := by
  change (closure (NonmonomialOrderLocal.ordGe (markedPullback (m := m) f M) (q+1)))ᶜ =
    f ⁻¹' (closure (NonmonomialOrderLocal.ordGe M (q+1)))ᶜ
  have hopen := HironakaSmoothSubmersionOrderedImageTrace.isOpenMap_of_isSubmersion hf
  rw [ordGe_markedPullback hf hn M hM hne,preimage_compl,
    IsOpenMap.preimage_closure_eq_closure_preimage hopen hf.contMDiff.continuous
      (NonmonomialOrderLocal.ordGe M (q+1))]

theorem markedPullback_companionOf
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hn : 0 < n) (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (hne : ∀ y ∈ M.N, IsNonzeroAlongAt M.N M.ideal y) (o : ℕ) :
    markedPullback (m := m) f (CompanionRebase.companionOf n M o) =
      CompanionRebase.companionOf m (markedPullback (m := m) f M) o := by
  have hmon := isCoherent_monomialPartAlong hn hM.isClosedSubmanifold_N
    hM.isSNCDivisor hM.isTransverse hM.isCoherent hne
  have hnon := isCoherent_nonmonomialPartAlong hn hM.isClosedSubmanifold_N
    hM.isSNCDivisor hM.isTransverse hM.isCoherent hne
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · change f ⁻¹' (CompanionRebase.companionOf n M o).N = _
    simp only [CompanionRebase.companionOf,CompanionReductionAlong.companionAlong_N,markedPullback]
  · change (CompanionRebase.companionOf n M o).E.map (f ⁻¹' ·) = _
    simp only [CompanionRebase.companionOf,CompanionReductionAlong.companionAlong_E,markedPullback]
  · change GermIdeal.pullback (m := m) f (CompanionRebase.companionOf n M o).ideal = _
    simp only [CompanionRebase.companionOf,CompanionRebase.companionAlong_ideal,markedPullback]
    split_ifs
    · rw [pullback_sumIdeal_dimensions hf.contMDiff
        (isCoherent_idealPow hnon _) (isCoherent_idealPow hmon _),
        pullback_idealPow hf.contMDiff hnon,pullback_idealPow hf.contMDiff hmon,
        pullback_nonmonomialPartAlong hf hn hM.isClosedSubmanifold_N
          hM.isSNCDivisor hM.isTransverse hM.isCoherent hne,
        pullback_monomialPartAlong hf hn hM.isClosedSubmanifold_N
          hM.isSNCDivisor hM.isTransverse hM.isCoherent hne]
    · exact pullback_nonmonomialPartAlong hf hn hM.isClosedSubmanifold_N
        hM.isSNCDivisor hM.isTransverse hM.isCoherent hne
  · change (CompanionRebase.companionOf n M o).d = _
    simp only [CompanionRebase.companionOf,CompanionRebase.companionAlong_d,markedPullback]

end
end Hironaka.HironakaSmoothSubmersionRelativePartsCompanion
