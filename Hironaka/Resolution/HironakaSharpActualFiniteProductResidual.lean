/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualChronologicalDistinctDefect

/-! Genuine relative member primality gives actual full-product exceptional
exclusion BEFORE intrinsic exponent/monomial/nonmonomial dictionaries. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualFiniteProductResidual
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualFiniteMemberProduct HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpActualChronologicalNoOldFactor HironakaSharpActualChronologicalResidualDictionary
  HironakaSharpActualRelativeMemberPrime RelativePrincipalizationSpan RestrictedIdealExtension
  GermIdealOrder DivisorExponentAlong MonomialPartAlong MemberTraceIdealAlong IdealWeightPowers
  NormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal
variable {n : ℕ} {X : CMfd.{u} n}

/-- True finite product germs remain outside each actual restricted member ideal. -/
theorem relativeIdealListProduct_no_member_factor (hn : 0 < n) {N : Set X} {E : List (Set X)}
    (hE : IsSNCDivisor n E) (hT : IsTransverse n N E) (L : List (GermIdeal n X))
    (hc : ∀ I ∈ L,I.IsCoherent)
    (hnd : ∀ I ∈ L,∀ x ∈ N,∀ i : Fin E.length,x ∈ E.get i → ∃ a,I.mem x a ∧
      ¬IsInSpanOnAt (n := n) N ((vanishingIdeal (n := n) (E.get i)).mem x) x a) :
    ∀ x ∈ N,∀ i : Fin E.length,x ∈ E.get i → ∃ a,(relativeIdealListProduct N L).mem x a ∧
      ¬IsInSpanOnAt (n := n) N ((vanishingIdeal (n := n) (E.get i)).mem x) x a := by
  induction L with
  | nil =>
    intro x hx i hxi
    refine ⟨1,holomorphicAt_const 1,fun hs => ?_⟩
    have hv := (isInSpanOnAt_vanishingIdeal_iff_mem hE hT hx i (holomorphicAt_const (n := n) (x := x) 1)).mp hs
    exact one_ne_zero (hv.2.self_of_nhds ⟨hx,hxi⟩)
  | cons I L ih =>
    intro x hx i hxi
    obtain ⟨f,hf,hnf⟩ := hnd I (by simp) x hx i hxi
    obtain ⟨g,hg,hng⟩ := ih (fun J hJ => hc J (List.mem_cons_of_mem _ hJ))
      (fun J hJ => hnd J (List.mem_cons_of_mem _ hJ)) x hx i hxi
    have hfhol := RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem (hc I (by simp)) hf
    have hghol : HolomorphicAt n g x := by
      cases L with
      | nil => exact hg
      | cons J L => exact hg.1
    have hp : (I.mul (relativeIdealListProduct N L)).mem x (f*g) := by
      change IsInSpanAt (n := n) (fun s => ∃ a b,I.mem x a ∧ (relativeIdealListProduct N L).mem x b ∧ s=a*b) x (f*g)
      exact InvertibleIdealQuotient.isInSpanAt_self ⟨f,g,hf,hg,rfl⟩ (hfhol.mul hghol)
    refine ⟨f*g,⟨hfhol.mul hghol,IsInSpanAt.restrict (InvertibleIdealQuotient.isInSpanAt_self hp (hfhol.mul hghol))⟩,?_⟩
    intro hfg
    rcases transverse_member_relative_product_prime hn hE hT hx i f g hfhol hghol hfg with h | h
    · exact hnf h
    · exact hng h

/-- ONLY original data supply all actual full-product exceptional witnesses. -/
theorem original_chronological_product_no_exceptional_factor (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T) :
    let A := geoTransformAlong (geometricTemplate W []) T
    ∀ y ∈ A.N,∀ j : Fin A.E.length,y ∈ A.E.get j → ∃ a,(chronologicalMemberProduct W E T).mem y a ∧
      ¬IsInSpanOnAt (n := n) A.N ((vanishingIdeal (n := n) (A.E.get j)).mem y) y a := by
  have hw : (geometricTemplate W []).IsWellFormed :=
    ⟨hW,isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hwA := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw T hT
  have hfam : ∀ I ∈ chronologicalMemberFamily W E T,I.IsCoherent ∧
      ∀ y ∈ (geoTransformAlong (geometricTemplate W []) T).N,
        ∀ j : Fin (geoTransformAlong (geometricTemplate W []) T).E.length,
        y ∈ (geoTransformAlong (geometricTemplate W []) T).E.get j → ∃ a,I.mem y a ∧
          ¬IsInSpanOnAt (n := n) (geoTransformAlong (geometricTemplate W []) T).N
            ((vanishingIdeal (n := n) ((geoTransformAlong (geometricTemplate W []) T).E.get j)).mem y) y a := by
    intro I hI
    obtain ⟨H,hH,rfl⟩ := List.mem_map.mp hI
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hH
    obtain ⟨hNi,hEi,_hmi,hwi,_hnzi,_hpri⟩ := original_members_actual_finite_chronological_geometry hn hW hE hdense i T hT
    have hnd := original_members_actual_finite_chronological_no_exceptional_factor hn hW hE hdense i T hT
    dsimp only at hnd
    rw [hNi,hEi] at hnd
    exact ⟨hwi.isCoherent,hnd⟩
  exact relativeIdealListProduct_no_member_factor hn hwA.isSNCDivisor hwA.isTransverse
    (chronologicalMemberFamily W E T) (fun I hI => (hfam I hI).1) (fun I hI => (hfam I hI).2)

/-- Real original-only product exclusion precedes WHOLE intrinsic dictionaries. -/
theorem original_chronological_full_product_residual_dictionary (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T) :
    let A := geoTransformAlong (geometricTemplate W []) T
    let P := chronologicalMemberProduct W E T
    (∀ y ∈ A.N,∀ j : Fin A.E.length,y ∈ A.E.get j → divExpAlong n A.N P (A.E.get j) y=0) ∧
      monomialPartAlong n A.N P A.E=unitIdeal n Y ∧
      nonmonomialPartAlong n A.N P A.E=restrictOn n A.N P ∧
      ∀ y ∈ A.N,∀ g,(nonmonomialPartAlong n A.N P A.E).mem y g ↔ P.mem y g := by
  have hw : (geometricTemplate W []).IsWellFormed :=
    ⟨hW,isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hwA := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw T hT
  obtain ⟨hcP,_hnzP,hprP,_hordP⟩ := original_chronological_full_product_actual_geometry hn hW hE hdense T hT
  have hnd := original_chronological_product_no_exceptional_factor hn hW hE hdense T hT
  have hNm := nonmonomialPartAlong_eq_restrictOn_of_no_member_factor hwA.isClosedSubmanifold_N
    hwA.isSNCDivisor hwA.isTransverse hcP hnd
  refine ⟨fun y hy j hyj => divExpAlong_eq_zero_of_no_member_factor hwA.isSNCDivisor hwA.isTransverse hcP hnd hy j hyj,
    monomialPartAlong_eq_unit_of_no_member_factor hwA.isSNCDivisor hwA.isTransverse hcP hnd,hNm,?_⟩
  intro y hy g
  rw [hNm]
  obtain ⟨f,_hf,hgen⟩ := hprP y hy
  constructor
  · intro hg
    exact (hgen g).mpr ⟨hg.1,IsInSpanOnAt.trans (fun s hs => ((hgen s).mp hs).2) hg.2⟩
  · exact fun hg => le_restrictOn hcP y g hg

end
end Hironaka.HironakaSharpActualFiniteProductResidual
