/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualRelativeProductOrder

/-! Literal actual finite chronological products, with real carrier normalization,
coherence/nonzero/principal generators and ALL multiplicity order sums. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualFiniteMemberProduct
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualRelativeProductOrder HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpOriginalProductTraceOrder RelativePrincipalizationSpan RestrictedIdealExtension
  GermIdealOrder DivisorExponentAlong MonomialPartAlong InvertibleIdealQuotient IdealWeightPowers
  MarkedIdeals MarkedIdeals.MarkedIdeal
variable {n : ℕ} {X : CMfd.{u} n}

/-- Actual relative multiplication, independent of any product certificate. -/
def relativeIdealListProduct (N : Set X) : List (GermIdeal n X) → GermIdeal n X
  | [] => unitIdeal n X
  | I::L => restrictOn n N (I.mul (relativeIdealListProduct N L))

/-- EVERY actual original position's independently defined chronological ideal. -/
def chronologicalMemberFamily (W : Set X) (E : List (Set X))
    {Y : CMfd.{u} n} (T : BlowupTower X Y) : List (GermIdeal n Y) :=
  E.map fun H => (chronologicalMarked (originalRelativeMemberMarked W H) T).ideal

def chronologicalMemberProduct (W : Set X) (E : List (Set X))
    {Y : CMfd.{u} n} (T : BlowupTower X Y) : GermIdeal n Y :=
  relativeIdealListProduct (geoTransformAlong (geometricTemplate W []) T).N (chronologicalMemberFamily W E T)

/-- BOTH actual cosupport directions preserve true finite ordinary order. -/
theorem ordinaryTraceOrder_restrictOn_eq {N : Set X} (hN : IsClosedSubmanifold n N)
    {I : GermIdeal n X} (hI : I.IsCoherent) (hi : ∀ y ∈ N,IsNonzeroAlongAt N I y)
    {x : X} (hx : x ∈ N) : ordinaryTraceOrder N (restrictOn n N I) x=ordinaryTraceOrder N I x := by
  have hr := isCoherent_restrictOn hI (VanishingIdealCoherent.isCoherent_vanishingIdeal hN)
  have hnz : ∀ y ∈ N,IsNonzeroAlongAt N (restrictOn n N I) y := by
    intro y hy
    obtain ⟨g,hg,hfreq⟩ := hi y hy
    exact ⟨g,le_restrictOn hI y g hg,hfreq⟩
  apply Nat.le_antisymm
  · apply (ordinaryTraceOrder_cosupport_iff hN hI hi hx _).mp
    exact MarkedIdealOperationsAlong.cosupport_subset_of_restrictLe (restrictLe_self_restrictOn hI) _
      ((ordinaryTraceOrder_cosupport_iff hN hr hnz hx _).mpr le_rfl)
  · apply (ordinaryTraceOrder_cosupport_iff hN hr hnz hx _).mp
    exact MarkedIdealOperationsAlong.cosupport_subset_of_restrictLe restrictLe_restrictOn _
      ((ordinaryTraceOrder_cosupport_iff hN hI hi hx _).mpr le_rfl)

/-- Real finite-list induction supplies ALL geometry BEFORE the true order SUM. -/
theorem relativeIdealListProduct_actual_geometry {N : Set X} (hN : IsClosedSubmanifold n N)
    (L : List (GermIdeal n X))
    (hcoh : ∀ I ∈ L,I.IsCoherent) (hnz : ∀ I ∈ L,∀ x ∈ N,IsNonzeroAlongAt N I x)
    (hpr : ∀ I ∈ L,∀ x ∈ N,∃ f : X → ℂ,HolomorphicAt n f x ∧
      ∀ g,I.mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=f) x g) :
    (relativeIdealListProduct N L).IsCoherent ∧
    (∀ x ∈ N,IsNonzeroAlongAt N (relativeIdealListProduct N L) x) ∧
    (∀ x ∈ N,∃ f : X → ℂ,HolomorphicAt n f x ∧ ∀ g,(relativeIdealListProduct N L).mem x g ↔
      HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=f) x g) ∧
    ∀ x ∈ N,ordinaryTraceOrder N (relativeIdealListProduct N L) x=(L.map fun I => ordinaryTraceOrder N I x).sum := by
  induction L with
  | nil =>
    refine ⟨isCoherent_unitIdeal,?_,?_,?_⟩
    · intro x hx
      refine ⟨1,holomorphicAt_const 1,?_⟩
      apply frequently_iff.mpr
      intro U hU
      exact ⟨x,mem_of_mem_nhds hU,hx,one_ne_zero⟩
    · intro x _hx
      refine ⟨1,holomorphicAt_const 1,fun g => ?_⟩
      constructor
      · intro hg
        exact ⟨hg,isInSpanOnAt_eq_iff.mpr ⟨g,hg,Eventually.of_forall fun _ _ => by simp⟩⟩
      · exact fun hg => hg.1
    · intro x _hx
      have hnot : x ∉ NonmonomialOrderLocal.ordGe (ordinaryTraceMarked N (unitIdeal n X)) 1 := by
        rw [ordGe_ordinaryTraceMarked_eq_cosupport N _ isCoherent_unitIdeal,cosupport_unitIdeal (show 1≤1 from le_rfl)]
        simp
      exact Nat.eq_zero_of_le_zero (NonmonomialOrderLocal.nmOrd_le_of_notMem hnot)
  | cons I L ih =>
    have hI := hcoh I (by simp)
    have hi := hnz I (by simp)
    have hpI := hpr I (by simp)
    obtain ⟨hP,hp,hprP,hordP⟩ := ih (fun J hJ => hcoh J (List.mem_cons_of_mem _ hJ))
      (fun J hJ => hnz J (List.mem_cons_of_mem _ hJ)) (fun J hJ => hpr J (List.mem_cons_of_mem _ hJ))
    have hmul := isCoherent_mul hI hP
    have hnzMul : ∀ x ∈ N,IsNonzeroAlongAt N (I.mul (relativeIdealListProduct N L)) x := by
      intro x hx
      obtain ⟨f,hf,hfi⟩ := hpI x hx
      obtain ⟨g,hg,hgp⟩ := hprP x hx
      exact isNonzeroAlongAt_mul_of_relative_principal hN hI hP hi hp hx hf hg hfi hgp
    refine ⟨isCoherent_restrictOn hmul (VanishingIdealCoherent.isCoherent_vanishingIdeal hN),?_,?_,?_⟩
    · intro x hx
      obtain ⟨g,hg,hfreq⟩ := hnzMul x hx
      exact ⟨g,le_restrictOn hmul x g hg,hfreq⟩
    · intro x hx
      obtain ⟨f,hf,hfi⟩ := hpI x hx
      obtain ⟨g,hg,hgp⟩ := hprP x hx
      exact ⟨f*g,hf.mul hg,restrictOn_mul_relative_principal_mem_iff hf hg hfi hgp⟩
    · intro x hx
      obtain ⟨f,hf,hfi⟩ := hpI x hx
      obtain ⟨g,hg,hgp⟩ := hprP x hx
      change ordinaryTraceOrder N (restrictOn n N (I.mul (relativeIdealListProduct N L))) x = _
      rw [ordinaryTraceOrder_restrictOn_eq hN hmul hnzMul hx,
        ordinaryTraceOrder_mul_of_relative_principal hN hI hP hi hp hx hf hg hfi hgp,hordP x hx]
      rfl

/-- ONLY original finite-history data construct the TRUE full product and SUM. -/
theorem original_chronological_full_product_actual_geometry (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : NormalCrossings.IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T) :
    let N := (geoTransformAlong (geometricTemplate W []) T).N
    let P := chronologicalMemberProduct W E T
    P.IsCoherent ∧ (∀ y ∈ N,IsNonzeroAlongAt N P y) ∧
    (∀ y ∈ N,∃ f : Y → ℂ,HolomorphicAt n f y ∧ ∀ g,P.mem y g ↔
      HolomorphicAt n g y ∧ IsInSpanOnAt (n := n) N (·=f) y g) ∧
    ∀ y ∈ N,ordinaryTraceOrder N P y=
      ((chronologicalMemberFamily W E T).map fun I => ordinaryTraceOrder N I y).sum := by
  have hw : (geometricTemplate W []).IsWellFormed :=
    ⟨hW,isCoherent_unitIdeal,NormalCrossings.isSNCDivisor_nil,NormalCrossings.isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hN := (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw T hT).isClosedSubmanifold_N
  have hfam : ∀ I ∈ chronologicalMemberFamily W E T,I.IsCoherent ∧
      (∀ y ∈ (geoTransformAlong (geometricTemplate W []) T).N,IsNonzeroAlongAt (geoTransformAlong (geometricTemplate W []) T).N I y) ∧
      ∀ y ∈ (geoTransformAlong (geometricTemplate W []) T).N,∃ f : Y → ℂ,HolomorphicAt n f y ∧
        ∀ g,I.mem y g ↔ HolomorphicAt n g y ∧ IsInSpanOnAt (n := n) (geoTransformAlong (geometricTemplate W []) T).N (·=f) y g := by
    intro I hI
    obtain ⟨H,hH,rfl⟩ := List.mem_map.mp hI
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hH
    obtain ⟨hNi,_hEi,_hmi,hwi,hnzi,hpri⟩ := original_members_actual_finite_chronological_geometry hn hW hE hdense i T hT
    rw [hNi] at hnzi hpri
    exact ⟨hwi.isCoherent,hnzi,hpri⟩
  exact relativeIdealListProduct_actual_geometry hN (chronologicalMemberFamily W E T)
    (fun I hI => (hfam I hI).1) (fun I hI => (hfam I hI).2.1) (fun I hI => (hfam I hI).2.2)

end
end Hironaka.HironakaSharpActualFiniteMemberProduct
