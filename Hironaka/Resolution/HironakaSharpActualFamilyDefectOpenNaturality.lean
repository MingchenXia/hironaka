/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualDistinctCountOpenNaturality
/-! Whole literal relative products and dynamic FIRST defects on actual opens.
Original positions and actual auxiliary/born ordered lists remain separate. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualFamilyDefectOpenNaturality
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaSharpActualDistinctCountOpenNaturality HironakaSharpActualChronologicalOpenNaturality
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualChronologicalDistinctDefect
  HironakaSharpActualFiniteMemberProduct HironakaSharpOriginalProductTraceOrder
  RelativePrincipalizationSpan RestrictedIdealExtension IdealWeightPowers
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen GermIdealPullbackCalculus NonmonomialOrderLocal NormalCrossings
variable {n m : ℕ} {X : CMfd.{u} n}

/-- Actual finite product spans, in BOTH entire coherent open directions. -/
theorem coherent_mul_open {I J : GermIdeal n X} (hI : I.IsCoherent) (hJ : J.IsCoherent) (U : Opens X) :
    GermIdeal.pullback (m := n) (Subtype.val : U → X) (I.mul J)=
      (GermIdeal.pullback (m := n) (Subtype.val : U → X) I).mul
        (GermIdeal.pullback (m := n) (Subtype.val : U → X) J) := by
  apply GermIdeal.ext
  funext x g
  apply propext
  rw [mem_pullback_val_iff U (isCoherent_mul hI hJ)]
  constructor
  · rintro ⟨hhol,K,s,a,hs,ha,heq⟩
    refine ⟨(holomorphicAt_iff_extendOpens U).mpr hhol,K,
      fun i => s i ∘ Subtype.val,fun i => a i ∘ Subtype.val,?_,?_,?_⟩
    · intro i
      obtain ⟨p,q,hp,hq,he⟩ := hs i
      exact ⟨p ∘ Subtype.val,q ∘ Subtype.val,comp_val_mem_pullback_val U hI hp,
        comp_val_mem_pullback_val U hJ hq,by
          funext y
          change s i y.val=p y.val*q y.val
          exact congrFun he y.val⟩
    · intro i
      exact (holomorphicAt_comp_val_iff U).mpr (ha i)
    · have h := (eventually_nhds_val_iff U).mp heq
      filter_upwards [h] with y hy
      simpa only [extendOpens_val,Function.comp_apply] using hy
  · rintro ⟨hhol,K,s,a,hs,ha,heq⟩
    choose p q hp hq hprod using hs
    refine ⟨(holomorphicAt_iff_extendOpens U).mp hhol,K,
      fun i => extendOpens U (p i)*extendOpens U (q i),fun i => extendOpens U (a i),?_,?_,?_⟩
    · intro i
      exact ⟨extendOpens U (p i),extendOpens U (q i),(mem_pullback_val_iff U hI).mp (hp i),
        (mem_pullback_val_iff U hJ).mp (hq i),rfl⟩
    · intro i
      exact (holomorphicAt_iff_extendOpens U).mp (ha i)
    · apply (eventually_nhds_val_iff U).mpr
      filter_upwards [heq] with y hy
      simpa only [extendOpens_val,hprod,Pi.mul_apply] using hy

private theorem restrictOn_open {N : Set X} (hN : IsClosedSubmanifold n N)
    {I : GermIdeal n X} (hI : I.IsCoherent) (U : Opens X) :
    GermIdeal.pullback (m := n) (Subtype.val : U → X) (restrictOn n N I)=
      restrictOn n ((Subtype.val : U → X) ⁻¹' N) (GermIdeal.pullback (m := n) (Subtype.val : U → X) I) := by
  apply GermIdeal.ext
  funext x g
  apply propext
  rw [mem_pullback_val_iff U (isCoherent_restrictOn hI (VanishingIdealCoherent.isCoherent_vanishingIdeal hN))]
  exact (restrictOn_pullback_val_iff U hI).symm

private theorem unit_open (U : Opens X) :
    GermIdeal.pullback (m := n) (Subtype.val : U → X) (unitIdeal n X)=unitIdeal n U := by
  apply GermIdeal.ext
  funext x g
  apply propext
  rw [mem_pullback_val_iff U isCoherent_unitIdeal]
  exact (holomorphicAt_iff_extendOpens U).symm

private theorem relative_product_coherent {N : Set X} (hN : IsClosedSubmanifold n N)
    (L : List (GermIdeal n X)) (hc : ∀ I∈L,I.IsCoherent) : (relativeIdealListProduct N L).IsCoherent := by
  induction L with
  | nil => exact isCoherent_unitIdeal
  | cons I L ih =>
    exact isCoherent_restrictOn (isCoherent_mul (hc I (by simp))
      (ih (fun J hJ => hc J (List.mem_cons_of_mem I hJ)))) (VanishingIdealCoherent.isCoherent_vanishingIdeal hN)

/-- ENTIRE actual recursively carrier-relative finite product identity. -/
theorem relativeIdealListProduct_open {N : Set X} (hN : IsClosedSubmanifold n N)
    (L : List (GermIdeal n X)) (hc : ∀ I∈L,I.IsCoherent) (U : Opens X) :
    GermIdeal.pullback (m := n) (Subtype.val : U → X) (relativeIdealListProduct N L)=
      relativeIdealListProduct (X := CMfd.of (n := n) U) ((Subtype.val : U → X) ⁻¹' N)
        (L.map fun I => GermIdeal.pullback (m := n) (Subtype.val : U → X) I) := by
  induction L with
  | nil => exact unit_open U
  | cons I L ih =>
    have hI := hc I (by simp)
    have hL := fun J hJ => hc J (List.mem_cons_of_mem I hJ)
    change GermIdeal.pullback (m := n) (Subtype.val : U → X)
      (restrictOn n N (I.mul (relativeIdealListProduct N L)))=
      restrictOn n ((Subtype.val : U → X) ⁻¹' N)
        ((GermIdeal.pullback (m := n) (Subtype.val : U → X) I).mul
          (relativeIdealListProduct (X := CMfd.of (n := n) U) ((Subtype.val : U → X) ⁻¹' N)
            (L.map fun J => GermIdeal.pullback (m := n) (Subtype.val : U → X) J)))
    rw [restrictOn_open hN (isCoherent_mul hI (relative_product_coherent hN L hL)),
      coherent_mul_open hI (relative_product_coherent hN L hL),ih hL]

/-- True whole product order follows actual whole ideal equality, not an order certificate. -/
theorem actual_family_product_order_open (hn : 0<n) {N : Set X} (hN : IsClosedSubmanifold n N)
    (F : Fin m → GermIdeal n X) (hc : ∀ i,(F i).IsCoherent)
    (hnz : ∀ i,∀ y∈N,DivisorExponentAlong.IsNonzeroAlongAt N (F i) y)
    (hpr : ∀ i,∀ y∈N,∃ f : X → ℂ,HolomorphicAt n f y ∧
      ∀ g,(F i).mem y g ↔ HolomorphicAt n g y ∧ IsInSpanOnAt (n := n) N (·=f) y g)
    (U : Opens X) (x : U) :
    ordinaryTraceOrder (X := CMfd.of (n := n) U) ((Subtype.val : U → X) ⁻¹' N)
      (relativeIdealListProduct (X := CMfd.of (n := n) U) ((Subtype.val : U → X) ⁻¹' N)
        (List.ofFn fun i => GermIdeal.pullback (m := n) (Subtype.val : U → X) (F i))) x=
      ordinaryTraceOrder N (relativeIdealListProduct N (List.ofFn F)) x.val := by
  have hList : ∀ I∈List.ofFn F,I.IsCoherent ∧ (∀ y∈N,DivisorExponentAlong.IsNonzeroAlongAt N I y) ∧
      ∀ y∈N,∃ f : X → ℂ,HolomorphicAt n f y ∧
        ∀ g,I.mem y g ↔ HolomorphicAt n g y ∧ IsInSpanOnAt (n := n) N (·=f) y g := by
    intro I hI
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hI
    exact ⟨hc i,hnz i,hpr i⟩
  obtain ⟨hP,hNz,_⟩ := relativeIdealListProduct_actual_geometry hN (List.ofFn F)
    (fun I hI => (hList I hI).1) (fun I hI => (hList I hI).2.1) (fun I hI => (hList I hI).2.2)
  have hOrder := nmOrd_pullback_val hn (ordinaryTraceMarked_isWellFormed hN hP) hNz U x
  have hProd := relativeIdealListProduct_open hN (List.ofFn F) (fun I hI => (hList I hI).1) U
  rw [List.map_ofFn] at hProd
  have hRecord : MarkedIdeal.pullback (Subtype.val : U → X)
      (ordinaryTraceMarked N (relativeIdealListProduct N (List.ofFn F)))=
      ordinaryTraceMarked (X := CMfd.of (n := n) U) ((Subtype.val : U → X) ⁻¹' N)
        (relativeIdealListProduct (X := CMfd.of (n := n) U) ((Subtype.val : U → X) ⁻¹' N)
          (List.ofFn fun i => GermIdeal.pullback (m := n) (Subtype.val : U → X) (F i))) :=
    MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl hProd rfl
  rw [hRecord] at hOrder
  exact hOrder

/-- Literal TRUE quotient-count versus product-order defect, at EVERY ambient point. -/
theorem actual_family_distinct_defect_open (hn : 0<n) {N : Set X} (hN : IsClosedSubmanifold n N)
    (F : Fin m → GermIdeal n X) (hc : ∀ i,(F i).IsCoherent)
    (hnz : ∀ i,∀ y∈N,DivisorExponentAlong.IsNonzeroAlongAt N (F i) y)
    (hpr : ∀ i,∀ y∈N,∃ f : X → ℂ,HolomorphicAt n f y ∧
      ∀ g,(F i).mem y g ↔ HolomorphicAt n g y ∧ IsInSpanOnAt (n := n) N (·=f) y g) (U : Opens X) :
    actualFamilyDistinctDefect (X := CMfd.of (n := n) U) ((Subtype.val : U → X) ⁻¹' N)
      (fun i => GermIdeal.pullback (m := n) (Subtype.val : U → X) (F i))=
        (Subtype.val : U → X) ⁻¹' actualFamilyDistinctDefect N F := by
  ext x
  change (x.val∈N ∧ _ < _) ↔ (x.val∈N ∧ _ < _)
  rw [actual_distinct_proper_count_open F hc U x,actual_family_product_order_open hn hN F hc hnz hpr U x]

/-- ONLY original inputs supply carrier, every ideal and the literal full dynamic FIRST-open dictionary. -/
theorem original_chronological_distinct_defect_open (hn : 0<n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E) (hdense : W⊆closure (W \ ⋃ H∈E,H))
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T) (U : Opens X) :
    actualFamilyDistinctDefect (X := CMfd.of (n := n) (openPreimage T U))
      (geoTransformAlong (geometricTemplate (X := CMfd.of (n := n) U) ((Subtype.val : U → X) ⁻¹' W) []) (restrict U T)).N
      (fun i : Fin E.length => (chronologicalMarked (originalRelativeMemberMarked (X := CMfd.of (n := n) U)
        ((Subtype.val : U → X) ⁻¹' W) ((Subtype.val : U → X) ⁻¹' E.get i)) (restrict U T)).ideal)=
      (Subtype.val : openPreimage T U → Y) ⁻¹' chronologicalDistinctDefect W E T := by
  let N := (geoTransformAlong (geometricTemplate W []) T).N
  let F := fun i : Fin E.length => (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
  have hN := (isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hW isCoherent_unitIdeal T hT).1
  have hfam : ∀ i,(F i).IsCoherent ∧ (∀ y∈N,DivisorExponentAlong.IsNonzeroAlongAt N (F i) y) ∧
      ∀ y∈N,∃ f : Y → ℂ,HolomorphicAt n f y ∧
        ∀ g,(F i).mem y g ↔ HolomorphicAt n g y ∧ IsInSpanOnAt (n := n) N (·=f) y g := by
    intro i
    obtain ⟨hNi,_hEi,_hmi,hwi,hnzi,hpri⟩ := original_members_actual_finite_chronological_geometry hn hW hE hdense i T hT
    rw [hNi] at hnzi hpri
    exact ⟨hwi.isCoherent,hnzi,hpri⟩
  have hInitial : MarkedIdeal.pullback (Subtype.val : U → X) (geometricTemplate W [])=
      geometricTemplate (X := CMfd.of (n := n) U) ((Subtype.val : U → X) ⁻¹' W) [] :=
    MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl (unit_open U) rfl
  have hGeo := geoTransformAlong_restrict U hW isCoherent_unitIdeal T hT
  rw [hInitial] at hGeo
  have hCarrier := congrArg MarkedIdeal.N hGeo
  have hFamily : (fun i => GermIdeal.pullback (m := n) (Subtype.val : openPreimage T U → Y) (F i))=
      (fun i : Fin E.length => (chronologicalMarked (originalRelativeMemberMarked (X := CMfd.of (n := n) U)
        ((Subtype.val : U → X) ⁻¹' W) ((Subtype.val : U → X) ⁻¹' E.get i)) (restrict U T)).ideal) := by
    funext i
    exact congrArg MarkedIdeal.ideal (original_members_chronological_open hn hW hE hdense i T hT U)
  rw [←hFamily,hCarrier]
  exact actual_family_distinct_defect_open hn hN F (fun i => (hfam i).1)
    (fun i => (hfam i).2.1) (fun i => (hfam i).2.2) (openPreimage T U)

private theorem actual_family_length_transport {a b : ℕ} (h : a=b)
    (N : Set X) (F : Fin b → GermIdeal n X) :
    actualFamilyDistinctDefect N (fun i : Fin a => F (Fin.cast h i))=actualFamilyDistinctDefect N F := by
  cases h
  rfl

/-- The canonical independently mapped finite list, with genuine whole length transport. -/
theorem chronologicalDistinctDefect_open (hn : 0<n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E) (hdense : W⊆closure (W \ ⋃ H∈E,H))
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T) (U : Opens X) :
    chronologicalDistinctDefect (X := CMfd.of (n := n) U) ((Subtype.val : U → X) ⁻¹' W)
      (E.map ((Subtype.val : U → X) ⁻¹' ·)) (restrict U T)=
        (Subtype.val : openPreimage T U → Y) ⁻¹' chronologicalDistinctDefect W E T := by
  let EU := E.map ((Subtype.val : U → X) ⁻¹' ·)
  let NU := (geoTransformAlong (geometricTemplate (X := CMfd.of (n := n) U)
    ((Subtype.val : U → X) ⁻¹' W) []) (restrict U T)).N
  let F := fun i : Fin E.length => (chronologicalMarked (originalRelativeMemberMarked (X := CMfd.of (n := n) U)
    ((Subtype.val : U → X) ⁻¹' W) ((Subtype.val : U → X) ⁻¹' E.get i)) (restrict U T)).ideal
  have hLen : EU.length=E.length := List.length_map _
  have hFamily : (fun i : Fin EU.length => (chronologicalMarked (originalRelativeMemberMarked (X := CMfd.of (n := n) U)
      ((Subtype.val : U → X) ⁻¹' W) (EU.get i)) (restrict U T)).ideal)=
      (fun i : Fin EU.length => F (Fin.cast hLen i)) := by
    funext i
    simp only [EU,F,List.get_eq_getElem,List.getElem_map,Fin.val_cast]
  change actualFamilyDistinctDefect (X := CMfd.of (n := n) (openPreimage T U)) NU
    (fun i : Fin EU.length => (chronologicalMarked (originalRelativeMemberMarked (X := CMfd.of (n := n) U)
      ((Subtype.val : U → X) ⁻¹' W) (EU.get i)) (restrict U T)).ideal)=_
  rw [hFamily,actual_family_length_transport hLen NU F]
  exact original_chronological_distinct_defect_open hn hW hE hdense T hT U

end
end Hironaka.HironakaSharpActualFamilyDefectOpenNaturality
