/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualProductNewExceptionalFactor
import Hironaka.Resolution.HironakaSharpActualFiniteProductResidual

/-! Actual all-power relative product STRICT commutation. Independent actual
member-prime cancellation precedes TOTAL saturation comparison. Composite
original RAW TOTAL and modified invariant/history decrease remain OPEN. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualProductRelativeStrict
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualProductNewExceptionalFactor HironakaSharpActualRelativeProductTotal
  HironakaSharpActualRelativeProductOrder HironakaSharpActualFiniteMemberProduct
  HironakaSharpActualFiniteProductResidual HironakaSharpActualChronologicalNoOldFactor
  HironakaSharpActualChronologicalStrictStep HironakaSharpActualExceptionalPowerCancellation
  HironakaSharpOriginalFirstMemberRelativeStrict HironakaSharpActualFiniteChronologicalHistory
  RelativePrincipalizationSpan RestrictedIdealExtension RestrictedIdealQuotient
  MonomialPartAlong DivisorExponentAlong NormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal
  IdealWeightPowers InvertibleIdealQuotient GermIdealOrder
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Real member-prime and excluded-generator geometry cancels every true power. -/
theorem relative_principal_no_member_factor_power_colon (hn : 0 < n) {N : Set X} {E : List (Set X)}
    (hE : IsSNCDivisor n E) (hT : IsTransverse n N E) {J : GermIdeal n X}
    {x : X} (hx : x ∈ N) (c : X → ℂ) (hc : HolomorphicAt n c x)
    (hJgen : ∀ g,J.mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=c) x g)
    (i : Fin E.length)
    (hnd : x ∈ E.get i → ∃ v,J.mem x v ∧
      ¬IsInSpanOnAt (n := n) N ((vanishingIdeal (n := n) (E.get i)).mem x) x v)
    (k : ℕ) (g : X → ℂ) :
    (colonAlong n N J (idealPow (vanishingIdeal (n := n) (E.get i)) k)).mem x g ↔ J.mem x g := by
  have hcollapse (v : X → ℂ) (hv : (restrictOn n N J).mem x v) : J.mem x v :=
    (hJgen v).mpr ⟨hv.1,IsInSpanOnAt.trans (fun s hs => ((hJgen s).mp hs).2) hv.2⟩
  have hpowcoh := GermIdealPullbackCalculus.isCoherent_idealPow
    (VanishingIdealCoherent.isCoherent_vanishingIdeal (MonomialPart.isClosedSubmanifold_get hn hE i)) k
  constructor
  · rintro ⟨hg,hcolon⟩
    by_cases hxi : x ∈ E.get i
    · obtain ⟨a,ha,hA,U,hU,hxU,hnon⟩ := exists_actual_transverse_member_generator hn hE hT hx i hxi
      have hnot : ¬IsInSpanOnAt (n := n) N ((vanishingIdeal (n := n) (E.get i)).mem x) x c := by
        intro hcD
        obtain ⟨v,hv,hvnot⟩ := hnd hxi
        apply hvnot
        exact IsInSpanOnAt.trans (S := (·=c)) (T := (vanishingIdeal (n := n) (E.get i)).mem x)
          (fun s hs => hs ▸ hcD) ((hJgen v).mp hv).2
      have haD : (vanishingIdeal (n := n) (E.get i)).mem x a :=
        (hA a).mpr (InvertibleIdealQuotient.isInSpanAt_self rfl ha)
      have hpow := MonomialPart.pow_mem_idealPow haD ha k
      have hJpow := hcollapse _ (hcolon _ hpow)
      have hspan : IsInSpanOnAt (n := n) N (·=c) x ((fun y => a y^k)*g) := ((hJgen _).mp hJpow).2
      have hcancel : ∀ t : ℕ,∀ v : X → ℂ,HolomorphicAt n v x →
          IsInSpanOnAt (n := n) N (·=c) x ((fun y => a y^t)*v) →
          IsInSpanOnAt (n := n) N (·=c) x v := by
        intro t
        induction t with
        | zero =>
          intro v _hv hspan
          exact IsInSpanOnAt.congr_right hspan (Eventually.of_forall fun y _ => by simp)
        | succ t ih =>
          intro v hv hspan
          have hspan' : IsInSpanOnAt (n := n) N (·=c) x (a*((fun y => a y^t)*v)) := by
            refine IsInSpanOnAt.congr_right hspan (Eventually.of_forall fun y _ => ?_)
            change a y*(a y^t*v y)=a y^(t+1)*v y
            ring
          exact ih v hv (cancel_actual_member_factor hn hE hT hx i a c ha hc hA hU hxU hnon hnot _ (HolomorphicAt.mul (BlowupFunctionTransform.holomorphicAt_pow ha t) hv) hspan')
      exact (hJgen g).mpr ⟨hg,hcancel k g hg hspan⟩
    · have h1D : (vanishingIdeal (n := n) (E.get i)).mem x (1 : X → ℂ) := by
        refine ⟨holomorphicAt_const 1,?_⟩
        filter_upwards [(hE.1 _ (List.get_mem E i)).isOpen_compl.mem_nhds hxi] with y hy hyH
        exact False.elim (hy hyH)
      have h1pow : (idealPow (vanishingIdeal (n := n) (E.get i)) k).mem x (1 : X → ℂ) := by
        change (idealPow (vanishingIdeal (n := n) (E.get i)) k).mem x (fun _ => 1)
        simpa using MonomialPart.pow_mem_idealPow h1D (holomorphicAt_const 1) k
      have hh := hcollapse _ (hcolon _ h1pow)
      convert hh using 1
      funext y
      simp
  · intro hg
    refine ⟨((hJgen g).mp hg).1,fun a ha => ?_⟩
    have haHol := RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hpowcoh ha
    refine ⟨haHol.mul ((hJgen g).mp hg).1,?_⟩
    exact IsInSpanOnAt.mono (S := (·=c)) (fun v hv => (hJgen v).mpr
      ⟨hv ▸ hc,isInSpanOnAt_eq_iff.mpr ⟨1,holomorphicAt_const 1,Eventually.of_forall fun _ _ => by simp [hv]⟩⟩)
      (IsInSpanOnAt.mul_left haHol ((hJgen g).mp hg).2)

/-- Independently actual factor dictionaries plus TRUE cancellation identify
literal all-power saturation; no greatest-exponent claim is needed. -/
theorem relative_factor_saturation_mem_iff (hn : 0 < n) {N D : Set X}
    (hE : IsSNCDivisor n [D]) (hT : IsTransverse n N [D])
    {I J : GermIdeal n X} {x : X} (hx : x ∈ N) (e : ℕ)
    (hfac : ∀ g,I.mem x g ↔ (restrictOn n N ((idealPow (vanishingIdeal (n := n) D) e).mul J)).mem x g)
    (c : X → ℂ) (hc : HolomorphicAt n c x)
    (hgen : ∀ g,J.mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=c) x g)
    (hnd : x ∈ D → ∃ v,J.mem x v ∧ ¬IsInSpanOnAt (n := n) N ((vanishingIdeal (n := n) D).mem x) x v)
    (g : X → ℂ) : (relativeExceptionalSaturation N I D).mem x g ↔ J.mem x g := by
  have hpowcoh := GermIdealPullbackCalculus.isCoherent_idealPow
    (VanishingIdealCoherent.isCoherent_vanishingIdeal (MonomialPart.isClosedSubmanifold_get hn hE (0 : Fin [D].length))) e
  have hle (v : X → ℂ) (hv : I.mem x v) : J.mem x v := by
    obtain ⟨hvhol,hspan⟩ := (hfac v).mp hv
    apply (hgen v).mpr
    refine ⟨hvhol,IsInSpanOnAt.trans (fun b hb => ?_) hspan⟩
    change IsInSpanAt (n := n) (fun s => ∃ a b,(idealPow (vanishingIdeal (n := n) D) e).mem x a ∧ J.mem x b ∧ s=a*b) x b at hb
    refine IsInSpanOnAt.trans (fun v hv => ?_) (IsInSpanAt.restrict hb)
    obtain ⟨a,b,ha,hb,rfl⟩ := hv
    exact IsInSpanOnAt.mul_left (RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hpowcoh ha) ((hgen b).mp hb).2
  constructor
  · rintro ⟨k,hg,hcolon⟩
    apply (relative_principal_no_member_factor_power_colon hn hE hT hx c hc hgen
      (0 : Fin [D].length) hnd k g).mp
    refine ⟨hg,fun a ha => ?_⟩
    obtain ⟨hv,hspan⟩ := hcolon a ha
    exact ⟨hv,IsInSpanOnAt.mono (fun s hs => hle s hs) hspan⟩
  · intro hg
    have hghol := ((hgen g).mp hg).1
    refine ⟨e,hghol,fun a ha => ?_⟩
    have haHol := RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hpowcoh ha
    have hp : ((idealPow (vanishingIdeal (n := n) D) e).mul J).mem x (a*g) := by
      change IsInSpanAt (n := n) (fun s => ∃ a b,(idealPow (vanishingIdeal (n := n) D) e).mem x a ∧ J.mem x b ∧ s=a*b) x (a*g)
      exact isInSpanAt_self ⟨a,g,ha,hg,rfl⟩ (haHol.mul hghol)
    have hi : I.mem x (a*g) := (hfac _).mpr
      ⟨haHol.mul hghol,IsInSpanAt.restrict (isInSpanAt_self hp (haHol.mul hghol))⟩
    exact ⟨haHol.mul hghol,IsInSpanAt.restrict (isInSpanAt_self hi (haHol.mul hghol))⟩

private theorem relative_product_off_carrier {N : Set Y} (hN : IsClosed N) {y : Y} (hy : y ∉ N)
    (L : List (GermIdeal n Y)) (g : Y → ℂ) :
    (relativeIdealListProduct N L).mem y g ↔ HolomorphicAt n g y := by
  cases L with
  | nil => exact Iff.rfl
  | cons I L => exact ⟨fun h => h.1,fun hg => restrictOn_eq_top_of_disjoint hN.isOpen_compl hy (by simp) hg⟩

/-- Genuine WHOLE next STRICT/product equality from actual source ideal geometry. -/
theorem nextRelativeStrict_relative_product_eq (hn : 0 < n) {N C : Set X}
    (hN : IsClosedSubmanifold n N) {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N)
    (L : List (GermIdeal n X)) (hcoh : ∀ I ∈ L,I.IsCoherent)
    (hnz : ∀ I ∈ L,∀ x ∈ N,IsNonzeroAlongAt N I x)
    (hpr : ∀ I ∈ L,∀ x ∈ N,∃ f : X → ℂ,HolomorphicAt n f x ∧ ∀ g,I.mem x g ↔
      HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=f) x g) :
    nextRelativeStrict N (relativeIdealListProduct N L) C π=
      relativeIdealListProduct (BlowupStrictSubmanifold.geoStrictTransform π C N)
        (L.map fun I => nextRelativeStrict N I C π) := by
  let N' := BlowupStrictSubmanifold.geoStrictTransform π C N
  let D := π ⁻¹' C
  let S := relativeIdealListProduct N' (L.map fun I => nextRelativeStrict N I C π)
  let M : MarkedIdeal n X := ⟨N,[],unitIdeal n X,0⟩
  have hwM : M.IsWellFormed := ⟨hN,isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hN⟩
  have hadm : M.IsAdmissibleCentre C := by
    refine ⟨hπ.1,?_,hasNormalCrossings_nil_of_isClosedSubmanifold hπ.1⟩
    change C ⊆ cosupport n N (unitIdeal n X) 0
    rw [cosupport_zero (fun _ _ hg => hg)]
    exact hCN
  have hwNew := GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hwM hadm hπ
  have hN' : IsClosedSubmanifold n N' := hwNew.isClosedSubmanifold_N
  have hE' : IsSNCDivisor n [D] := hwNew.isSNCDivisor
  have hT' : IsTransverse n N' [D] := hwNew.isTransverse
  have hEach (I : GermIdeal n X) (hI : I ∈ L) := nextRelativeStrict_actual_geometry hn hN (hcoh I hI) (hnz I hI) (hpr I hI) hπ hCN
  have hCohS : ∀ I ∈ L.map (fun I => nextRelativeStrict N I C π),I.IsCoherent := by
    intro I hI
    obtain ⟨J,hJ,rfl⟩ := List.mem_map.mp hI
    exact (hEach J hJ).2.1
  have hNzS : ∀ I ∈ L.map (fun I => nextRelativeStrict N I C π),∀ y ∈ N',IsNonzeroAlongAt N' I y := by
    intro I hI
    obtain ⟨J,hJ,rfl⟩ := List.mem_map.mp hI
    exact (hEach J hJ).2.2.1
  have hPrS : ∀ I ∈ L.map (fun I => nextRelativeStrict N I C π),∀ y ∈ N',∃ f : Y → ℂ,HolomorphicAt n f y ∧
      ∀ g,I.mem y g ↔ HolomorphicAt n g y ∧ IsInSpanOnAt (n := n) N' (·=f) y g := by
    intro I hI
    obtain ⟨J,hJ,rfl⟩ := List.mem_map.mp hI
    intro y hy
    obtain ⟨f,hf,hgen⟩ := (hEach J hJ).2.2.2.1 y hy
    exact ⟨f,((hgen f).mp hf).1,hgen⟩
  have hNotS : ∀ I ∈ L.map (fun I => nextRelativeStrict N I C π),∀ y ∈ N',∀ i : Fin [D].length,y ∈ [D].get i →
      ∃ a,I.mem y a ∧ ¬IsInSpanOnAt (n := n) N' ((vanishingIdeal (n := n) ([D].get i)).mem y) y a := by
    intro I hI
    obtain ⟨J,hJ,rfl⟩ := List.mem_map.mp hI
    intro y hy i hyi
    exact nextRelativeStrict_no_accumulated_member_factor hn hN isSNCDivisor_nil
      (isTransverse_nil_of_isClosedSubmanifold hN) (hcoh J hJ) (hnz J hJ) (hpr J hJ) hπ hCN
      (hasNormalCrossings_nil_of_isClosedSubmanifold hπ.1) (fun _ _ i => Fin.elim0 i) hy i hyi
  obtain ⟨_hcS,_hnzS,hprS,_hordS⟩ := relativeIdealListProduct_actual_geometry hN' _ hCohS hNzS hPrS
  have hndS := relativeIdealListProduct_no_member_factor hn hE' hT' _ hCohS hNotS
  have hfac := next_relative_product_whole_exceptional_factor_sum hn hN hπ hCN L hcoh hnz hpr
  have hTot : (nextTotalMarked N (relativeIdealListProduct N L) C π).ideal=
      restrictOn n N' (GermIdeal.pullback (m := n) π (relativeIdealListProduct N L)) :=
    HironakaSharpOriginalFirstMemberExceptionalFactor.geoTransform_zeroMark_ideal_eq_restricted_total
      (⟨N,[],relativeIdealListProduct N L,0⟩ : MarkedIdeal n X) rfl C π
  ext y g
  change (relativeExceptionalSaturation N' (GermIdeal.pullback (m := n) π (relativeIdealListProduct N L)) D).mem y g ↔ S.mem y g
  by_cases hy : y ∈ N'
  · obtain ⟨c,hc,hgen⟩ := hprS y hy
    have heq := relative_factor_saturation_mem_iff hn hE' hT' hy
      (L.map fun I => HironakaSharpOriginalFirstMemberWholeFactor.singleExceptionalExponent N'
        (nextTotalMarked N I C π).ideal D y).sum (hfac y) c hc hgen
      (fun hyD => hndS y hy (0 : Fin [D].length) hyD) g
    rw [hTot] at heq
    exact (relativeExceptionalSaturation_restrictOn_mem_iff _ _ _ y g).symm.trans heq
  · have hSat : (relativeExceptionalSaturation N' (GermIdeal.pullback (m := n) π (relativeIdealListProduct N L)) D).mem y g ↔ HolomorphicAt n g y := by
      refine ⟨fun hg => hg.choose_spec.1,fun hg => ?_⟩
      exact ⟨0,hg,fun a ha => restrictOn_eq_top_of_disjoint hN'.1.isOpen_compl hy (by simp) (ha.mul hg)⟩
    exact hSat.trans (relative_product_off_carrier hN'.1 hy _ g).symm

/-- ONLY original actual finite histories supply every current ideal premise. -/
theorem original_next_chronological_product_eq_full_relative_strict (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    {Z : CMfd.{u} n} (T : BlowupTower X Z) (ht : IsGeoTestTower (geometricTemplate W []) T)
    {C : Set Z} {π : Y → Z} (hπ : IsBlowupAlong n C π)
    (hCN : C ⊆ (geoTransformAlong (geometricTemplate W []) T).N) :
    nextRelativeStrict (geoTransformAlong (geometricTemplate W []) T).N (chronologicalMemberProduct W E T) C π=
      chronologicalMemberProduct W E (.step T C π hπ) := by
  have hw : (geometricTemplate W []).IsWellFormed :=
    ⟨hW,isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hwT := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw T ht
  have hfam : ∀ I ∈ chronologicalMemberFamily W E T,I.IsCoherent ∧
      (∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,IsNonzeroAlongAt
        (geoTransformAlong (geometricTemplate W []) T).N I x) ∧
      ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,∃ f : Z → ℂ,HolomorphicAt n f x ∧
        ∀ g,I.mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) (geoTransformAlong (geometricTemplate W []) T).N (·=f) x g := by
    intro I hI
    obtain ⟨H,hH,rfl⟩ := List.mem_map.mp hI
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hH
    obtain ⟨hNi,_hEi,_hmi,hwi,hnzi,hpri⟩ := original_members_actual_finite_chronological_geometry hn hW hE hdense i T ht
    rw [hNi] at hnzi hpri
    exact ⟨hwi.isCoherent,hnzi,hpri⟩
  rw [chronological_product_next_eq E T hπ]
  exact nextRelativeStrict_relative_product_eq hn hwT.isClosedSubmanifold_N hπ hCN _
    (fun I hI => (hfam I hI).1) (fun I hI => (hfam I hI).2.1) (fun I hI => (hfam I hI).2.2)

end
end Hironaka.HironakaSharpActualProductRelativeStrict
