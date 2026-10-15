/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualRelativeProductTotal

/-! Genuine single-step TOTAL product factorization with the SUM of actual
individual normalized NEW exceptional exponents. Greatest/composite comparison
and modified original-invariant decrease remain independent OPEN producers. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualProductNewExceptionalFactor
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualRelativeProductTotal HironakaSharpActualRelativeProductOrder
  HironakaSharpActualFiniteMemberProduct HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpActualChronologicalStrictStep HironakaSharpOriginalMemberProduct
  HironakaSharpOriginalProductTraceOrder HironakaSharpOriginalFirstMemberWholeFactor
  RelativePrincipalizationSpan RestrictedIdealExtension MonomialPartAlong InvertibleIdealQuotient
  IdealWeightPowers MarkedIdeals MarkedIdeals.MarkedIdeal BlowupStrictSubmanifold NormalCrossings
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- True ambient power ideals have the SAME actual generator power, including0. -/
theorem idealPow_principal_mem_iff {D : GermIdeal n X} {x : X} {a : X → ℂ}
    (ha : HolomorphicAt n a x) (hD : ∀ g,D.mem x g ↔ IsInSpanAt (n := n) (·=a) x g) :
    ∀ e g,(idealPow D e).mem x g ↔ IsInSpanAt (n := n) (·=a^e) x g := by
  intro e
  induction e with
  | zero => exact unit_mem_iff_principal
  | succ e ih =>
    exact mul_mem_iff_principal (BlowupDerivativeIdeal.holomorphicAt_pow ha e) ha ih hD

/-- A true ambient left generator and actual relative right generator multiply
in BOTH normalized directions, preserving every carrier-normal germ. -/
theorem normalized_product_ambient_relative_principal {N : Set X} {I J : GermIdeal n X}
    {x : X} {f g : X → ℂ} (hf : HolomorphicAt n f x) (hg : HolomorphicAt n g x)
    (hIf : ∀ a,I.mem x a ↔ IsInSpanAt (n := n) (·=f) x a)
    (hJg : ∀ a,J.mem x a ↔ HolomorphicAt n a x ∧ IsInSpanOnAt (n := n) N (·=g) x a) :
    ∀ a,(restrictOn n N (I.mul J)).mem x a ↔ HolomorphicAt n a x ∧ IsInSpanOnAt (n := n) N (·=f*g) x a := by
  intro a
  constructor
  · rintro ⟨ha,hspan⟩
    refine ⟨ha,IsInSpanOnAt.trans (fun b hb => ?_) hspan⟩
    change IsInSpanAt (n := n) (fun s => ∃ b c,I.mem x b ∧ J.mem x c ∧ s=b*c) x b at hb
    refine IsInSpanOnAt.trans (fun v hv => ?_) (IsInSpanAt.restrict hb)
    obtain ⟨b,c,hb,hc,rfl⟩ := hv
    obtain ⟨_hb,s,hs,hbs⟩ := isInSpanAt_eq_iff.mp ((hIf b).mp hb)
    obtain ⟨t,ht,hct⟩ := isInSpanOnAt_eq_iff.mp ((hJg c).mp hc).2
    refine isInSpanOnAt_eq_iff.mpr ⟨s*t,hs.mul ht,?_⟩
    filter_upwards [hbs,hct] with y hyb hyc hyN
    change b y*c y=(s y*t y)*(f y*g y)
    rw [hyb,hyc hyN]
    ring
  · rintro ⟨ha,hspan⟩
    have hfI := (hIf f).mpr (isInSpanAt_eq_iff.mpr ⟨hf,1,holomorphicAt_const 1,Eventually.of_forall fun _ => by simp⟩)
    have hgJ := (hJg g).mpr ⟨hg,isInSpanOnAt_eq_iff.mpr ⟨1,holomorphicAt_const 1,Eventually.of_forall fun _ _ => by simp⟩⟩
    have hp : (I.mul J).mem x (f*g) := by
      change IsInSpanAt (n := n) (fun s => ∃ b c,I.mem x b ∧ J.mem x c ∧ s=b*c) x (f*g)
      exact isInSpanAt_self ⟨f,g,hfI,hgJ,rfl⟩ (hf.mul hg)
    exact ⟨ha,IsInSpanOnAt.mono (S := (·=f*g)) (fun b hb => hb ▸ hp) hspan⟩

private theorem unit_relative_principal (N : Set X) (x : X) :
    ∀ a,(unitIdeal n X).mem x a ↔ HolomorphicAt n a x ∧ IsInSpanOnAt (n := n) N (·=(1 : X → ℂ)) x a := by
  intro a
  exact ⟨fun ha => ⟨ha,isInSpanOnAt_eq_iff.mpr ⟨a,ha,Eventually.of_forall fun _ _ => by simp⟩⟩,fun ha => ha.1⟩

private theorem exists_product_generator (N : Set X) (L : List (GermIdeal n X)) (x : X)
    (hp : ∀ I ∈ L,∃ f : X → ℂ,HolomorphicAt n f x ∧ ∀ a,I.mem x a ↔ HolomorphicAt n a x ∧ IsInSpanOnAt (n := n) N (·=f) x a) :
    ∃ f : X → ℂ,HolomorphicAt n f x ∧ ∀ a,(relativeIdealListProduct N L).mem x a ↔ HolomorphicAt n a x ∧ IsInSpanOnAt (n := n) N (·=f) x a := by
  induction L with
  | nil => exact ⟨1,holomorphicAt_const 1,unit_relative_principal N x⟩
  | cons I L ih =>
    obtain ⟨f,hf,hfi⟩ := hp I (by simp)
    obtain ⟨g,hg,hgp⟩ := ih (fun J hJ => hp J (List.mem_cons_of_mem _ hJ))
    exact ⟨f*g,hf.mul hg,restrictOn_mul_relative_principal_mem_iff hf hg hfi hgp⟩

/-- Real finite factor algebra sums ACTUAL exponents before full factor claims. -/
theorem relative_product_factor_power_sum {N : Set X} {D : GermIdeal n X} {x : X} {a : X → ℂ}
    (ha : HolomorphicAt n a x) (hD : ∀ g,D.mem x g ↔ IsInSpanAt (n := n) (·=a) x g)
    {α : Type*} (L : List α) (F S : α → GermIdeal n X) (e : α → ℕ)
    (hfac : ∀ I ∈ L,∀ g,(F I).mem x g ↔ (restrictOn n N ((idealPow D (e I)).mul (S I))).mem x g)
    (hpr : ∀ I ∈ L,∃ c : X → ℂ,HolomorphicAt n c x ∧ ∀ g,(S I).mem x g ↔
      HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=c) x g) :
    ∀ g,(relativeIdealListProduct N (L.map F)).mem x g ↔
      (restrictOn n N ((idealPow D (L.map e).sum).mul (relativeIdealListProduct N (L.map S)))).mem x g := by
  induction L with
  | nil =>
    have hh := normalized_product_ambient_relative_principal (holomorphicAt_const (n := n) (x := x) 1)
      (holomorphicAt_const 1) (unit_mem_iff_principal (n := n) (x := x)) (unit_relative_principal N x)
    intro g
    have hg : (restrictOn n N ((unitIdeal n X).mul (unitIdeal n X))).mem x g ↔
        HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=(1 : X → ℂ)*1) x g := hh g
    rw [one_mul] at hg
    exact (unit_relative_principal N x g).trans hg.symm
  | cons I L ih =>
    obtain ⟨c,hc,hcgen⟩ := hpr I (by simp)
    have hprL := fun J hJ => hpr J (List.mem_cons_of_mem _ hJ)
    obtain ⟨b,hb,hbgen⟩ := exists_product_generator N (L.map S) x (by
      intro J hJ
      obtain ⟨K,hK,rfl⟩ := List.mem_map.mp hJ
      exact hprL K hK)
    have htail := ih (fun J hJ => hfac J (List.mem_cons_of_mem _ hJ)) hprL
    have hehol := BlowupDerivativeIdeal.holomorphicAt_pow ha (e I)
    have hshol := BlowupDerivativeIdeal.holomorphicAt_pow ha (L.map e).sum
    have hHead : ∀ g,(F I).mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=a^(e I)*c) x g :=
      fun g => (hfac I (by simp) g).trans (normalized_product_ambient_relative_principal hehol hc (idealPow_principal_mem_iff ha hD (e I)) hcgen g)
    have hTail : ∀ g,(relativeIdealListProduct N (L.map F)).mem x g ↔ HolomorphicAt n g x ∧
        IsInSpanOnAt (n := n) N (·=a^((L.map e).sum)*b) x g := fun g => (htail g).trans
      (normalized_product_ambient_relative_principal hshol hb (idealPow_principal_mem_iff ha hD _) hbgen g)
    have hLeft := restrictOn_mul_relative_principal_mem_iff (hehol.mul hc) (hshol.mul hb) hHead hTail
    have hNext := restrictOn_mul_relative_principal_mem_iff hc hb hcgen hbgen
    have hRight := normalized_product_ambient_relative_principal
      (BlowupDerivativeIdeal.holomorphicAt_pow ha (e I+(L.map e).sum)) (hc.mul hb)
      (idealPow_principal_mem_iff ha hD _) hNext
    have hmul : (a^(e I)*c)*(a^((L.map e).sum)*b)=a^(e I+(L.map e).sum)*(c*b) := by
      funext y
      simp only [Pi.mul_apply,Pi.pow_apply,pow_add]
      ring
    change ∀ g,(restrictOn n N ((F I).mul (relativeIdealListProduct N (L.map F)))).mem x g ↔
      HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=(a^(e I)*c)*(a^((L.map e).sum)*b)) x g at hLeft
    change ∀ g,(restrictOn n N ((idealPow D (e I+(L.map e).sum)).mul
      (relativeIdealListProduct N ((I::L).map S)))).mem x g ↔ HolomorphicAt n g x ∧
        IsInSpanOnAt (n := n) N (·=a^(e I+(L.map e).sum)*(c*b)) x g at hRight
    rw [hmul] at hLeft
    exact fun g => (hLeft g).trans (hRight g).symm

private theorem restrict_off_carrier {N : Set Y} (hN : IsClosed N) {y : Y} (hy : y ∉ N)
    (I : GermIdeal n Y) (g : Y → ℂ) : (restrictOn n N I).mem y g ↔ HolomorphicAt n g y :=
  ⟨fun h => h.1,fun hg => restrictOn_eq_top_of_disjoint hN.isOpen_compl hy (by simp) hg⟩

/-- WHOLE actual one-step factorization; the SUM is not named greatest. -/
theorem next_relative_product_whole_exceptional_factor_sum (hn : 0 < n) {N C : Set X}
    (hN : IsClosedSubmanifold n N) {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N)
    (L : List (GermIdeal n X)) (hcoh : ∀ I ∈ L,I.IsCoherent)
    (hnz : ∀ I ∈ L,∀ x ∈ N,DivisorExponentAlong.IsNonzeroAlongAt N I x)
    (hpr : ∀ I ∈ L,∀ x ∈ N,∃ f : X → ℂ,HolomorphicAt n f x ∧ ∀ g,I.mem x g ↔
      HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=f) x g) :
    ∀ y : Y,∀ g : Y → ℂ,
      (nextTotalMarked N (relativeIdealListProduct N L) C π).ideal.mem y g ↔
      (restrictOn n (geoStrictTransform π C N)
        ((idealPow (vanishingIdeal (n := n) (π ⁻¹' C))
          (L.map fun I => singleExceptionalExponent (geoStrictTransform π C N) (nextTotalMarked N I C π).ideal (π ⁻¹' C) y).sum).mul
        (relativeIdealListProduct (geoStrictTransform π C N) (L.map fun I => nextRelativeStrict N I C π)))).mem y g := by
  have hTot := nextTotal_relative_product_eq_relative_product_totals hN hπ L hpr
  have hEnew := actual_accumulated_exceptional_geometry hN isCoherent_unitIdeal isSNCDivisor_nil
    (isTransverse_nil_of_isClosedSubmanifold hN) hπ hCN (hasNormalCrossings_nil_of_isClosedSubmanifold hπ.1)
  have hDsnc : IsSNCDivisor n [π ⁻¹' C] := hEnew.1
  intro y g
  by_cases hy : y ∈ geoStrictTransform π C N
  · obtain ⟨a,ha,hDgen⟩ := exists_originalMember_principal hn hDsnc (show π ⁻¹' C ∈ [π ⁻¹' C] by simp) y
    have hEach (I : GermIdeal n X) (hI : I ∈ L) := nextRelativeStrict_actual_geometry hn hN (hcoh I hI) (hnz I hI) (hpr I hI) hπ hCN
    rw [hTot]
    apply relative_product_factor_power_sum ha hDgen L
      (fun I => (nextTotalMarked N I C π).ideal) (fun I => nextRelativeStrict N I C π)
      (fun I => singleExceptionalExponent (geoStrictTransform π C N) (nextTotalMarked N I C π).ideal (π ⁻¹' C) y)
    · intro I hI
      exact (hEach I hI).2.2.2.2 y
    · intro I hI
      obtain ⟨c,hc,hgen⟩ := (hEach I hI).2.2.2.1 y hy
      exact ⟨c,((hgen c).mp hc).1,hgen⟩
  · change ((⟨N,[],relativeIdealListProduct N L,0⟩ : MarkedIdeal n X).geoTransform C π).ideal.mem y g ↔ _
    rw [HironakaSharpOriginalFirstMemberExceptionalFactor.geoTransform_zeroMark_ideal_eq_restricted_total
      (⟨N,[],relativeIdealListProduct N L,0⟩ : MarkedIdeal n X) rfl C π]
    exact (restrict_off_carrier isClosed_closure hy _ g).trans (restrict_off_carrier isClosed_closure hy _ g).symm

/-- Literal recursion identifies the actual next family/product before comparison. -/
theorem chronological_product_next_eq {W : Set X} (E : List (Set X))
    {Z : CMfd.{u} n} (T : BlowupTower X Z) {C : Set Z} {π : Y → Z} (hπ : IsBlowupAlong n C π) :
    chronologicalMemberProduct W E (.step T C π hπ)=
      relativeIdealListProduct (geoStrictTransform π C (geoTransformAlong (geometricTemplate W []) T).N)
        ((chronologicalMemberFamily W E T).map fun I => nextRelativeStrict (geoTransformAlong (geometricTemplate W []) T).N I C π) := by
  have hfam : chronologicalMemberFamily W E (.step T C π hπ)=
      (chronologicalMemberFamily W E T).map (fun I => nextRelativeStrict (geoTransformAlong (geometricTemplate W []) T).N I C π) := by
    unfold chronologicalMemberFamily
    rw [List.map_map]
    apply List.map_congr_left
    intro H _hH
    have hNi := (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W H) T).1
    change nextRelativeStrict (chronologicalMarked (originalRelativeMemberMarked W H) T).N
      (chronologicalMarked (originalRelativeMemberMarked W H) T).ideal C π=_
    rw [hNi]
    rfl
  unfold chronologicalMemberProduct
  rw [hfam]
  rfl

/-- ONLY original current-family geometry supplies the WHOLE next chronological
factorization with the SUM of independently actual normalized exponents. -/
theorem original_next_chronological_product_whole_exceptional_factor_sum (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    {Z : CMfd.{u} n} (T : BlowupTower X Z) (ht : IsGeoTestTower (geometricTemplate W []) T)
    {C : Set Z} {π : Y → Z} (hπ : IsBlowupAlong n C π)
    (hCN : C ⊆ (geoTransformAlong (geometricTemplate W []) T).N) :
    let N := (geoTransformAlong (geometricTemplate W []) T).N
    ∀ y : Y,∀ g : Y → ℂ,(nextTotalMarked N (chronologicalMemberProduct W E T) C π).ideal.mem y g ↔
      (restrictOn n (geoStrictTransform π C N)
        ((idealPow (vanishingIdeal (n := n) (π ⁻¹' C))
          ((chronologicalMemberFamily W E T).map fun I => singleExceptionalExponent (geoStrictTransform π C N)
            (nextTotalMarked N I C π).ideal (π ⁻¹' C) y).sum).mul
          (chronologicalMemberProduct W E (.step T C π hπ)))).mem y g := by
  have hw : (geometricTemplate W []).IsWellFormed :=
    ⟨hW,isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hwT := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw T ht
  have hfam : ∀ I ∈ chronologicalMemberFamily W E T,I.IsCoherent ∧
      (∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,DivisorExponentAlong.IsNonzeroAlongAt
        (geoTransformAlong (geometricTemplate W []) T).N I x) ∧
      ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,∃ f : Z → ℂ,HolomorphicAt n f x ∧
        ∀ g,I.mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) (geoTransformAlong (geometricTemplate W []) T).N (·=f) x g := by
    intro I hI
    obtain ⟨H,hH,rfl⟩ := List.mem_map.mp hI
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hH
    obtain ⟨hNi,_hEi,_hmi,hwi,hnzi,hpri⟩ := original_members_actual_finite_chronological_geometry hn hW hE hdense i T ht
    rw [hNi] at hnzi hpri
    exact ⟨hwi.isCoherent,hnzi,hpri⟩
  have hh := next_relative_product_whole_exceptional_factor_sum hn hwT.isClosedSubmanifold_N hπ hCN
    (chronologicalMemberFamily W E T) (fun I hI => (hfam I hI).1) (fun I hI => (hfam I hI).2.1) (fun I hI => (hfam I hI).2.2)
  rw [← chronological_product_next_eq E T hπ] at hh
  exact hh

end
end Hironaka.HironakaSharpActualProductNewExceptionalFactor
