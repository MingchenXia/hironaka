/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpOriginalFirstMemberWholeFactor

/-! Genuine next chronological STRICT = true pullback then NEW-exceptional
arbitrary saturation. Whole accumulated SNC uses actual whole-old-list centre
NC explicitly. No selected next centre/accumulated-total comparison is assumed. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualChronologicalStrictStep
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpOriginalFirstMemberWholeFactor HironakaSharpOriginalFirstMemberRelativeStrict
  HironakaSharpOriginalFirstMemberExceptionalFactor HironakaSharpOriginalFirstMemberResidualPrincipal
  HironakaSharpOriginalDistinctDefectPhase HironakaSharpOriginalMemberProductDomain
  HironakaCoherentTransformExtension RelativePrincipalizationSpan RestrictedIdealExtension
  MonomialPartAlong InvDomainCompanion NormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal
  IdealWeightPowers InvertibleIdealQuotient DivisorExponentAlong GermIdealOrder
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Literal actual empty-auxiliary-boundary mark-zero TOTAL record. -/
def nextTotalMarked (N : Set X) (I : GermIdeal n X) (C : Set X) (π : Y → X) : MarkedIdeal n Y :=
  (⟨N,[],I,0⟩ : MarkedIdeal n X).geoTransform C π

/-- Independent actual chronological construction from TRUE old ideal pullback
and ALL powers of the true NEW exceptional ideal, before any residual theorem. -/
def nextRelativeStrict (N : Set X) (I : GermIdeal n X) (C : Set X) (π : Y → X) : GermIdeal n Y :=
  relativeExceptionalSaturation (nextTotalMarked N I C π).N (GermIdeal.pullback (m := n) π I) (π ⁻¹' C)

/-- Real relative source equations compose on the actual strict carrier;
all source normal-vanishing germs are retained in BOTH new ideal directions. -/
theorem nextTotal_actual_relative_principal {N C : Set X} {I : GermIdeal n X}
    (hN : IsClosedSubmanifold n N) {π : Y → X} (hπ : IsBlowupAlong n C π)
    (hprincipal : ∀ x ∈ N,∃ f : X → ℂ,HolomorphicAt n f x ∧
      ∀ g,I.mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=f) x g)
    (y : Y) (hy : y ∈ (nextTotalMarked N I C π).N) :
    ∃ f : Y → ℂ,HolomorphicAt n f y ∧ ∀ g,(nextTotalMarked N I C π).ideal.mem y g ↔
      HolomorphicAt n g y ∧ IsInSpanOnAt (n := n) (nextTotalMarked N I C π).N (·=f) y g := by
  have hmaps := BlowupStrictSubmanifold.geoStrictTransform_subset_preimage (C := C) hπ.contMDiff.continuous hN.1
  obtain ⟨f,hf,hgen⟩ := hprincipal (π y) (hmaps hy)
  have hfp := hf.comp_contMDiff (Eventually.of_forall fun _ => hπ.contMDiff.contMDiffAt)
  have hfI : I.mem (π y) f := (hgen f).mpr
    ⟨hf,isInSpanOnAt_eq_iff.mpr ⟨1,holomorphicAt_const 1,Eventually.of_forall fun _ _ => by simp⟩⟩
  have hfP : (GermIdeal.pullback (m := n) π I).mem y (f ∘ π) := GermIdeal.mem_pullback_iff.mpr
    (isInSpanAt_self ⟨f,hfI,rfl⟩ hfp)
  have heq : (nextTotalMarked N I C π).ideal=restrictOn n (nextTotalMarked N I C π).N
      (GermIdeal.pullback (m := n) π I) :=
    geoTransform_zeroMark_ideal_eq_restricted_total (⟨N,[],I,0⟩ : MarkedIdeal n X) rfl C π
  refine ⟨f ∘ π,hfp,?_⟩
  intro g
  rw [heq]
  constructor
  · intro hg
    refine ⟨hg.1,IsInSpanOnAt.trans (fun a ha => ?_) hg.2⟩
    refine IsInSpanOnAt.trans (fun v hv => ?_) (IsInSpanAt.restrict (GermIdeal.mem_pullback_iff.mp ha))
    obtain ⟨b,hb,rfl⟩ := hv
    obtain ⟨c,hc,hbc⟩ := isInSpanOnAt_eq_iff.mp ((hgen b).mp hb).2
    refine isInSpanOnAt_eq_iff.mpr ⟨c ∘ π,hc.comp_contMDiff (Eventually.of_forall fun _ => hπ.contMDiff.contMDiffAt),?_⟩
    filter_upwards [hπ.contMDiff.continuous.tendsto y |>.eventually hbc] with z hz hzN
    exact hz (hmaps hzN)
  · rintro ⟨hg,hspan⟩
    exact ⟨hg,IsInSpanOnAt.mono (S := (·=f ∘ π))
      (T := (GermIdeal.pullback (m := n) π I).mem y) (fun a ha => ha ▸ hfP) hspan⟩

/-- Genuine next chronological closure from actual old ideal geometry; no
desired next ideal, nonzero, principal or saturation certificate is input. -/
theorem nextRelativeStrict_actual_geometry (hn : 0 < n) {N C : Set X} {I : GermIdeal n X}
    (hN : IsClosedSubmanifold n N) (hI : I.IsCoherent)
    (hnz : ∀ x ∈ N,IsNonzeroAlongAt N I x)
    (hprincipal : ∀ x ∈ N,∃ f : X → ℂ,HolomorphicAt n f x ∧
      ∀ g,I.mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=f) x g)
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N) :
    let P := nextTotalMarked N I C π
    let S := nextRelativeStrict N I C π
    S=nonmonomialPartAlong n P.N P.ideal [π ⁻¹' C] ∧ S.IsCoherent ∧
      (∀ y ∈ P.N,IsNonzeroAlongAt P.N S y) ∧
      (∀ y ∈ P.N,∃ c : Y → ℂ,S.mem y c ∧ ∀ g,S.mem y g ↔
        HolomorphicAt n g y ∧ IsInSpanOnAt (n := n) P.N (·=c) y g) ∧
      ∀ y : Y,∀ g : Y → ℂ,P.ideal.mem y g ↔
        (restrictOn n P.N ((idealPow (vanishingIdeal (n := n) (π ⁻¹' C))
          (singleExceptionalExponent P.N P.ideal (π ⁻¹' C) y)).mul S)).mem y g := by
  let M : MarkedIdeal n X := ⟨N,[],I,0⟩
  let P := nextTotalMarked N I C π
  have hwM : M.IsWellFormed := ⟨hN,hI,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hN⟩
  have hadm : M.IsAdmissibleCentre C := by
    refine ⟨hπ.1,?_,hasNormalCrossings_nil_of_isClosedSubmanifold hπ.1⟩
    change C ⊆ cosupport n N I 0
    rw [cosupport_zero (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hg)]
    exact hCN
  have hwP := GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hwM hadm hπ
  have hnzP := isNonzeroAlongAt_geoTransform_without_admissibility M hN hI hπ hCN hnz
  have hpr := nextTotal_actual_relative_principal hN hπ hprincipal
  obtain ⟨hS,hcoh,hnzS⟩ := actual_single_exceptional_saturation_eq_residual hn hwP.isClosedSubmanifold_N
    hwP.isSNCDivisor hwP.isTransverse hwP.isCoherent hnzP hpr
  have hTotal : P.ideal=restrictOn n P.N (GermIdeal.pullback (m := n) π I) :=
    geoTransform_zeroMark_ideal_eq_restricted_total M rfl C π
  change relativeExceptionalSaturation P.N P.ideal (π ⁻¹' C)=nonmonomialPartAlong n P.N P.ideal [π ⁻¹' C] at hS
  change (relativeExceptionalSaturation P.N P.ideal (π ⁻¹' C)).IsCoherent at hcoh
  change ∀ y ∈ P.N,IsNonzeroAlongAt P.N (relativeExceptionalSaturation P.N P.ideal (π ⁻¹' C)) y at hnzS
  have hSat : relativeExceptionalSaturation P.N P.ideal (π ⁻¹' C)=nextRelativeStrict N I C π := by
    ext y g
    rw [hTotal]
    exact relativeExceptionalSaturation_restrictOn_mem_iff _ _ _ y g
  rw [hSat] at hS hcoh hnzS
  refine ⟨hS,hcoh,hnzS,?_,?_⟩
  · intro y hy
    obtain ⟨f,hf,hgen⟩ := hpr y hy
    obtain ⟨_m,c,_hm,_hmM,hc,_hfc,hcgen⟩ := exists_actual_relative_principal_residual hn
      hwP.isClosedSubmanifold_N hwP.isSNCDivisor hwP.isTransverse hwP.isCoherent hnzP hy f hf hgen
    rw [hS]
    exact ⟨c,hc,hcgen⟩
  · intro y g
    have hnorm : restrictOn n P.N P.ideal=P.ideal := by
      rw [hTotal]
      exact GermIdeal.ext (funext fun z => funext fun v => propext (by
        constructor
        · rintro ⟨hv,hspan⟩; exact ⟨hv,IsInSpanOnAt.trans (fun s hs => hs.2) hspan⟩
        · intro hv; exact ⟨hv.1,IsInSpanAt.restrict (isInSpanAt_self hv hv.1)⟩))
    rw [hS]
    have hfactor := actual_single_total_normalized_factor_mem_iff hn hwP.isClosedSubmanifold_N
      hwP.isSNCDivisor hwP.isTransverse hwP.isCoherent hnzP y g
    change (restrictOn n P.N P.ideal).mem y g ↔ _ at hfactor
    rw [hnorm] at hfactor
    exact hfactor

/-- Actual whole OLD exceptional NC is genuinely used; carrier containment
and the auxiliary empty-boundary geometry do not replace this condition. -/
theorem actual_accumulated_exceptional_geometry {N C : Set X} {I : GermIdeal n X}
    {E : List (Set X)} (hN : IsClosedSubmanifold n N) (hI : I.IsCoherent)
    (hE : IsSNCDivisor n E) (hT : IsTransverse n N E) {π : Y → X}
    (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N) (hNC : HasNormalCrossings n C E) :
    IsSNCDivisor n (E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]) ∧
      IsTransverse n (nextTotalMarked N I C π).N
        (E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]) := by
  let M : MarkedIdeal n X := ⟨N,E,I,0⟩
  have hw : M.IsWellFormed := ⟨hN,hI,hE,hT⟩
  have hadm : M.IsAdmissibleCentre C := by
    refine ⟨hπ.1,?_,hNC⟩
    change C ⊆ cosupport n N I 0
    rw [cosupport_zero (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hg)]
    exact hCN
  have hnew := GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hw hadm hπ
  exact ⟨hnew.isSNCDivisor,hnew.isTransverse⟩

/-- ONLY original inputs provide the SAME first projection and genuine first
STRICT geometry, for every actual geometrically admissible next blowup. -/
theorem exists_original_first_to_second_chronological_strict (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    {d : ℕ} (hd : d+1 ≤ n) (hreg : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1))
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (hcompact : IsCompact W)
    (hne : (originalDistinctDefectPhase W E).Nonempty) :
    ∃ (C : Set X) (Y : CMfd.{u} n) (π : Y → X),IsBlowupAlong n C π ∧
      C=ResolutionDriver.maxLocus ((CanonicalCentres.invFamily hn (n+1)).inv
        (originalMemberProductMarked W E 1) (.refl : BlowupTower X X)) (originalDistinctDefectPhase W E) ∧
      ∀ i : Fin E.length,
        let P := memberTotalMarked W (E.get i) C π
        let S := firstRelativeStrictMemberIdeal W (E.get i) C π
        ∀ {Z : CMfd.{u} n} (D : Set Y) (q : Z → Y),IsBlowupAlong n D q → D ⊆ P.N → HasNormalCrossings n D P.E →
          let Q := nextTotalMarked P.N S D q
          let V := nextRelativeStrict P.N S D q
          V=nonmonomialPartAlong n Q.N Q.ideal [q ⁻¹' D] ∧
            V.IsCoherent ∧ (∀ z ∈ Q.N,IsNonzeroAlongAt Q.N V z) ∧
            (∀ z ∈ Q.N,∃ c : Z → ℂ,V.mem z c ∧ ∀ g,V.mem z g ↔
              HolomorphicAt n g z ∧ IsInSpanOnAt (n := n) Q.N (·=c) z g) ∧
            (∀ z : Z,∀ g : Z → ℂ,Q.ideal.mem z g ↔
              (restrictOn n Q.N ((idealPow (vanishingIdeal (n := n) (q ⁻¹' D))
                (singleExceptionalExponent Q.N Q.ideal (q ⁻¹' D) z)).mul V)).mem z g) ∧
            IsSNCDivisor n (P.E.map (BlowupStrictSubmanifold.geoStrictTransform q D) ++ [q ⁻¹' D]) ∧
            IsTransverse n Q.N (P.E.map (BlowupStrictSubmanifold.geoStrictTransform q D) ++ [q ⁻¹' D]) := by
  obtain ⟨C,Y,π,hπ,hCeq,hgeom⟩ := exists_actual_original_first_member_exceptional_factor hn hW hE hd hreg hdense hcompact hne
  refine ⟨C,Y,π,hπ,hCeq,?_⟩
  intro i
  dsimp only
  let P := memberTotalMarked W (E.get i) C π
  obtain ⟨hw,hTotal,hnz,_hJ,_hnzJ,_hfac,_hnot⟩ := hgeom i
  have hpr := fun y (_hy : y ∈ P.N) => exists_actual_original_member_total_principal (W := W) hn hE hπ i y
  obtain ⟨hS,hcoh,hnzS⟩ := actual_single_exceptional_saturation_eq_residual hn hw.isClosedSubmanifold_N
    hw.isSNCDivisor hw.isTransverse hw.isCoherent hnz hpr
  have hSat : relativeExceptionalSaturation P.N P.ideal (π ⁻¹' C)=firstRelativeStrictMemberIdeal W (E.get i) C π := by
    ext y g
    rw [hTotal]
    exact relativeExceptionalSaturation_restrictOn_mem_iff _ _ _ y g
  rw [hSat] at hS hcoh hnzS
  have hprS : ∀ y ∈ P.N,∃ f : Y → ℂ,HolomorphicAt n f y ∧ ∀ g,
      (firstRelativeStrictMemberIdeal W (E.get i) C π).mem y g ↔ HolomorphicAt n g y ∧
        IsInSpanOnAt (n := n) P.N (·=f) y g := by
    intro y hy
    obtain ⟨f,hf,hgen⟩ := hpr y hy
    obtain ⟨_m,c,_hm,_hmM,hc,_hfc,hcgen⟩ := exists_actual_relative_principal_residual hn
      hw.isClosedSubmanifold_N hw.isSNCDivisor hw.isTransverse hw.isCoherent hnz hy f hf hgen
    rw [hS]
    exact ⟨c,hc.1,hcgen⟩
  intro Z D q hq hDN hNC
  obtain ⟨hnext,hcohV,hnzV,hprV,hfactor⟩ := nextRelativeStrict_actual_geometry hn hw.isClosedSubmanifold_N hcoh hnzS hprS hq hDN
  obtain ⟨hEnext,hTnext⟩ := actual_accumulated_exceptional_geometry hw.isClosedSubmanifold_N hcoh
    hw.isSNCDivisor hw.isTransverse hq hDN hNC
  exact ⟨hnext,hcohV,hnzV,hprV,hfactor,hEnext,hTnext⟩

end
end Hironaka.HironakaSharpActualChronologicalStrictStep
