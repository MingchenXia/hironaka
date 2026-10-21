/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalReferenceValueLocalBlowup
/-! Actual canonical-next-step comparison for the SAME fixed OLD full reference
cut. Centre traces and strict-decrease hypotheses are internally proved.
Original coefficient transformed semicoherence/global scheduling stay OPEN. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalReferenceValueCanonicalNextTransform
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen CanonicalCentres
  HironakaOriginalReferenceValueOpenNaturality HironakaOriginalReferenceValueAuxiliaryMarked
  HironakaOriginalReferenceValueLocalBlowup GermIdealOrder NormalCrossings
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- True inverse image of the actual original reference window under the next blowup. -/
def nextOpen {D : Set Y} {π : Z → Y} (hπ : IsBlowupAlong n D π) (W : Opens Y) : Opens Z :=
  ⟨π ⁻¹' (W : Set Y),W.isOpen.preimage hπ.contMDiff.continuous⟩

/-- Actual next projection with true original-window membership. -/
def nextMap {D : Set Y} {π : Z → Y} (hπ : IsBlowupAlong n D π) (W : Opens Y) : nextOpen hπ W → W :=
  fun z => ⟨π z,z.property⟩

/-- Literal next ORIGINAL full threshold at the SAME fixed OLD attained reference value. -/
def nextFixedReferenceLocus (hn : 0 < n) (d : ℕ) (m : MarkedIdeal n X)
    (T : BlowupTower X Y) (x : Y) {D : Set Y} {π : Z → Y} (hπ : IsBlowupAlong n D π) (W : Opens Y) :
    Set (nextOpen hπ W) :=
  {z | (z : Z) ∈ (geoTransformAlong m (.step T D π hπ)).cosupp ∧
    (invFamily hn d).inv m T x ≤ (invFamily hn d).inv m (.step T D π hπ) z}

private theorem actual_centre_trace_dichotomy (hn : 0 < n) (d : ℕ) (m : MarkedIdeal n X)
    (T : BlowupTower X Y) (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (W : Opens Y)
    (hbound : ∀ y ∈ (geoTransformAlong m T).cosupp,y ∈ W → (invFamily hn d).inv m T y ≤ (invFamily hn d).inv m T x)
    {D : Set Y} {π : Z → Y} (hπ : IsBlowupAlong n D π)
    (hc : IsCanonical m ((invFamily hn d).inv m) (.step T D π hπ)) :
    (Subtype.val : W → Y) ⁻¹' D=∅ ∨
      (Subtype.val : W → Y) ⁻¹' D=(Subtype.val : W → Y) ⁻¹' fullReferenceLocus hn d m T x := by
  by_cases hne : ((Subtype.val : W → Y) ⁻¹' D).Nonempty
  · obtain ⟨p,hp⟩ := hne
    rcases hc.2 with hD | hD
    · exact False.elim (by have hh : (p : Y) ∈ D := hp; rw [hD] at hh; exact hh)
    · right
      have hpmax := hD ▸ hp
      have hpx : (invFamily hn d).inv m T x = (invFamily hn d).inv m T p :=
        (hpmax.2 x hx).antisymm (hbound p hpmax.1 p.property)
      ext q
      constructor
      · intro hq
        have hqmax := hD ▸ hq
        exact ⟨hqmax.1,hqmax.2 x hx⟩
      · rintro ⟨hq,hv⟩
        rw [hD]
        exact ⟨hq,fun y hy => (hpmax.2 y hy).trans (hpx.symm.le.trans hv)⟩
  · exact Or.inl (not_nonempty_iff_eq_empty.mp hne)

private theorem actual_next_empty_trace_dictionary (hn : 0 < n) (d : ℕ) (m : MarkedIdeal n X)
    (h : IsInvDomain d m) (T : BlowupTower X Y)
    (hcT : IsCanonical m ((invFamily hn d).inv m) T) (x : Y) (W : Opens Y)
    {D : Set Y} {π : Z → Y} (hπ : IsBlowupAlong n D π)
    (hc : IsCanonical m ((invFamily hn d).inv m) (.step T D π hπ))
    (hD : (Subtype.val : W → Y) ⁻¹' D=∅) :
    nextFixedReferenceLocus hn d m T x hπ W =
      (nextMap hπ W) ⁻¹' ((Subtype.val : W → Y) ⁻¹' fullReferenceLocus hn d m T x) := by
  have ht := (invFamily hn d).isInvValue.isGeoTestTower_of_isCanonical h T hcT
  have hd := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T ht
  ext z
  have hzD : π z ∉ D := by
    intro hz
    have hh : (⟨π z,z.property⟩ : W) ∈ (Subtype.val : W → Y) ⁻¹' D := hz
    rw [hD] at hh
    exact hh
  have hcos := TransformOffCentre.mem_cosupp_geoTransform_iff (geoTransformAlong m T)
    hd.isWellFormed.isClosedSubmanifold_N.1
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hd.isWellFormed.isCoherent hg) hπ hzD
  constructor
  · rintro ⟨hz,hv⟩
    have hdrop := stepDrop_of_isInvValue (invFamily hn d).isInvValue h T D π hπ hc z hz
    exact ⟨hdrop.1,by change (invFamily hn d).inv m T x ≤ (invFamily hn d).inv m T (π z); exact hv.trans (hdrop.2.2 hzD).le⟩
  · rintro ⟨hz,hv⟩
    have hz' : (z : Z) ∈ (geoTransformAlong m (.step T D π hπ)).cosupp := hcos.mpr hz
    have hdrop := stepDrop_of_isInvValue (invFamily hn d).isInvValue h T D π hπ hc z hz'
    exact ⟨hz',hv.trans (hdrop.2.2 hzD).symm.le⟩

private theorem actual_next_full_trace_dictionary (hn : 0 < n) (d : ℕ) (m : MarkedIdeal n X)
    (h : IsInvDomain d m) (T : BlowupTower X Y) (x : Y) (W : Opens Y)
    (hbound : ∀ y ∈ (geoTransformAlong m T).cosupp,y ∈ W → (invFamily hn d).inv m T y ≤ (invFamily hn d).inv m T x)
    {D : Set Y} {π : Z → Y} (hπ : IsBlowupAlong n D π)
    (hc : IsCanonical m ((invFamily hn d).inv m) (.step T D π hπ))
    (hD : (Subtype.val : W → Y) ⁻¹' D=(Subtype.val : W → Y) ⁻¹' fullReferenceLocus hn d m T x) :
    nextFixedReferenceLocus hn d m T x hπ W=∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  rintro z ⟨hz,hv⟩
  have hdrop := stepDrop_of_isInvValue (invFamily hn d).isInvValue h T D π hπ hc z hz
  have hb := hbound (π z) hdrop.1 z.property
  have hzD : π z ∈ D := by
    have hnoninc : (invFamily hn d).inv m (.step T D π hπ) z ≤ (invFamily hn d).inv m T (π z) := by
      by_cases hzz : π z ∈ D
      · exact (hdrop.2.1 hzz).le
      · exact (hdrop.2.2 hzz).le
    have hmem : (⟨π z,z.property⟩ : W) ∈ (Subtype.val : W → Y) ⁻¹' fullReferenceLocus hn d m T x :=
      ⟨hdrop.1,hv.trans hnoninc⟩
    have hh : (⟨π z,z.property⟩ : W) ∈ (Subtype.val : W → Y) ⁻¹' D := hD.symm ▸ hmem
    exact hh
  exact (not_lt_of_ge hv) ((hdrop.2.1 hzD).trans_le hb)

/-- ONLY original inputs choose one true window for EVERY actual canonical next-step centre and whole fixed-threshold dictionary. -/
theorem exists_original_canonical_next_reference_dictionary (hn : 0 < n) (d : ℕ)
    (m : MarkedIdeal n X) (h : IsInvDomain d m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn d).inv m) T) (x : Y)
    (hx : x ∈ (geoTransformAlong m T).cosupp) :
    ∃ W : Opens Y,x ∈ W ∧
      IsClosedSubmanifold n ((Subtype.val : W → Y) ⁻¹' fullReferenceLocus hn d m T x) ∧
      ∀ {Z : CMfd.{u} n} (D : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n D π),
        IsCanonical m ((invFamily hn d).inv m) (.step T D π hπ) →
        (((Subtype.val : W → Y) ⁻¹' D=∅ ∧ nextFixedReferenceLocus hn d m T x hπ W=
          (nextMap hπ W) ⁻¹' ((Subtype.val : W → Y) ⁻¹' fullReferenceLocus hn d m T x)) ∨
        ((Subtype.val : W → Y) ⁻¹' D=(Subtype.val : W → Y) ⁻¹' fullReferenceLocus hn d m T x ∧
          nextFixedReferenceLocus hn d m T x hπ W=∅)) := by
  obtain ⟨W,hxW,hbound,_hCne,hCadm,_hBadm,_hBcos⟩ := exists_original_reference_admissible_open hn d m h T hc x hx
  refine ⟨W,hxW,hCadm.1,?_⟩
  intro Z D π hπ hcnext
  rcases actual_centre_trace_dichotomy hn d m T x hx W hbound hπ hcnext with hD | hD
  · exact Or.inl ⟨hD,actual_next_empty_trace_dictionary hn d m h T hc x W hπ hcnext hD⟩
  · exact Or.inr ⟨hD,actual_next_full_trace_dictionary hn d m h T x W hbound hπ hcnext hD⟩


private theorem empty_vanishing_ideal_unit {A : CMfd.{u} n} :
    vanishingIdeal (n := n) (∅ : Set A)=IdealWeightPowers.unitIdeal n A := by
  refine GermIdeal.ext (funext fun x => funext fun g => propext ⟨fun hg => hg.1,fun hg => ?_⟩)
  exact ⟨hg,Eventually.of_forall fun _ hx => hx.elim⟩

private theorem actual_empty_centre_controlled_vanishing {A B : CMfd.{u} n} {D : Set A} {f : B → A}
    (hf : IsBlowupAlong n D f) (hD : D=∅) {C : Set A} (hC : IsClosedSubmanifold n C) :
    BlowupControlledTransform.controlledTransform hf (vanishingIdeal (n := n) C) 1 =
      vanishingIdeal (n := n) (f ⁻¹' C) := by
  obtain ⟨s,hs,hfs,hsf⟩ := BlowupIsomorphismOff.exists_section_compl hf
  let O : Opens A := ⟨Dᶜ,hf.1.1.isOpen_compl⟩
  let j : A → O := fun x => ⟨x,by change x ∈ Dᶜ; simp [hD]⟩
  have hj : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ j := by
    apply (ContMDiff.subtypeVal_comp_iff _ _).mp
    exact contMDiff_id
  let g : A → B := s ∘ j
  have hg : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ g := hs.comp hj
  have hfg : ∀ a,f (g a)=a := fun a => congrFun hfs (j a)
  have hgf : ∀ b,g (f b)=b := fun b => hsf b (by simp [hD])
  have hv := MarkedIdealBiholomorphism.pullback_vanishingIdeal_preimage (φ := f) (ψ := g)
    hf.contMDiff hg hfg hgf (g := (id : B → B)) contMDiff_id C
  have hpull : GermIdeal.pullback (m := n) f (vanishingIdeal (n := n) C) =
      vanishingIdeal (n := n) (f ⁻¹' C) := by
    have hid : GermIdeal.pullback (m := n) (id : B → B) (vanishingIdeal (n := n) (f ⁻¹' C)) =
        vanishingIdeal (n := n) (f ⁻¹' C) :=
      GermIdeal.ext (funext fun _ => funext fun _ => propext BlowupExistenceCodimOne.pullback_id_vanishingIdeal_mem_iff)
    simpa only [Function.comp_id,hid] using hv.symm
  have hden : IdealWeightPowers.idealPow (GermIdeal.pullback (m := n) f (vanishingIdeal (n := n) D)) 1 =
      IdealWeightPowers.unitIdeal n B := by
    rw [hD,empty_vanishing_ideal_unit,BlowupExceptionalDivisor.pullback_unitIdeal,
      BlowupControlledTransform.idealPow_unitIdeal]
  unfold BlowupControlledTransform.controlledTransform
  change InvertibleIdealQuotient.colon (GermIdeal.pullback (m := n) f (vanishingIdeal (n := n) C))
    (IdealWeightPowers.idealPow (GermIdeal.pullback (m := n) f (vanishingIdeal (n := n) D)) 1) = _
  rw [hden,BlowupControlledTransform.colon_unitIdeal
    (GermIdealPullbackCalculus.isCoherent_pullback hf.contMDiff (VanishingIdealCoherent.isCoherent_vanishingIdeal hC))]
  exact hpull

private theorem actual_next_map_blowup {D : Set Y} {π : Z → Y} (hπ : IsBlowupAlong n D π) (W : Opens Y) :
    IsBlowupAlong n ((Subtype.val : W → Y) ⁻¹' D) (nextMap hπ W) :=
  BlowupRestrictOpen.isBlowupAlong_restrict hπ W (W.isOpen.preimage hπ.contMDiff.continuous)

/-- ONLY original input constructs ONE actual window whose WHOLE auxiliary
geometric next ideal is precisely the actual SAME-fixed-old-reference ideal. -/
theorem exists_original_canonical_next_reference_ideal_transform (hn : 0 < n) (d : ℕ)
    (m : MarkedIdeal n X) (h : IsInvDomain d m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn d).inv m) T) (x : Y)
    (hx : x ∈ (geoTransformAlong m T).cosupp) :
    ∃ W : Opens Y,x ∈ W ∧
      ∀ {Z : CMfd.{u} n} (D : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n D π),
        IsCanonical m ((invFamily hn d).inv m) (.step T D π hπ) →
        let B := (referenceMarked hn d m T x W).geoTransform ((Subtype.val : W → Y) ⁻¹' D) (nextMap hπ W)
        B.ideal=vanishingIdeal (n := n) (nextFixedReferenceLocus hn d m T x hπ W) ∧
        B.ideal.IsCoherent ∧ B.cosupp=nextFixedReferenceLocus hn d m T x hπ W ∧
        IsComplexAnalyticSubset (n := n) (nextFixedReferenceLocus hn d m T x hπ W) := by
  obtain ⟨W,hxW,hC,hdict⟩ := exists_original_canonical_next_reference_dictionary hn d m h T hc x hx
  refine ⟨W,hxW,?_⟩
  intro Z D π hπ hcnext
  let C := (Subtype.val : W → Y) ⁻¹' fullReferenceLocus hn d m T x
  let B := (referenceMarked hn d m T x W).geoTransform ((Subtype.val : W → Y) ⁻¹' D) (nextMap hπ W)
  have hr := actual_next_map_blowup hπ W
  have hI : (windowIdeal hn d m T x W).IsCoherent := VanishingIdealCoherent.isCoherent_vanishingIdeal hC
  have hwhole : B.N=univ := geoTransform_N_eq_univ (𝔪 := referenceMarked hn d m T x W) rfl hr
  have hgeo : B.ideal=BlowupControlledTransform.controlledTransform hr (windowIdeal hn d m T x W) 1 :=
    geoTransform_ideal_eq_controlledTransform (𝔪 := referenceMarked hn d m T x W) rfl hI hr
  rcases hdict D π hπ hcnext with ⟨hD,hnext⟩ | ⟨hD,hnext⟩
  · have heq : B.ideal=vanishingIdeal (n := n) (nextFixedReferenceLocus hn d m T x hπ W) := by
      rw [hgeo,hnext]
      exact actual_empty_centre_controlled_vanishing (A := CMfd.of (n := n) W)
        (B := CMfd.of (n := n) (nextOpen hπ W)) hr hD hC
    have hcoh : B.ideal.IsCoherent := by
      rw [hgeo]
      change (BlowupControlledTransform.controlledTransform hr (vanishingIdeal (n := n) C) 1).IsCoherent
      have hpc : (GermIdeal.pullback (m := n) (nextMap hπ W) (vanishingIdeal (n := n) C)).IsCoherent :=
        GermIdealPullbackCalculus.isCoherent_pullback hr.contMDiff hI
      have hcontrolled : BlowupControlledTransform.controlledTransform hr (vanishingIdeal (n := n) C) 1 =
          GermIdeal.pullback (m := n) (nextMap hπ W) (vanishingIdeal (n := n) C) := by
        unfold BlowupControlledTransform.controlledTransform
        change InvertibleIdealQuotient.colon _
          (IdealWeightPowers.idealPow (GermIdeal.pullback (m := n) (nextMap hπ W)
            (vanishingIdeal (n := n) ((Subtype.val : W → Y) ⁻¹' D))) 1) = _
        rw [hD,empty_vanishing_ideal_unit (A := CMfd.of (n := n) W),BlowupExceptionalDivisor.pullback_unitIdeal,
          BlowupControlledTransform.idealPow_unitIdeal,BlowupControlledTransform.colon_unitIdeal hpc]
      exact hcontrolled.symm ▸ hpc
    have hA := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hr.contMDiff
      (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hC)
    have hAnext : IsComplexAnalyticSubset (n := n) (nextFixedReferenceLocus hn d m T x hπ W) := hnext.symm ▸ hA
    refine ⟨heq,hcoh,?_,hAnext⟩
    change cosupport n B.N B.ideal 1 = _
    rw [hwhole,heq,cosupport_one (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
      (heq ▸ hcoh) hg),univ_inter,BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hAnext.isClosed]
  · have hrC : IsBlowupAlong n ((Subtype.val : W → Y) ⁻¹' fullReferenceLocus hn d m T x) (nextMap hπ W) := hD ▸ hr
    have hunit := referenceMarked_geoTransform_unit_of_full_centre (Z := CMfd.of (n := n) (nextOpen hπ W))
      (π := nextMap hπ W) hn d m T x W hC hrC
    have heqI : B.ideal=IdealWeightPowers.unitIdeal n (nextOpen hπ W) := by
      change ((referenceMarked hn d m T x W).geoTransform ((Subtype.val : W → Y) ⁻¹' D) (nextMap hπ W)).ideal=_
      rw [hD]
      exact hunit.2.1
    have hcoh : B.ideal.IsCoherent := heqI.symm ▸ IdealWeightPowers.isCoherent_unitIdeal
    have hAnext : IsComplexAnalyticSubset (n := n) (nextFixedReferenceLocus hn d m T x hπ W) :=
      hnext.symm ▸ isComplexAnalyticSubset_empty
    refine ⟨?_,hcoh,?_,hAnext⟩
    · rw [heqI,hnext,empty_vanishing_ideal_unit (A := CMfd.of (n := n) (nextOpen hπ W))]
    · change cosupport n B.N B.ideal 1 = _
      rw [heqI,hnext]
      exact cosupport_unitIdeal le_rfl

end
end Hironaka.HironakaOriginalReferenceValueCanonicalNextTransform
