/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalReferenceValueCanonicalNextTransform
/-! Genuine fixed-threshold induction geometry, including current EMPTY cuts.
After erasure raw whole-unit transforms persist without implying auxiliary
admissibility. Full original coefficient semicoherence/global scheduler OPEN. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalReferenceValueBoundedStep
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen CanonicalCentres
  HironakaOriginalReferenceValueCanonicalNextTransform GermIdealOrder NormalCrossings
  IdealWeightPowers BlowupControlledTransform
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- Actual empty-centre complement geometry constructs BOTH whole inverse laws,
then genuine closed-smooth and WHOLE vanishing-ideal transport. -/
theorem exists_empty_centre_inverse_geometry {A B : CMfd.{u} n} {D : Set A} {f : B → A}
    (hf : IsBlowupAlong n D f) (hD : D=∅) :
    ∃ g : A → B,ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ g ∧
      (∀ a,f (g a)=a) ∧ (∀ b,g (f b)=b) ∧
      ∀ C : Set A,IsClosedSubmanifold n C → IsClosedSubmanifold n (f ⁻¹' C) ∧
        GermIdeal.pullback (m := n) f (vanishingIdeal (n := n) C)=vanishingIdeal (n := n) (f ⁻¹' C) := by
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
  refine ⟨g,hg,hfg,hgf,?_⟩
  intro C hC
  refine ⟨MarkedIdealBiholomorphism.isClosedSubmanifold_preimage hf.contMDiff hg hfg hgf hC,?_⟩
  have hv := MarkedIdealBiholomorphism.pullback_vanishingIdeal_preimage (φ := f) (ψ := g)
    hf.contMDiff hg hfg hgf (g := (id : B → B)) contMDiff_id C
  have hid : GermIdeal.pullback (m := n) (id : B → B) (vanishingIdeal (n := n) (f ⁻¹' C)) =
      vanishingIdeal (n := n) (f ⁻¹' C) :=
    GermIdeal.ext (funext fun _ => funext fun _ => propext BlowupExistenceCodimOne.pullback_id_vanishingIdeal_mem_iff)
  simpa only [Function.comp_id,hid] using hv.symm

/-- Every actual denominator germ is holomorphic, so the true controlled unit
ideal remains unit under ANY genuine centre and ANY mark. No admissibility inferred. -/
theorem controlledTransform_unit {A B : CMfd.{u} n} {D : Set A} {f : B → A}
    (hf : IsBlowupAlong n D f) (q : ℕ) :
    controlledTransform hf (unitIdeal n A) q=unitIdeal n B := by
  have hden := DivisorMetric.isCoherent_of_isInvertible (isInvertible_idealPow_exceptionalDivisor hf q)
  unfold controlledTransform
  rw [BlowupExceptionalDivisor.pullback_unitIdeal]
  refine GermIdeal.ext (funext fun x => funext fun g => propext ⟨fun hg => hg.1,fun hg => ?_⟩)
  exact ⟨hg,fun a ha => (RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hden ha).mul hg⟩

/-- The actual whole-carrier unit geometric record persists under ANY genuine
blowup, even when the centre is not auxiliary-admissible after erasure. -/
theorem unit_geoTransform {A B : CMfd.{u} n} (M : MarkedIdeal n A)
    (hN : M.N=univ) (hI : M.ideal=unitIdeal n A) {D : Set A} {f : B → A}
    (hf : IsBlowupAlong n D f) :
    (M.geoTransform D f).N=univ ∧ (M.geoTransform D f).ideal=unitIdeal n B := by
  have hcoh : M.ideal.IsCoherent := hI.symm ▸ isCoherent_unitIdeal
  refine ⟨geoTransform_N_eq_univ hN hf,?_⟩
  rw [geoTransform_ideal_eq_controlledTransform hN hcoh hf,hI]
  exact controlledTransform_unit hf M.d

/-- Literal fixed-threshold cut at the SAME original prefix and true window. -/
def thresholdCut (hn : 0 < n) (d : ℕ) (m : MarkedIdeal n X)
    (T : BlowupTower X Y) (b : ValTy d) (W : Opens Y) : Set W :=
  {p | (p : Y) ∈ (geoTransformAlong m T).cosupp ∧ b ≤ (invFamily hn d).inv m T p}


private theorem empty_vanishing_unit {A : CMfd.{u} n} :
    vanishingIdeal (n := n) (∅ : Set A)=unitIdeal n A := by
  refine GermIdeal.ext (funext fun x => funext fun g => propext ⟨fun hg => hg.1,fun hg => ?_⟩)
  exact ⟨hg,Eventually.of_forall fun _ hx => hx.elim⟩

/-- Actual empty-centre denominator powers are unit, so the true controlled
transform of ANY genuine coherent ideal is its WHOLE pullback. -/
theorem controlledTransform_empty_centre {A B : CMfd.{u} n} {D : Set A} {f : B → A}
    (hf : IsBlowupAlong n D f) (hD : D=∅) {I : GermIdeal n A} (hI : I.IsCoherent) (q : ℕ) :
    controlledTransform hf I q=GermIdeal.pullback (m := n) f I := by
  unfold controlledTransform
  change InvertibleIdealQuotient.colon (GermIdeal.pullback (m := n) f I)
    (idealPow (GermIdeal.pullback (m := n) f (vanishingIdeal (n := n) D)) q) = _
  rw [hD,empty_vanishing_unit (A := A),BlowupExceptionalDivisor.pullback_unitIdeal,
    idealPow_unitIdeal,colon_unitIdeal (GermIdealPullbackCalculus.isCoherent_pullback hf.contMDiff hI)]

private theorem next_map_blowup {D : Set Y} {π : Z → Y} (hπ : IsBlowupAlong n D π) (W : Opens Y) :
    IsBlowupAlong n ((Subtype.val : W → Y) ⁻¹' D) (nextMap hπ W) :=
  BlowupRestrictOpen.isBlowupAlong_restrict hπ W (W.isOpen.preimage hπ.contMDiff.continuous)

private theorem next_bound (hn : 0 < n) (d : ℕ) (m : MarkedIdeal n X) (h : IsInvDomain d m)
    (T : BlowupTower X Y) (b : ValTy d) (W : Opens Y)
    (hb : ∀ y ∈ (geoTransformAlong m T).cosupp,y ∈ W → (invFamily hn d).inv m T y ≤ b)
    {D : Set Y} {π : Z → Y} (hπ : IsBlowupAlong n D π)
    (hc : IsCanonical m ((invFamily hn d).inv m) (.step T D π hπ)) :
    ∀ z ∈ (geoTransformAlong m (.step T D π hπ)).cosupp,z ∈ nextOpen hπ W →
      (invFamily hn d).inv m (.step T D π hπ) z ≤ b := by
  intro z hz hzW
  have hd := stepDrop_of_isInvValue (invFamily hn d).isInvValue h T D π hπ hc z hz
  have hbo := hb (π z) hd.1 hzW
  by_cases hzD : π z ∈ D
  · exact (hd.2.1 hzD).le.trans hbo
  · exact (hd.2.2 hzD).le.trans hbo

private theorem next_cut_empty_trace (hn : 0 < n) (d : ℕ) (m : MarkedIdeal n X)
    (h : IsInvDomain d m) (T : BlowupTower X Y)
    (hcT : IsCanonical m ((invFamily hn d).inv m) T) (b : ValTy d) (W : Opens Y)
    {D : Set Y} {π : Z → Y} (hπ : IsBlowupAlong n D π)
    (hc : IsCanonical m ((invFamily hn d).inv m) (.step T D π hπ))
    (hD : (Subtype.val : W → Y) ⁻¹' D=∅) :
    thresholdCut hn d m (.step T D π hπ) b (nextOpen hπ W)=
      (nextMap hπ W) ⁻¹' thresholdCut hn d m T b W := by
  have ht := (invFamily hn d).isInvValue.isGeoTestTower_of_isCanonical h T hcT
  have hdom := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T ht
  ext z
  have hzD : π z ∉ D := by
    intro hz
    have hh : (⟨π z,z.property⟩ : W) ∈ (Subtype.val : W → Y) ⁻¹' D := hz
    rw [hD] at hh
    exact hh
  have hcos := TransformOffCentre.mem_cosupp_geoTransform_iff (geoTransformAlong m T)
    hdom.isWellFormed.isClosedSubmanifold_N.1
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hdom.isWellFormed.isCoherent hg) hπ hzD
  constructor
  · rintro ⟨hz,hv⟩
    have hd := stepDrop_of_isInvValue (invFamily hn d).isInvValue h T D π hπ hc z hz
    exact ⟨hd.1,hv.trans (hd.2.2 hzD).le⟩
  · rintro ⟨hz,hv⟩
    have hz' : (z : Z) ∈ (geoTransformAlong m (.step T D π hπ)).cosupp := hcos.mpr hz
    have hd := stepDrop_of_isInvValue (invFamily hn d).isInvValue h T D π hπ hc z hz'
    exact ⟨hz',hv.trans (hd.2.2 hzD).symm.le⟩

private theorem attained_cut_trace (hn : 0 < n) (d : ℕ) (m : MarkedIdeal n X)
    (T : BlowupTower X Y) (b : ValTy d) (W : Opens Y)
    (hb : ∀ y ∈ (geoTransformAlong m T).cosupp,y ∈ W → (invFamily hn d).inv m T y ≤ b)
    (hne : (thresholdCut hn d m T b W).Nonempty)
    {D : Set Y} {π : Z → Y} (hπ : IsBlowupAlong n D π)
    (hc : IsCanonical m ((invFamily hn d).inv m) (.step T D π hπ)) :
    (Subtype.val : W → Y) ⁻¹' D=∅ ∨ (Subtype.val : W → Y) ⁻¹' D=thresholdCut hn d m T b W := by
  obtain ⟨p,hp,hpb⟩ := hne
  by_cases htrace : ((Subtype.val : W → Y) ⁻¹' D).Nonempty
  · obtain ⟨q,hq⟩ := htrace
    rcases hc.2 with hD | hD
    · exact False.elim (by have hh : (q : Y) ∈ D := hq; rw [hD] at hh; exact hh)
    · have hqmax := hD ▸ hq
      have hqb : (invFamily hn d).inv m T q=b := (hb q hqmax.1 q.property).antisymm
        (hpb.trans (hqmax.2 p hp))
      right
      ext z
      constructor
      · intro hz
        have hzmax := hD ▸ hz
        exact ⟨hzmax.1,hpb.trans (hzmax.2 p hp)⟩
      · rintro ⟨hz,hbz⟩
        rw [hD]
        exact ⟨hz,fun y hy => (hqmax.2 y hy).trans (hqb.le.trans hbz)⟩
  · exact Or.inl (not_nonempty_iff_eq_empty.mp htrace)

private theorem next_cut_full_trace_empty (hn : 0 < n) (d : ℕ) (m : MarkedIdeal n X)
    (h : IsInvDomain d m) (T : BlowupTower X Y) (b : ValTy d) (W : Opens Y)
    (hb : ∀ y ∈ (geoTransformAlong m T).cosupp,y ∈ W → (invFamily hn d).inv m T y ≤ b)
    {D : Set Y} {π : Z → Y} (hπ : IsBlowupAlong n D π)
    (hc : IsCanonical m ((invFamily hn d).inv m) (.step T D π hπ))
    (hD : (Subtype.val : W → Y) ⁻¹' D=thresholdCut hn d m T b W) :
    thresholdCut hn d m (.step T D π hπ) b (nextOpen hπ W)=∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  rintro z ⟨hz,hbz⟩
  have hd := stepDrop_of_isInvValue (invFamily hn d).isInvValue h T D π hπ hc z hz
  have hnoninc : (invFamily hn d).inv m (.step T D π hπ) z ≤ (invFamily hn d).inv m T (π z) := by
    by_cases hzD : π z ∈ D
    · exact (hd.2.1 hzD).le
    · exact (hd.2.2 hzD).le
  have hp : (⟨π z,z.property⟩ : W) ∈ thresholdCut hn d m T b W := ⟨hd.1,hbz.trans hnoninc⟩
  have hh : (⟨π z,z.property⟩ : W) ∈ (Subtype.val : W → Y) ⁻¹' D := hD.symm ▸ hp
  exact not_lt_of_ge hbz ((hd.2.1 hh).trans_le (hb (π z) hd.1 z.property))

/-- Genuine bounded-step induction closure, allowing the SAME fixed threshold
cut to be EMPTY. These explicit geometric/numerical induction hypotheses do
not assert a caller whole-tail presentation or a new attained reference. -/
theorem bounded_fixed_threshold_step (hn : 0 < n) (d : ℕ) (m : MarkedIdeal n X)
    (h : IsInvDomain d m) (T : BlowupTower X Y)
    (hcT : IsCanonical m ((invFamily hn d).inv m) T) (b : ValTy d) (W : Opens Y)
    (hb : ∀ y ∈ (geoTransformAlong m T).cosupp,y ∈ W → (invFamily hn d).inv m T y ≤ b)
    (hC : IsClosedSubmanifold n (thresholdCut hn d m T b W))
    {D : Set Y} {π : Z → Y} (hπ : IsBlowupAlong n D π)
    (hc : IsCanonical m ((invFamily hn d).inv m) (.step T D π hπ)) :
    IsClosedSubmanifold n (thresholdCut hn d m (.step T D π hπ) b (nextOpen hπ W)) ∧
    (∀ z ∈ (geoTransformAlong m (.step T D π hπ)).cosupp,z ∈ nextOpen hπ W →
      (invFamily hn d).inv m (.step T D π hπ) z ≤ b) ∧
    controlledTransform (next_map_blowup hπ W) (vanishingIdeal (n := n) (thresholdCut hn d m T b W)) 1 =
      vanishingIdeal (n := n) (thresholdCut hn d m (.step T D π hπ) b (nextOpen hπ W)) ∧
    (vanishingIdeal (n := n) (thresholdCut hn d m (.step T D π hπ) b (nextOpen hπ W))).IsCoherent := by
  have hbnext := next_bound hn d m h T b W hb hπ hc
  let C := thresholdCut hn d m T b W
  let Q := thresholdCut hn d m (.step T D π hπ) b (nextOpen hπ W)
  have hr := next_map_blowup hπ W
  suffices hp : IsClosedSubmanifold n Q ∧ controlledTransform hr (vanishingIdeal (n := n) C) 1=vanishingIdeal (n := n) Q by
    exact ⟨hp.1,hbnext,hp.2,VanishingIdealCoherent.isCoherent_vanishingIdeal hp.1⟩
  by_cases hne : C.Nonempty
  · rcases attained_cut_trace hn d m T b W hb hne hπ hc with hD | hD
    · have hQ := next_cut_empty_trace hn d m h T hcT b W hπ hc hD
      obtain ⟨g,hg,hfg,hgf,htrans⟩ := exists_empty_centre_inverse_geometry
        (A := CMfd.of (n := n) W) (B := CMfd.of (n := n) (nextOpen hπ W)) hr hD
      obtain ⟨hsm,hideal⟩ := htrans C hC
      have hQ' : Q=(nextMap hπ W) ⁻¹' C := hQ
      refine ⟨hQ'.symm ▸ hsm,?_⟩
      rw [controlledTransform_empty_centre (A := CMfd.of (n := n) W)
        (B := CMfd.of (n := n) (nextOpen hπ W)) hr hD (VanishingIdealCoherent.isCoherent_vanishingIdeal hC),hQ']
      exact hideal
    · have hQ := next_cut_full_trace_empty hn d m h T b W hb hπ hc hD
      have hQ' : Q=∅ := hQ
      have hD' : (Subtype.val : W → Y) ⁻¹' D=C := hD
      have hsm : IsClosedSubmanifold n Q := hQ'.symm ▸ ⟨isClosed_empty,by simp⟩
      refine ⟨hsm,?_⟩
      have hrC : IsBlowupAlong n C (nextMap hπ W) := hD' ▸ hr
      have hideal := BlowupStrictIdeal.controlledTransform_vanishingIdeal hrC hC subset_rfl
      rw [BlowupStrictIdeal.geoStrictTransform_self] at hideal
      rw [hQ']
      unfold controlledTransform at hideal ⊢
      change InvertibleIdealQuotient.colon _ (idealPow (GermIdeal.pullback (m := n) (nextMap hπ W)
        (vanishingIdeal (n := n) ((Subtype.val : W → Y) ⁻¹' D))) 1) = _
      rw [hD']
      exact hideal
  · have hCempty : C=∅ := not_nonempty_iff_eq_empty.mp hne
    have hQempty : Q=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro z ⟨hz,hbz⟩
      have hd := stepDrop_of_isInvValue (invFamily hn d).isInvValue h T D π hπ hc z hz
      have hnoninc : (invFamily hn d).inv m (.step T D π hπ) z ≤ (invFamily hn d).inv m T (π z) := by
        by_cases hzD : π z ∈ D
        · exact (hd.2.1 hzD).le
        · exact (hd.2.2 hzD).le
      have hp : (⟨π z,z.property⟩ : W) ∈ C := ⟨hd.1,hbz.trans hnoninc⟩
      rw [hCempty] at hp
      exact hp
    refine ⟨hQempty.symm ▸ ⟨isClosed_empty,by simp⟩,?_⟩
    rw [hCempty,hQempty,empty_vanishing_unit (A := CMfd.of (n := n) W),
      empty_vanishing_unit (A := CMfd.of (n := n) (nextOpen hπ W))]
    exact controlledTransform_unit (A := CMfd.of (n := n) W)
      (B := CMfd.of (n := n) (nextOpen hπ W)) hr 1

end
end Hironaka.HironakaOriginalReferenceValueBoundedStep
