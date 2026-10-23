/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaCompactCosupportOpenTowerExtension

/-!
# Extending a prescribed finite history over the whole cosupport

A closed original cosupport contained in the chosen open makes every actual
local admissible centre globally closed.  This replaces compactness in the
genuine blowup-existence and universal-uniqueness construction.  The result
retains the entire prescribed tower and whole transformed marked record.
It does not construct local resolving histories or a locally finite scheduler.
Blueprint: `hironaka-open-cosupport-history-extension.tex`.
-/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOpenCosupportHistoryExtension
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen MarkedIdealTowerTransport
  BlowupTowerIsomorphism BlowupRestrictOpen BlowupExistence BlowupUniqueness
  AnalyticSubsetOpens GermIdealPullbackCalculus

/-- A relatively closed subset supported in an ambient closed subset wholly
inside the open has a genuinely closed image in the original space. -/
theorem isClosed_image_val_of_closed_carrier {X : Type u} [TopologicalSpace X]
    {U : Opens X} {F : Set X} (hF : IsClosed F) (hFU : F ⊆ U)
    {C : Set U} (hC : IsClosed C) (hCF : (Subtype.val : U → X) '' C ⊆ F) :
    IsClosed ((Subtype.val : U → X) '' C) := by
  obtain ⟨B, hB, hBC⟩ := Topology.IsInducing.subtypeVal.isClosed_iff.mp hC
  have hImage : (Subtype.val : U → X) '' C = F ∩ B := by
    ext x
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨hCF ⟨c, hc, rfl⟩, ?_⟩
      have hcB : c ∈ (Subtype.val : U → X) ⁻¹' B := hBC.symm ▸ hc
      exact hcB
    · rintro ⟨hxF, hxB⟩
      refine ⟨⟨x, hFU hxF⟩, ?_, rfl⟩
      rw [← hBC]
      exact hxB
  rw [hImage]
  exact hF.inter hB

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {M : MarkedIdeal n X} {U : Opens X} {C : Set U}

/-- The whole local centre is admissible for the original marked ideal:
closedness follows from the actual closed cosupport, with no compactness input. -/
theorem isAdmissibleCentre_image_val (hM : M.IsWellFormed) (hU : M.cosupp ⊆ U)
    (hC : (MarkedIdeal.pullback (Subtype.val : U → X) M).IsAdmissibleCentre C) :
    M.IsAdmissibleCentre ((Subtype.val : U → X) '' C) := by
  have hSub : (Subtype.val : U → X) '' C ⊆ M.cosupp := by
    rintro _ ⟨c, hc, rfl⟩
    have hmem := hC.2.1 hc
    rw [cosupp_pullback_val M
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
        hM.isCoherent hg) U] at hmem
    exact hmem
  have hClosed : IsClosed ((Subtype.val : U → X) '' C) :=
    isClosed_image_val_of_closed_carrier
      (GiraudAlong.isClosed_cosupport_along hM.isCoherent hM.isClosedSubmanifold_N M.d)
      hU hC.1.1 hSub
  refine ⟨⟨hClosed, ?_⟩, hSub,
    HironakaCompactOpenBlowupExtension.hasNormalCrossings_image_val hC.2.2⟩
  rintro _ ⟨c, hc, rfl⟩
  obtain ⟨k, hk⟩ := hC.1.2 c hc
  exact ⟨k, regularAtDim_image_val_iff.mpr hk⟩

/-- Actual blowup existence and uniqueness extend the SAME prescribed local
step and construct its endpoint biholomorphism over the original inclusion. -/
theorem exists_step_extension (hM : M.IsWellFormed) (hU : M.cosupp ⊆ U)
    (hC : (MarkedIdeal.pullback (Subtype.val : U → X) M).IsAdmissibleCentre C)
    {Y : CMfd.{u} n} {π : Y → U} (hπ : IsBlowupAlong n C π) :
    ∃ (Z : CMfd.{u} n) (q : Z → X)
      (hq : IsBlowupAlong n ((Subtype.val : U → X) '' C) q),
      M.IsAdmissibleCentre ((Subtype.val : U → X) '' C) ∧
      ∃ χ : Y ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
          (⟨q ⁻¹' (U : Set X), U.isOpen.preimage hq.contMDiff.continuous⟩ : Opens Z),
        ∀ y : Y, q (χ y).val = (π y).val := by
  have hAmbient := isAdmissibleCentre_image_val hM hU hC
  obtain ⟨Z, tZ, cZ, mZ, q, hq⟩ := exists_isBlowupAlong
    ((Subtype.val : U → X) '' C) hAmbient.1
    (HironakaCompactOpenBlowupExtension.interior_image_val_eq_empty hπ.2.1)
  let : TopologicalSpace Z := tZ
  let : ChartedSpace (ComplexModel n) Z := cZ
  let : IsComplexManifold n Z := mZ
  let V : Opens Z := ⟨q ⁻¹' (U : Set X), U.isOpen.preimage hq.contMDiff.continuous⟩
  let r : V → U := fun p => ⟨q p.val, p.property⟩
  have hr : IsBlowupAlong n C r := by
    simpa only [Subtype.val_injective.preimage_image] using
      isBlowupAlong_restrict hq U V.isOpen
  obtain ⟨e, f, he, hf, hqe, _hπf, hfe, hef⟩ := exists_biholomorphism_over hπ hr
  refine ⟨⟨Z⟩, q, hq, hAmbient, ⟨⟨e, f, congrFun hfe, congrFun hef⟩, he, hf⟩, ?_⟩
  intro y
  exact congrArg Subtype.val (congrFun hqe y)

section History
variable {X : CMfd.{u} n}

/-- Construct a genuine ambient test tower extending the SAME prescribed finite
history, together with the entire tower isomorphism and whole marked-record
identity.  The open contains the entire original cosupport; no compactness,
global-centre closedness, output testness or comparison is assumed. -/
theorem exists_extension (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (U : Opens X) (hU : M.cosupp ⊆ U) {Z : CMfd.{u} n}
    (T : BlowupTower (CMfd.of (n := n) U) Z)
    (hT : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → X) M) T) :
    ∃ (Y : CMfd.{u} n) (Q : BlowupTower X Y), IsGeoTestTower M Q ∧
      ∃ e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ openPreimage Q U,
        IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞) T (restrict U Q) e ∧
        T.length = Q.length ∧
        geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) M) T =
          MarkedIdeal.pullback (fun p => (e p).val) (geoTransformAlong M Q) := by
  have hN := hM.isClosedSubmanifold_N
  have hI := hM.isCoherent
  have hNU : IsClosedSubmanifold n (MarkedIdeal.pullback (Subtype.val : U → X) M).N :=
    isClosedSubmanifold_preimage_val hN U
  have hIU : (MarkedIdeal.pullback (Subtype.val : U → X) M).ideal.IsCoherent :=
    isCoherent_pullback contMDiff_subtype_val hI
  have hExtend : ∃ (Y : CMfd.{u} n) (Q : BlowupTower X Y), IsGeoTestTower M Q ∧
      ∃ e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ openPreimage Q U,
        IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞) T (restrict U Q) e := by
    induction T with
    | refl =>
      exact ⟨X, .refl, trivial, Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞, .refl⟩
    | @step A B T C π hπ ih =>
      obtain ⟨Y, Q, hQ, e, he⟩ := ih hT.1
      let V : Opens Y := openPreimage Q U
      let D : Set V := e.symm ⁻¹' C
      have hDpre : e ⁻¹' D = C := by
        ext c
        simp only [D, mem_preimage, e.symm_apply_apply]
      have hMoved : IsBlowupAlong n D (e ∘ π) :=
        MarkedIdealBiholomorphism.isBlowupAlong_comp_inverse e.symm.contMDiff e.contMDiff
          e.symm_apply_apply e.apply_symm_apply hπ
      have hMQ := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM Q hQ
      have hIV : (MarkedIdeal.pullback (Subtype.val : V → Y)
          (geoTransformAlong M Q)).ideal.IsCoherent :=
        isCoherent_pullback contMDiff_subtype_val hMQ.isCoherent
      have hRec := IsTowerIso.geoTransformAlong_eq
        (X := CMfd.of (n := n) U) (X' := CMfd.of (n := n) U)
        (𝔪 := MarkedIdeal.pullback (Subtype.val : U → X) M)
        (T' := T) (T := restrict U Q) (χ := e)
        (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞) hNU hIU he
        (isGeoTestTower_restrict U hN hI Q hQ)
      change geoTransformAlong (MarkedIdeal.pullback (id : U → U)
        (MarkedIdeal.pullback (Subtype.val : U → X) M)) T = _ at hRec
      rw [ContactCanonicalAlong.pullback_id _ hIU,
        geoTransformAlong_restrict U hN hI Q hQ] at hRec
      have hDC : (MarkedIdeal.pullback (Subtype.val : V → Y)
          (geoTransformAlong M Q)).IsAdmissibleCentre D := by
        apply (isAdmissibleCentre_pullback_iff (Φ := e) hIV).mp
        rw [hDpre, ← hRec]
        exact hT.2
      have hV : (geoTransformAlong M Q).cosupp ⊆ V :=
        fun _ hy => hU (StepOneLowerDomain.proj_mem_cosupp_of_mem_cosupp hN hI Q hQ hy)
      obtain ⟨W, q, hq, hAmbient, ξ, hξ⟩ := exists_step_extension hMQ hV hDC hMoved
      refine ⟨W, .step Q ((Subtype.val : V → Y) '' D) q hq,
        ⟨hQ, hAmbient⟩, ξ, ?_⟩
      refine IsTowerIso.step
        (Z := CMfd.of (n := n)
          (openPreimage (.step Q ((Subtype.val : V → Y) '' D) q hq) U))
        he hπ (isBlowupAlong_restrict hq V
          (V.isOpen.preimage hq.contMDiff.continuous)) ξ ?_ ?_
      · intro p
        apply Subtype.ext
        exact hξ p
      · change e ⁻¹' ((Subtype.val : V → Y) ⁻¹'
          ((Subtype.val : V → Y) '' D)) = C
        rw [Subtype.val_injective.preimage_image]
        exact hDpre
  obtain ⟨Y, Q, hQ, e, he⟩ := hExtend
  refine ⟨Y, Q, hQ, e, he, ?_, ?_⟩
  · exact he.length_eq.trans (length_restrict U Q)
  · have hRec := IsTowerIso.geoTransformAlong_eq
      (X := CMfd.of (n := n) U) (X' := CMfd.of (n := n) U)
      (𝔪 := MarkedIdeal.pullback (Subtype.val : U → X) M)
      (T' := T) (T := restrict U Q) (χ := e)
      (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞) hNU hIU he
      (isGeoTestTower_restrict U hN hI Q hQ)
    change geoTransformAlong (MarkedIdeal.pullback (id : U → U)
      (MarkedIdeal.pullback (Subtype.val : U → X) M)) T = _ at hRec
    rw [ContactCanonicalAlong.pullback_id _ hIU,
      geoTransformAlong_restrict U hN hI Q hQ] at hRec
    exact hRec.trans (StepOneTangentChange.pullback_pullback_of_comp
      (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM Q hQ).isCoherent
      contMDiff_subtype_val e.contMDiff (fun _ => rfl))

end History
end
end Hironaka.HironakaOpenCosupportHistoryExtension
