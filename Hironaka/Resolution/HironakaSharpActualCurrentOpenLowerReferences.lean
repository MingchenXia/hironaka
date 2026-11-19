import Hironaka.Resolution.HironakaSharpActualFirstFullInvariantDrop

/-!
# Actual CURRENT-stage open comparison and unchanged original lower references

The open lies in the current endpoint and need not descend from the original
base. Actual blowup uniqueness constructs the comparison. Whole marked records,
order clocks and companion references are consequences, not incoming matching
certificates. Recursive persistent-tail value comparison and sharp termination
are separate obligations.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaSharpActualCurrentOpenLowerReferences
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit BlowupTowerIsomorphism
  BlowupRestrictOpen BlowupUniqueness MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen MarkedIdealTowerTransport
  InvDomainTowerAlong NonmonomialOrderLocal NonmonomialOrderRegime
  NonmonomialOrderTail NonmonomialOrderTransport StepOneRegime
  CompanionRebase GeneralValue GeneralCompare RelativePrincipalizationSpan
open ResolutionInvariantSpec (IsInvDomain)
variable {n k : ℕ} {X Y Z Z' : CMfd.{u} n}

/-- The actual inverse image of an open of the CURRENT target. -/
def stepWindow {C : Set Y} {π : Z → Y} (hπ : IsBlowupAlong n C π) (V : Opens Y) : Opens Z :=
  ⟨π ⁻¹' (V : Set Y), V.isOpen.preimage hπ.contMDiff.continuous⟩

/-- The literal projection of the actual step window onto the current open. -/
def windowProjection {C : Set Y} {π : Z → Y} (hπ : IsBlowupAlong n C π) (V : Opens Y) :
    stepWindow hπ V → V := fun z => ⟨π z.val, z.property⟩

/-- The actual order mask inside an arbitrary CURRENT open. -/
def referenceWindow (Q : MarkedIdeal n Z) (U : Opens Z) (o : ℕ) : Opens U :=
  ⟨(Subtype.val : U → Z) ⁻¹' ordMask Q o,
    (ordMask Q o).isOpen.preimage continuous_subtype_val⟩

/-- The literal inclusion of this current masked window into the original
order mask on which the actual companion reference was formed. -/
def referenceInclusion (Q : MarkedIdeal n Z) (U : Opens Z) (o : ℕ) :
    referenceWindow Q U o → ordMask Q o := fun z => ⟨z.val.val, z.property⟩

/-- Whole geometric equality of current centre traces internally produces the
UNIQUE actual comparison, without an incoming upper map or inverse. -/
theorem existsUnique_current_step_comparison {C C' : Set Y} {π : Z → Y} {π' : Z' → Y}
    (hπ : IsBlowupAlong n C π) (hπ' : IsBlowupAlong n C' π') (V : Opens Y)
    (hC : (Subtype.val : V → Y) ⁻¹' C = (Subtype.val : V → Y) ⁻¹' C') :
    ∃! η : stepWindow hπ V ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ stepWindow hπ' V,
      ∀ z : stepWindow hπ V, π' (η z).val = π z.val := by
  have h1 := isBlowupAlong_restrict hπ V (stepWindow hπ V).isOpen
  have h2 := isBlowupAlong_restrict hπ' V (stepWindow hπ' V).isOpen
  rw [← hC] at h2
  obtain ⟨e, f, he, hf, hsq, _hback, hfe, hef⟩ := exists_biholomorphism_over h1 h2
  let η : stepWindow hπ V ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ stepWindow hπ' V :=
    ⟨⟨e, f, congrFun hfe, congrFun hef⟩, he, hf⟩
  have hη : ∀ z : stepWindow hπ V, π' (η z).val = π z.val :=
    fun z => congrArg Subtype.val (congrFun hsq z)
  refine ⟨η, hη, ?_⟩
  intro θ hθ
  obtain ⟨g, _hg, hUnique⟩ := existsUnique_comparison h1 h2
  have hθg := hUnique θ ⟨θ.contMDiff, funext fun z => Subtype.ext (hθ z)⟩
  have hηg := hUnique η ⟨η.contMDiff, funext fun z => Subtype.ext (hη z)⟩
  apply Diffeomorph.ext
  exact congrFun (hθg.trans hηg.symm)

private theorem current_record_eq (Q : MarkedIdeal n Y) (hQ : Q.IsWellFormed)
    {C C' : Set Y} (hAdm : Q.IsAdmissibleCentre C) (hAdm' : Q.IsAdmissibleCentre C')
    {π : Z → Y} {π' : Z' → Y} (hπ : IsBlowupAlong n C π) (hπ' : IsBlowupAlong n C' π')
    (V : Opens Y) (hC : (Subtype.val : V → Y) ⁻¹' C = (Subtype.val : V → Y) ⁻¹' C')
    (η : stepWindow hπ V ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ stepWindow hπ' V)
    (hsq : ∀ z : stepWindow hπ V, π' (η z).val = π z.val) :
    MarkedIdeal.pullback (Subtype.val : stepWindow hπ V → Z) (Q.geoTransform C π) =
      MarkedIdeal.pullback η
        (MarkedIdeal.pullback (Subtype.val : stepWindow hπ' V → Z') (Q.geoTransform C' π')) := by
  let S : BlowupTower Y Z := .step .refl C π hπ
  let S' : BlowupTower Y Z' := .step .refl C' π' hπ'
  let QV := MarkedIdeal.pullback (Subtype.val : V → Y) Q
  have hQV := MarkedIdealRestrictOpen.IsWellFormed.pullback_val hQ V
  have hTest : IsGeoTestTower Q S := ⟨trivial, hAdm⟩
  have hTest' : IsGeoTestTower Q S' := ⟨trivial, hAdm'⟩
  have hiso : IsTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) V ∞)
      (restrict V S) (restrict V S') η := by
    refine IsTowerIso.step (X := CMfd.of (n := n) V) (X' := CMfd.of (n := n) V)
      (Y := CMfd.of (n := n) V) (Y' := CMfd.of (n := n) V)
      (Z' := CMfd.of (n := n) (stepWindow hπ V)) (Z := CMfd.of (n := n) (stepWindow hπ' V))
      (π' := windowProjection hπ V) (π := windowProjection hπ' V) .refl
      (isBlowupAlong_restrict hπ V (stepWindow hπ V).isOpen)
      (isBlowupAlong_restrict hπ' V (stepWindow hπ' V).isOpen) η
      (fun z => Subtype.ext (hsq z)) ?_
    exact hC.symm
  have hrec := IsTowerIso.geoTransformAlong_eq
    (X := CMfd.of (n := n) V) (X' := CMfd.of (n := n) V) (𝔪 := QV)
    (T' := restrict V S) (T := restrict V S') (χ := η)
    (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) V ∞)
    hQV.isClosedSubmanifold_N hQV.isCoherent hiso
    (isGeoTestTower_restrict V hQ.isClosedSubmanifold_N hQ.isCoherent S' hTest')
  change geoTransformAlong (MarkedIdeal.pullback (id : V → V) QV) (restrict V S) = _ at hrec
  rw [ContactCanonicalAlong.pullback_id _ hQV.isCoherent,
    geoTransformAlong_restrict V hQ.isClosedSubmanifold_N hQ.isCoherent S hTest,
    geoTransformAlong_restrict V hQ.isClosedSubmanifold_N hQ.isCoherent S' hTest'] at hrec
  exact hrec

/-- Whole records and ALL unchanged-original order-regime clocks on an actual
CURRENT open; the genuine comparison is constructed internally. -/
theorem exists_current_step_record_and_clocks (hn : 0 < n) (M : MarkedIdeal n X)
    (hM : IsInvDomain k M) (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    {C C' : Set Y} (hAdm : (geoTransformAlong M T).IsAdmissibleCentre C)
    (hAdm' : (geoTransformAlong M T).IsAdmissibleCentre C')
    {π : Z → Y} {π' : Z' → Y} (hπ : IsBlowupAlong n C π) (hπ' : IsBlowupAlong n C' π')
    (V : Opens Y) (hC : (Subtype.val : V → Y) ⁻¹' C = (Subtype.val : V → Y) ⁻¹' C') :
    ∃ η : stepWindow hπ V ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ stepWindow hπ' V,
      (∀ z : stepWindow hπ V, π' (η z).val = π z.val) ∧
      MarkedIdeal.pullback (Subtype.val : stepWindow hπ V → Z)
          (geoTransformAlong M (.step T C π hπ)) =
        MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : stepWindow hπ' V → Z')
          (geoTransformAlong M (.step T C' π' hπ'))) ∧
      (∀ z : stepWindow hπ V,
        nmOrd (geoTransformAlong M (.step T C π hπ)) z.val =
          nmOrd (geoTransformAlong M (.step T C' π' hπ')) (η z).val) ∧
      (∀ (q : ℕ) (z : stepWindow hπ V),
        z.val ∈ ordGe (geoTransformAlong M (.step T C π hπ)) q ↔
          (η z).val ∈ ordGe (geoTransformAlong M (.step T C' π' hπ')) q) ∧
      ∀ (o : ℕ) (z : stepWindow hπ V),
        regimeRun (OrdRegime M o) (.step T C π hπ) z.val =
          regimeRun (OrdRegime M o) (.step T C' π' hπ') (η z).val := by
  obtain ⟨η, hsq, _hUnique⟩ := existsUnique_current_step_comparison hπ hπ' V hC
  have hQ := isInvDomain_geoTransformAlong hM T hT
  have hrec := current_record_eq (geoTransformAlong M T) hQ.isWellFormed hAdm hAdm' hπ hπ' V hC η hsq
  change MarkedIdeal.pullback (Subtype.val : stepWindow hπ V → Z)
      (geoTransformAlong M (.step T C π hπ)) =
    MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : stepWindow hπ' V → Z')
      (geoTransformAlong M (.step T C' π' hπ'))) at hrec
  have hA := isInvDomain_geoTransformAlong hM (.step T C π hπ) ⟨hT, hAdm⟩
  have hB := isInvDomain_geoTransformAlong hM (.step T C' π' hπ') ⟨hT, hAdm'⟩
  have hBW := isInvDomain_pullback_val (stepWindow hπ' V) hB
  have hge (q : ℕ) (z : stepWindow hπ V) :
      z.val ∈ ordGe (geoTransformAlong M (.step T C π hπ)) q ↔
        (η z).val ∈ ordGe (geoTransformAlong M (.step T C' π' hπ')) q := by
    rw [← mem_ordGe_pullback_val_iff hn hA.isWellFormed hA.isNonzeroAlongAt (stepWindow hπ V) q z,
      hrec, mem_ordGe_pullback_diffeo_iff
        (M := CMfd.of (n := n) (stepWindow hπ' V)) (M' := CMfd.of (n := n) (stepWindow hπ V))
        hn η hBW.isWellFormed hBW.isNonzeroAlongAt q z,
      mem_ordGe_pullback_val_iff hn hB.isWellFormed hB.isNonzeroAlongAt (stepWindow hπ' V) q (η z)]
  refine ⟨η, hsq, hrec, ?_, hge, ?_⟩
  · intro z
    exact nmOrd_congr fun q => hge q z
  · intro o z
    rw [regimeRun_step, regimeRun_step, hsq z]

private theorem companion_window_eq (hn : 0 < n)
    {A : MarkedIdeal n Z} {B : MarkedIdeal n Z'} (hA : IsInvDomain k A) (hB : IsInvDomain k B)
    (U : Opens Z) (U' : Opens Z')
    (η : U ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ U')
    (hrec : MarkedIdeal.pullback (Subtype.val : U → Z) A =
      MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') B)) (o : ℕ) :
    MarkedIdeal.pullback (Subtype.val : U → Z) (companionOf n A o) =
      MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') (companionOf n B o)) := by
  have hBW := isInvDomain_pullback_val U' hB
  calc
    MarkedIdeal.pullback (Subtype.val : U → Z) (companionOf n A o) =
        companionOf n (M := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → Z) A) o :=
      pullback_val_companionOf hn hA.isWellFormed hA.isNonzeroAlongAt U o
    _ = companionOf n (M := CMfd.of (n := n) U)
        (MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') B)) o :=
      congrArg (fun Q => companionOf n (M := CMfd.of (n := n) U) Q o) hrec
    _ = MarkedIdeal.pullback η
        (companionOf n (M := CMfd.of (n := n) U') (MarkedIdeal.pullback (Subtype.val : U' → Z') B) o) :=
      (pullback_diffeo_companionOf (M := CMfd.of (n := n) U') (M' := CMfd.of (n := n) U)
        hn η hBW.isWellFormed hBW.isNonzeroAlongAt o).symm
    _ = MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') (companionOf n B o)) :=
      congrArg (MarkedIdeal.pullback η) (pullback_val_companionOf hn hB.isWellFormed hB.isNonzeroAlongAt U' o).symm

/-- The ACTUAL `compAt` reference on a genuine current masked window is the
whole pullback of its actual companion; no reflexive current restart is used. -/
theorem companion_reference_on_current_window (hn : 0 < n) (M : MarkedIdeal n X)
    (hM : IsInvDomain k M) (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (U : Opens Y) {o : ℕ} (ho : 1 ≤ o) :
    MarkedIdeal.pullback (referenceInclusion (geoTransformAlong M T) U o) (compAt M o T) =
      MarkedIdeal.pullback (fun z : referenceWindow (geoTransformAlong M T) U o => z.val.val)
        (companionOf n (geoTransformAlong M T) o) := by
  have hQ := isInvDomain_geoTransformAlong hM T hT
  have hComp := InvDomainCompanion.isInvDomain_companionAlong hn hQ ho
  have hi : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (referenceInclusion (geoTransformAlong M T) U o) :=
    BlowupRestrictOpen.contMDiff_opens_mk
      (contMDiff_subtype_val.comp contMDiff_subtype_val) (fun z => z.property)
  rw [compAt_eq_pullback hn o T hQ]
  exact StepOneTangentChange.pullback_pullback_of_comp hComp.isWellFormed.isCoherent
    contMDiff_subtype_val hi (fun _ => rfl)

private theorem masked_companion_window_eq (hn : 0 < n)
    {A : MarkedIdeal n Z} {B : MarkedIdeal n Z'} (hA : IsInvDomain k A) (hB : IsInvDomain k B)
    (U : Opens Z) (U' : Opens Z')
    (η : U ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ U')
    (hrec : MarkedIdeal.pullback (Subtype.val : U → Z) A =
      MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') B))
    (hge : ∀ (q : ℕ) (z : U), z.val ∈ ordGe A q ↔ (η z).val ∈ ordGe B q)
    {o : ℕ} (ho : 1 ≤ o) :
    ∃ ψ : referenceWindow A U o ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ referenceWindow B U' o,
      (∀ z : referenceWindow A U o, (ψ z).val = η z.val) ∧
      MarkedIdeal.pullback (fun z : referenceWindow A U o => z.val.val) (companionOf n A o) =
        MarkedIdeal.pullback ψ
          (MarkedIdeal.pullback (fun z : referenceWindow B U' o => z.val.val) (companionOf n B o)) := by
  have hW (z : U) : z ∈ referenceWindow A U o ↔ η z ∈ referenceWindow B U' o := by
    change z.val ∈ ordMask A o ↔ (η z).val ∈ ordMask B o
    rw [mem_ordMask_iff hn hA.isWellFormed hA.isNonzeroAlongAt o z.val,
      mem_ordMask_iff hn hB.isWellFormed hB.isNonzeroAlongAt o (η z).val]
    exact not_congr (hge (o + 1) z)
  let ψ := StepOneTangentChange.diffeoOpens
    (X' := CMfd.of (n := n) U) (X := CMfd.of (n := n) U')
    η (referenceWindow A U o) (referenceWindow B U' o) hW
  have hψ : ∀ z : referenceWindow A U o, (ψ z).val = η z.val := fun _ => rfl
  have hAc := (InvDomainCompanion.isInvDomain_companionAlong hn hA ho).isWellFormed.isCoherent
  have hBc := (InvDomainCompanion.isInvDomain_companionAlong hn hB ho).isWellFormed.isCoherent
  have hBWc : (MarkedIdeal.pullback (Subtype.val : U' → Z') (companionOf n B o)).ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hBc
  have hc := companion_window_eq hn hA hB U U' η hrec o
  refine ⟨ψ, hψ, ?_⟩
  calc
    MarkedIdeal.pullback (fun z : referenceWindow A U o => z.val.val) (companionOf n A o) =
        MarkedIdeal.pullback (Subtype.val : referenceWindow A U o → U)
          (MarkedIdeal.pullback (Subtype.val : U → Z) (companionOf n A o)) :=
      (StepOneTangentChange.pullback_pullback_of_comp hAc
        contMDiff_subtype_val contMDiff_subtype_val (fun _ => rfl)).symm
    _ = MarkedIdeal.pullback (Subtype.val : referenceWindow A U o → U)
        (MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') (companionOf n B o))) :=
      congrArg (MarkedIdeal.pullback (Subtype.val : referenceWindow A U o → U)) hc
    _ = MarkedIdeal.pullback (fun z : referenceWindow A U o => η z.val)
        (MarkedIdeal.pullback (Subtype.val : U' → Z') (companionOf n B o)) :=
      StepOneTangentChange.pullback_pullback_of_comp hBWc
        η.contMDiff contMDiff_subtype_val (fun _ => rfl)
    _ = MarkedIdeal.pullback (fun z : referenceWindow A U o => (η z.val).val) (companionOf n B o) :=
      StepOneTangentChange.pullback_pullback_of_comp hBc
        contMDiff_subtype_val (η.contMDiff.comp contMDiff_subtype_val) (fun _ => rfl)
    _ = MarkedIdeal.pullback (fun z : referenceWindow A U o => (ψ z).val.val) (companionOf n B o) := rfl
    _ = MarkedIdeal.pullback ψ
        (MarkedIdeal.pullback (fun z : referenceWindow B U' o => z.val.val) (companionOf n B o)) :=
      (StepOneTangentChange.pullback_pullback_of_comp hBc
        (contMDiff_subtype_val.comp contMDiff_subtype_val) ψ.contMDiff (fun _ => rfl)).symm

/-- The SAME internally constructed current-open comparison carries actual
fresh masked companion references and every persistent original start head.
No matched-reference, value or locality conclusion is an input. -/
theorem exists_current_step_lower_references (hn : 0 < n) (M : MarkedIdeal n X)
    (hM : IsInvDomain k M) (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    {C C' : Set Y} (hAdm : (geoTransformAlong M T).IsAdmissibleCentre C)
    (hAdm' : (geoTransformAlong M T).IsAdmissibleCentre C')
    {π : Z → Y} {π' : Z' → Y} (hπ : IsBlowupAlong n C π) (hπ' : IsBlowupAlong n C' π')
    (V : Opens Y) (hC : (Subtype.val : V → Y) ⁻¹' C = (Subtype.val : V → Y) ⁻¹' C') :
    ∃ η : stepWindow hπ V ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ stepWindow hπ' V,
      (∀ z : stepWindow hπ V, π' (η z).val = π z.val) ∧
      MarkedIdeal.pullback (Subtype.val : stepWindow hπ V → Z)
          (geoTransformAlong M (.step T C π hπ)) =
        MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : stepWindow hπ' V → Z')
          (geoTransformAlong M (.step T C' π' hπ'))) ∧
      (∀ z : stepWindow hπ V,
        nmOrd (geoTransformAlong M (.step T C π hπ)) z.val =
          nmOrd (geoTransformAlong M (.step T C' π' hπ')) (η z).val) ∧
      (∀ (o : ℕ) (z : stepWindow hπ V),
        regimeRun (OrdRegime M o) (.step T C π hπ) z.val =
          regimeRun (OrdRegime M o) (.step T C' π' hπ') (η z).val) ∧
      (∀ o : ℕ, MarkedIdeal.pullback (Subtype.val : stepWindow hπ V → Z)
          (companionOf n (geoTransformAlong M (.step T C π hπ)) o) =
        MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : stepWindow hπ' V → Z')
          (companionOf n (geoTransformAlong M (.step T C' π' hπ')) o))) ∧
      (∀ (o : ℕ) (z : stepWindow hπ V),
        z.val ∈ ordMask (geoTransformAlong M (.step T C π hπ)) o ↔
          (η z).val ∈ ordMask (geoTransformAlong M (.step T C' π' hπ')) o) ∧
      (∀ (o : ℕ), 1 ≤ o →
        ∃ ψ : referenceWindow (geoTransformAlong M (.step T C π hπ)) (stepWindow hπ V) o
            ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
              referenceWindow (geoTransformAlong M (.step T C' π' hπ')) (stepWindow hπ' V) o,
          (∀ z, (ψ z).val = η z.val) ∧
          MarkedIdeal.pullback
              (referenceInclusion (geoTransformAlong M (.step T C π hπ)) (stepWindow hπ V) o)
              (compAt M o (.step T C π hπ)) =
            MarkedIdeal.pullback ψ (MarkedIdeal.pullback
              (referenceInclusion (geoTransformAlong M (.step T C' π' hπ')) (stepWindow hπ' V) o)
              (compAt M o (.step T C' π' hπ')))) ∧
      ∀ (o j : ℕ) (z : stepWindow hπ V),
        regimeRun (OrdRegime M o) (.step T C π hπ) z.val = j + 1 →
          compAt M o (head (.step T C π hπ) (j + 1)) = compAt M o (head T j) ∧
          compAt M o (head (.step T C' π' hπ') (j + 1)) = compAt M o (head T j) ∧
          (tail (.step T C π hπ) (j + 1)).proj z.val =
            (tail (.step T C' π' hπ') (j + 1)).proj (η z).val := by
  obtain ⟨η, hsq, hrec, horder, hge, hRun⟩ :=
    exists_current_step_record_and_clocks hn M hM T hT hAdm hAdm' hπ hπ' V hC
  have hA := isInvDomain_geoTransformAlong hM (.step T C π hπ) ⟨hT, hAdm⟩
  have hB := isInvDomain_geoTransformAlong hM (.step T C' π' hπ') ⟨hT, hAdm'⟩
  refine ⟨η, hsq, hrec, horder, hRun, ?_, ?_, ?_, ?_⟩
  · exact fun o => companion_window_eq hn hA hB (stepWindow hπ V) (stepWindow hπ' V) η hrec o
  · intro o z
    rw [mem_ordMask_iff hn hA.isWellFormed hA.isNonzeroAlongAt o z.val,
      mem_ordMask_iff hn hB.isWellFormed hB.isNonzeroAlongAt o (η z).val]
    exact not_congr (hge (o + 1) z)
  · intro o ho
    obtain ⟨ψ, hψ, hFresh⟩ := masked_companion_window_eq hn hA hB
      (stepWindow hπ V) (stepWindow hπ' V) η hrec hge ho
    have hLeft := companion_reference_on_current_window hn M hM (.step T C π hπ)
      ⟨hT, hAdm⟩ (stepWindow hπ V) ho
    have hRight := companion_reference_on_current_window hn M hM (.step T C' π' hπ')
      ⟨hT, hAdm'⟩ (stepWindow hπ' V) ho
    exact ⟨ψ, hψ, hLeft.trans (hFresh.trans (congrArg (MarkedIdeal.pullback ψ) hRight).symm)⟩
  · intro o j z _hRun
    refine ⟨rfl, rfl, ?_⟩
    exact congrArg (tail T j).proj (hsq z).symm

end
end Hironaka.HironakaSharpActualCurrentOpenLowerReferences
