import Hironaka.Resolution.HironakaSharpActualCurrentOpenLowerReferences
import Hironaka.Resolution.HironakaCoherentTransformExtension
import Hironaka.Resolution.HironakaActualLocallyFiniteLimitStrictTransforms
import Hironaka.Coherence.CartanIrreducible

/-!
# Whole analytic transforms of arbitrary actual blowup histories

Analytic carriers and general coherent colons give genuine whole controlled
ideals without a test-history or centre-containment premise. This is a record
locality producer, not a recursive invariant-value or termination certificate.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaActualNoncanonicalAnalyticTransformLocality
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupRestrictOpen MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen GermIdealPullbackCalculus
  HironakaCoherentTransformExtension HironakaActualLocallyFiniteLimitStrictTransforms
  HironakaSharpActualCurrentOpenLowerReferences
variable {n : ℕ} {X Y Z Z' : CMfd.{u} n}

/-- No admissibility or centre-containment premise is needed for the actual
analytic strict carrier and the actual whole controlled ideal. -/
theorem analytic_and_coherent_geoTransform (M : MarkedIdeal n X)
    (hN : IsComplexAnalyticSubset (n := n) M.N) (hI : M.ideal.IsCoherent)
    {C : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π) :
    IsComplexAnalyticSubset (n := n) (M.geoTransform C π).N ∧
      (M.geoTransform C π).ideal.IsCoherent := by
  have hN' : IsComplexAnalyticSubset (n := n) (M.geoTransform C π).N := by
    change IsComplexAnalyticSubset (n := n) (closure (π ⁻¹' (M.N \ C)))
    rw [preimage_sdiff]
    exact ClosureDifferenceAnalytic.isComplexAnalyticSubset_closure_diff
      (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hπ.contMDiff hN)
      (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hπ.contMDiff
        (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hπ.1))
  refine ⟨hN', ?_⟩
  exact isCoherent_colonAlong_without_inclusion (isCoherent_pullback hπ.contMDiff hI)
    (CartanIrreducible.cartanCoherence _ hN')
    (isCoherent_idealPow (isCoherent_pullback hπ.contMDiff
      (BlowupExceptionalDivisor.isCoherent_vanishingIdeal_centre hπ)) M.d)

/-- The actual entire transformed ideal is coherent at EVERY original prefix,
even for towers which are not test towers of this marked record. -/
theorem analytic_and_coherent_geoTransformAlong (M : MarkedIdeal n X)
    (hN : IsComplexAnalyticSubset (n := n) M.N) (hI : M.ideal.IsCoherent) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      IsComplexAnalyticSubset (n := n) (geoTransformAlong M T).N ∧
        (geoTransformAlong M T).ideal.IsCoherent
  | _, .refl => ⟨hN, hI⟩
  | _, .step T C π hπ => by
    obtain ⟨hNT, hIT⟩ := analytic_and_coherent_geoTransformAlong M hN hI T
    exact analytic_and_coherent_geoTransform (geoTransformAlong M T) hNT hIT hπ

/-- Whole marked-record restriction on an arbitrary actual history, with no
incoming canonical or test-history certificate. -/
theorem geoTransformAlong_restrict (M : MarkedIdeal n X)
    (hN : IsComplexAnalyticSubset (n := n) M.N) (hI : M.ideal.IsCoherent) (U : Opens X) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) M) (restrict U T) =
        MarkedIdeal.pullback (Subtype.val : openPreimage T U → Y) (geoTransformAlong M T)
  | _, .refl => rfl
  | _, .step T C π hπ => by
    have ih := geoTransformAlong_restrict M hN hI U T
    have hcT := (analytic_and_coherent_geoTransformAlong M hN hI T).2
    have hcPost := (analytic_and_coherent_geoTransformAlong M hN hI (.step T C π hπ)).2
    change (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) M) (restrict U T)).geoTransform
      ((Subtype.val : openPreimage T U → _) ⁻¹' C)
      (fun p : openPreimage (.step T C π hπ) U => ⟨π p.val, p.property⟩) = _
    rw [ih]
    exact geoTransform_pullback_val hcT hπ hcPost (openPreimage T U)
      (openPreimage (.step T C π hπ) U).isOpen

private theorem current_record_eq (Q : MarkedIdeal n Y)
    (hN : IsComplexAnalyticSubset (n := n) Q.N) (hI : Q.ideal.IsCoherent)
    {C C' : Set Y} {π : Z → Y} {π' : Z' → Y}
    (hπ : IsBlowupAlong n C π) (hπ' : IsBlowupAlong n C' π') (V : Opens Y)
    (hC : (Subtype.val : V → Y) ⁻¹' C = (Subtype.val : V → Y) ⁻¹' C')
    (η : stepWindow hπ V ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ stepWindow hπ' V)
    (hsq : ∀ z : stepWindow hπ V, π' (η z).val = π z.val) :
    MarkedIdeal.pullback (Subtype.val : stepWindow hπ V → Z) (Q.geoTransform C π) =
      MarkedIdeal.pullback η
        (MarkedIdeal.pullback (Subtype.val : stepWindow hπ' V → Z') (Q.geoTransform C' π')) := by
  let QV := MarkedIdeal.pullback (Subtype.val : V → Y) Q
  let CV : Set V := (Subtype.val : V → Y) ⁻¹' C'
  have hIV : QV.ideal.IsCoherent := isCoherent_pullback contMDiff_subtype_val hI
  have hNV : IsComplexAnalyticSubset (n := n) QV.N :=
    AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hN V
  have hπV := isBlowupAlong_restrict hπ' V (stepWindow hπ' V).isOpen
  have hpostV := (analytic_and_coherent_geoTransform
    (X := CMfd.of (n := n) V) (Y := CMfd.of (n := n) (stepWindow hπ' V)) QV hNV hIV hπV).2
  have hICV := BlowupExceptionalDivisor.isCoherent_vanishingIdeal_centre hπV
  have hr' : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (windowProjection hπ' V) :=
    BlowupRestrictOpen.contMDiff_opens_mk
      (hπ'.contMDiff.comp contMDiff_subtype_val) (fun z => z.property)
  have hproj : windowProjection hπ V = windowProjection hπ' V ∘ η := by
    funext z
    exact Subtype.ext (hsq z).symm
  have hnatural : QV.geoTransform CV (windowProjection hπ V) =
      MarkedIdeal.pullback η (QV.geoTransform CV (windowProjection hπ' V)) := by
    rw [hproj]
    exact BlowupBiholomorphismLift.geoTransform_comp_diffeo η QV hIV CV hICV hr' hpostV
  have hrec := geoTransform_pullback_val hI hπ
    (analytic_and_coherent_geoTransform Q hN hI hπ).2 V (stepWindow hπ V).isOpen
  have hrec' := geoTransform_pullback_val hI hπ'
    (analytic_and_coherent_geoTransform Q hN hI hπ').2 V (stepWindow hπ' V).isOpen
  change QV.geoTransform ((Subtype.val : V → Y) ⁻¹' C) (windowProjection hπ V) = _ at hrec
  rw [hC] at hrec
  calc
    MarkedIdeal.pullback (Subtype.val : stepWindow hπ V → Z) (Q.geoTransform C π) =
        QV.geoTransform CV (windowProjection hπ V) := hrec.symm
    _ = MarkedIdeal.pullback η (QV.geoTransform CV (windowProjection hπ' V)) := hnatural
    _ = MarkedIdeal.pullback η
        (MarkedIdeal.pullback (Subtype.val : stepWindow hπ' V → Z') (Q.geoTransform C' π')) :=
      congrArg (MarkedIdeal.pullback η) hrec'

/-- An arbitrary CURRENT-open centre-trace equation constructs the actual
comparison and whole post-record equality after any actual original prefix.
Global lower testness, regularity or invariant values are not assumed. -/
theorem exists_current_step_whole_record (M : MarkedIdeal n X)
    (hN : IsComplexAnalyticSubset (n := n) M.N) (hI : M.ideal.IsCoherent)
    (T : BlowupTower X Y) {C C' : Set Y} {π : Z → Y} {π' : Z' → Y}
    (hπ : IsBlowupAlong n C π) (hπ' : IsBlowupAlong n C' π') (V : Opens Y)
    (hC : (Subtype.val : V → Y) ⁻¹' C = (Subtype.val : V → Y) ⁻¹' C') :
    ∃! η : stepWindow hπ V ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ stepWindow hπ' V,
      (∀ z : stepWindow hπ V, π' (η z).val = π z.val) ∧
      MarkedIdeal.pullback (Subtype.val : stepWindow hπ V → Z)
          (geoTransformAlong M (.step T C π hπ)) =
        MarkedIdeal.pullback η
          (MarkedIdeal.pullback (Subtype.val : stepWindow hπ' V → Z')
            (geoTransformAlong M (.step T C' π' hπ'))) := by
  obtain ⟨η, hsq, hUnique⟩ := existsUnique_current_step_comparison hπ hπ' V hC
  obtain ⟨hNT, hIT⟩ := analytic_and_coherent_geoTransformAlong M hN hI T
  refine ⟨η, ⟨hsq, ?_⟩, fun θ hθ => hUnique θ hθ.1⟩
  exact current_record_eq (geoTransformAlong M T) hNT hIT hπ hπ' V hC η hsq

end
end Hironaka.HironakaActualNoncanonicalAnalyticTransformLocality
