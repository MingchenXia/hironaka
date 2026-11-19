import Hironaka.Resolution.HironakaActualAnchoredInitialRefinement
import Hironaka.Resolution.HironakaActualRawRecordPullbacks

/-! Different ORIGINAL reference masks may shrink asymmetrically. Actual
current-window refinement retains the literal source reference and tail. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualAnchoredRestrictedReferenceHistories
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
open MarkedIdealBiholomorphism RelativePrincipalizationSpan
open HironakaActualGeneratedCurrentHistories HironakaActualAnchoredCurrentHistories
open HironakaActualAnchoredMaskedHistories HironakaActualAnchoredInitialRefinement
noncomputable section
variable {n : ℕ} {X X' Y Y' : CMfd.{u} n}

/-- Internally refine only the current comparison to transport arbitrary
literal original reference records on DIFFERENT original masks. No source
testness, target domain/canonicality certificate, or numerical comparison
is used; target testness is the natural geometric lower-tail premise. -/
theorem exists_actual_restricted_reference_histories
 (A : MarkedIdeal n X) (B : MarkedIdeal n X')
 (hA : ∀x g,A.ideal.mem x g → HolomorphicAt n g x)
 (hB : ∀x g,B.ideal.mem x g → HolomorphicAt n g x)
 {V₀ : Opens X} {V₀' : Opens X'}
 {φ : CMfd.of (n := n) V₀ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) V₀'}
 (hInitial : MarkedIdeal.pullback (Subtype.val : V₀ → X) A=
   MarkedIdeal.pullback φ (MarkedIdeal.pullback (Subtype.val : V₀' → X') B))
 {S : BlowupTower X Y} {T : BlowupTower X' Y'} {U : Opens Y} {U' : Opens Y'} {η}
 (H : Anchored V₀ V₀' φ S T U U' η) (W : Opens X) (W' : Opens X')
 (z : U) (hzW : S.proj z.val∈W) (hzW' : T.proj (η z).val∈W')
 (hTarget : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : W' → X') B) (restrict W' T)) :
 ∃(Us : Opens Y)(Ut : Opens Y')(hUs : (Us : Set Y)⊆U)(_hUt : (Ut : Set Y')⊆U'),
   z.val∈Us ∧ (η z).val∈Ut ∧
   ∃ν : CMfd.of (n := n) (MaxLocusLocal.nestedOpens (openPreimage S W) Us)
       ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
         CMfd.of (n := n) (MaxLocusLocal.nestedOpens (openPreimage T W') Ut),
     (∀p,(ν p).val.val=(η ⟨p.val.val,hUs p.property⟩).val) ∧
     Generated (MarkedIdeal.pullback (Subtype.val : W → X) A)
       (MarkedIdeal.pullback (Subtype.val : W' → X') B)
       (restrict W S) (restrict W' T)
       (MaxLocusLocal.nestedOpens (openPreimage S W) Us)
       (MaxLocusLocal.nestedOpens (openPreimage T W') Ut) ν := by
 let p : V₀ := ⟨S.proj z.val,H.source_mem_initial z⟩
 have hp' : (φ p).val∈W' := by
   rw [←H.projection_square z]
   exact hzW'
 obtain ⟨V,V',hpV,hpV',hVV₀,hV'V₀',hVW,hV'W',htr⟩ :=
   exists_initial_windows_inside V₀ V₀' φ W W' p hzW hp'
 let φr := restrictComparison φ V V' hVV₀ hV'V₀' htr.symm
 let Us := U ⊓ openPreimage S V
 let Ut := U' ⊓ openPreimage T V'
 let ρ := refinedComparison H V V' htr
 have Href := HironakaActualAnchoredInitialRefinement.Anchored.refine_initial H V V' hVV₀ hV'V₀' htr
 have hRecRef := whole_records_restrict φ V V' hVV₀ hV'V₀' htr.symm A B hA hB hInitial
 have hMaskRef : (Subtype.val : V → X) ⁻¹' (W : Set X)=
     φr ⁻¹' ((Subtype.val : V' → X') ⁻¹' (W' : Set X')) := by
   ext q
   exact ⟨fun _ => hV'W' (φr q).property,fun _ => hVW q.property⟩
 obtain ⟨ψ,hψ,hRecMask⟩ :=
   HironakaActualCurrentMaskedReferenceValues.exists_actual_current_masked_reference_records
     A B hA hB W V W' V' φr hRecRef hMaskRef
 let φm := maskedComparison W V W' V' φr hMaskRef
 have hEq : ψ=φm := by
   apply Diffeomorph.ext
   intro q
   apply Subtype.ext
   apply Subtype.ext
   exact hψ q
 rw [hEq] at hRecMask
 obtain ⟨ν,hν,Hν⟩ := exists_anchored_original_masked_histories Href W W' hMaskRef
 have hGenerated := Hν.to_generated
   (MarkedIdeal.pullback (Subtype.val : W → X) A)
   (MarkedIdeal.pullback (Subtype.val : W' → X') B) hRecMask hTarget
 let zr : Us := ⟨z.val,⟨z.property,hpV⟩⟩
 have hzr' : (η z).val∈Ut := (ρ zr).property
 refine ⟨Us,Ut,(fun _ h => h.1),(fun _ h => h.1),zr.property,hzr',ν,?_,hGenerated⟩
 intro q
 exact hν q

end
end Hironaka.HironakaActualAnchoredRestrictedReferenceHistories
