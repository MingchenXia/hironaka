import Hironaka.Resolution.HironakaActualCompactCentreImage
import Hironaka.Resolution.HironakaActualAnchoredCurrentHistories
import Hironaka.Resolution.HironakaOriginalCompactCosupportGlobalScheduler

/-! Compact whole-target histories extend to actual global source histories.
Only the target has a globally good marked domain. Every target current open
is the WHOLE endpoint, so no part of a compact target centre is discarded.
A simultaneous family retains the source carrier and full ambient boundary.
No source history, centre extension, numerical matching or future tail is
supplied. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaActualCompactHistoryExtension
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
open MarkedIdealBiholomorphism MarkedIdealRestrictOpen RelativePrincipalizationSpan
open MarkedIdealTowerTransport HironakaActualGeneratedCurrentHistories
open HironakaActualCompactCentreImage HironakaActualRawRecordPullbacks
open HironakaActualAnchoredCurrentHistories
open ResolutionDriver
open ResolutionInvariantSpec (IsInvDomain)
noncomputable section
variable {n : ℕ}

/-- The whole-target comparison pulls a genuinely compact target centre
into a compact source-open centre; its literal image is globally admissible
simultaneously for EVERY marked record. -/
theorem exists_actual_compact_source_successor
 {ι : Type v} {X X' Y Y' Z' : CMfd.{u} n}
 (A : ι → MarkedIdeal n X) (B : ι → MarkedIdeal n X')
 (hA : ∀i x g,(A i).ideal.mem x g → HolomorphicAt n g x)
 (hB : ∀i,(B i).IsWellFormed)
 (S : BlowupTower X Y) (T : BlowupTower X' Y')
 (U : Opens Y)
 (η : CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
   CMfd.of (n := n) (⊤ : Opens Y'))
 (H : ∀i,Generated (A i) (B i) S T U ⊤ η)
 {C' : Set Y'} (hK : IsCompact C') {π' : Z' → Y'} (hπ' : IsBlowupAlong n C' π')
 (hAdm : ∀i,(geoTransformAlong (B i) T).IsAdmissibleCentre C') :
 ∃(C : Set Y)(Z : CMfd.{u} n)(π : Z → Y)(hπ : IsBlowupAlong n C π),
   IsCompact C ∧ C⊆U ∧ (∀i,(geoTransformAlong (A i) S).IsAdmissibleCentre C) ∧
   ∃hTrace : η ⁻¹' ((Subtype.val : (⊤ : Opens Y') → Y') ⁻¹' C')=
     (Subtype.val : U → Y) ⁻¹' C,
   ∀i,Generated (A i) (B i) (.step S C π hπ) (.step T C' π' hπ')
     (BlowupBiholomorphismLift.preOpen hπ U) ⊤
     (nextComparison hπ hπ' U ⊤ η hTrace) := by
 classical
 let g : Y' → U := fun y => η.symm ⟨y,mem_univ y⟩
 let C₀ : Set U := g '' C'
 have htop : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
     (fun y : Y' => (⟨y,mem_univ y⟩ : (⊤ : Opens Y'))) :=
   BlowupRestrictOpen.contMDiff_opens_mk contMDiff_id (fun y => mem_univ y)
 have hg : Continuous g := η.symm.contMDiff.continuous.comp htop.continuous
 have hK₀ : IsCompact C₀ := hK.image hg
 have hTrace₀ : η ⁻¹' ((Subtype.val : (⊤ : Opens Y') → Y') ⁻¹' C')=C₀ := by
   ext p
   constructor
   · intro hp
     exact ⟨(η p).val,hp,η.symm_apply_apply p⟩
   · rintro ⟨y,hy,rfl⟩
     change (η (η.symm ⟨y,mem_univ y⟩)).val∈C'
     simpa only [η.apply_symm_apply] using hy
 have hLocal (i : ι) :
     (MarkedIdeal.pullback (Subtype.val : U → Y) (geoTransformAlong (A i) S)).IsAdmissibleCentre C₀ := by
   have hw := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong (hB i) T (H i).target_test
   have hhol : ∀x f,(geoTransformAlong (B i) T).ideal.mem x f → HolomorphicAt n f x :=
     fun _ _ hf => GermIdeal.IsCoherent.holomorphicAt_mem hw.isCoherent hf
   have ha := MarkedIdealRestrictOpen.IsAdmissibleCentre.pullback_val hhol (hAdm i) (⊤ : Opens Y')
   have hc : (MarkedIdeal.pullback (Subtype.val : (⊤ : Opens Y') → Y')
       (geoTransformAlong (B i) T)).ideal.IsCoherent := GermIdealPullbackCalculus.isCoherent_pullback
     (contMDiff_subtype_val (n := ∞)) hw.isCoherent
   have hs := (isAdmissibleCentre_pullback_iff (Φ := η) hc).mpr ha
   rw [←(H i).whole_records (hA i) (hB i),hTrace₀] at hs
   exact hs
 let C : Set Y := (Subtype.val : U → Y) '' C₀
 have hKC : IsCompact C := hK₀.image continuous_subtype_val
 have hAd (i : ι) : (geoTransformAlong (A i) S).IsAdmissibleCentre C :=
   (compact_admissible_centre_image _ (holomorphic_geoTransformAlong (A i) (hA i) S) U C₀ hK₀ (hLocal i)).2.1
 have hInt₀ : interior C₀=∅ := by
   have hf : IsOpenMap η := η.toHomeomorph.isOpenMap
   have he := hf.preimage_interior_eq_interior_preimage η.contMDiff.continuous
     ((Subtype.val : (⊤ : Opens Y') → Y') ⁻¹' C')
   have ht := BlowupRestrictOpen.interior_preimage_val_eq_empty hπ'.2.1 (⊤ : Opens Y')
   have hp : η ⁻¹' interior ((Subtype.val : (⊤ : Opens Y') → Y') ⁻¹' C')=∅ := by
     rw [ht,preimage_empty]
   exact (congrArg interior hTrace₀.symm).trans (he.symm.trans hp)
 obtain ⟨Z,π,hπ⟩ := exists_blowup C (by
   exact ⟨hKC.isClosed,by
     rintro y ⟨p,hp,rfl⟩
     have hloc := (MarkedIdealTowerTransport.isClosedSubmanifold_preimage_iff η).mpr
       (BlowupRestrictOpen.isClosedSubmanifold_preimage_val hπ'.1 (⊤ : Opens Y'))
     rw [hTrace₀] at hloc
     obtain ⟨k,hk⟩ := hloc.2 p hp
     exact ⟨k,AnalyticSubsetOpens.regularAtDim_image_val_iff.mpr hk⟩⟩)
   (interior_image_val_eq_empty U C₀ hInt₀)
 have hTrace : η ⁻¹' ((Subtype.val : (⊤ : Opens Y') → Y') ⁻¹' C')=
     (Subtype.val : U → Y) ⁻¹' C := by
   rw [Subtype.val_injective.preimage_image C₀]
   exact hTrace₀
 refine ⟨C,Z,π,hπ,hKC,(by rintro y ⟨p,_hp,rfl⟩;exact p.property),hAd,hTrace,?_⟩
 intro i
 exact Generated.step (H i) (hAdm i) hπ hπ' hTrace

end
end Hironaka.HironakaActualCompactHistoryExtension
