import Hironaka.Resolution.HironakaActualGeneratedOriginalHeads

/-! Actual original order-mask dictionaries across generated different
histories. Closures are retained literally even for globally raw sources. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualGeneratedOriginalOrderMasks
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
open MarkedIdealBiholomorphism RelativePrincipalizationSpan NonmonomialOrderLocal NonmonomialOrderTail
open DerivativeIdealAlongEtale InvertibleIdealQuotient
open HironakaActualRawRecordPullbacks HironakaActualRawOrderLocality HironakaActualGeneratedCurrentHistories
noncomputable section
variable {n : ℕ} {X X' Y Y' : CMfd.{u} n}

theorem order_threshold_traces_from_records (A : MarkedIdeal n X) (B : MarkedIdeal n X')
 (hA : ∀x g,A.ideal.mem x g → HolomorphicAt n g x)
 (hAc : ∀x g,IsInSpanAt (n := n) (A.ideal.mem x) x g → A.ideal.mem x g)
 (hB : ∀x g,B.ideal.mem x g → HolomorphicAt n g x)
 (hBc : ∀x g,IsInSpanAt (n := n) (B.ideal.mem x) x g → B.ideal.mem x g)
 (U : Opens X) (U' : Opens X')
 (η : CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U')
 (hrec : MarkedIdeal.pullback (Subtype.val : U → X) A =
   MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → X') B)) (q : ℕ) :
 (Subtype.val : U → X) ⁻¹' ordGe A q =
   η ⁻¹' ((Subtype.val : U' → X') ⁻¹' ordGe B q) := by
 let BU : MarkedIdeal n (CMfd.of (n := n) U') := MarkedIdeal.pullback (Subtype.val : U' → X') B
 have hBU : ∀x g,BU.ideal.mem x g → HolomorphicAt n g x := fun _ _ hg => hg.1
 have hBUc : ∀x g,IsInSpanAt (n := n) (BU.ideal.mem x) x g → BU.ideal.mem x g := by
   intro x g hg
   dsimp only [BU,MarkedIdeal.pullback,GermIdeal.pullback] at hg ⊢
   exact IsInSpanAt.trans (fun _ hs => hs) hg
 have hs := ordGe_pullback_of_local (X := X) (Y := CMfd.of (n := n) U)
   contMDiff_subtype_val (fun p => ⟨DerivativeIdealAlongEtale.openInv U p,
     DerivativeIdealAlongEtale.isLocalInverseAt_val U p⟩) A hA hAc q
 have hm := congrArg (fun Q : MarkedIdeal n (CMfd.of (n := n) U) => ordGe Q q) hrec
 have ht₁ := ordGe_pullback_of_local (X := CMfd.of (n := n) U') (Y := CMfd.of (n := n) U)
   η.contMDiff (fun p => ⟨η.symm,CompanionRebase.isLocalInverseAt_diffeo η p⟩) BU hBU hBUc q
 have ht₂ := ordGe_pullback_of_local (X := X') (Y := CMfd.of (n := n) U')
   contMDiff_subtype_val (fun p => ⟨DerivativeIdealAlongEtale.openInv U' p,
     DerivativeIdealAlongEtale.isLocalInverseAt_val U' p⟩) B hB hBc q
 exact hs.symm.trans (hm.trans (ht₁.trans (congrArg (η ⁻¹' ·) ht₂)))

/-- The closure in the actual original raw mask is preserved; no global
closedness assertion about the raw order threshold is used. -/
theorem order_mask_traces_from_records (A : MarkedIdeal n X) (B : MarkedIdeal n X')
 (hA : ∀x g,A.ideal.mem x g → HolomorphicAt n g x)
 (hAc : ∀x g,IsInSpanAt (n := n) (A.ideal.mem x) x g → A.ideal.mem x g)
 (hB : ∀x g,B.ideal.mem x g → HolomorphicAt n g x)
 (hBc : ∀x g,IsInSpanAt (n := n) (B.ideal.mem x) x g → B.ideal.mem x g)
 (U : Opens X) (U' : Opens X')
 (η : CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U')
 (hrec : MarkedIdeal.pullback (Subtype.val : U → X) A =
   MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → X') B)) (o : ℕ) :
 (Subtype.val : U → X) ⁻¹' (ordMask A o : Set X) =
   η ⁻¹' ((Subtype.val : U' → X') ⁻¹' (ordMask B o : Set X')) := by
 have h := order_threshold_traces_from_records A B hA hAc hB hBc U U' η hrec (o+1)
 have hclS : (Subtype.val : U → X) ⁻¹' closure (ordGe A (o+1)) =
     closure ((Subtype.val : U → X) ⁻¹' ordGe A (o+1)) :=
   U.isOpen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage continuous_subtype_val _
 have hclT : (Subtype.val : U' → X') ⁻¹' closure (ordGe B (o+1)) =
     closure ((Subtype.val : U' → X') ⁻¹' ordGe B (o+1)) :=
   U'.isOpen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage continuous_subtype_val _
 have hηcl : η ⁻¹' closure ((Subtype.val : U' → X') ⁻¹' ordGe B (o+1)) =
     closure (η ⁻¹' ((Subtype.val : U' → X') ⁻¹' ordGe B (o+1))) :=
   η.toHomeomorph.preimage_closure _
 change (Subtype.val : U → X) ⁻¹' (closure (ordGe A (o+1)))ᶜ =
   η ⁻¹' ((Subtype.val : U' → X') ⁻¹' (closure (ordGe B (o+1)))ᶜ)
 rw [preimage_compl,preimage_compl,preimage_compl,hclS,hclT,hηcl,h]

/-- The original head mask follows the entire generated actual history,
despite arbitrary intermediate shrinkings of the current comparison. -/
theorem generated_original_order_mask_traces {A : MarkedIdeal n X} {B : MarkedIdeal n X'}
 (hA : ∀x g,A.ideal.mem x g → HolomorphicAt n g x)
 (hAc : ∀x g,IsInSpanAt (n := n) (A.ideal.mem x) x g → A.ideal.mem x g)
 (hB : B.IsWellFormed) (o : ℕ)
 {S : BlowupTower X Y} {T : BlowupTower X' Y'} {U : Opens Y} {U' : Opens Y'} {η}
 (H : Generated A B S T U U' η) :
 (Subtype.val : U → Y) ⁻¹' (openPreimage S (ordMask A o) : Set Y) =
   η ⁻¹' ((Subtype.val : U' → Y') ⁻¹' (openPreimage T (ordMask B o) : Set Y')) := by
 have hBhol : ∀x g,B.ideal.mem x g → HolomorphicAt n g x :=
   fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hB.isCoherent hg
 have hBc : ∀x g,IsInSpanAt (n := n) (B.ideal.mem x) x g → B.ideal.mem x g :=
   fun _ _ hg => GermIdealTotalTransform.mem_of_isInSpanAt_mem hB.isCoherent hg
 induction H with
 | initial U U' η hrec => exact order_mask_traces_from_records A B hA hAc hBhol hBc U U' η hrec o
 | @shrink Y Y' S T U U' η H V V' hV hV' htr ih =>
   ext z
   exact Set.ext_iff.mp ih ⟨z.val,hV z.property⟩
 | @step Y Y' Z Z' S T U U' η H C C' hAdm' π π' hπ hπ' hC ih =>
   ext z
   have h := Set.ext_iff.mp ih ⟨π z.val,z.property⟩
   change S.proj (π z.val)∈ordMask A o ↔
     T.proj (π' (nextComparison hπ hπ' U U' η hC z).val)∈ordMask B o
   rw [nextComparison_square hπ hπ' U U' η hC z]
   exact h

/-- Actual original-restricted histories have a generated current endpoint
comparison and an entire transformed-record identity. The records and the
tails remain the literal original ones on the original head masks. -/
theorem exists_generated_original_masked_whole_records {A : MarkedIdeal n X} {B : MarkedIdeal n X'}
 (hA : ∀x g,A.ideal.mem x g → HolomorphicAt n g x)
 (hAc : ∀x g,IsInSpanAt (n := n) (A.ideal.mem x) x g → A.ideal.mem x g)
 (hB : B.IsWellFormed) (o : ℕ)
 {S : BlowupTower X Y} {T : BlowupTower X' Y'} {U : Opens Y} {U' : Opens Y'} {η}
 (H : Generated A B S T U U' η) :
 let Ws := openPreimage S (ordMask A o)
 let Wt := openPreimage T (ordMask B o)
 ∃ν : CMfd.of (n := n) (MaxLocusLocal.nestedOpens Ws U)
     ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
       CMfd.of (n := n) (MaxLocusLocal.nestedOpens Wt U'),
   (∀p,(ν p).val.val=(η ⟨p.val.val,p.property⟩).val) ∧
   MarkedIdeal.pullback (Subtype.val : MaxLocusLocal.nestedOpens Ws U → Ws)
       (geoTransformAlong (X := CMfd.of (n := n) (ordMask A o)) (Y := CMfd.of (n := n) Ws)
         (MarkedIdeal.pullback (Subtype.val : ordMask A o → X) A) (restrict (ordMask A o) S)) =
     MarkedIdeal.pullback ν
       (MarkedIdeal.pullback (Subtype.val : MaxLocusLocal.nestedOpens Wt U' → Wt)
         (geoTransformAlong (X := CMfd.of (n := n) (ordMask B o)) (Y := CMfd.of (n := n) Wt)
           (MarkedIdeal.pullback (Subtype.val : ordMask B o → X') B) (restrict (ordMask B o) T))) := by
 let Ws := openPreimage S (ordMask A o)
 let Wt := openPreimage T (ordMask B o)
 have hBhol : ∀x g,B.ideal.mem x g → HolomorphicAt n g x :=
   fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hB.isCoherent hg
 have hsHol := holomorphic_geoTransformAlong A hA S
 have htHol := holomorphic_geoTransformAlong B hBhol T
 have hMasks := generated_original_order_mask_traces hA hAc hB o H
 obtain ⟨ν,hphys,hrec⟩ :=
   HironakaActualCurrentMaskedReferenceValues.exists_actual_current_masked_reference_records
     (geoTransformAlong A S) (geoTransformAlong B T) hsHol htHol
     Ws U Wt U' η (H.whole_records hA hB) hMasks
 have hs := geoTransformAlong_restrict_of_hhol A hA (ordMask A o) S
 have ht := geoTransformAlong_restrict_of_hhol B hBhol (ordMask B o) T
 have hs' := congrArg
   (MarkedIdeal.pullback (Subtype.val : MaxLocusLocal.nestedOpens Ws U → Ws)) hs
 have ht' := congrArg
   (fun Q : MarkedIdeal n (CMfd.of (n := n) Wt) => MarkedIdeal.pullback ν
     (MarkedIdeal.pullback (Subtype.val : MaxLocusLocal.nestedOpens Wt U' → Wt) Q)) ht
 exact ⟨ν,hphys,hs'.trans (hrec.trans ht'.symm)⟩

end
end Hironaka.HironakaActualGeneratedOriginalOrderMasks
