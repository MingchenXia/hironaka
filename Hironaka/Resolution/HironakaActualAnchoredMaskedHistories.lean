import Hironaka.Resolution.HironakaActualAnchoredCurrentHistories
import Hironaka.Resolution.HironakaActualCurrentMaskedReferenceValues

/-! Arbitrary ORIGINAL masks of one actual anchored geometry. Neither
marked records nor numerical comparisons occur in the geometric producer. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualAnchoredMaskedHistories
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open BlowupTowers BlowupTowerTransforms HironakaActualGeneratedCurrentHistories
open HironakaActualAnchoredCurrentHistories
noncomputable section
variable {n : ℕ} {X X' Y Y' : CMfd.{u} n}

private def swap_masks {Y : CMfd.{u} n} (W U : Opens Y) :
 MaxLocusLocal.nestedOpens U W ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ MaxLocusLocal.nestedOpens W U :=
 (MaxLocusLocal.nestedDiffeo U (MaxLocusLocal.nestedOpens U W) (U ⊓ W)
   (fun p => ⟨fun h => ⟨p.property,h⟩,fun h => h.2⟩) (fun _ h => h.1)).trans
 (MaxLocusLocal.nestedDiffeo W (MaxLocusLocal.nestedOpens W U) (U ⊓ W)
   (fun p => ⟨fun h => ⟨h,p.property⟩,fun h => h.1⟩) (fun _ h => h.2)).symm

def maskedComparison (W U : Opens Y) (W' U' : Opens Y')
 (η : CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U')
 (hMask : (Subtype.val : U → Y) ⁻¹' (W : Set Y)=
   η ⁻¹' ((Subtype.val : U' → Y') ⁻¹' (W' : Set Y'))) :
 CMfd.of (n := n) (MaxLocusLocal.nestedOpens W U)
   ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (MaxLocusLocal.nestedOpens W' U') :=
 (swap_masks W U).symm.trans
   ((StepOneTangentChange.diffeoOpens (X' := CMfd.of (n := n) U) (X := CMfd.of (n := n) U')
     η (MaxLocusLocal.nestedOpens U W) (MaxLocusLocal.nestedOpens U' W')
     (Set.ext_iff.mp hMask)).trans (swap_masks W' U'))

theorem maskedComparison_val (W U : Opens Y) (W' U' : Opens Y')
 (η : CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U')
 (hMask : (Subtype.val : U → Y) ⁻¹' (W : Set Y)=
   η ⁻¹' ((Subtype.val : U' → Y') ⁻¹' (W' : Set Y')))
 (p : MaxLocusLocal.nestedOpens W U) :
 (maskedComparison W U W' U' η hMask p).val.val=(η ⟨p.val.val,p.property⟩).val := rfl

theorem Anchored.original_mask_traces {V₀ : Opens X} {V₀' : Opens X'} {φ}
 {S : BlowupTower X Y} {T : BlowupTower X' Y'} {U : Opens Y} {U' : Opens Y'} {η}
 (H : Anchored V₀ V₀' φ S T U U' η) (W : Opens X) (W' : Opens X')
 (hMask : (Subtype.val : V₀ → X) ⁻¹' (W : Set X)=
   φ ⁻¹' ((Subtype.val : V₀' → X') ⁻¹' (W' : Set X'))) :
 (Subtype.val : U → Y) ⁻¹' (openPreimage S W : Set Y)=
   η ⁻¹' ((Subtype.val : U' → Y') ⁻¹' (openPreimage T W' : Set Y')) := by
 ext z
 change S.proj z.val∈W ↔ T.proj (η z).val∈W'
 rw [H.projection_square z]
 exact Set.ext_iff.mp hMask ⟨S.proj z.val,H.source_mem_initial z⟩

/-- One actual initial mask trace identity generates the entire paired
original-restricted histories through arbitrary current shrinkings. -/
theorem exists_anchored_original_masked_histories {V₀ : Opens X} {V₀' : Opens X'} {φ}
 {S : BlowupTower X Y} {T : BlowupTower X' Y'} {U : Opens Y} {U' : Opens Y'} {η}
 (H : Anchored V₀ V₀' φ S T U U' η) (W : Opens X) (W' : Opens X')
 (hMask : (Subtype.val : V₀ → X) ⁻¹' (W : Set X)=
   φ ⁻¹' ((Subtype.val : V₀' → X') ⁻¹' (W' : Set X'))) :
 let Ws := openPreimage S W
 let Wt := openPreimage T W'
 ∃ν : CMfd.of (n := n) (MaxLocusLocal.nestedOpens Ws U)
     ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
       CMfd.of (n := n) (MaxLocusLocal.nestedOpens Wt U'),
   (∀p,(ν p).val.val=(η ⟨p.val.val,p.property⟩).val) ∧
   Anchored (X := CMfd.of (n := n) W) (X' := CMfd.of (n := n) W')
     (MaxLocusLocal.nestedOpens W V₀) (MaxLocusLocal.nestedOpens W' V₀')
     (maskedComparison W V₀ W' V₀' φ hMask)
     (restrict W S) (restrict W' T)
     (MaxLocusLocal.nestedOpens Ws U) (MaxLocusLocal.nestedOpens Wt U') ν := by
 induction H with
 | initial =>
   exact ⟨maskedComparison W V₀ W' V₀' φ hMask,(fun _ => rfl),Anchored.initial⟩
 | @shrink Y Y' S T U U' η H V V' hV hV' htr ih =>
   obtain ⟨ν,hν,Hν⟩ := ih
   let Ws := openPreimage S W
   let Wt := openPreimage T W'
   let Vs := MaxLocusLocal.nestedOpens Ws V
   let Vt := MaxLocusLocal.nestedOpens Wt V'
   have hs : (Vs : Set Ws) ⊆ MaxLocusLocal.nestedOpens Ws U := fun p hp => hV hp
   have ht : (Vt : Set Wt) ⊆ MaxLocusLocal.nestedOpens Wt U' := fun p hp => hV' hp
   have htrace : ν ⁻¹' ((Subtype.val : MaxLocusLocal.nestedOpens Wt U' → Wt) ⁻¹' (Vt : Set Wt)) =
       (Subtype.val : MaxLocusLocal.nestedOpens Ws U → Ws) ⁻¹' (Vs : Set Ws) := by
     ext p
     change (ν p).val.val∈V' ↔ p.val.val∈V
     rw [hν p]
     exact Set.ext_iff.mp htr ⟨p.val.val,p.property⟩
   let ρ := restrictComparison (Y := CMfd.of (n := n) Ws) (Y' := CMfd.of (n := n) Wt)
     ν Vs Vt hs ht htrace
   have Hρ := Anchored.shrink (Y := CMfd.of (n := n) Ws) (Y' := CMfd.of (n := n) Wt)
     Hν Vs Vt hs ht htrace
   have Hstep := Anchored.shrink H V V' hV hV' htr
   let ψ := maskedComparison Ws V Wt V'
     (restrictComparison η V V' hV hV' htr) (Anchored.original_mask_traces Hstep W W' hMask)
   have hψ : ∀p,(ψ p).val.val=
       (restrictComparison η V V' hV hV' htr ⟨p.val.val,p.property⟩).val := fun _ => rfl
   have hEq : ψ=ρ := by
     apply Diffeomorph.ext
     intro p
     apply Subtype.ext
     apply Subtype.ext
     exact (hψ p).trans (hν ⟨p.val,hs p.property⟩).symm
   exact ⟨ψ,hψ,hEq.symm ▸ Hρ⟩
 | @step Y Y' Z Z' S T U U' η H C C' π π' hπ hπ' hC ih =>
   obtain ⟨ν,hν,Hν⟩ := ih
   let Ws := openPreimage S W
   let Wt := openPreimage T W'
   let Ws₁ := openPreimage (.step S C π hπ) W
   let Wt₁ := openPreimage (.step T C' π' hπ') W'
   let Us := MaxLocusLocal.nestedOpens Ws U
   let Ut := MaxLocusLocal.nestedOpens Wt U'
   let r : Ws₁ → Ws := fun p => ⟨π p.val,p.property⟩
   let r' : Wt₁ → Wt := fun p => ⟨π' p.val,p.property⟩
   have hs : IsBlowupAlong n ((Subtype.val : Ws → Y) ⁻¹' C) r :=
     BlowupRestrictOpen.isBlowupAlong_restrict hπ Ws Ws₁.isOpen
   have ht : IsBlowupAlong n ((Subtype.val : Wt → Y') ⁻¹' C') r' :=
     BlowupRestrictOpen.isBlowupAlong_restrict hπ' Wt Wt₁.isOpen
   have htrace : ν ⁻¹' ((Subtype.val : Ut → Wt) ⁻¹' ((Subtype.val : Wt → Y') ⁻¹' C')) =
       (Subtype.val : Us → Ws) ⁻¹' ((Subtype.val : Ws → Y) ⁻¹' C) := by
     ext p
     change (ν p).val.val∈C' ↔ p.val.val∈C
     rw [hν p]
     exact Set.ext_iff.mp hC ⟨p.val.val,p.property⟩
   have Hstep := Anchored.step H hπ hπ' hC
   have Hnext := Anchored.step
     (Y := CMfd.of (n := n) Ws) (Y' := CMfd.of (n := n) Wt)
     (Z := CMfd.of (n := n) Ws₁) (Z' := CMfd.of (n := n) Wt₁) Hν hs ht htrace
   let ψ := maskedComparison Ws₁ (BlowupBiholomorphismLift.preOpen hπ U)
     Wt₁ (BlowupBiholomorphismLift.preOpen hπ' U')
     (nextComparison hπ hπ' U U' η hC) (Anchored.original_mask_traces Hstep W W' hMask)
   have hψ : ∀p,(ψ p).val.val=(nextComparison hπ hπ' U U' η hC ⟨p.val.val,p.property⟩).val := fun _ => rfl
   have hψsq : ∀p,r' (ψ p).val=(ν ⟨r p.val,p.property⟩).val := by
     intro p
     apply Subtype.ext
     change π' (ψ p).val.val=(ν ⟨⟨π p.val.val,p.val.property⟩,p.property⟩).val.val
     rw [hψ p,nextComparison_square hπ hπ' U U' η hC]
     exact (hν ⟨⟨π p.val.val,p.val.property⟩,p.property⟩).symm
   have hEq : ψ=nextComparison
       (Y := CMfd.of (n := n) Ws) (Y' := CMfd.of (n := n) Wt)
       (Z := CMfd.of (n := n) Ws₁) (Z' := CMfd.of (n := n) Wt₁) hs ht Us Ut ν htrace :=
     (Classical.choose_spec
       (HironakaActualDifferentHistoryRecords.existsUnique_next_comparison
         (X := CMfd.of (n := n) Ws) (X' := CMfd.of (n := n) Wt)
         (Y := CMfd.of (n := n) Ws₁) (Y' := CMfd.of (n := n) Wt₁)
         hs ht Us Ut ν htrace)).2 ψ hψsq
   exact ⟨ψ,hψ,hEq.symm ▸ Hnext⟩

end
end Hironaka.HironakaActualAnchoredMaskedHistories
