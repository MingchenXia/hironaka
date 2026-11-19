import Hironaka.Resolution.HironakaActualInitialFamilyRecordValues
import Hironaka.Invariant.StepOneTangentChange

/-! Actual nested-mask comparisons and their entire fresh initial family values.
No global source regularity or supplied numerical comparison is used. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualCurrentMaskedReferenceValues
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
open MarkedIdealBiholomorphism MarkedIdealRestrictOpen RelativePrincipalizationSpan GermIdealPullbackCalculus
open ResolutionInvariantSpec (IsInvDomain)
noncomputable section
variable {n : ℕ} {Z Z' : CMfd.{u} n}

section Compose
variable {P Q R : Type u} [TopologicalSpace P] [ChartedSpace (ComplexModel n) P] [IsComplexManifold n P]
 [TopologicalSpace Q] [ChartedSpace (ComplexModel n) Q] [IsComplexManifold n Q]
 [TopologicalSpace R] [ChartedSpace (ComplexModel n) R] [IsComplexManifold n R]
private theorem pullback_comp_hhol {f : P → R} {g : Q → P}
 (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
 (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
 {𝔞 : GermIdeal n R} (hhol : ∀ x v, 𝔞.mem x v → HolomorphicAt n v x) :
 GermIdeal.pullback (m := n) (f ∘ g) 𝔞 =
   GermIdeal.pullback (m := n) g (GermIdeal.pullback (m := n) f 𝔞) := by
  refine GermIdeal.ext (funext fun z => funext fun v => propext ⟨fun hv => ?_, fun hv => ?_⟩)
  · have hfat : ∀ᶠ y in 𝓝 (g z),
        ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f y :=
      Eventually.of_forall fun y => hf.contMDiffAt
    refine GermIdeal.mem_pullback_iff.mpr
      (IsInSpanAt.mono ?_ (GermIdeal.mem_pullback_iff.mp hv))
    rintro u ⟨c, hc, rfl⟩
    have hchol : HolomorphicAt n c (f (g z)) :=
      hhol _ _ hc
    have hcfhol : HolomorphicAt n (c ∘ f) (g z) := hchol.comp_contMDiff hfat
    have hcf : (GermIdeal.pullback (m := n) f 𝔞).mem (g z) (c ∘ f) :=
      GermIdeal.mem_pullback_iff.mpr (isInSpanAt_of_eq_mul ⟨c, hc, rfl⟩ hcfhol
        (holomorphicAt_const 1) (Eventually.of_forall fun _ => (one_mul _).symm))
    exact ⟨c ∘ f, hcf, rfl⟩
  · refine GermIdeal.mem_pullback_iff.mpr
      (IsInSpanAt.trans ?_ (GermIdeal.mem_pullback_iff.mp hv))
    rintro u ⟨c, hc, rfl⟩
    refine IsInSpanAt.mono ?_
      (isInSpanAt_comp hg (GermIdeal.mem_pullback_iff.mp hc))
    rintro u' ⟨σ, ⟨d, hd, rfl⟩, rfl⟩
    exact ⟨d, hd, rfl⟩

private theorem marked_pullback_comp_hhol {J : MarkedIdeal n R}
 (hhol : ∀ x v, J.ideal.mem x v → HolomorphicAt n v x) {a : P → R} {b : Q → P} {d : Q → R}
 (ha : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ a)
 (hb : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ b) (h : ∀ q,a (b q)=d q) :
 MarkedIdeal.pullback b (MarkedIdeal.pullback a J) = MarkedIdeal.pullback d J := by
 have hfun : a ∘ b = d := funext h
 refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of ?_ ?_ ?_ rfl
 · show b ⁻¹' (a ⁻¹' J.N)=d ⁻¹' J.N
   rw [←preimage_comp,hfun]
 · show (J.E.map (a ⁻¹' ·)).map (b ⁻¹' ·)=J.E.map (d ⁻¹' ·)
   rw [List.map_map]
   refine List.map_congr_left fun S _ => ?_
   show b ⁻¹' (a ⁻¹' S)=d ⁻¹' S
   rw [←preimage_comp,hfun]
 · show GermIdeal.pullback (m := n) b (GermIdeal.pullback (m := n) a J.ideal)=GermIdeal.pullback (m := n) d J.ideal
   rw [←pullback_comp_hhol ha hb hhol,hfun]
end Compose

private def swap_current_and_original_masks (W U : Opens Z) :
 MaxLocusLocal.nestedOpens U W ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
   MaxLocusLocal.nestedOpens W U :=
 (MaxLocusLocal.nestedDiffeo U (MaxLocusLocal.nestedOpens U W) (U ⊓ W)
   (fun p => ⟨fun h => ⟨p.property,h⟩,fun h => h.2⟩) (fun _ h => h.1)).trans
 (MaxLocusLocal.nestedDiffeo W (MaxLocusLocal.nestedOpens W U) (U ⊓ W)
   (fun p => ⟨fun h => ⟨h,p.property⟩,fun h => h.1⟩) (fun _ h => h.2)).symm

/-- Current record and mask geometry internally constructs the actual
comparison on the original masked records, keeping the full ordered record. -/
theorem exists_actual_current_masked_reference_records
 (A : MarkedIdeal n Z) (B : MarkedIdeal n Z')
 (hA : ∀ x g,A.ideal.mem x g → HolomorphicAt n g x)
 (hB : ∀ x g,B.ideal.mem x g → HolomorphicAt n g x)
 (W U : Opens Z) (W' U' : Opens Z')
 (η : U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ U')
 (hrec : MarkedIdeal.pullback (Subtype.val : U → Z) A=
   MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') B))
 (hMask : (Subtype.val : U → Z) ⁻¹' (W : Set Z)=
   η ⁻¹' ((Subtype.val : U' → Z') ⁻¹' (W' : Set Z'))) :
 ∃ ν : MaxLocusLocal.nestedOpens W U
     ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ MaxLocusLocal.nestedOpens W' U',
   (∀ p,(ν p).val.val=(η ⟨p.val.val,p.property⟩).val) ∧
   MarkedIdeal.pullback (Subtype.val : MaxLocusLocal.nestedOpens W U → W)
       (MarkedIdeal.pullback (Subtype.val : W → Z) A)=
     MarkedIdeal.pullback ν
       (MarkedIdeal.pullback (Subtype.val : MaxLocusLocal.nestedOpens W' U' → W')
         (MarkedIdeal.pullback (Subtype.val : W' → Z') B)) := by
 let Os := MaxLocusLocal.nestedOpens W U
 let Ot := MaxLocusLocal.nestedOpens W' U'
 let Cs := MaxLocusLocal.nestedOpens U W
 let Ct := MaxLocusLocal.nestedOpens U' W'
 have hW : ∀ p : U,p∈Cs ↔ η p∈Ct :=
   Set.ext_iff.mp hMask
 let ψ := StepOneTangentChange.diffeoOpens
   (X' := CMfd.of (n := n) U) (X := CMfd.of (n := n) U') η Cs Ct hW
 let es := swap_current_and_original_masks W U
 let et := swap_current_and_original_masks W' U'
 let ν := es.symm.trans (ψ.trans et)
 let f : Os → U := fun p => ⟨p.val.val,p.property⟩
 let d : Os → Z' := fun p => (η (f p)).val
 have hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f :=
   BlowupRestrictOpen.contMDiff_opens_mk
     (contMDiff_subtype_val.comp contMDiff_subtype_val) (fun p => p.property)
 have hphys : ∀ p : Os,(ν p).val.val=d p := fun _ => rfl
 have hS₁ := marked_pullback_comp_hhol hA
   (a := (Subtype.val : W → Z)) (b := (Subtype.val : Os → W))
   (d := fun p : Os => p.val.val) contMDiff_subtype_val contMDiff_subtype_val (fun _ => rfl)
 have hS₂ := marked_pullback_comp_hhol hA
   (a := (Subtype.val : U → Z)) (b := f) (d := fun p : Os => p.val.val)
   contMDiff_subtype_val hf (fun _ => rfl)
 have hSource := hS₁.trans hS₂.symm
 have hMiddle₀ := congrArg (MarkedIdeal.pullback f) hrec
 have hMiddle₁ := marked_pullback_comp_hhol
   (J := MarkedIdeal.pullback (Subtype.val : U' → Z') B) (fun _ _ hg => hg.1)
   (a := η) (b := f) (d := fun p : Os => η (f p)) η.contMDiff hf (fun _ => rfl)
 have hMiddle₂ := marked_pullback_comp_hhol hB
   (a := (Subtype.val : U' → Z')) (b := fun p : Os => η (f p)) (d := d)
   contMDiff_subtype_val (η.contMDiff.comp hf) (fun _ => rfl)
 have hT₁ := marked_pullback_comp_hhol hB
   (a := (Subtype.val : W' → Z')) (b := (Subtype.val : Ot → W'))
   (d := fun p : Ot => p.val.val) contMDiff_subtype_val contMDiff_subtype_val (fun _ => rfl)
 have hT₂ := marked_pullback_comp_hhol hB
   (a := fun p : Ot => p.val.val) (b := ν) (d := d)
   (contMDiff_subtype_val.comp contMDiff_subtype_val) ν.contMDiff hphys
 have hTarget := (congrArg (MarkedIdeal.pullback ν) hT₁).trans hT₂
 exact ⟨ν,hphys,hSource.trans (hMiddle₀.trans (hMiddle₁.trans (hMiddle₂.trans hTarget.symm)))⟩

/-- The complete numerical fresh lower invariant follows from actual masked
record geometry and the good TARGET lower domain. No numerical comparison
or global source-domain hypothesis is supplied by the caller. -/
theorem exists_actual_current_masked_initial_family_values
 (hn : 0<n) (q : ℕ) (A : MarkedIdeal n Z) (B : MarkedIdeal n Z')
 (hA : ∀ x g,A.ideal.mem x g → HolomorphicAt n g x)
 (hB : ∀ x g,B.ideal.mem x g → HolomorphicAt n g x)
 (W U : Opens Z) (W' U' : Opens Z')
 (hgood : IsInvDomain q (MarkedIdeal.pullback (Subtype.val : W' → Z') B))
 (η : U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ U')
 (hrec : MarkedIdeal.pullback (Subtype.val : U → Z) A=
   MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') B))
 (hMask : (Subtype.val : U → Z) ⁻¹' (W : Set Z)=
   η ⁻¹' ((Subtype.val : U' → Z') ⁻¹' (W' : Set Z'))) :
 ∃ ν : MaxLocusLocal.nestedOpens W U
     ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ MaxLocusLocal.nestedOpens W' U',
   (∀ p,(ν p).val.val=(η ⟨p.val.val,p.property⟩).val) ∧
   ∀ p : MaxLocusLocal.nestedOpens W U,
     p.val∈(MarkedIdeal.pullback (Subtype.val : W → Z) A).cosupp →
     (CanonicalCentres.invFamily hn q).inv
       (X := CMfd.of (n := n) W) (Y := CMfd.of (n := n) W)
       (MarkedIdeal.pullback (Subtype.val : W → Z) A) .refl p.val=
     (CanonicalCentres.invFamily hn q).inv
       (X := CMfd.of (n := n) W') (Y := CMfd.of (n := n) W')
       (MarkedIdeal.pullback (Subtype.val : W' → Z') B) .refl (ν p).val := by
 obtain ⟨ν,hphys,hRecords⟩ := exists_actual_current_masked_reference_records A B hA hB W U W' U' η hrec hMask
 let Js : MarkedIdeal n (CMfd.of (n := n) W) := MarkedIdeal.pullback (Subtype.val : W → Z) A
 let Jt : MarkedIdeal n (CMfd.of (n := n) W') := MarkedIdeal.pullback (Subtype.val : W' → Z') B
 have hJsHol : ∀ x g,Js.ideal.mem x g → HolomorphicAt n g x := fun _ _ hg => hg.1
 have hJsClosed : ∀ x g,IsInSpanAt (n := n) (Js.ideal.mem x) x g → Js.ideal.mem x g := by
   intro x g hg
   dsimp only [Js,MarkedIdeal.pullback,GermIdeal.pullback] at hg ⊢
   exact IsInSpanAt.trans (fun _ hs => hs) hg
 refine ⟨ν,hphys,?_⟩
 intro p hp
 exact HironakaActualInitialFamilyRecordValues.initial_family_values_from_record
   (Z := CMfd.of (n := n) W) (Z' := CMfd.of (n := n) W')
   hn q Js Jt hJsHol hJsClosed hgood
   (MaxLocusLocal.nestedOpens W U) (MaxLocusLocal.nestedOpens W' U') ν hRecords p hp

end
end Hironaka.HironakaActualCurrentMaskedReferenceValues
