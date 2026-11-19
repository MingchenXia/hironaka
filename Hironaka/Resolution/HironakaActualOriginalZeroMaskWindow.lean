import Hironaka.Resolution.HironakaActualAnchoredStrictCarriers
import Hironaka.Resolution.HironakaActualGeneratedStepOneClocks

/-! A target alternate-tangent window internally gives a genuine source
window inside the LITERAL ORIGINAL source maskB. Source old members need
not be globally closed; no desired mask containment is supplied. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualOriginalZeroMaskWindow
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  RelativePrincipalizationSpan StepOneValue CodimOneSupportAlong BoundaryCount
  HironakaActualAnchoredCurrentHistories HironakaActualGeneratedCurrentHistories
  HironakaActualGeneratedStepOneClocks
variable {n : ℕ} {X X' Y Y' : CMfd.{u} n}

theorem exists_original_source_zero_mask_window
    (A : MarkedIdeal n X) (B : MarkedIdeal n X') (hB : B.IsWellFormed)
    {V₀ : Opens X} {V₀' : Opens X'}
    {φ : CMfd.of (n := n) V₀ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) V₀'}
    {S : BlowupTower X Y} {T : BlowupTower X' Y'} {U : Opens Y} {U' : Opens Y'} {η}
    (H : Anchored V₀ V₀' φ S T U U' η)
    (Hbar : Generated (barMarked A) (barMarked B) S T U U' η)
    (p₀ : Y) (p₀' : Y') (Vg : Opens Y')
    (hMask : Vg≤maskB B T p₀')
    (hDomain : (Vg : Set Y')⊆T.proj ⁻¹'
      ((Subtype.val : V₀' → X') '' ((φ.symm) ⁻¹' ((Subtype.val : V₀ → X) ⁻¹'
        (tangentChoice A (S.proj p₀)).1)))) :
    ∃Vs : Opens Y,Vs≤U ∧ Vs≤maskB A S p₀ ∧
      η ⁻¹' ((Subtype.val : U' → Y') ⁻¹' (Vg : Set Y'))=
        (Subtype.val : U → Y) ⁻¹' (Vs : Set Y) := by
  classical
  let K : Set U:=η ⁻¹' ((Subtype.val : U' → Y') ⁻¹' (Vg : Set Y'))
  have hK : IsOpen K:=(Vg.isOpen.preimage continuous_subtype_val).preimage η.continuous
  let Vs : Opens Y:=⟨(Subtype.val : U → Y) '' K,U.isOpen.isOpenMap_subtype_val _ hK⟩
  have hVsU : Vs≤U:=by rintro _ ⟨p,_hp,rfl⟩;exact p.property
  have hFacts:=generated_step_one_facts A B hB Hbar
  have hSubset : (Vs : Set Y)⊆{w | S.proj w∈(tangentChoice A (S.proj p₀)).1 ∧
      (∀E∈origMembers A S,w∉E) ∧ w∉codimOnePartAlong
        (geoTransformAlong (barMarked A) S).N (geoTransformAlong (barMarked A) S).ideal
        (geoTransformAlong (barMarked A) S).d} := by
    rintro _ ⟨p,hp,rfl⟩
    have hpVg : (η p).val∈Vg:=hp
    have hpMask:=interior_subset (hMask hpVg)
    have hBase : S.proj p.val∈(tangentChoice A (S.proj p₀)).1 := by
      obtain ⟨t,ht,heq⟩:=hDomain hpVg
      let q : V₀:=⟨S.proj p.val,HironakaActualAnchoredCurrentHistories.Anchored.source_mem_initial H p⟩
      have hsq : T.proj (η p).val=(φ q).val:=
        HironakaActualAnchoredCurrentHistories.Anchored.projection_square H p
      have htq : t=φ q:=Subtype.ext (heq.trans hsq)
      change (φ.symm t).val∈(tangentChoice A (S.proj p₀)).1 at ht
      rwa [htq,φ.symm_apply_apply] at ht
    have hOldIff : (∀E∈origMembers A S,p.val∉E) ↔
        (∀E∈origMembers B T,(η p).val∉E) := by
      have h:=congrArg (fun L : List (Set U)=>∀K∈L,p∉K) hFacts.1
      simpa only [List.forall_mem_map,mem_preimage] using Iff.of_eq h
    have hLevelB : level B T (η p).val=0 := by
      unfold level boundaryCount
      rw [Finset.card_eq_zero,Finset.filter_eq_empty_iff]
      intro i _hi hi
      exact hpMask.2.1 _ (List.get_mem _ i) hi
    have hNotSpecialB : ¬IsSpecial B T (η p).val := by
      rintro (⟨_hzero,hcod⟩ | ⟨hpos,_hmem⟩)
      · exact hpMask.2.2 hcod
      · omega
    refine ⟨hBase,hOldIff.mpr hpMask.2.1,?_⟩
    intro hcod
    apply hNotSpecialB
    apply (hFacts.2 p).2.1.mp
    exact Or.inl ⟨(hFacts.2 p).1.trans hLevelB,hcod⟩
  refine ⟨Vs,hVsU,?_,?_⟩
  · exact interior_maximal hSubset Vs.isOpen
  · ext p
    change p∈K ↔ p.val∈(Subtype.val : U → Y) '' K
    exact ⟨fun hp=>⟨p,hp,rfl⟩,fun ⟨q,hq,heq⟩=>by
      have : q=p:=Subtype.ext heq
      simpa only [this] using hq⟩

end
end Hironaka.HironakaActualOriginalZeroMaskWindow
