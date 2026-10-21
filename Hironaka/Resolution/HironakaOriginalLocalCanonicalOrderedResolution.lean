/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalLocalPureHeadHosts

/-!
# The same actual ordered canonical head-and-tail algorithm on a local base

Original locally good parts, a genuine relatively compact open base and the
actual ordered SNC boundary internally produce the actual ordered-resolution
tree. Every separator is the same individual-sum recipe and every head is a
true pure first-meeting stage; no compactness of local parts is assumed.
Blueprint: `hironaka-original-local-canonical-ordered-resolution-extension.tex`.
-/
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalLocalCanonicalOrderedResolution
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings HironakaBaseChange
  HironakaAdmissibleSequence HironakaAdmissibleCalculus RestrictEmptyTower
  HironakaEmbeddedAnalyticLocal HironakaOriginalCanonicalPartListResolution
  HironakaOriginalCanonicalOrderedResolution HironakaOriginalLocalCanonicalPartListResolution
  HironakaOriginalLocalPureHeadHosts
variable {n : ℕ}

private theorem centresOver_mono {X : CMfd.{u} n} {F G : Set X} (hFG : F ⊆ G) :
    ∀ {D : CMfd.{u} n} (T : BlowupTower X D),CentresOver F T → CentresOver G T
  | _,.refl,_ => True.intro
  | _,.step T _ _ _,h => ⟨centresOver_mono hFG T h.1,fun _ hz => hFG (h.2 hz)⟩

private theorem partsUnion_preimage {A B : Type u} (j : A → B) (L : List (Set B × ℕ)) :
    partsUnion (L.map (fun p => (j ⁻¹' p.1,p.2)))=j ⁻¹' partsUnion L := by
  ext z
  simp [partsUnion]

/-- Original locally good data internally construct the SAME actual ordered
canonical tree on the local base, with whole final strict geometry. -/
theorem exists_local_canonical_ordered_resolution (ℓ : ℕ) :
    ∀ {X : CMfd.{u} n} (E₀ : List (Set X)) (_hE₀ : IsSNCDivisor n E₀)
      (G : Set X) (_hG : IsClosed G) (L : List (Set X × ℕ)),L.length=ℓ →
      (∀ p∈L,IsLocGoodPart n E₀ G p.1 p.2) → L.Pairwise (fun p q => p.1 ∩ q.1 ⊆ G) →
      ∀ {B₀ : CMfd.{u} n} (ι : B₀ → X),IsOpenHoloEmbedding n ι →
      (∃ K : Set X,IsCompact K ∧ range ι ⊆ K) →
      ∃ (D : CMfd.{u} n) (T : BlowupTower B₀ D) (Ef : List (Set D)),
        CanonicalOrderedResolution (E₀.map (ι ⁻¹' ·)) (ι ⁻¹' G)
          (L.map (fun p => (ι ⁻¹' p.1,p.2))) T Ef ∧ CentresOver (ι ⁻¹' G) T ∧
        IsAdmissibleBlowupSequence n B₀ (E₀.map (ι ⁻¹' ·)) (ι ⁻¹' G) D T.proj Ef ∧
        IsSNCDivisor n Ef ∧
        (∀ p∈L,(∀ z∈strictTransform n T.proj (ι ⁻¹' p.1),
          RegularAtDim (n := n) (strictTransform n T.proj (ι ⁻¹' p.1)) z p.2) ∧
          HasNormalCrossings n (strictTransform n T.proj (ι ⁻¹' p.1)) Ef) ∧
        L.Pairwise (fun p q => Disjoint (strictTransform n T.proj (ι ⁻¹' p.1))
          (strictTransform n T.proj (ι ⁻¹' q.1))) := by
  induction ℓ with
  | zero =>
      intro X E₀ hE₀ G _hG L hL _hgood _hpair B₀ ι hι _hKι
      rw [List.length_eq_zero_iff.mp hL]
      exact ⟨B₀,.refl,E₀.map (ι ⁻¹' ·),.nil,True.intro,
        IsAdmissibleBlowupSequence.refl,hι.isSNCDivisor_map_preimage hE₀,
        fun p hp => absurd hp List.not_mem_nil,List.Pairwise.nil⟩
  | succ ℓ ih =>
      intro X E₀ hE₀ G hG L hL hgood hpair B₀ ι hι hKι
      obtain ⟨⟨A,d⟩,L',rfl⟩ := List.exists_cons_of_length_eq_add_one hL
      have hL' : L'.length=ℓ := by simpa using hL
      obtain ⟨hAsep,hpair'⟩ := List.pairwise_cons.mp hpair
      have hA := hgood (A,d) (List.mem_cons_self ..)
      have hgood' : ∀ p∈L',IsLocGoodPart n E₀ G p.1 p.2 :=
        fun p hp => hgood p (List.mem_cons_of_mem _ hp)
      obtain ⟨C₀,T₀,E₁,H₀,EH₀,GH₀,P₀,j₀,hsep,hover₀,hadm₀,hE₁,hEH₀,hGH₀,hj₀,hKj₀,
          hE₀dict,hG₀dict,hgood₀,hdis₀,hinter₀,hstrict₀,hhostsep₀,hsrcsep₀⟩ :=
        exists_local_canonical_ordered_separator ℓ E₀ hE₀ G hG A d hA L' hL' hgood' hAsep ι hι hKι
      obtain ⟨C₁,T₁,H₁,EH₁,GH₁,P₁,j₁,hhead,hoverHead,hadmHead,hEH₁,hGH₁,hj₁,hKj₁,
          hE₁dict,hG₁dict,hgood₁,hdis₁,hinter₁,hstrict₁,hregHost,hNCHost⟩ :=
        exists_local_pure_head_host EH₀ hEH₀ GH₀ hGH₀ (P₀ A) d (hgood₀ A d hA) j₀ hj₀ hKj₀
      have hAeq₀ := hstrict₀ A hA.isClosed hA.2.2.2.2
      rw [← hE₀dict,← hAeq₀] at hhead hadmHead hE₁dict
      rw [hG₀dict] at hoverHead hadmHead hG₁dict
      let A₁ := strictTransform n T₀.proj (ι ⁻¹' A)
      let MHead := partMarkedIdeal E₁ A₁
      let E₂ := (geoTransformAlong MHead T₁).E
      change E₂=EH₁.map (j₁ ⁻¹' ·) at hE₁dict
      let G₁ := T₀.proj ⁻¹' (ι ⁻¹' G)
      let Lsource := strictParts T₁ (strictParts T₀ (L'.map (fun p => (ι ⁻¹' p.1,p.2))))
      let LH := L'.map (fun p => (P₁ (P₀ p.1),p.2))
      let KH := partsUnion LH
      let GH := GH₁ ∩ KH
      have hgoodH (p : Set X × ℕ) (hp : p∈L') :
          IsLocGoodPart n EH₁ GH₁ (P₁ (P₀ p.1)) p.2 := hgood₁ _ p.2 (hgood₀ _ p.2 (hgood' p hp))
      have hKH : IsClosed KH := by
        apply HironakaEmbeddedBoundary.isClosed_biUnion_of_forall_isClosed
        intro S hS
        obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hS
        obtain ⟨p₀,hp₀,rfl⟩ := List.mem_map.mp hp
        exact (hgoodH p₀ hp₀).isClosed
      have hmemKH : ∀ p∈LH,p.1 ⊆ KH := fun p hp z hz =>
        mem_iUnion₂.mpr ⟨p.1,List.mem_map_of_mem hp,hz⟩
      have hgoodHcut : ∀ p∈LH,IsLocGoodPart n EH₁ GH p.1 p.2 := by
        intro p hp
        obtain ⟨p₀,hp₀,rfl⟩ := List.mem_map.mp hp
        exact (hgoodH p₀ hp₀).inter (hmemKH _ hp)
      have hpairH : LH.Pairwise (fun p q => p.1 ∩ q.1 ⊆ GH) := by
        simp only [LH,List.pairwise_map]
        refine hpair'.imp_of_mem fun {p q} hp hq hpq z hz => ⟨?_,?_⟩
        · exact hinter₁ _ _ (hgood₀ _ p.2 (hgood' p hp)).isClosed
            (hgood₀ _ q.2 (hgood' q hq)).isClosed
            (hinter₀ _ _ (hgood' p hp).isClosed (hgood' q hq).isClosed hpq) hz
        · exact hmemKH _ (List.mem_map_of_mem hp) hz.1
      have hGH : IsClosed GH := hGH₁.inter hKH
      obtain ⟨D,T,Ef,hTree,hoverTail,hadmTail,hEf,hResTail,hDisjTail⟩ :=
        ih EH₁ hEH₁ GH hGH LH (by simpa only [LH,List.length_map] using hL') hgoodHcut hpairH j₁ hj₁ hKj₁
      have hpartEq (p : Set X × ℕ) (hp : p∈L') :
          strictTransform n T₁.proj (strictTransform n T₀.proj (ι ⁻¹' p.1))=j₁ ⁻¹' P₁ (P₀ p.1) := by
        rw [hstrict₀ p.1 (hgood' p hp).isClosed (hgood' p hp).2.2.2.2]
        exact hstrict₁ _ (hgood₀ _ p.2 (hgood' p hp)).isClosed (hgood₀ _ p.2 (hgood' p hp)).2.2.2.2
      have hLeq : Lsource=LH.map (fun p => (j₁ ⁻¹' p.1,p.2)) := by
        simp only [Lsource,LH,strictParts,List.map_map]
        apply List.map_congr_left
        intro p hp
        exact Prod.ext (hpartEq p hp) rfl
      have hbad : j₁ ⁻¹' GH=T₁.proj ⁻¹' G₁ ∩ partsUnion Lsource := by
        rw [preimage_inter,hG₁dict,hLeq,partsUnion_preimage]
      have hTree' : CanonicalOrderedResolution E₂
          (T₁.proj ⁻¹' G₁ ∩ partsUnion Lsource) Lsource T Ef := by
        rw [hE₁dict,← hbad,hLeq]
        exact hTree
      have hoverTail' : CentresOver (T₁.proj ⁻¹' G₁ ∩ partsUnion Lsource) T := by rw [← hbad];exact hoverTail
      have hadmTail' : IsAdmissibleBlowupSequence n C₁ E₂
          (T₁.proj ⁻¹' G₁ ∩ partsUnion Lsource) D T.proj Ef := by
        rw [hE₁dict,← hbad]
        exact hadmTail
      let TT := T₀.append (T₁.append T)
      have hTreeT : CanonicalOrderedResolution (E₀.map (ι ⁻¹' ·)) (ι ⁻¹' G)
          (((A,d)::L').map (fun p => (ι ⁻¹' p.1,p.2))) TT Ef :=
        .cons T₀ T₁ T hsep hhead hTree'
      have hoverT : CentresOver (ι ⁻¹' G) TT :=
        (centresOver_append_iff _ T₀ (T₁.append T)).mpr ⟨hover₀,
          (centresOver_append_iff G₁ T₁ T).mpr
            ⟨hoverHead,centresOver_mono inter_subset_left T hoverTail'⟩⟩
      have hadmTailG := hadmTail'.mono (inter_subset_left :
        T₁.proj ⁻¹' G₁ ∩ partsUnion Lsource ⊆ T₁.proj ⁻¹' G₁)
      have hadmT : IsAdmissibleBlowupSequence n B₀ (E₀.map (ι ⁻¹' ·)) (ι ⁻¹' G) D TT.proj Ef := by
        simpa only [TT,BlowupTower.proj_append] using
          IsAdmissibleBlowupSequence.comp hadm₀ (IsAdmissibleBlowupSequence.comp hadmHead hadmTailG)
      let A₂ := strictTransform n T₁.proj A₁
      have hAeq₁ : A₂=j₁ ⁻¹' P₁ (P₀ A) := by
        change strictTransform n T₁.proj A₁=j₁ ⁻¹' P₁ (P₀ A)
        rw [show A₁=j₀ ⁻¹' P₀ A from hAeq₀]
        exact hstrict₁ _ (hgood₀ A d hA).isClosed (hgood₀ A d hA).2.2.2.2
      have hregHead : ∀ z∈A₂,RegularAtDim (n := n) A₂ z d := by
        rw [hAeq₁]
        intro z hz
        exact hj₁.regularAtDim_preimage (hregHost (j₁ z) hz)
      have hNCHead : HasNormalCrossings n A₂ E₂ := by
        rw [hAeq₁,hE₁dict]
        exact hj₁.hasNormalCrossings_preimage hNCHost
      have hA₂K₂ : Disjoint A₂ (partsUnion Lsource) := by
        rw [disjoint_left]
        intro z hzA hzK
        obtain ⟨S,hS,hzS⟩ := mem_iUnion₂.mp hzK
        obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hS
        obtain ⟨p₁,hp₁,rfl⟩ := List.mem_map.mp hp
        obtain ⟨p₀,hp₀,rfl⟩ := List.mem_map.mp hp₁
        obtain ⟨pOrig,hpOrig,rfl⟩ := List.mem_map.mp hp₀
        exact disjoint_left.mp (hsrcsep₀ pOrig hpOrig)
          (strictTransform_subset_preimage T₁.contMDiff_proj.continuous isClosed_closure hzA)
          (strictTransform_subset_preimage T₁.contMDiff_proj.continuous isClosed_closure hzS)
      have hA₂bad : Disjoint A₂ (T₁.proj ⁻¹' G₁ ∩ partsUnion Lsource) :=
        hA₂K₂.mono_right inter_subset_right
      have hbadClosed : IsClosed (T₁.proj ⁻¹' G₁ ∩ partsUnion Lsource) := by
        rw [← hbad]
        exact hGH.preimage hj₁.continuous
      have hST (S : Set X) : strictTransform n TT.proj (ι ⁻¹' S)=
          strictTransform n T.proj (strictTransform n T₁.proj (strictTransform n T₀.proj (ι ⁻¹' S))) := by
        rw [show TT.proj=T₀.proj ∘ (T₁.proj ∘ T.proj) by simp only [TT,BlowupTower.proj_append],
          StrictTransformComposition.strictTransform_comp T₀.contMDiff_proj (T₁.contMDiff_proj.comp T.contMDiff_proj),
          StrictTransformComposition.strictTransform_comp T₁.contMDiff_proj T.contMDiff_proj]
      have hResT : ∀ p∈(A,d)::L',(∀ z∈strictTransform n TT.proj (ι ⁻¹' p.1),
          RegularAtDim (n := n) (strictTransform n TT.proj (ι ⁻¹' p.1)) z p.2) ∧
          HasNormalCrossings n (strictTransform n TT.proj (ι ⁻¹' p.1)) Ef := by
        intro p hp
        rw [hST]
        rcases List.mem_cons.mp hp with rfl | hp
        · have hexc := IsAdmissibleBlowupSequence.exceptionalLocus_subset hadmTail'
          have hpre : strictTransform n T.proj A₂=T.proj ⁻¹' A₂ :=
            strictTransform_eq_preimage_of_disjoint T.contMDiff_proj.continuous hexc isClosed_closure hA₂bad
          change (∀ z∈strictTransform n T.proj A₂,RegularAtDim (n := n) (strictTransform n T.proj A₂) z d) ∧ _
          rw [hpre]
          have hE₂ : IsSNCDivisor n E₂ := by rw [hE₁dict];exact hj₁.isSNCDivisor_map_preimage hEH₁
          exact ⟨fun z hz => regularAtDim_preimage_of_disjoint T.contMDiff_proj hexc hA₂bad (hregHead (T.proj z) hz),
            IsAdmissibleBlowupSequence.hasNormalCrossings_preimage_of_disjoint hadmTail' hE₂.1
              hbadClosed hA₂bad hNCHead⟩
        · rw [hpartEq p hp]
          exact hResTail _ (List.mem_map_of_mem hp)
      have hDisjT : ((A,d)::L').Pairwise (fun p q =>
          Disjoint (strictTransform n TT.proj (ι ⁻¹' p.1)) (strictTransform n TT.proj (ι ⁻¹' q.1))) := by
        rw [List.pairwise_cons]
        refine ⟨?_,?_⟩
        · intro p hp
          rw [show TT.proj=T₀.proj ∘ (T₁.proj ∘ T.proj) by simp only [TT,BlowupTower.proj_append],
            StrictTransformComposition.strictTransform_comp T₀.contMDiff_proj (T₁.contMDiff_proj.comp T.contMDiff_proj),
            StrictTransformComposition.strictTransform_comp T₀.contMDiff_proj (T₁.contMDiff_proj.comp T.contMDiff_proj)]
          exact ((hsrcsep₀ p hp).preimage (T₁.proj ∘ T.proj)).mono
            (strictTransform_subset_preimage (T₁.contMDiff_proj.comp T.contMDiff_proj).continuous isClosed_closure)
            (strictTransform_subset_preimage (T₁.contMDiff_proj.comp T.contMDiff_proj).continuous isClosed_closure)
        · have hh := hDisjTail
          simp only [LH,List.pairwise_map] at hh
          refine hh.imp_of_mem fun {p q} hp hq hpq => ?_
          rw [hST,hST,hpartEq p hp,hpartEq q hq]
          exact hpq
      exact ⟨D,TT,Ef,hTreeT,hoverT,hadmT,hEf,hResT,hDisjT⟩

end
end Hironaka.HironakaOriginalLocalCanonicalOrderedResolution
