/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualOpenTowerHosts
import Hironaka.Resolution.HironakaOriginalCanonicalPartListResolution
import Hironaka.Resolution.HironakaEmbeddedAnalyticLocal

/-!
# The same ordered individual-sum algorithm on a relatively compact open base

Each actual local canonical stage retains its genuine larger host. This lets
induction continue on original locally good parts without pretending that their
restricted carriers or intersections are compact. The literal actual chain,
whole boundary and whole strict sets are retained at the source.
Blueprint: `hironaka-original-local-canonical-part-list-resolution-extension.tex`.
-/
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalLocalCanonicalPartListResolution
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings HironakaBaseChange
  HironakaAdmissibleSequence HironakaAdmissibleCalculus RestrictEmptyTower EmbeddedFromResolution
  HironakaEmbeddedAnalyticLocal HironakaOriginalCanonicalPartListResolution
  HironakaOriginalCanonicalSumSeparation HironakaOriginalLocalCanonicalSumSeparation
  HironakaSmoothSubmersionCartesianTower HironakaOriginalStoppedPrefixSmoothComparison
  HironakaSmoothSubmersionOrderedGlobalTrace HironakaActualOpenTowerHosts
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n : ℕ}

private theorem centresOver_mono {X : CMfd.{u} n} {F G : Set X} (hFG : F ⊆ G) :
    ∀ {D : CMfd.{u} n} (T : BlowupTower X D),CentresOver F T → CentresOver G T
  | _,.refl,_ => True.intro
  | _,.step T _ _ _,h => ⟨centresOver_mono hFG T h.1,fun _ hz => hFG (h.2 hz)⟩

private theorem submersion_of_open {X B : CMfd.{u} n} {ι : B → X}
    (hι : IsOpenHoloEmbedding n ι) :
    Manifold.IsSubmersion 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ ι := by
  obtain ⟨O,Φ,hΦ⟩ := hι
  have hh := isSubmersion_val_comp (B := B) O
    (HironakaSmoothSubmersionOriginalGlobalFinite.isSubmersion_biholomorphism
      (D := B) (C := CMfd.of (n := n) O) Φ)
  have he : ι=(Subtype.val : O → X) ∘ Φ := funext hΦ
  rw [he]
  exact hh

/-- Original local parts produce the SAME actual ordered canonical chain,
with a genuine compact-enclosed final host for further local recursion. -/
theorem exists_local_canonical_ordered_separator (ℓ : ℕ) :
    ∀ {X : CMfd.{u} n} (E : List (Set X)) (_hE : IsSNCDivisor n E)
      (G : Set X) (_hG : IsClosed G) (A : Set X) (d : ℕ) (_hA : IsLocGoodPart n E G A d)
      (L : List (Set X × ℕ)),L.length=ℓ →
      (∀ p∈L,IsLocGoodPart n E G p.1 p.2) → (∀ p∈L,A ∩ p.1 ⊆ G) →
      ∀ {B₀ : CMfd.{u} n} (ι : B₀ → X),IsOpenHoloEmbedding n ι →
      (∃ K : Set X,IsCompact K ∧ range ι ⊆ K) →
      ∃ (C : CMfd.{u} n) (T : BlowupTower B₀ C) (Ef : List (Set C))
        (H : CMfd.{u} n) (EH : List (Set H)) (GH : Set H)
        (P : Set X → Set H) (j : C → H),
        CanonicalSeparationChain (E.map (ι ⁻¹' ·)) (ι ⁻¹' A)
          (L.map (fun p => (ι ⁻¹' p.1,p.2))) T Ef ∧
        CentresOver (ι ⁻¹' G) T ∧
        IsAdmissibleBlowupSequence n B₀ (E.map (ι ⁻¹' ·)) (ι ⁻¹' G) C T.proj Ef ∧
        IsSNCDivisor n Ef ∧ IsSNCDivisor n EH ∧ IsClosed GH ∧
        IsOpenHoloEmbedding n j ∧ (∃ K : Set H,IsCompact K ∧ range j ⊆ K) ∧
        Ef=EH.map (j ⁻¹' ·) ∧ j ⁻¹' GH=T.proj ⁻¹' (ι ⁻¹' G) ∧
        (∀ S e,IsLocGoodPart n E G S e → IsLocGoodPart n EH GH (P S) e) ∧
        (∀ S R,IsClosed S → IsClosed R → Disjoint S R → Disjoint (P S) (P R)) ∧
        (∀ S R,IsClosed S → IsClosed R → S ∩ R ⊆ G → P S ∩ P R ⊆ GH) ∧
        (∀ S,IsClosed S → S ⊆ closure (S \ G) →
          strictTransform n T.proj (ι ⁻¹' S)=j ⁻¹' P S) ∧
        (∀ p∈L,Disjoint (P A) (P p.1)) ∧
        (∀ p∈L,Disjoint (strictTransform n T.proj (ι ⁻¹' A))
          (strictTransform n T.proj (ι ⁻¹' p.1))) := by
  induction ℓ with
  | zero =>
      intro X E hE G hG A d _hA L hL _hgood _hsep B₀ ι hι hKι
      rw [List.length_eq_zero_iff.mp hL]
      refine ⟨B₀,.refl,E.map (ι ⁻¹' ·),X,E,G,id,ι,.nil,True.intro,
        IsAdmissibleBlowupSequence.refl,hι.isSNCDivisor_map_preimage hE,hE,hG,hι,hKι,rfl,rfl,
        fun _ _ h => h,fun _ _ _ _ h => h,fun _ _ _ _ h => h,?_,
        fun p hp => absurd hp List.not_mem_nil,fun p hp => absurd hp List.not_mem_nil⟩
      intro S hS _hden
      change strictTransform n id (ι ⁻¹' S)=ι ⁻¹' S
      simp only [strictTransform,exceptionalLocus_id,sdiff_empty,preimage_id,
        (hS.preimage hι.continuous).closure_eq]
  | succ ℓ ih =>
      intro X E hE G hG A d hA L hL hgood hsep B₀ ι hι hKι
      obtain ⟨⟨B,e⟩,L',rfl⟩ := List.exists_cons_of_length_eq_add_one hL
      have hL' : L'.length=ℓ := by simpa using hL
      have hB := hgood (B,e) (List.mem_cons_self ..)
      have hgood' : ∀ p∈L',IsLocGoodPart n E G p.1 p.2 :=
        fun p hp => hgood p (List.mem_cons_of_mem _ hp)
      have hAB : A ∩ B ⊆ G := hsep (B,e) (List.mem_cons_self ..)
      obtain ⟨U,hιU,hUc,hcι⟩ := exists_opens_of_range_subset (n := n) hKι
      let ι₁ : B₀ → U := fun z => ⟨ι z,hιU (subset_closure ⟨z,rfl⟩)⟩
      have hι₁ : IsOpenHoloEmbedding n ι₁ := hι.codRestrict U _
      have hb := submersion_of_open (X := CMfd.of (n := n) U) hι₁
      let AU := (Subtype.val : U → X) ⁻¹' A
      let BU := (Subtype.val : U → X) ⁻¹' B
      let EU := E.map ((Subtype.val : U → X) ⁻¹' ·)
      let GU := (Subtype.val : U → X) ⁻¹' G
      obtain ⟨D₀,T₀,hM,hcT₀,hrT₀,hover₀,hadm₀,hE₁,_hpb,_hsupp,hdis₀,
        _hhol,_hproper,_hsurj,_hiso,hsource₀⟩ :=
        exists_local_canonical_sum_separation hA.1 hB.1 hA.interior_eq_empty
          (hA.subset_closure_diff_of_inter_subset hAB)
          (hB.subset_closure_diff_of_inter_subset (by rw [inter_comm];exact hAB))
          E hE U hUc subset_closure
      let M := sumMarkedIdeal (X := CMfd.of (n := n) U) AU BU EU
      let E₁ := (geoTransformAlong M T₀).E
      let G₁ := T₀.proj ⁻¹' GU
      let P₀ : Set X → Set D₀ := fun S => strictTransform n T₀.proj ((Subtype.val : U → X) ⁻¹' S)
      have hval := isOpenHoloEmbedding_val (n := n) U
      have hABU : AU ∩ BU ⊆ GU := preimage_mono hAB
      have hadm₀G := hadm₀.mono hABU
      have hover₀G : CentresOver GU T₀ := centresOver_mono hABU T₀ hover₀
      have hG₁ : IsClosed G₁ := (hG.preimage continuous_subtype_val).preimage T₀.contMDiff_proj.continuous
      have hgood₀ (S : Set X) (f : ℕ) (hS : IsLocGoodPart n E G S f) :
          IsLocGoodPart n E₁ G₁ (P₀ S) f :=
        (hS.preimage hval).strictTransform hadm₀G (hval.isSNCDivisor_map_preimage hE).1
      have hsep₁ : ∀ p∈L'.map (fun p => (P₀ p.1,p.2)),P₀ A ∩ p.1 ⊆ G₁ := by
        intro p hp z hz
        obtain ⟨p₀,hp₀,rfl⟩ := List.mem_map.mp hp
        exact hsep p₀ (List.mem_cons_of_mem _ hp₀)
          ⟨strictTransform_subset_preimage T₀.contMDiff_proj.continuous
              (hA.isClosed.preimage continuous_subtype_val) hz.1,
            strictTransform_subset_preimage T₀.contMDiff_proj.continuous
              ((hgood' p₀ hp₀).isClosed.preimage continuous_subtype_val) hz.2⟩
      obtain ⟨C₀,Q₀,g₀,hactual,_heq,hN,_hg,_hlen,_hcomm,_hcart,hcQ₀,hrQ₀,hoverQ₀,hadmQ₀,
        _hSNCEQ,hEQ₀,_hpbQ,_hsuppQ,_hstrictA,_hstrictB,_hdisQ,_hholQ,_hproperQ,_hsurjQ,_hisoQ⟩ :=
        hsource₀ B₀ ι₁ hb
      have hg₀ := upper_isOpenHoloEmbedding hactual hι₁
      have hKg₀ := upper_range_subset_compact U hιU hcι hactual
      let O : Opens (CMfd.of (n := n) U) := ⟨GUᶜ,(hG.preimage continuous_subtype_val).isOpen_compl⟩
      have havoid : CentresAvoid O T₀ := centresAvoid_of_centresOver O disjoint_compl_left T₀ hover₀G
      have hstrict₀ (S : Set X) (hden : S ⊆ closure (S \ G)) :
          strictTransform n Q₀.proj (ι ⁻¹' S)=g₀ ⁻¹' P₀ S := by
        apply IsActualTowerPullback.strictTransform_preimage_of_centresAvoid hb hactual O havoid
          ((Subtype.val : U → X) ⁻¹' S)
        change (Subtype.val : U → X) ⁻¹' S ⊆ closure
          ((Subtype.val : U → X) ⁻¹' S \ (Subtype.val : U → X) ⁻¹' G)
        simpa only [hval.preimage_closure,preimage_sdiff] using
          (preimage_mono hden : (Subtype.val : U → X) ⁻¹' S ⊆ _)
      obtain ⟨C,T,Ef,H,EH,GH,P₁,j,hchain,hover,hadm,hEf,hEH,hGH,hj,hKj,hEfinal,hGfinal,
        hgoodH,hdisH,hinterH,hstrictH,hsepH,_hsepSource⟩ :=
        ih E₁ hE₁ G₁ hG₁ (P₀ A) d (hgood₀ A d hA)
          (L'.map (fun p => (P₀ p.1,p.2))) (by simpa only [List.length_map] using hL')
          (by intro p hp;obtain ⟨p₀,hp₀,rfl⟩ := List.mem_map.mp hp;exact hgood₀ p₀.1 p₀.2 (hgood' p₀ hp₀))
          hsep₁ g₀ hg₀ hKg₀
      let TT := Q₀.append T
      let P : Set X → Set H := fun S => P₁ (P₀ S)
      have hEinit : (EU.map (ι₁ ⁻¹' ·))=E.map (ι ⁻¹' ·) := by simp only [EU,List.map_map];rfl
      rw [hEinit] at hN hcQ₀ hrQ₀ hadmQ₀ hEQ₀
      change (geoTransformAlong (sumMarkedIdeal (X := B₀) (ι ⁻¹' A) (ι ⁻¹' B)
        (E.map (ι ⁻¹' ·))) Q₀).E=E₁.map (g₀ ⁻¹' ·) at hEQ₀
      have hAeq := hstrict₀ A hA.2.2.2.2
      have hLeq : (L'.map (fun p => (P₀ p.1,p.2))).map (fun p => (g₀ ⁻¹' p.1,p.2))=
          (L'.map (fun p => (ι ⁻¹' p.1,p.2))).map (fun p => (strictTransform n Q₀.proj p.1,p.2)) := by
        simp only [List.map_map]
        apply List.map_congr_left
        intro p hp
        exact Prod.ext (hstrict₀ p.1 (hgood' p hp).2.2.2.2).symm rfl
      have hchain' : CanonicalSeparationChain
          (geoTransformAlong (sumMarkedIdeal (X := B₀) (ι ⁻¹' A) (ι ⁻¹' B) (E.map (ι ⁻¹' ·))) Q₀).E
          (strictTransform n Q₀.proj (ι ⁻¹' A))
          ((L'.map (fun p => (ι ⁻¹' p.1,p.2))).map (fun p => (strictTransform n Q₀.proj p.1,p.2))) T Ef := by
        rw [hEQ₀,hAeq,← hLeq]
        exact hchain
      have hchainT : CanonicalSeparationChain (E.map (ι ⁻¹' ·)) (ι ⁻¹' A)
          (((B,e)::L').map (fun p => (ι ⁻¹' p.1,p.2))) TT Ef := by
        exact .cons Q₀ T (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hι.contMDiff hA.1)
          (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hι.contMDiff hB.1) hN hcQ₀ hrQ₀ hchain'
      have hbad : g₀ ⁻¹' G₁=Q₀.proj ⁻¹' (ι ⁻¹' G) := by
        ext z
        change ((T₀.proj (g₀ z) : U) : X) ∈ G ↔ ι (Q₀.proj z) ∈ G
        rw [hactual.proj_comm z]
      have hadmQ₀G : IsAdmissibleBlowupSequence n B₀ (E.map (ι ⁻¹' ·)) (ι ⁻¹' G)
          C₀ Q₀.proj (geoTransformAlong (sumMarkedIdeal (X := B₀) (ι ⁻¹' A) (ι ⁻¹' B)
            (E.map (ι ⁻¹' ·))) Q₀).E := hadmQ₀.mono (preimage_mono hAB)
      change CentresOver (ι ⁻¹' (A ∩ B)) Q₀ at hoverQ₀
      have hoverQ₀G := centresOver_mono (preimage_mono hAB (f := ι)) Q₀ hoverQ₀
      have hadm' : IsAdmissibleBlowupSequence n C₀
          (geoTransformAlong (sumMarkedIdeal (X := B₀) (ι ⁻¹' A) (ι ⁻¹' B) (E.map (ι ⁻¹' ·))) Q₀).E
          (Q₀.proj ⁻¹' (ι ⁻¹' G)) C T.proj Ef := by
        rw [hEQ₀,← hbad]
        exact hadm
      have hoverT : CentresOver (ι ⁻¹' G) TT :=
        (centresOver_append_iff _ Q₀ T).mpr ⟨hoverQ₀G,by rw [← hbad];exact hover⟩
      have hadmT : IsAdmissibleBlowupSequence n B₀ (E.map (ι ⁻¹' ·)) (ι ⁻¹' G) C TT.proj Ef := by
        simpa only [TT,BlowupTower.proj_append] using IsAdmissibleBlowupSequence.comp hadmQ₀G hadm'
      have hP₀dis (S R : Set X) (hS : IsClosed S) (hR : IsClosed R) (hSR : Disjoint S R) :
          Disjoint (P₀ S) (P₀ R) :=
        ((hSR.preimage (Subtype.val : U → X)).preimage T₀.proj).mono
          (strictTransform_subset_preimage T₀.contMDiff_proj.continuous (hS.preimage continuous_subtype_val))
          (strictTransform_subset_preimage T₀.contMDiff_proj.continuous (hR.preimage continuous_subtype_val))
      have hP₀inter (S R : Set X) (hS : IsClosed S) (hR : IsClosed R) (hSR : S ∩ R ⊆ G) :
          P₀ S ∩ P₀ R ⊆ G₁ := by
        intro z hz
        exact hSR ⟨strictTransform_subset_preimage T₀.contMDiff_proj.continuous
            (hS.preimage continuous_subtype_val) hz.1,
          strictTransform_subset_preimage T₀.contMDiff_proj.continuous
            (hR.preimage continuous_subtype_val) hz.2⟩
      have hstrictFull (S : Set X) (hS : IsClosed S) (hden : S ⊆ closure (S \ G)) :
          strictTransform n TT.proj (ι ⁻¹' S)=j ⁻¹' P S := by
        rw [BlowupTower.proj_append,StrictTransformComposition.strictTransform_comp
          Q₀.contMDiff_proj T.contMDiff_proj,hstrict₀ S hden]
        apply hstrictH (P₀ S) isClosed_closure
        apply strictTransform_subset_closure_diff T₀.contMDiff_proj (hS.preimage continuous_subtype_val)
        simpa only [hval.preimage_closure,preimage_sdiff] using
          (preimage_mono hden : (Subtype.val : U → X) ⁻¹' S ⊆ _)
      have hsepFull : ∀ p∈(B,e)::L',Disjoint (P A) (P p.1) := by
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact hdisH _ _ isClosed_closure isClosed_closure hdis₀
        · exact hsepH _ (List.mem_map_of_mem hp)
      refine ⟨C,TT,Ef,H,EH,GH,P,j,hchainT,hoverT,hadmT,hEf,hEH,hGH,hj,hKj,hEfinal,?_,
        fun S f hS => hgoodH _ f (hgood₀ S f hS),
        fun S R hS hR hSR => hdisH _ _ isClosed_closure isClosed_closure (hP₀dis S R hS hR hSR),
        fun S R hS hR hSR => hinterH _ _ isClosed_closure isClosed_closure (hP₀inter S R hS hR hSR),
        hstrictFull,hsepFull,?_⟩
      · rw [hGfinal,hbad,BlowupTower.proj_append]
        rfl
      · intro p hp
        rw [hstrictFull A hA.isClosed hA.2.2.2.2,
          hstrictFull p.1 (hgood p hp).isClosed (hgood p hp).2.2.2.2]
        exact (hsepFull p hp).preimage j

end
end Hironaka.HironakaOriginalLocalCanonicalPartListResolution
