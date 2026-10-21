/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Support.OriginalCentresOverAppendHeadExact
import Hironaka.Resolution.HironakaOriginalCanonicalDimensionList
import Hironaka.Resolution.HironakaOriginalCanonicalSumSeparation
import Hironaka.Resolution.HironakaActualTowerPullbackAppend

/-!
# Actual canonical stages of the ordered part recursion

The finite separator chain retains every actual canonical sum terminal stage,
the whole accumulated boundaries, and the same actual composite projection.
Its source is constructed stagewise by actual smooth pullback, without source
compactness or a source history premise.  This is a subroutine of the subsequent
mixed-dimensional resolution, rather than one CAN history for a different ideal.

Blueprint: `hironaka-original-canonical-part-list-resolution-extension.tex`.
-/

set_option autoImplicit false

open Set Filter Function TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaOriginalCanonicalPartListResolution

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  CanonicalCentres HironakaAdmissibleSequence RestrictEmptyTower EmbeddedFromResolution
  HironakaAdmissibleCalculus
  HironakaEmbeddedAnalytic HironakaOriginalCanonicalSumSeparation
  HironakaSmoothSubmersionOrderedChoiceBaseChange HironakaSmoothSubmersionCartesianTower
  HironakaOriginalStoppedPrefixSmoothComparison HironakaSmoothSubmersionRelativeGeometry
  HironakaSmoothSubmersionNormalCrossings

open ResolutionInvariantSpec (IsInvDomain IsCanonical)

/-- The ordered finite chain records genuine canonical terminal sum stages,
their actual towers, and the entire boundary passed to the next stage. -/
inductive CanonicalSeparationChain {n : ℕ} :
    {X : CMfd.{u} n} → (E₀ : List (Set X)) → (A : Set X) →
    (L : List (Set X × ℕ)) → {D : CMfd.{u} n} → BlowupTower X D → List (Set D) → Prop
  | nil {X : CMfd.{u} n} {E₀ : List (Set X)} {A : Set X} :
      CanonicalSeparationChain E₀ A [] .refl E₀
  | cons {X : CMfd.{u} n} {E₀ : List (Set X)} {A B : Set X}
      {e : ℕ} {L : List (Set X × ℕ)} {D Z : CMfd.{u} n}
      (T : BlowupTower X D) (S : BlowupTower D Z)
      (hAa : IsComplexAnalyticSubset (n := n) A) (hBa : IsComplexAnalyticSubset (n := n) B)
      (hM : IsInvDomain n (sumMarkedIdeal A B E₀))
      (hc : IsCanonical (sumMarkedIdeal A B E₀) ((canonicalInvariant n).inv (sumMarkedIdeal A B E₀)) T)
      (hr : IsGeoResolution (sumMarkedIdeal A B E₀) T) {E₁ : List (Set Z)}
      (hs : CanonicalSeparationChain (geoTransformAlong (sumMarkedIdeal A B E₀) T).E
        (strictTransform n T.proj A) (L.map (fun p => (strictTransform n T.proj p.1,p.2))) S E₁) :
      CanonicalSeparationChain E₀ A ((B,e)::L) (T.append S) E₁

variable {n : ℕ}

private theorem centresOver_mono {X : CMfd.{u} n} {F G : Set X} (hFG : F ⊆ G) :
    ∀ {D : CMfd.{u} n} (T : BlowupTower X D), CentresOver F T → CentresOver G T
  | _, .refl, _ => True.intro
  | _, .step T _C _π _hπ, h => ⟨centresOver_mono hFG T h.1,fun _z hz => hFG (h.2 hz)⟩

private theorem preimage_bad_eq {m : ℕ} {X D : CMfd.{u} n} {Y C : CMfd.{u} m}
    {b : Y → X} {g : C → D} {Q : BlowupTower Y C} {T : BlowupTower X D}
    (h : IsActualTowerPullback b Q T g) (G : Set X) :
    g ⁻¹' (T.proj ⁻¹' G) = Q.proj ⁻¹' (b ⁻¹' G) := by
  ext z
  change T.proj (g z) ∈ G ↔ b (Q.proj z) ∈ G
  rw [h.proj_comm]

/-- Original compact good parts produce the actual ordered canonical chain,
then every smooth source of that SAME chain, with whole intrinsic stage inputs. -/
theorem exists_canonical_ordered_separator (ℓ : ℕ) :
    ∀ {X : CMfd.{u} n} (E₀ : List (Set X)) (_hE₀ : IsSNCDivisor n E₀)
      (G : Set X) (_hG : IsClosed G) (A : Set X) (d : ℕ) (_hA : IsGoodPart n E₀ G A d)
      (L : List (Set X × ℕ)), L.length = ℓ →
      (∀ p ∈ L, IsGoodPart n E₀ G p.1 p.2) → (∀ p ∈ L, A ∩ p.1 ⊆ G) →
      ∃ (D : CMfd.{u} n) (T : BlowupTower X D) (E₁ : List (Set D)),
        CanonicalSeparationChain E₀ A L T E₁ ∧ CentresOver G T ∧
        IsAdmissibleBlowupSequence n X E₀ G D T.proj E₁ ∧ IsSNCDivisor n E₁ ∧
        (∀ p ∈ L, Disjoint (strictTransform n T.proj A) (strictTransform n T.proj p.1)) ∧
        ∀ {m : ℕ} (Y : CMfd.{u} m) (b : Y → X),
          Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b →
          ∃ (C : CMfd.{u} m) (Q : BlowupTower Y C) (g : C → D),
            IsActualTowerPullback b Q T g ∧
            CanonicalSeparationChain (E₀.map (b ⁻¹' ·)) (b ⁻¹' A)
              (L.map (fun p => (b ⁻¹' p.1,p.2+(m-n)))) Q (E₁.map (g ⁻¹' ·)) ∧
            IsAdmissibleBlowupSequence m Y (E₀.map (b ⁻¹' ·)) (b ⁻¹' G)
              C Q.proj (E₁.map (g ⁻¹' ·)) ∧
            IsSNCDivisor m (E₁.map (g ⁻¹' ·)) ∧
            strictTransform m Q.proj (b ⁻¹' A) = g ⁻¹' strictTransform n T.proj A ∧
            (∀ p ∈ L, strictTransform m Q.proj (b ⁻¹' p.1) = g ⁻¹' strictTransform n T.proj p.1) ∧
            (∀ p ∈ L, Disjoint (strictTransform m Q.proj (b ⁻¹' A))
              (strictTransform m Q.proj (b ⁻¹' p.1))) ∧
            Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ g ∧
            Q.length = T.length ∧ (∀ z, T.proj (g z) = b (Q.proj z)) ∧
            HolomorphicSquarePullback b g Q.proj T.proj := by
  induction ℓ with
  | zero =>
      intro X E₀ hE₀ G hG A d hA L hL _hgood _hsep
      rw [List.length_eq_zero_iff.mp hL]
      refine ⟨X,.refl,E₀,.nil,True.intro,IsAdmissibleBlowupSequence.refl,hE₀,
        fun p hp => absurd hp List.not_mem_nil,?_⟩
      intro m Y b hb
      have hactual := IsActualTowerPullback.refl hb
      have hstrict := IsActualTowerPullback.strictTransform_preimage_of_centresAvoid hb hactual
        ⊤ True.intro A (by simpa using (subset_closure : A ⊆ closure A))
      exact ⟨Y,.refl,b,hactual,.nil,IsAdmissibleBlowupSequence.refl,
        isSNCDivisor_preimage_submersion hb E₀ hE₀,hstrict,
        fun p hp => absurd hp List.not_mem_nil,fun p hp => absurd hp List.not_mem_nil,
        hb,rfl,fun _ => rfl,hactual.universal⟩
  | succ ℓ ih =>
      intro X E₀ hE₀ G hG A d hA L hL hgood hsep
      obtain ⟨⟨B,e⟩,L',rfl⟩ := List.exists_cons_of_length_eq_add_one hL
      have hL' : L'.length = ℓ := by simpa using hL
      have hB := hgood (B,e) (List.mem_cons_self ..)
      have hgood' : ∀ p ∈ L', IsGoodPart n E₀ G p.1 p.2 :=
        fun p hp => hgood p (List.mem_cons_of_mem _ hp)
      have hAB : A ∩ B ⊆ G := hsep (B,e) (List.mem_cons_self ..)
      obtain ⟨D₀,T₀,hM,hcT,hrT,hover₀,hadm₀,hE₁,_hprincipal,_hsupp,hdisj₀,
        _hhol,_hproper,_hsurj,_hiso,hSource₀⟩ :=
        exists_canonical_sum_separation hA.1 hB.1 hA.interior_eq_empty
          (hA.2.1.inter_right hB.isClosed) (hA.subset_closure_diff_of_inter_subset hAB)
          (hB.subset_closure_diff_of_inter_subset (by rw [inter_comm]; exact hAB)) E₀ hE₀
      let M := sumMarkedIdeal A B E₀
      let E₁ := (geoTransformAlong M T₀).E
      let A₁ := strictTransform n T₀.proj A
      let L₁ := L'.map (fun p => (strictTransform n T₀.proj p.1,p.2))
      have hadm₀G := hadm₀.mono hAB
      have hover₀G : CentresOver G T₀ := centresOver_mono hAB T₀ hover₀
      have hf₀ := T₀.contMDiff_proj
      have hA₁ : IsGoodPart n E₁ (T₀.proj ⁻¹' G) A₁ d := hA.strictTransform hadm₀G hE₀.1
      have hgood₁ : ∀ p ∈ L₁, IsGoodPart n E₁ (T₀.proj ⁻¹' G) p.1 p.2 := by
        intro p hp
        obtain ⟨p₀,hp₀,rfl⟩ := List.mem_map.mp hp
        exact (hgood' p₀ hp₀).strictTransform hadm₀G hE₀.1
      have hsep₁ : ∀ p ∈ L₁, A₁ ∩ p.1 ⊆ T₀.proj ⁻¹' G := by
        intro p hp z hz
        obtain ⟨p₀,hp₀,rfl⟩ := List.mem_map.mp hp
        exact hsep p₀ (List.mem_cons_of_mem _ hp₀)
          ⟨HironakaAdmissibleCalculus.strictTransform_subset_preimage hf₀.continuous hA.isClosed hz.1,
            HironakaAdmissibleCalculus.strictTransform_subset_preimage hf₀.continuous (hgood' p₀ hp₀).isClosed hz.2⟩
      obtain ⟨D,T,E₂,hchain,hover,hadm,hE₂,hdisj,hSource⟩ :=
        ih E₁ hE₁ (T₀.proj ⁻¹' G) (hG.preimage hf₀.continuous) A₁ d hA₁ L₁
          (by simpa only [L₁,List.length_map] using hL') hgood₁ hsep₁
      let TT := T₀.append T
      have hchainT : CanonicalSeparationChain E₀ A ((B,e)::L') TT E₂ :=
        .cons T₀ T hA.1 hB.1 hM hcT hrT hchain
      have hoverT : CentresOver G TT := (centresOver_append_iff G T₀ T).mpr ⟨hover₀G,hover⟩
      have hadmT : IsAdmissibleBlowupSequence n X E₀ G D TT.proj E₂ := by
        simpa only [TT,BlowupTower.proj_append] using IsAdmissibleBlowupSequence.comp hadm₀G hadm
      have hdisjT : ∀ p ∈ (B,e)::L',
          Disjoint (strictTransform n TT.proj A) (strictTransform n TT.proj p.1) := by
        intro p hp
        rw [BlowupTower.proj_append,
          StrictTransformComposition.strictTransform_comp hf₀ T.contMDiff_proj,
          StrictTransformComposition.strictTransform_comp hf₀ T.contMDiff_proj]
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact (hdisj₀.preimage T.proj).mono
            (HironakaAdmissibleCalculus.strictTransform_subset_preimage T.contMDiff_proj.continuous isClosed_closure)
            (HironakaAdmissibleCalculus.strictTransform_subset_preimage T.contMDiff_proj.continuous isClosed_closure)
        · exact hdisj _ (List.mem_map_of_mem hp')
      refine ⟨D,TT,E₂,hchainT,hoverT,hadmT,hE₂,hdisjT,?_⟩
      intro m Y b hb
      obtain ⟨C₀,Q₀,g₀,hactual₀,_hrecord,hN,_hg₀,_hlen₀,_hcomm₀,_hcart₀,hcQ₀,hrQ₀,
        _hoverQ₀,hadmQ₀,_hSNCQ₀,hEQ₀,_hprincipalQ₀,_hsuppQ₀,_hstrictA₀,_hstrictB₀,
        _hdisjQ₀,_hholQ₀,_hproperQ₀,_hsurjQ₀,_hisoQ₀⟩ := hSource₀ Y b hb
      obtain ⟨C,Q,g,hactual,hchainQ,hadmQ,_hEQ,hstrictAQ,_hstrictLQ,_hdisjQ,
        _hg,_hlen,_hcomm,_hcart⟩ := hSource C₀ g₀ hactual₀.isSubmersion
      let QQ := Q₀.append Q
      have hfull : IsActualTowerPullback b QQ TT g := hactual₀.append hactual
      let O : Opens X := ⟨Gᶜ,hG.isOpen_compl⟩
      have hav₀ : CentresAvoid O T₀ := centresAvoid_of_centresOver O disjoint_compl_left T₀ hover₀G
      have hav : CentresAvoid O TT := centresAvoid_of_centresOver O disjoint_compl_left TT hoverT
      have hstrict₀ (P : Set X) (hdense : P ⊆ closure (P \ G)) :
          strictTransform m Q₀.proj (b ⁻¹' P) = g₀ ⁻¹' strictTransform n T₀.proj P :=
        IsActualTowerPullback.strictTransform_preimage_of_centresAvoid hb hactual₀ O hav₀ P
          (by change P ⊆ closure (P \ G); exact hdense)
      have hAeq := hstrict₀ A hA.2.2.2.2.2
      have hLeq : (L₁.map (fun p => (g₀ ⁻¹' p.1,p.2+(m-n)))) =
          (L'.map (fun p => (b ⁻¹' p.1,p.2+(m-n)))).map
            (fun p => (strictTransform m Q₀.proj p.1,p.2)) := by
        simp only [L₁,List.map_map]
        apply List.map_congr_left
        intro p hp
        exact Prod.ext (hstrict₀ p.1 (hgood' p hp).2.2.2.2.2).symm rfl
      have hchainQ' : CanonicalSeparationChain
          (geoTransformAlong (sumMarkedIdeal (b ⁻¹' A) (b ⁻¹' B) (E₀.map (b ⁻¹' ·))) Q₀).E
          (strictTransform m Q₀.proj (b ⁻¹' A))
          ((L'.map (fun p => (b ⁻¹' p.1,p.2+(m-n)))).map
            (fun p => (strictTransform m Q₀.proj p.1,p.2))) Q (E₂.map (g ⁻¹' ·)) := by
        rw [hEQ₀,hAeq,← hLeq]
        exact hchainQ
      have hchainFull : CanonicalSeparationChain (E₀.map (b ⁻¹' ·)) (b ⁻¹' A)
          (((B,e)::L').map (fun p => (b ⁻¹' p.1,p.2+(m-n)))) QQ (E₂.map (g ⁻¹' ·)) :=
        .cons Q₀ Q
          (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hb.contMDiff hA.1)
          (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hb.contMDiff hB.1)
          hN hcQ₀ hrQ₀ hchainQ'
      have hadmQ₀G := hadmQ₀.mono (preimage_mono hAB (f := b))
      have hbad := preimage_bad_eq hactual₀ G
      have hadmQ' : IsAdmissibleBlowupSequence m C₀
          (geoTransformAlong (sumMarkedIdeal (b ⁻¹' A) (b ⁻¹' B) (E₀.map (b ⁻¹' ·))) Q₀).E
          (Q₀.proj ⁻¹' (b ⁻¹' G)) C Q.proj (E₂.map (g ⁻¹' ·)) := by
        rw [hEQ₀,← hbad]
        exact hadmQ
      have hstrictFull (P : Set X) (hdense : P ⊆ closure (P \ G)) :
          strictTransform m QQ.proj (b ⁻¹' P) = g ⁻¹' strictTransform n TT.proj P :=
        IsActualTowerPullback.strictTransform_preimage_of_centresAvoid hb hfull O hav P
          (by change P ⊆ closure (P \ G); exact hdense)
      have hstrictA := hstrictFull A hA.2.2.2.2.2
      have hstrictL : ∀ p ∈ (B,e)::L', strictTransform m QQ.proj (b ⁻¹' p.1) =
          g ⁻¹' strictTransform n TT.proj p.1 := fun p hp => hstrictFull p.1 (hgood p hp).2.2.2.2.2
      have hadmFull : IsAdmissibleBlowupSequence m Y (E₀.map (b ⁻¹' ·)) (b ⁻¹' G)
          C QQ.proj (E₂.map (g ⁻¹' ·)) := by
        simpa only [QQ,BlowupTower.proj_append] using IsAdmissibleBlowupSequence.comp hadmQ₀G hadmQ'
      refine ⟨C,QQ,g,hfull,hchainFull,hadmFull,
        isSNCDivisor_preimage_submersion hfull.isSubmersion E₂ hE₂,hstrictA,hstrictL,?_,
        hfull.isSubmersion,hfull.length_eq,hfull.proj_comm,hfull.universal⟩
      intro p hp
      rw [hstrictA,hstrictL p hp]
      exact (hdisjT p hp).preimage g

end

end Hironaka.HironakaOriginalCanonicalPartListResolution
