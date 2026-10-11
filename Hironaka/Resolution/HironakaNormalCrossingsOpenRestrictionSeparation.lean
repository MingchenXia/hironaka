/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaNormalCrossingsSeparationChoiceComparison
import Hironaka.Resolution.HironakaBaseChange
import Hironaka.Blowup.BlowupExistenceCodimOne
import Hironaka.Blowup.BlowupEmptyCentreExact
import Hironaka.Blowup.BlowupTowerRestrictLengthExact

/-! # Actual NC separation on opens with internally omitted empty steps

The genuine global and independent local higher-stratum procedures are compared
by induction on the actual global count bound. A literal empty centre trace
produces a real biholomorphism and leaves the local procedure waiting; a nonempty
trace internally identifies the local attained maximum and produces the actual
single-blowup comparison. No compressed tower, history, termination or naturality
certificate is supplied. Genuine restriction-append tower isomorphisms transport
the recursive comparisons to the literal restriction of the entire global tower.

Only actual empty source blowups are omitted. Universal uniqueness gives the
unique last-stage map. The entire differential original and the full finite
accumulated boundary agree after deleting literal empty entries. Restricted
uncompressed lengths can exceed local procedure lengths. Every local higher
centre is internally nonempty. Default actual choices and the intrinsic dimension
bound give a natural procedure and unique restriction comparison on every open.

Empty opens, empty originals, dimension zero and disconnected/noncompact bases
are included. Count-one Cartier centres are never blown up. These are intrinsic
unordered geometric procedures; old marked colex labels and additional marked
ideal cosupport admissibility remain open. The protected strict statement modules
are absent from imports and the actual proof/type cone.
-/


set_option autoImplicit false

open Set
open scoped Topology Manifold ContDiff

universe u
namespace Hironaka.HironakaNormalCrossingsOpenRestrictionSeparation
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsMultiplicityStrata
  HironakaNormalCrossingsHighestStratumBlowup HironakaNormalCrossingsBoundaryTransform
  HironakaNormalCrossingsBoundarySeparation HironakaNormalCrossingsBiholomorphicMultiplicity
  HironakaNormalCrossingsSeparationChoiceComparison
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism BlowupStrictSubmanifold MarkedIdeals
  MarkedIdeals.MarkedIdeal HironakaStageCenters NormalCrossings RestrictEmptyTower

open Hironaka

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

/-- The actual whole original and finite boundary pull back to their literal open traces. -/
theorem boundaryAdapted_open {A : CMfd.{u} n} (U : TopologicalSpace.Opens A)
    {H : Set A} {E : List (Set A)} (h : IsBoundaryAdaptedCarrier (n := n) H E) :
    IsBoundaryAdaptedCarrier (n := n) ((Subtype.val : U → A) ⁻¹' H)
      (E.map (fun B => (Subtype.val : U → A) ⁻¹' B)) :=
  boundaryAdapted_preimage contMDiff_subtype_val
    (by intro x; rw [HironakaBaseChange.exceptionalLocus_val]; exact notMem_empty x) h

/-- Literal open original branch counts are intrinsically equal at every actual point. -/
theorem branchMultiplicity_open {A : CMfd.{u} n} (U : TopologicalSpace.Opens A)
    {H : Set A} (hH : IsNormalCrossingsCarrier (n := n) H)
    (hp : IsNormalCrossingsCarrier (n := n) ((Subtype.val : U → A) ⁻¹' H)) (x : U) :
    branchMultiplicity hp x = branchMultiplicity hH (x : A) :=
  branchMultiplicity_preimage contMDiff_subtype_val
    (by intro x; rw [HironakaBaseChange.exceptionalLocus_val]; exact notMem_empty x) hH hp x

/-- The entire actual count-r open stratum is the literal original trace. -/
theorem superlevel_branchMultiplicity_open {A : CMfd.{u} n} (U : TopologicalSpace.Opens A)
    {H : Set A} (hH : IsNormalCrossingsCarrier (n := n) H)
    (hp : IsNormalCrossingsCarrier (n := n) ((Subtype.val : U → A) ⁻¹' H)) (r : ℕ) :
    {x | r ≤ branchMultiplicity hp x} = (Subtype.val : U → A) ⁻¹' {y | r ≤ branchMultiplicity hH y} := by
  ext x
  simp only [mem_ofPred_eq,mem_preimage,branchMultiplicity_open U hH hp x]

/-- A real empty-centre projection is internally an actual biholomorphism. -/
theorem exists_empty_blowup_biholomorphism {A B : CMfd.{u} n} {π : B → A}
    (hπ : IsBlowupAlong n (∅ : Set A) π) :
    ∃ χ : B ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ A, ∀ z, χ z = π z := by
  obtain ⟨χ,hcomm,-⟩ := exists_unique_lift (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) A ∞)
    hπ BlowupExistenceCodimOne.isBlowupAlong_id_empty rfl
  exact ⟨χ,hcomm⟩

/-- Remove exactly the literal empty entries of the actual finite boundary. -/
def cleanBoundary {A : Type*} (E : List (Set A)) : List (Set A) :=
  E.filter (fun B => decide B.Nonempty)

@[simp] theorem cleanBoundary_nil {A : Type*} : cleanBoundary ([] : List (Set A)) = [] := rfl

@[simp] theorem cleanBoundary_cons {A : Type*} (B : Set A) (E : List (Set A)) :
    cleanBoundary (B :: E) = if B.Nonempty then B :: cleanBoundary E else cleanBoundary E := by
  by_cases hB : B.Nonempty <;> simp [cleanBoundary,hB]

@[simp] theorem cleanBoundary_append {A : Type*} (E F : List (Set A)) :
    cleanBoundary (E ++ F) = cleanBoundary E ++ cleanBoundary F := by
  exact List.filter_append E F

/-- Actual bijections preserve the cleaned literal preimage list, including repeated empty members. -/
theorem cleanBoundary_map_preimage {A' A : Type*} (χ : A' ≃ A) (E : List (Set A)) :
    cleanBoundary (E.map (fun B => χ ⁻¹' B)) = (cleanBoundary E).map (fun B => χ ⁻¹' B) := by
  induction E with
  | nil => rfl
  | cons B E ih =>
    have hnon : (χ ⁻¹' B).Nonempty ↔ B.Nonempty := by
      constructor
      · rintro ⟨x,hx⟩; exact ⟨χ x,hx⟩
      · rintro ⟨x,hx⟩; exact ⟨χ.symm x,by simpa using hx⟩
    simp only [List.map_cons,cleanBoundary_cons,hnon]
    split <;> simp_all

/-- Geometric maps that send empty to empty can delete actual empty inputs before their literal map. -/
theorem cleanBoundary_map_remove_empty {A B : Type*} (F : Set A → Set B)
    (hF : F ∅ = ∅) (E : List (Set A)) :
    cleanBoundary (E.map F) = cleanBoundary ((cleanBoundary E).map F) := by
  induction E with
  | nil => rfl
  | cons A E ih =>
    by_cases ha : A.Nonempty
    · simp only [List.map_cons,cleanBoundary_cons,if_pos ha]
      rw [ih]
    · have he : A = ∅ := Set.not_nonempty_iff_eq_empty.mp ha
      subst A
      simp [hF,ih]

/-- A genuine recorded comparison omits only actual empty source blowups. -/
inductive IsStageCompression {A' A : CMfd.{u} n}
    (Φ : A' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ A) :
    {D' D : CMfd.{u} n} → BlowupTower A' D' → BlowupTower A D →
      (D' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ D) → Prop
  | refl : IsStageCompression Φ .refl .refl Φ
  | matched {Y' Y Z' Z : CMfd.{u} n} {T' : BlowupTower A' Y'} {T : BlowupTower A Y}
      {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y}
      (h : IsStageCompression Φ T' T χ)
      {C' : Set Y'} {π' : Z' → Y'} (hπ' : IsBlowupAlong n C' π')
      {C : Set Y} {π : Z → Y} (hπ : IsBlowupAlong n C π)
      (χ₁ : Z' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Z)
      (hcomm : ∀ z, π (χ₁ z) = χ (π' z)) (hC : χ ⁻¹' C = C') :
      IsStageCompression Φ (.step T' C' π' hπ') (.step T C π hπ) χ₁
  | silent {Y' Y Z' : CMfd.{u} n} {T' : BlowupTower A' Y'} {T : BlowupTower A Y}
      {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y}
      (h : IsStageCompression Φ T' T χ) {π' : Z' → Y'} (hπ' : IsBlowupAlong n (∅ : Set Y') π')
      (χ₁ : Z' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y)
      (hcomm : ∀ z, χ₁ z = χ (π' z)) :
      IsStageCompression Φ (.step T' ∅ π' hπ') T χ₁

/-- Actual compression squares commute with the entire original projections. -/
theorem IsStageCompression.proj_comm {A' A D' D : CMfd.{u} n}
    {Φ : A' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ A}
    {T' : BlowupTower A' D'} {T : BlowupTower A D}
    {χ : D' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ D}
    (h : IsStageCompression Φ T' T χ) : ∀ z, Φ (T'.proj z) = T.proj (χ z) := by
  induction h with
  | refl => exact fun _ => rfl
  | @matched Y' Y Z' Z T' T χ h C' π' hπ' C π hπ χ₁ hcomm hC ih =>
    intro z
    change Φ (T'.proj (π' z)) = T.proj (π (χ₁ z))
    rw [hcomm]
    exact ih _
  | silent h hπ' χ₁ hcomm ih => intro z; rw [hcomm]; exact ih _

/-- The genuine local procedure length is bounded by the real uncompressed source length. -/
theorem IsStageCompression.length_le {A' A D' D : CMfd.{u} n}
    {Φ : A' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ A}
    {T' : BlowupTower A' D'} {T : BlowupTower A D}
    {χ : D' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ D}
    (h : IsStageCompression Φ T' T χ) : T.length ≤ T'.length := by
  induction h with
  | refl => exact le_rfl
  | matched h hπ' hπ χ₁ hcomm hC ih => exact Nat.add_le_add_right ih 1
  | silent h hπ' χ₁ hcomm ih => exact ih.trans (Nat.le_add_right _ _)

/-- Concatenation uses the real restricted head and smaller tail comparisons. -/
theorem IsStageCompression.append {A' A Y' Y Z' Z : CMfd.{u} n}
    {Φ : A' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ A}
    {T' : BlowupTower A' Y'} {T : BlowupTower A Y}
    {χ₀ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y}
    (h₀ : IsStageCompression Φ T' T χ₀)
    {S' : BlowupTower Y' Z'} {S : BlowupTower Y Z}
    {χ : Z' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Z}
    (h₁ : IsStageCompression χ₀ S' S χ) :
    IsStageCompression Φ (T'.append S') (T.append S) χ := by
  induction h₁ with
  | refl => exact h₀
  | matched h hπ' hπ χ₁ hcomm hC ih => exact IsStageCompression.matched ih hπ' hπ χ₁ hcomm hC
  | silent h hπ' χ₁ hcomm ih => exact IsStageCompression.silent ih hπ' χ₁ hcomm

/-- Genuine compression transports the whole differential original, including all silent stages. -/
theorem IsStageCompression.strict_original_eq {A' A D' D : CMfd.{u} n}
    {Φ : A' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ A}
    {T' : BlowupTower A' D'} {T : BlowupTower A D}
    {χ : D' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ D}
    (hi : IsStageCompression Φ T' T χ) {H : Set A} (hH : IsClosed H) :
    strictTransform n T'.proj (Φ ⁻¹' H) = χ ⁻¹' strictTransform n T.proj H :=
  strictTransform_preimage_of_square Φ χ T'.contMDiff_proj T.contMDiff_proj H hH
    (fun z => (hi.proj_comm z).symm)

/-- Every actual geometric accumulated boundary is closed, without ideal coherence or marked admissibility. -/
theorem isClosed_boundary_geoTransformAlong {A D : CMfd.{u} n}
    (M : MarkedIdeal n A) (hE : ∀ B ∈ M.E, IsClosed B) (T : BlowupTower A D) :
    ∀ B ∈ (geoTransformAlong M T).E, IsClosed B := by
  cases T with
  | refl => exact hE
  | step T C π hπ =>
    intro B hB
    change B ∈ (geoTransformAlong M T).E.map (geoStrictTransform π C) ++ [π ⁻¹' C] at hB
    rcases List.mem_append.mp hB with hB | hB
    · obtain ⟨B,hmem,rfl⟩ := List.mem_map.mp hB
      exact isClosed_closure
    · rw [List.mem_singleton.mp hB]
      exact hπ.1.1.preimage hπ.contMDiff.continuous

/-- Equality of actual cleaned input lists gives equality after any genuine empty-preserving geometric map. -/
theorem cleanBoundary_map_congr {A B : Type*} (F : Set A → Set B) (hF : F ∅ = ∅)
    {E E' : List (Set A)} (hE : cleanBoundary E = cleanBoundary E') :
    cleanBoundary (E.map F) = cleanBoundary (E'.map F) := by
  rw [cleanBoundary_map_remove_empty F hF E,cleanBoundary_map_remove_empty F hF E',hE]

/-- The actual source tower isomorphism transports every genuine retained or empty step. -/
theorem IsStageCompression.source_iso {A'' A' A : CMfd.{u} n}
    {Ψ : A'' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ A'}
    {Φ : A' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ A}
    {D'' D' D : CMfd.{u} n} {T'' : BlowupTower A'' D''} {T' : BlowupTower A' D'} {T : BlowupTower A D}
    {θ : D'' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ D'}
    {χ : D' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ D}
    (hc : IsStageCompression Φ T' T χ) (hi : IsTowerIso Ψ T'' T' θ) :
    IsStageCompression (Ψ.trans Φ) T'' T (θ.trans χ) := by
  induction hc generalizing D'' with
  | refl =>
    cases T'' with
    | refl => obtain rfl := hi.refl_inv; exact IsStageCompression.refl
    | step T'' C'' π'' hπ'' => exact absurd hi.length_eq (by simp)
  | @matched Y' Y Z' Z T' T χ hc C' π' hπ' C π hπ χ₁ hcomm hC ih =>
    cases T'' with
    | refl => exact absurd hi.length_eq (by simp)
    | step T'' C'' π'' hπ'' =>
      obtain ⟨θ₀,hi₀,hcomm₀,hC₀⟩ := hi.step_inv
      refine IsStageCompression.matched (ih hi₀) hπ'' hπ (θ.trans χ₁) (fun z => ?_) ?_
      · simp only [Diffeomorph.coe_trans,Function.comp_apply]
        rw [hcomm,hcomm₀]
      · rw [Diffeomorph.coe_trans,preimage_comp,hC,hC₀]
  | @silent Y' Y Z' T' T χ hc π' hπ' χ₁ hcomm ih =>
    cases T'' with
    | refl => exact absurd hi.length_eq (by simp)
    | step T'' C'' π'' hπ'' =>
      obtain ⟨θ₀,hi₀,hcomm₀,hC₀⟩ := hi.step_inv
      have he : C'' = ∅ := by rw [← hC₀]; exact preimage_empty
      subst C''
      refine IsStageCompression.silent (ih hi₀) hπ'' (θ.trans χ₁) (fun z => ?_)
      simp only [Diffeomorph.coe_trans,Function.comp_apply]
      rw [hcomm,hcomm₀]

/-- Actual compression carries the cleaned whole accumulated boundary, using only the original closed-set dictionary. -/
theorem IsStageCompression.cleaned_boundary_eq {A' A D' D : CMfd.{u} n}
    {Φ : A' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ A}
    {T' : BlowupTower A' D'} {T : BlowupTower A D}
    {χ : D' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ D}
    (hi : IsStageCompression Φ T' T χ) (M' : MarkedIdeal n A') (M : MarkedIdeal n A)
    (hclosed : ∀ B ∈ M'.E, IsClosed B)
    (hE : cleanBoundary M'.E = cleanBoundary (M.E.map (fun B => Φ ⁻¹' B))) :
    cleanBoundary (geoTransformAlong M' T').E =
      cleanBoundary ((geoTransformAlong M T).E.map (fun B => χ ⁻¹' B)) := by
  induction hi with
  | refl => exact hE
  | @matched Y' Y Z' Z T' T χ hi C' π' hπ' C π hπ χ₁ hcomm hC ih =>
    simp only [geoTransformAlong_step,geoTransform_E,List.map_append,List.map_singleton,cleanBoundary_append]
    apply congrArg₂ (fun E F => E ++ F)
    · calc
        cleanBoundary ((geoTransformAlong M' T').E.map (geoStrictTransform π' C')) =
            cleanBoundary (((geoTransformAlong M T).E.map (fun B => χ ⁻¹' B)).map (geoStrictTransform π' C')) :=
          cleanBoundary_map_congr (geoStrictTransform π' C') (by simp [geoStrictTransform]) ih
        _ = cleanBoundary (((geoTransformAlong M T).E.map (geoStrictTransform π C)).map (fun B => χ₁ ⁻¹' B)) := by
          apply congrArg cleanBoundary
          simp only [List.map_map]
          apply List.map_congr_left
          intro B hB
          rw [← hC]
          exact geoStrictTransform_preimage_of_square χ χ₁ π' π C B hcomm
    · have hEx : π' ⁻¹' C' = χ₁ ⁻¹' (π ⁻¹' C) := by
        rw [← hC]
        ext z
        exact Iff.of_eq (congrArg (fun y => y ∈ C) (hcomm z).symm)
      exact congrArg (fun B => cleanBoundary [B]) hEx
  | @silent Y' Y Z' T' T χ hi π' hπ' χ₁ hcomm ih =>
    change cleanBoundary ((geoTransformAlong M' T').E.map (geoStrictTransform π' ∅) ++ [π' ⁻¹' ∅]) = _
    simp only [preimage_empty,cleanBoundary_append,cleanBoundary_cons,Set.not_nonempty_empty,
      if_false,cleanBoundary_nil,List.append_nil]
    have hMap : (geoTransformAlong M' T').E.map (geoStrictTransform π' ∅) =
        (geoTransformAlong M' T').E.map (fun B => π' ⁻¹' B) := by
      apply List.map_congr_left
      intro B hB
      unfold geoStrictTransform
      rw [sdiff_empty]
      exact (isClosed_boundary_geoTransformAlong M' hclosed T' B hB).preimage
        hπ'.contMDiff.continuous |>.closure_eq
    rw [hMap]
    calc
      cleanBoundary ((geoTransformAlong M' T').E.map (fun B => π' ⁻¹' B)) =
          cleanBoundary (((geoTransformAlong M T).E.map (fun B => χ ⁻¹' B)).map (fun B => π' ⁻¹' B)) :=
        cleanBoundary_map_congr (fun B => π' ⁻¹' B) preimage_empty ih
      _ = cleanBoundary ((geoTransformAlong M T).E.map (fun B => χ₁ ⁻¹' B)) := by
        apply congrArg cleanBoundary
        rw [List.map_map]
        apply List.map_congr_left
        intro B hB
        ext z
        exact Iff.of_eq (congrArg (fun y => y ∈ B) (hcomm z).symm)

/-- The real local-base embedding internally transports the whole original and finite pair. -/
theorem boundaryAdapted_open_embedding {A' A : CMfd.{u} n} {ι : A' → A}
    (hι : HironakaBaseChange.IsOpenHoloEmbedding n ι)
    {H : Set A} {E : List (Set A)} (h : IsBoundaryAdaptedCarrier (n := n) H E) :
    IsBoundaryAdaptedCarrier (n := n) (ι ⁻¹' H) (E.map (fun B => ι ⁻¹' B)) :=
  boundaryAdapted_preimage hι.contMDiff hι.notMem_exceptionalLocus h

/-- Every actual open-base original count is intrinsic, with no supplied count identity. -/
theorem branchMultiplicity_open_embedding {A' A : CMfd.{u} n} {ι : A' → A}
    (hι : HironakaBaseChange.IsOpenHoloEmbedding n ι) {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) (hp : IsNormalCrossingsCarrier (n := n) (ι ⁻¹' H)) (x : A') :
    branchMultiplicity hp x = branchMultiplicity hH (ι x) :=
  branchMultiplicity_preimage hι.contMDiff hι.notMem_exceptionalLocus hH hp x

/-- A genuine empty highest trace internally gives the strict local original count drop. -/
theorem count_le_pred_of_empty_highest_trace {A' A : CMfd.{u} n} {ι : A' → A}
    (hι : HironakaBaseChange.IsOpenHoloEmbedding n ι) {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) (hp : IsNormalCrossingsCarrier (n := n) (ι ⁻¹' H)) {r : ℕ}
    (hempty : ι ⁻¹' {x | r ≤ branchMultiplicity hH x} = ∅) :
    ∀ x : A', branchMultiplicity hp x ≤ r-1 := by
  intro x
  have hn : ¬ r ≤ branchMultiplicity hp x := by
    intro hr
    rw [branchMultiplicity_open_embedding hι hH hp] at hr
    have hx : x ∈ ι ⁻¹' {x | r ≤ branchMultiplicity hH x} := hr
    rw [hempty] at hx
    exact hx
  omega

/-- A real nonempty whole highest trace identifies the independently attained local maximum. -/
theorem attained_local_maximum_eq_of_nonempty_highest_trace {A' A : CMfd.{u} n} {ι : A' → A}
    (hι : HironakaBaseChange.IsOpenHoloEmbedding n ι) {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) (hp : IsNormalCrossingsCarrier (n := n) (ι ⁻¹' H)) {r s : ℕ}
    (hmax : ∀ x : A, branchMultiplicity hH x ≤ r)
    (hne : (ι ⁻¹' {x | r ≤ branchMultiplicity hH x}).Nonempty)
    (hlocal : ∀ x : A', branchMultiplicity hp x ≤ s)
    (hatt : {x | branchMultiplicity hp x = s}.Nonempty) : s = r := by
  apply attained_maximum_eq hp hlocal hatt
  · intro x
    rw [branchMultiplicity_open_embedding hι hH hp]
    exact hmax (ι x)
  · obtain ⟨x,hx⟩ := hne
    refine ⟨x,?_⟩
    change branchMultiplicity hp x = r
    rw [branchMultiplicity_open_embedding hι hH hp]
    exact (hmax (ι x)).antisymm hx

/-- The actual recorded tower projection of the internally recursive procedure. -/
def procedureTower (β : HigherBlowupChoices.{u} n) (b : ℕ)
    {A : CMfd.{u} n} (M : MarkedIdeal n A) {H : Set A}
    (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (hb : ∀ x : A, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ b) :
    Σ D : CMfd.{u} n, BlowupTower A D :=
  ⟨(separateWith β b M h hb).D,(separateWith β b M h hb).T⟩

private theorem procedureTower_zero (β : HigherBlowupChoices.{u} n)
    {A : CMfd.{u} n} (M : MarkedIdeal n A) {H : Set A}
    (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (hb : ∀ x : A, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ 0) :
    procedureTower β 0 M h hb = ⟨A,.refl⟩ := rfl

private theorem procedureTower_stop (β : HigherBlowupChoices.{u} n) (b : ℕ)
    {A : CMfd.{u} n} (M : MarkedIdeal n A) {H : Set A}
    (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (hb : ∀ x : A, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ b)
    (hone : ∀ x : A, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ 1) :
    procedureTower β b M h hb = ⟨A,.refl⟩ := by
  cases b with
  | zero => rfl
  | succ b => unfold procedureTower; rw [separateWith.eq_2,dif_pos hone]; rfl

private theorem procedureTower_step (β : HigherBlowupChoices.{u} n) (b : ℕ)
    {A : CMfd.{u} n} (M : MarkedIdeal n A) {H : Set A}
    (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (hb : ∀ x : A, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ b+1)
    (hnot : ¬ ∀ x : A, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ 1) :
    procedureTower β (b+1) M h hb =
      let s := higherStep β h hb hnot
      let T₀ : BlowupTower A s.D := .step .refl _ s.π s.hπ
      let tail := procedureTower β b (geoTransformAlong M T₀) s.hp
        (fun z => (s.hcount z).trans (by have := s.hrb; omega))
      ⟨tail.1,T₀.append tail.2⟩ := by
  unfold procedureTower
  rw [separateWith.eq_2,dif_neg hnot]
  rfl

/-- The whole differential original of a literal restricted tower is its actual open trace. -/
theorem strictTransform_restricted_tower {A D : CMfd.{u} n}
    (U : TopologicalSpace.Opens A) (T : BlowupTower A D) (H : Set A) :
    strictTransform n (restrict U T).proj ((Subtype.val : U → A) ⁻¹' H) =
      (Subtype.val : openPreimage T U → D) ⁻¹' strictTransform n T.proj H :=
  HironakaBaseChange.strictTransform_preimage_eq T.contMDiff_proj (restrict U T).contMDiff_proj
    (HironakaBaseChange.isOpenHoloEmbedding_val U)
    (HironakaBaseChange.isOpenHoloEmbedding_val (openPreimage T U))
    (fun z => (proj_restrict U T z).symm) H

/-- Two actual open-square readers give the whole differential strict dictionary. -/
theorem strictTransform_open_square {A' A B' B : CMfd.{u} n}
    (U : TopologicalSpace.Opens A) (V : TopologicalSpace.Opens B)
    (Φ : A' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) U)
    (χ : B' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) V)
    {π : B → A} {π' : B' → A'}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    (hπ' : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π')
    (hcomm : ∀ z, π (χ z : B) = (Φ (π' z) : A)) (H : Set A) :
    strictTransform n π' ((fun x : A' => (Φ x : A)) ⁻¹' H) =
      (fun z : B' => (χ z : B)) ⁻¹' strictTransform n π H :=
  HironakaBaseChange.strictTransform_preimage_eq hπ hπ'
    ⟨U,Φ,fun _ => rfl⟩ ⟨V,χ,fun _ => rfl⟩ hcomm H

/-- Actual procedure comparison on an arbitrary open; only genuinely empty global traces are omitted. -/
theorem procedureTower_open_comparison (β α : HigherBlowupChoices.{u} n) (b b' : ℕ)
    {A A' : CMfd.{u} n} (U : TopologicalSpace.Opens A)
    (Φ : A' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) U)
    (M : MarkedIdeal n A) (M' : MarkedIdeal n A') {H : Set A} {H' : Set A'}
    (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (h' : IsBoundaryAdaptedCarrier (n := n) H' M'.E)
    (hH : H' = (fun x : A' => (Φ x : A)) ⁻¹' H)
    (hb : ∀ x : A, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ b)
    (hb' : ∀ x : A', branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h') x ≤ b') :
    ∃ χ : CMfd.of (n := n) (openPreimage (procedureTower β b M h hb).2 U)
        ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ (procedureTower α b' M' h' hb').1,
      IsStageCompression Φ.symm (restrict U (procedureTower β b M h hb).2)
        (procedureTower α b' M' h' hb').2 χ := by
  induction b generalizing A A' b' with
  | zero =>
    subst H'
    have hι : HironakaBaseChange.IsOpenHoloEmbedding n (fun x : A' => (Φ x : A)) := ⟨U,Φ,fun _ => rfl⟩
    have hone' : ∀ x : A', branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h') x ≤ 1 := by
      intro x
      rw [branchMultiplicity_open_embedding hι (isNormalCrossingsCarrier_of_boundaryAdapted h)
        (isNormalCrossingsCarrier_of_boundaryAdapted h')]
      exact (hb _).trans (by omega)
    rw [procedureTower_zero,procedureTower_stop α b' M' h' hb' hone']
    exact ⟨Φ.symm,IsStageCompression.refl⟩
  | succ b ih =>
    subst H'
    have hι : HironakaBaseChange.IsOpenHoloEmbedding n (fun x : A' => (Φ x : A)) := ⟨U,Φ,fun _ => rfl⟩
    by_cases hone : ∀ x : A, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ 1
    · have hone' : ∀ x : A', branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h') x ≤ 1 := by
        intro x
        rw [branchMultiplicity_open_embedding hι (isNormalCrossingsCarrier_of_boundaryAdapted h)
          (isNormalCrossingsCarrier_of_boundaryAdapted h')]
        exact hone _
      rw [procedureTower_stop β (b+1) M h hb hone,procedureTower_stop α b' M' h' hb' hone']
      exact ⟨Φ.symm,IsStageCompression.refl⟩
    · let s := higherStep β h hb hone
      let C : Set A := {x | s.r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}
      let T₀ : BlowupTower A s.D := .step .refl C s.π s.hπ
      let V := openPreimage T₀ U
      let πU : CMfd.of (n := n) V → CMfd.of (n := n) U := fun z => ⟨s.π z.1,z.2⟩
      have hπU : IsBlowupAlong n ((Subtype.val : U → A) ⁻¹' C) πU :=
        BlowupRestrictOpen.isBlowupAlong_restrict s.hπ U V.isOpen
      let N := geoTransformAlong M T₀
      have hbt : ∀ z : s.D, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted s.hp) z ≤ b :=
        fun z => (s.hcount z).trans (by have := s.hrb; omega)
      let G := procedureTower β b N s.hp hbt
      by_cases hempty : (Subtype.val : U → A) ⁻¹' C = ∅
      · have hπempty : IsBlowupAlong n (∅ : Set (CMfd.of (n := n) U)) πU := by
          simpa only [hempty] using hπU
        obtain ⟨ε,hε⟩ := exists_empty_blowup_biholomorphism hπempty
        let η := ε.trans Φ.symm
        have hcomm : ∀ z : A', s.π (η.symm z : s.D) = (Φ z : A) := by
          intro z
          have he : πU (η.symm z) = Φ z := by
            rw [← hε]
            change ε (ε.symm (Φ z)) = Φ z
            exact ε.apply_symm_apply _
          exact congrArg Subtype.val he
        have hHt : (fun x : A' => (Φ x : A)) ⁻¹' H =
            (fun z : A' => (η.symm z : s.D)) ⁻¹' strictTransform n s.π H := by
          have hh := strictTransform_open_square U V Φ η.symm s.hπ.contMDiff contMDiff_id hcomm H
          simpa only [strictTransform,exceptionalLocus_id,sdiff_empty,
            preimage_id,h'.1.closure_eq] using hh
        obtain ⟨χ,hχ⟩ := ih b' V η.symm N M' s.hp h' hHt hbt hb'
        have hhead : IsStageCompression Φ.symm (restrict U T₀) .refl η := by
          have he : restrict U T₀ = .step .refl ∅ πU hπempty := by
            change (BlowupTower.step (.refl : BlowupTower (CMfd.of (n := n) U) _) ((Subtype.val : U → A) ⁻¹' C) πU hπU) = _
            congr 1
          rw [he]
          exact IsStageCompression.silent IsStageCompression.refl hπempty η (fun z => by
            change Φ.symm (ε z) = Φ.symm (πU z)
            rw [hε])
        have hcat := hhead.append hχ
        have hfull := hcat.source_iso (BlowupTowerIsoTail.isTowerIso_restrict_append U T₀ G.2)
        rw [procedureTower_step β b M h hb hone]
        refine ⟨(BlowupTowerIsoTail.opensCongr (BlowupTowerIsoTail.openPreimage_append T₀ G.2 U).symm).trans χ,?_⟩
        simpa only [Diffeomorph.refl_trans,BlowupTower.refl_append] using hfull
      · have hne : ((Subtype.val : U → A) ⁻¹' C).Nonempty := Set.nonempty_iff_ne_empty.mpr hempty
        have hlocal : ¬ ∀ x : A', branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h') x ≤ 1 := by
          intro hs
          obtain ⟨x,hx⟩ := hne
          have hc := hs (Φ.symm x)
          rw [branchMultiplicity_open_embedding hι (isNormalCrossingsCarrier_of_boundaryAdapted h)
            (isNormalCrossingsCarrier_of_boundaryAdapted h'),Φ.apply_symm_apply] at hc
          have := s.hr
          change s.r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) (x : A) at hx
          omega
        cases b' with
        | zero => exact False.elim (hlocal (fun x => (hb' x).trans (by omega)))
        | succ b' =>
          let s' := higherStep α h' hb' hlocal
          have hne' : ((fun x : A' => (Φ x : A)) ⁻¹' C).Nonempty := by
            obtain ⟨x,hx⟩ := hne
            exact ⟨Φ.symm x,by simpa using hx⟩
          have hrs : s'.r = s.r := attained_local_maximum_eq_of_nonempty_highest_trace hι
            (isNormalCrossingsCarrier_of_boundaryAdapted h)
            (isNormalCrossingsCarrier_of_boundaryAdapted h') s.hmax hne' s'.hmax s'.hatt
          let C' : Set A' := {x | s'.r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h') x}
          have hC : Φ.symm ⁻¹' C' = (Subtype.val : U → A) ⁻¹' C := by
            ext x
            change (s'.r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h') (Φ.symm x)) ↔
              s.r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) (x : A)
            rw [hrs,branchMultiplicity_open_embedding hι (isNormalCrossingsCarrier_of_boundaryAdapted h)
              (isNormalCrossingsCarrier_of_boundaryAdapted h'),Φ.apply_symm_apply]
          obtain ⟨η,hη,-⟩ := exists_unique_lift Φ.symm hπU s'.hπ hC
          let T₀' : BlowupTower A' s'.D := .step .refl C' s'.π s'.hπ
          let N' := geoTransformAlong M' T₀'
          have hcomm : ∀ z : s'.D, s.π (η.symm z : s.D) = (Φ (s'.π z) : A) := by
            intro z
            have he := hη (η.symm z)
            rw [η.apply_symm_apply] at he
            have he' := congrArg Φ he
            rw [Φ.apply_symm_apply] at he'
            exact congrArg Subtype.val he'.symm
          have hHt : strictTransform n s'.π ((fun x : A' => (Φ x : A)) ⁻¹' H) =
              (fun z : s'.D => (η.symm z : s.D)) ⁻¹' strictTransform n s.π H :=
            strictTransform_open_square U V Φ η.symm s.hπ.contMDiff s'.hπ.contMDiff hcomm H
          have hbt' : ∀ z : s'.D, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted s'.hp) z ≤ b' :=
            fun z => (s'.hcount z).trans (by have := s'.hrb; omega)
          let L := procedureTower α b' N' s'.hp hbt'
          obtain ⟨χ,hχ⟩ := ih b' V η.symm N N' s.hp s'.hp hHt hbt hbt'
          have hhead : IsStageCompression Φ.symm (restrict U T₀) T₀' η :=
            IsStageCompression.matched IsStageCompression.refl hπU s'.hπ η hη hC
          have hcat := hhead.append hχ
          have hfull := hcat.source_iso (BlowupTowerIsoTail.isTowerIso_restrict_append U T₀ G.2)
          rw [procedureTower_step β b M h hb hone,procedureTower_step α b' M' h' hb' hlocal]
          refine ⟨(BlowupTowerIsoTail.opensCongr (BlowupTowerIsoTail.openPreimage_append T₀ G.2 U).symm).trans χ,?_⟩
          simpa only [Diffeomorph.refl_trans] using hfull

/-- An actual compression to a tower with nonempty centres has a uniquely determined last map. -/
theorem IsStageCompression.unique_last {A' A D' D : CMfd.{u} n}
    {Φ : A' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ A}
    {T' : BlowupTower A' D'} {T : BlowupTower A D}
    {χ ψ : D' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ D}
    (hi : IsStageCompression Φ T' T χ) (hj : IsStageCompression Φ T' T ψ)
    (hne : StageCentres (fun _ C => C.Nonempty) T) : χ = ψ := by
  induction hi with
  | refl => cases hj; rfl
  | @matched Y' Y Z' Z T' T χ hi C' π' hπ' C π hπ χ₁ hcomm hC ih =>
    cases hj with
    | matched hj hπ' hπ ψ₁ hcommψ hCψ =>
      have he := ih hj hne.1
      subst he
      exact Diffeomorph.ext (congrFun (lift_eq_of_commuting χ hπ' hπ hC
        χ₁.contMDiff ψ.contMDiff hcomm hcommψ))
    | silent hj hπ' ψ₁ hcommψ =>
      obtain ⟨y,hy⟩ := hne.2
      have hx : χ.symm y ∈ χ ⁻¹' C := by simpa using hy
      rw [hC] at hx
      exact False.elim hx
  | @silent Y' Y Z' T' T χ hi π' hπ' χ₁ hcomm ih =>
    cases hj with
    | @matched _ _ _ _ _ _ ζ hj _ _ hπ' _ _ hπ _ hcommψ hCψ =>
      obtain ⟨y,hy⟩ := hne.2
      have hx : (ζ ⁻¹' _).Nonempty := ⟨ζ.symm y,by simpa using hy⟩
      rw [hCψ] at hx
      exact False.elim (Set.not_nonempty_empty hx)
    | silent hj hπ' ψ₁ hcommψ =>
      have he := ih hj hne
      subst he
      exact Diffeomorph.ext (fun z => (hcomm z).trans (hcommψ z).symm)

/-- Every retained centre in an independently generated local procedure is genuinely nonempty. -/
theorem separateWith_nonempty_centres (α : HigherBlowupChoices.{u} n) (b : ℕ)
    {A : CMfd.{u} n} (M : MarkedIdeal n A) {H : Set A}
    (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (hb : ∀ x : A, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ b) :
    StageCentres (fun _ C => C.Nonempty) (separateWith α b M h hb).T := by
  have hc := (separateWith α b M h hb).centres
  have hh : ∀ {D : CMfd.{u} n} (T : BlowupTower A D),
      StageCentres (fun R C => IsHigherSeparationCentre (n := n)
        (strictTransform n R.proj H) (geoTransformAlong M R).E C) T →
      StageCentres (fun _ C => C.Nonempty) T := by
    intro D T hT
    induction T with
    | refl => trivial
    | step T C π hπ ih =>
      refine ⟨ih hT.1,?_⟩
      obtain ⟨hp,r,hr,hm,he,hne⟩ := hT.2
      exact hne
  exact hh _ hc

/-- The complete literal accumulated geometric boundary commutes with open restriction without any ideal assumptions. -/
theorem boundary_geoTransformAlong_restrict {A D : CMfd.{u} n}
    (U : TopologicalSpace.Opens A) (M : MarkedIdeal n A) (T : BlowupTower A D) :
    (geoTransformAlong (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U → A) M)
      (restrict U T)).E = (geoTransformAlong M T).E.map
        (fun B => (Subtype.val : openPreimage T U → D) ⁻¹' B) := by
  induction T with
  | refl => rfl
  | @step D Z T C π hπ ih =>
    change (geoTransformAlong (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U → A) M)
        (restrict U T)).E.map (geoStrictTransform
          (fun z : openPreimage (.step T C π hπ) U => (⟨π z.1,z.2⟩ : openPreimage T U))
          ((Subtype.val : openPreimage T U → D) ⁻¹' C)) ++ [_] =
        ((geoTransformAlong M T).E.map (geoStrictTransform π C) ++ [π ⁻¹' C]).map _
    rw [ih,List.map_append,List.map_singleton]
    apply congrArg₂ (fun E F => E ++ F)
    · simp only [List.map_map]
      apply List.map_congr_left
      intro B hB
      exact MarkedIdealRestrictOpen.geoStrictTransform_restrict (openPreimage T U)
        ((openPreimage T U).isOpen.preimage hπ.contMDiff.continuous) B
    · rfl

/-- The internally compared real procedures have a unique actual last-stage map. -/
theorem separateWith_open_unique_comparison (β α : HigherBlowupChoices.{u} n) (b b' : ℕ)
    {A A' : CMfd.{u} n} (U : TopologicalSpace.Opens A)
    (Φ : A' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) U)
    (M : MarkedIdeal n A) (M' : MarkedIdeal n A') {H : Set A} {H' : Set A'}
    (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (h' : IsBoundaryAdaptedCarrier (n := n) H' M'.E)
    (hH : H' = (fun x : A' => (Φ x : A)) ⁻¹' H)
    (hb : ∀ x : A, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ b)
    (hb' : ∀ x : A', branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h') x ≤ b') :
    ∃! χ : CMfd.of (n := n) (openPreimage (separateWith β b M h hb).T U)
        ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ (separateWith α b' M' h' hb').D,
      IsStageCompression Φ.symm (restrict U (separateWith β b M h hb).T)
        (separateWith α b' M' h' hb').T χ := by
  obtain ⟨χ,hχ⟩ := procedureTower_open_comparison β α b b' U Φ M M' h h' hH hb hb'
  refine ⟨χ,hχ,fun ψ hψ => ?_⟩
  exact hψ.unique_last hχ (separateWith_nonempty_centres α b' M' h' hb')

/-- Actual initial whole trace dictionaries give the entire final differential original and cleaned accumulated boundary. -/
theorem separateWith_open_whole_dictionary (β α : HigherBlowupChoices.{u} n) (b b' : ℕ)
    {A A' : CMfd.{u} n} (U : TopologicalSpace.Opens A)
    (Φ : A' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) U)
    (M : MarkedIdeal n A) (M' : MarkedIdeal n A') {H : Set A} {H' : Set A'}
    (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (h' : IsBoundaryAdaptedCarrier (n := n) H' M'.E)
    (hH : H' = (fun x : A' => (Φ x : A)) ⁻¹' H)
    (hE : cleanBoundary (M.E.map (fun B => (Subtype.val : U → A) ⁻¹' B)) =
      cleanBoundary (M'.E.map (fun B => Φ.symm ⁻¹' B)))
    (hb : ∀ x : A, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ b)
    (hb' : ∀ x : A', branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h') x ≤ b') :
    ∃ χ : CMfd.of (n := n) (openPreimage (separateWith β b M h hb).T U)
        ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ (separateWith α b' M' h' hb').D,
      IsStageCompression Φ.symm (restrict U (separateWith β b M h hb).T)
        (separateWith α b' M' h' hb').T χ ∧
      (∀ z, Φ.symm ⟨(separateWith β b M h hb).T.proj z.1,z.2⟩ =
        (separateWith α b' M' h' hb').T.proj (χ z)) ∧
      (Subtype.val : openPreimage (separateWith β b M h hb).T U → (separateWith β b M h hb).D) ⁻¹'
          strictTransform n (separateWith β b M h hb).T.proj H =
        χ ⁻¹' strictTransform n (separateWith α b' M' h' hb').T.proj H' ∧
      cleanBoundary ((geoTransformAlong M (separateWith β b M h hb).T).E.map
        (fun B => (Subtype.val : openPreimage (separateWith β b M h hb).T U → (separateWith β b M h hb).D) ⁻¹' B)) =
        cleanBoundary ((geoTransformAlong M' (separateWith α b' M' h' hb').T).E.map (fun B => χ ⁻¹' B)) ∧
      (separateWith α b' M' h' hb').T.length ≤ (separateWith β b M h hb).T.length := by
  obtain ⟨χ,hχ,-⟩ := separateWith_open_unique_comparison β α b b' U Φ M M' h h' hH hb hb'
  refine ⟨χ,hχ,?_,?_,?_,?_⟩
  · intro z
    have hc := hχ.proj_comm z
    have hp := proj_restrict U (separateWith β b M h hb).T z
    have he : (restrict U (separateWith β b M h hb).T).proj z =
        (⟨(separateWith β b M h hb).T.proj z.1,z.2⟩ : U) := Subtype.ext hp
    rwa [he] at hc
  · have hH₀ : (Subtype.val : U → A) ⁻¹' H = Φ.symm ⁻¹' H' := by
      rw [hH]
      ext z
      simp only [mem_preimage,Φ.apply_symm_apply]
    rw [← strictTransform_restricted_tower U (separateWith β b M h hb).T H,hH₀]
    exact hχ.strict_original_eq h'.1
  · let MU := MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U → A) M
    have hclosed : ∀ B ∈ MU.E, IsClosed B := (boundaryAdapted_open U h).2.1
    have hc := hχ.cleaned_boundary_eq MU M' hclosed hE
    rwa [boundary_geoTransformAlong_restrict] at hc
  · have hc := hχ.length_le
    rwa [length_restrict] at hc

/-- An actual empty-centre blowup carries every whole closed original and all closed old boundary by its true projection. -/
theorem empty_blowup_whole_closed_dictionary {A B : CMfd.{u} n} {π : B → A}
    (hπ : IsBlowupAlong n (∅ : Set A) π) {H : Set A} (hH : IsClosed H)
    (E : List (Set A)) (hE : ∀ F ∈ E, IsClosed F) :
    (∃ ε : B ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ A, ∀ z, ε z = π z) ∧
      strictTransform n π H = π ⁻¹' H ∧
      E.map (geoStrictTransform π ∅) = E.map (fun F => π ⁻¹' F) ∧ π ⁻¹' (∅ : Set A) = ∅ := by
  obtain ⟨ε,hε⟩ := exists_empty_blowup_biholomorphism hπ
  refine ⟨⟨ε,hε⟩,?_,?_,preimage_empty⟩
  · have he : (ε : B → A) = π := funext hε
    rw [← he]
    have hn : exceptionalLocus n ε = ∅ := by
      ext z
      simp only [mem_empty_iff_false,iff_false]
      exact MarkedIdealBiholomorphism.notMem_exceptionalLocus_of_inverse
        ε.contMDiff ε.symm.contMDiff ε.apply_symm_apply ε.symm_apply_apply z
    simp only [strictTransform,hn,sdiff_empty,
      (hH.preimage ε.contMDiff.continuous).closure_eq]
  · apply List.map_congr_left
    intro F hF
    simp only [geoStrictTransform,sdiff_empty,(hE F hF).preimage hπ.contMDiff.continuous |>.closure_eq]

/-- The actual local natural procedure is internally generated on the literal open pair. -/
def restrictedNaturalSeparation {A : CMfd.{u} n} (U : TopologicalSpace.Opens A)
    (M : MarkedIdeal n A) {H : Set A} (h : IsBoundaryAdaptedCarrier (n := n) H M.E) :
    SeparationOutput (A := CMfd.of (n := n) U) (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U → A) M)
      ((Subtype.val : U → A) ⁻¹' H) n :=
  naturalSeparation (A := CMfd.of (n := n) U) (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U → A) M)
    (boundaryAdapted_open U h)

/-- Genuine default choices and the internal dimension bound give a unique comparison on every actual open set. -/
theorem naturalSeparation_open_unique_comparison {A : CMfd.{u} n}
    (U : TopologicalSpace.Opens A) (M : MarkedIdeal n A) {H : Set A}
    (h : IsBoundaryAdaptedCarrier (n := n) H M.E) :
    ∃! χ : CMfd.of (n := n) (openPreimage (naturalSeparation M h).T U)
        ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ (restrictedNaturalSeparation U M h).D,
      IsStageCompression (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞)
        (restrict U (naturalSeparation M h).T) (restrictedNaturalSeparation U M h).T χ :=
  separateWith_open_unique_comparison defaultHigherBlowupChoices defaultHigherBlowupChoices n n U
    (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞) M
    (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U → A) M) h
    (boundaryAdapted_open U h) rfl
    (fun x => branchMultiplicity_le (isNormalCrossingsCarrier_of_boundaryAdapted h) x)
    (fun x => branchMultiplicity_le (isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_open U h)) x)

/-- The whole actual natural final original and cleaned finite boundary are natural on every open, with no supplied procedure or certificates. -/
theorem naturalSeparation_open_whole_dictionary {A : CMfd.{u} n}
    (U : TopologicalSpace.Opens A) (M : MarkedIdeal n A) {H : Set A}
    (h : IsBoundaryAdaptedCarrier (n := n) H M.E) :
    let o := naturalSeparation M h
    let oU := restrictedNaturalSeparation U M h
    let MU := MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U → A) M
    ∃ χ : CMfd.of (n := n) (openPreimage o.T U)
        ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ oU.D,
      IsStageCompression (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞)
        (restrict U o.T) oU.T χ ∧
      (∀ z, (⟨o.T.proj z.1,z.2⟩ : U) = oU.T.proj (χ z)) ∧
      (Subtype.val : openPreimage o.T U → o.D) ⁻¹' strictTransform n o.T.proj H =
        χ ⁻¹' strictTransform n oU.T.proj ((Subtype.val : U → A) ⁻¹' H) ∧
      cleanBoundary ((geoTransformAlong M o.T).E.map (fun B => (Subtype.val : openPreimage o.T U → o.D) ⁻¹' B)) =
        cleanBoundary ((geoTransformAlong MU oU.T).E.map (fun B => χ ⁻¹' B)) ∧
      oU.T.length ≤ o.T.length :=
  separateWith_open_whole_dictionary defaultHigherBlowupChoices defaultHigherBlowupChoices n n U
    (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞) M
    (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U → A) M) h
    (boundaryAdapted_open U h) rfl (by simp [MarkedIdealBiholomorphism.MarkedIdeal.pullback,Function.comp_def])
    (fun x => branchMultiplicity_le (isNormalCrossingsCarrier_of_boundaryAdapted h) x)
    (fun x => branchMultiplicity_le (isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_open U h)) x)

end
end Hironaka.HironakaNormalCrossingsOpenRestrictionSeparation
