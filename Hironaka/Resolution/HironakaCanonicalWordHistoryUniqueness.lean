/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaHomogeneousCanonicalTowerMaxima
import Mathlib.Data.Fintype.Vector

/-!
# Exact empty/full recipes determine whole histories and finitely many attained maxima

Actual full-maximum or empty recipes preserve every historical slot, including
full maxima which happen to be empty. Genuine whole tower comparisons yield
finite attained maximum candidates at each length, without assuming attainment.
Blueprint: `hironaka-canonical-word-history-uniqueness-extension.tex`.
-/
set_option autoImplicit false
open Set Classical
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaCanonicalWordHistoryUniqueness
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerIsomorphism BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec ResolutionInvariantSeq
  MarkedIdealBiholomorphism HironakaNormalCrossingsFirstStepChartHistory
variable {n k : ℕ} {Λ : Type v} [LinearOrder Λ] {X X' : CMfd.{u} n}

/-- A reverse chronological literal recipe; true full maxima may themselves be empty. -/
def CanonicalWord (M : MarkedIdeal n X)
    (inv : ∀ {Y : CMfd.{u} n},BlowupTower X Y → Y → Λ) :
    ∀ {Y : CMfd.{u} n},BlowupTower X Y → List Bool → Prop
  | _,.refl,[] => True
  | _,.refl,_::_ => False
  | _,.step _ _ _ _,[] => False
  | _,.step T C _ _,b::w => CanonicalWord M inv T w ∧
      C=(if b then ResolutionDriver.maxLocus (inv T) (geoTransformAlong M T).cosupp else ∅)

theorem CanonicalWord.isCanonical (M : MarkedIdeal n X)
    (inv : ∀ {Y : CMfd.{u} n},BlowupTower X Y → Y → Λ) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y) (w : List Bool),
      CanonicalWord M inv T w → IsCanonical M inv T
  | _,.refl,_,_ => trivial
  | _,.step _ _ _ _,[],h => h.elim
  | _,.step T C π hπ,b::w,h => by
      change CanonicalWord M inv T w ∧ _ at h
      obtain ⟨hw,hC⟩ := h
      refine ⟨hw.isCanonical M inv T w,?_⟩
      cases b with
      | false => exact Or.inl hC
      | true => exact Or.inr hC

theorem CanonicalWord.length_eq (M : MarkedIdeal n X)
    (inv : ∀ {Y : CMfd.{u} n},BlowupTower X Y → Y → Λ) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y) (w : List Bool),
      CanonicalWord M inv T w → w.length=T.length
  | _,.refl,[],_ => rfl
  | _,.refl,_::_,h => h.elim
  | _,.step _ _ _ _,[],h => h.elim
  | _,.step T C π hπ,b::w,h => by
      change CanonicalWord M inv T w ∧ _ at h
      exact congrArg Nat.succ (h.1.length_eq M inv T w)

theorem exists_canonicalWord (M : MarkedIdeal n X)
    (inv : ∀ {Y : CMfd.{u} n},BlowupTower X Y → Y → Λ) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),IsCanonical M inv T →
      ∃ w : List Bool,CanonicalWord M inv T w
  | _,.refl,_ => ⟨[],trivial⟩
  | _,.step T C π hπ,h => by
      change IsCanonical M inv T ∧ _ at h
      obtain ⟨hT,hC⟩ := h
      obtain ⟨w,hw⟩ := exists_canonicalWord M inv T hT
      rcases hC with hC | hC
      · exact ⟨false::w,hw,hC⟩
      · exact ⟨true::w,hw,hC⟩

/-- The SAME recipe supplies a genuine whole history comparison, retaining empty positions. -/
theorem exists_isTowerIso_of_canonicalWord (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X) :
    ∀ {Y' Y : CMfd.{u} n} (T' : BlowupTower X' Y') (T : BlowupTower X Y) (w : List Bool),
      CanonicalWord (MarkedIdeal.pullback Φ M) (R.inv (MarkedIdeal.pullback Φ M)) T' w →
      CanonicalWord M (R.inv M) T w →
      ∃ χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y,IsTowerIso Φ T' T χ
  | _,_,.refl,.refl,_,_,_ => ⟨Φ,.refl⟩
  | _,_,.refl,.step _ _ _ _,w,h',h => by
      have hl := (h'.length_eq _ _ _ w).symm.trans (h.length_eq _ _ _ w)
      simp [BlowupTower.length] at hl
  | _,_,.step _ _ _ _,.refl,w,h',h => by
      have hl := (h'.length_eq _ _ _ w).symm.trans (h.length_eq _ _ _ w)
      simp [BlowupTower.length] at hl
  | _,_,.step _ _ _ _,.step _ _ _ _,[],h',_ => h'.elim
  | _,_,.step T' C' π' hπ',.step T C π hπ,b::w,h',h => by
      change CanonicalWord _ _ T' w ∧ _ at h'
      change CanonicalWord _ _ T w ∧ _ at h
      obtain ⟨hw',hC'⟩ := h'
      obtain ⟨hw,hC⟩ := h
      obtain ⟨χ,hiso⟩ := exists_isTowerIso_of_canonicalWord R M hM Φ T' T w hw' hw
      have hcan := hw.isCanonical M (R.inv M) T w
      have ht := R.isInvValue.isGeoTestTower_of_isCanonical hM T hcan
      have hcos := IsTowerIso.cosupp_geoTransformAlong Φ hM.isWellFormed.isClosedSubmanifold_N
        hM.isWellFormed.isCoherent hiso ht
      have hv := fun p hp => R.isInvValue.towerIso Φ M hM T' T χ hiso hcan p hp
      have hCC : χ ⁻¹' C=C' := by
        cases b with
        | false =>
          change C'=∅ at hC'
          change C=∅ at hC
          rw [hC,hC',preimage_empty]
        | true =>
          change C'=ResolutionDriver.maxLocus _ _ at hC'
          change C=ResolutionDriver.maxLocus _ _ at hC
          rw [hC,hC',hcos]
          exact (ResolutionInvariantSegments.maxLocus_preimage_of_surjective χ.toEquiv.surjective hv).symm
      obtain ⟨χ₁,hχ₁⟩ := exists_oneStep_isTowerIso χ hπ' hπ hCC
      exact ⟨χ₁,IsTowerIso.step hiso hπ' hπ χ₁ (fun p => (hχ₁.proj_comm p).symm) hCC⟩

private theorem maximum_value_eq_of_word (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    {Y' Y : CMfd.{u} n} (T' : BlowupTower X Y') (T : BlowupTower X Y) (w : List Bool)
    (hw' : CanonicalWord M (R.inv M) T' w) (hw : CanonicalWord M (R.inv M) T w)
    (x : Y') (hx : x ∈ ResolutionDriver.maxLocus (R.inv M T') (geoTransformAlong M T').cosupp)
    (y : Y) (hy : y ∈ ResolutionDriver.maxLocus (R.inv M T) (geoTransformAlong M T).cosupp) :
    R.inv M T' x=R.inv M T y := by
  let Φ := Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞
  have hid : MarkedIdeal.pullback Φ M=M := by
    change MarkedIdeal.pullback id M=M
    exact ContactCanonicalAlong.pullback_id M hM.isWellFormed.isCoherent
  obtain ⟨χ,hiso⟩ := exists_isTowerIso_of_canonicalWord R M hM Φ T' T w (by simpa only [hid] using hw') hw
  have hcan := hw.isCanonical M (R.inv M) T w
  have ht := R.isInvValue.isGeoTestTower_of_isCanonical hM T hcan
  have hcos := IsTowerIso.cosupp_geoTransformAlong Φ hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hiso ht
  rw [hid] at hcos
  have hv (p : Y') (hp : χ p ∈ (geoTransformAlong M T).cosupp) :
      R.inv M T' p=R.inv M T (χ p) := by
    simpa only [hid] using R.isInvValue.towerIso Φ M hM T' T χ hiso hcan p hp
  have hmax : ResolutionDriver.maxLocus (R.inv M T') (geoTransformAlong M T').cosupp=
      χ ⁻¹' ResolutionDriver.maxLocus (R.inv M T) (geoTransformAlong M T).cosupp := by
    rw [hcos]
    exact ResolutionInvariantSegments.maxLocus_preimage_of_surjective χ.toEquiv.surjective hv
  have hxχ : χ x ∈ ResolutionDriver.maxLocus (R.inv M T) (geoTransformAlong M T).cosupp :=
    (congrArg (fun A => x ∈ A) hmax).mp hx
  exact (hv x hxχ.1).trans (le_antisymm (hy.2 _ hxχ.1) (hxχ.2 _ hy.1))

/-- Finitely many ENTIRE attained maximum values, over ALL weak histories at a fixed length. -/
theorem finite_attained_maximum_values (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (j : ℕ) :
    {a : Λ | ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),T.length=j ∧
      IsCanonical M (R.inv M) T ∧
      ∃ x ∈ ResolutionDriver.maxLocus (R.inv M T) (geoTransformAlong M T).cosupp,R.inv M T x=a}.Finite := by
  let A : Set Λ := {a | ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),T.length=j ∧
    IsCanonical M (R.inv M) T ∧
    ∃ x ∈ ResolutionDriver.maxLocus (R.inv M T) (geoTransformAlong M T).cosupp,R.inv M T x=a}
  have hword (a : A) : ∃ w : List.Vector Bool j,
      ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),CanonicalWord M (R.inv M) T w.val ∧
      ∃ x ∈ ResolutionDriver.maxLocus (R.inv M T) (geoTransformAlong M T).cosupp,R.inv M T x=a.val := by
    obtain ⟨Y,T,hlen,hcan,x,hx,he⟩ := a.property
    obtain ⟨w,hw⟩ := exists_canonicalWord M (R.inv M) T hcan
    exact ⟨⟨w,(hw.length_eq M (R.inv M) T w).trans hlen⟩,Y,T,hw,x,hx,he⟩
  choose word hist using hword
  have hinj : Function.Injective word := by
    intro a b hab
    obtain ⟨Y,T,hw,x,hx,he⟩ := hist a
    obtain ⟨Z,S,hs,y,hy,hf⟩ := hist b
    have hweq : CanonicalWord M (R.inv M) T (word b).val := by rw [←hab];exact hw
    apply Subtype.ext
    exact he.symm.trans ((maximum_value_eq_of_word R M hM T S (word b).val hweq hs x hx y hy).trans hf)
  have : Finite A := Finite.of_injective word hinj
  exact Set.toFinite A

end
end Hironaka.HironakaCanonicalWordHistoryUniqueness
