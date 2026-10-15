/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalActualEmptyNormalization
/-! Whole finite original canonical histories with all actual empty steps removed.
Complete three-node mathematics preceded code. Actual whole length decreases at
each genuine empty deletion; no compressed history or value certificate input. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalFiniteEmptyCompression
noncomputable section
open Hironaka.BlowupSequences MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism HironakaStageCenters
  CanonicalCentres HomogenizedIdealAlong HironakaOriginalInteriorEmptyHistory
  HironakaOriginalRecursiveBoundaryHistoryMap HironakaOriginalActualEmptyNormalization
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- A genuine actual empty blowup and its literal entire suffix are found
internally from the failure of the true existing every-centre property. -/
theorem exists_actual_empty_step_split (T : BlowupTower X Y)
    (hne : ¬ StageCentres (fun _ C => C.Nonempty) T) :
    ∃ (A B : CMfd.{u} n) (H : BlowupTower X A) (π : B → A)
      (hπ : IsBlowupAlong n (∅ : Set A) π) (S : BlowupTower B Y),
      T=(H.step ∅ π hπ).append S := by
  classical
  induction T with
  | refl => exact False.elim (hne trivial)
  | @step Y Z T C π hπ ih =>
    by_cases hC : C.Nonempty
    · have hT : ¬ StageCentres (fun _ C => C.Nonempty) T := fun ht => hne ⟨ht,hC⟩
      obtain ⟨A,B,H,ρ,hρ,S,heq⟩ := ih hT
      refine ⟨A,B,H,ρ,hρ,S.step C π hπ,?_⟩
      rw [BlowupTower.append_step,← heq]
    · have he : C=∅ := Set.not_nonempty_iff_eq_empty.mp hC
      subst C
      exact ⟨Y,Z,T,π,hπ,.refl,rfl⟩

/-- Original-only complete family compression: every actual centre of the
internally constructed canonical tower is nonempty, with ONE entire value map. -/
theorem original_recursive_family_empty_free_compression (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (T : BlowupTower X Y)
    (hcan : IsCanonical M ((invFamily hn k).inv M) T) :
    ∃ (Z : CMfd.{u} n) (Q : BlowupTower X Z)
      (χ : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y) (F : ValTy k ↪o ValTy k),
      StageCentres (fun _ C => C.Nonempty) Q ∧ Q.length≤T.length ∧
      IsCanonical M ((invFamily hn k).inv M) Q ∧
      (∀ q, T.proj (χ q)=Q.proj q) ∧
      (geoTransformAlong M T).cosupp=χ.symm ⁻¹' (geoTransformAlong M Q).cosupp ∧
      (∀ y∈(geoTransformAlong M T).cosupp,
        (invFamily hn k).inv M T y=F ((invFamily hn k).inv M Q (χ.symm y))) ∧
      (IsGeoResolution M T ↔ IsGeoResolution M Q) := by
  classical
  generalize hlen : T.length=ℓ
  induction ℓ using Nat.strong_induction_on generalizing Y with
  | h ℓ ih =>
    by_cases hne : StageCentres (fun _ C => C.Nonempty) T
    · refine ⟨Y,T,Diffeomorph.refl 𝓘(ℂ,ComplexModel n) Y ∞,OrderEmbedding.id _,
        hne,hlen.le,hcan,fun _ => rfl,?_,fun _ _ => rfl,Iff.rfl⟩
      rfl
    obtain ⟨A,B,H,π,hπ,S,heq⟩ := exists_actual_empty_step_split T hne
    subst T
    obtain ⟨Y',S',χD,hlenD,hi,hcanD,hcosD,hvalD,hresD⟩ :=
      original_recursive_family_actual_empty_deletion hn k M hM H π hπ S hcan
    have hlt : (H.append S').length<ℓ := by
      rw [BlowupTower.length_append,hlenD]
      rw [BlowupTower.length_append] at hlen
      change H.length+1+S.length=ℓ at hlen
      omega
    obtain ⟨Z,Q,χQ,FQ,hneQ,hleQ,hcanQ,hprojQ,hcosQ,hvalQ,hresQ⟩ :=
      ih _ hlt (H.append S') hcanD rfl
    refine ⟨Z,Q,χQ.trans χD,FQ.comp (recursiveHistoryShiftEmbedding k (M.E.length+H.length)),
      hneQ,?_,hcanQ,?_,?_,?_,hresD.trans hresQ⟩
    · exact hleQ.trans hlt.le
    · intro q
      change ((H.step ∅ π hπ).append S).proj (χD (χQ q))=Q.proj q
      have hp := hi.proj_comm (χQ q)
      change (interiorEmptyHistory H S').proj (χQ q)=
        ((H.step ∅ π hπ).append S).proj (χD (χQ q)) at hp
      rw [proj_interiorEmptyHistory] at hp
      exact hp.symm.trans (hprojQ q)
    · ext y
      change y∈(geoTransformAlong M ((H.step ∅ π hπ).append S)).cosupp ↔
        χQ.symm (χD.symm y)∈(geoTransformAlong M Q).cosupp
      rw [hcosD]
      change χD.symm y∈(geoTransformAlong M (H.append S')).cosupp ↔ _
      rw [hcosQ]
      rfl
    · intro y hy
      have hyD : χD.symm y∈(geoTransformAlong M (H.append S')).cosupp := by
        rw [hcosD] at hy
        exact hy
      have hv := hvalD y hy
      rw [hvalQ (χD.symm y) hyD] at hv
      exact hv

/-- Original-only complete masked Step One compression: every actual centre of the
internally constructed canonical tower is nonempty, with ONE entire value map. -/
theorem original_recursive_step_empty_free_compression (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (T : BlowupTower X Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M) T) :
    ∃ (Z : CMfd.{u} n) (Q : BlowupTower X Z)
      (χ : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y) (F : (ℕ ×ₗ WithTop (ValTy k)) ↪o (ℕ ×ₗ WithTop (ValTy k))),
      StageCentres (fun _ C => C.Nonempty) Q ∧ Q.length≤T.length ∧
      IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M) Q ∧
      (∀ q, T.proj (χ q)=Q.proj q) ∧
      (geoTransformAlong M T).cosupp=χ.symm ⁻¹' (geoTransformAlong M Q).cosupp ∧
      (∀ y∈(geoTransformAlong M T).cosupp,
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M T y=F (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M Q (χ.symm y))) ∧
      (IsGeoResolution M T ↔ IsGeoResolution M Q) := by
  classical
  generalize hlen : T.length=ℓ
  induction ℓ using Nat.strong_induction_on generalizing Y with
  | h ℓ ih =>
    by_cases hne : StageCentres (fun _ C => C.Nonempty) T
    · refine ⟨Y,T,Diffeomorph.refl 𝓘(ℂ,ComplexModel n) Y ∞,OrderEmbedding.id _,
        hne,hlen.le,hcan,fun _ => rfl,?_,fun _ _ => rfl,Iff.rfl⟩
      rfl
    obtain ⟨A,B,H,π,hπ,S,heq⟩ := exists_actual_empty_step_split T hne
    subst T
    obtain ⟨Y',S',χD,hlenD,hi,hcanD,hcosD,hvalD,hresD⟩ :=
      original_recursive_step_actual_empty_deletion hn k M hM hmax H π hπ S hcan
    have hlt : (H.append S').length<ℓ := by
      rw [BlowupTower.length_append,hlenD]
      rw [BlowupTower.length_append] at hlen
      change H.length+1+S.length=ℓ at hlen
      omega
    obtain ⟨Z,Q,χQ,FQ,hneQ,hleQ,hcanQ,hprojQ,hcosQ,hvalQ,hresQ⟩ :=
      ih _ hlt (H.append S') hcanD rfl
    refine ⟨Z,Q,χQ.trans χD,FQ.comp (recursiveStepShiftEmbedding k (M.E.length+H.length)),
      hneQ,?_,hcanQ,?_,?_,?_,hresD.trans hresQ⟩
    · exact hleQ.trans hlt.le
    · intro q
      change ((H.step ∅ π hπ).append S).proj (χD (χQ q))=Q.proj q
      have hp := hi.proj_comm (χQ q)
      change (interiorEmptyHistory H S').proj (χQ q)=
        ((H.step ∅ π hπ).append S).proj (χD (χQ q)) at hp
      rw [proj_interiorEmptyHistory] at hp
      exact hp.symm.trans (hprojQ q)
    · ext y
      change y∈(geoTransformAlong M ((H.step ∅ π hπ).append S)).cosupp ↔
        χQ.symm (χD.symm y)∈(geoTransformAlong M Q).cosupp
      rw [hcosD]
      change χD.symm y∈(geoTransformAlong M (H.append S')).cosupp ↔ _
      rw [hcosQ]
      rfl
    · intro y hy
      have hyD : χD.symm y∈(geoTransformAlong M (H.append S')).cosupp := by
        rw [hcosD] at hy
        exact hy
      have hv := hvalD y hy
      rw [hvalQ (χD.symm y) hyD] at hv
      exact hv

end
end Hironaka.HironakaOriginalFiniteEmptyCompression
