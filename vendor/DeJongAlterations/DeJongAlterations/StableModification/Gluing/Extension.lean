/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane T45A)
-/
import DeJongAlterations.StableModification.Gluing.Normalization
import DeJongAlterations.StableModification.Blowups.Extension
import DeJongAlterations.Geometry.ModificationCenterOpen

/-!
# Extension by the identity of finitely many local modifications (PLAN-T5 node A8)

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), proof of
Proposition 4.3.1 (T:2970–2975: "each such blow up extends trivially from a neighborhood of `x` to
all of `C`") and of Proposition 4.5.1 (T:3243–3266); `PLAN-T5.md` §2.2 step 8. Iterating
`Blowups.extension` (lane T43A/BND, `lem:sm-modification-extension`) inserts finitely many local
modifications `fₖ : Yₖ → Uₖ`, each an isomorphism outside a closed `Tₖ ⊆ Uₖ` with `Uₖ ∩ Tₗ = ∅`
for `k ≠ l`, into one modification `β : X → C`.

## Main results

* `exists_extension_step`: one extension step, along a modification `β` which is an isomorphism
  over `U`.
* `exists_extension_finset`: **the iterated extension** — `β` is an isomorphism over every open
  inside all `Wₖ = C ∖ Tₖ` and agrees with `fₖ` over `Uₖ` (`IsoOver (β ∣_ Uₖ) fₖ`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace DeJongAlterations.StableModification.Gluing

open Geometry.ModificationCenter

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Step

variable {C X Y : Scheme.{u}}

/-- **One extension by the identity** (`Blowups.extension`, transported along an isomorphism):
let `β : X → C` be a modification which is an isomorphism over an open `U`, `W` an open with
`U ∪ W = C`, `W ≠ ∅`, and `f : Y → U` a modification which is an isomorphism over `U ∩ W`. Then
there is a modification `β' : X' → C` agreeing with `β` over `W` and with `f` over `U`. -/
theorem exists_extension_step (β : X ⟶ C) [IsModification β] (U W : C.Opens) (hUW : U ⊔ W = ⊤)
    (hW : (W : Set C).Nonempty) (hUβ : U ≤ isomorphismOpen β) (f : Y ⟶ U) [IsModification f]
    (hf : U.ι ⁻¹ᵁ W ≤ isomorphismOpen f) :
    ∃ (X' : Scheme.{u}) (β' : X' ⟶ C), IsModification β' ∧
      (∀ O : C.Opens, O ≤ W → IsoOver (β' ∣_ O) (β ∣_ O)) ∧ IsoOver (β' ∣_ U) f := by
  have hβ : IsModification β := inferInstance
  have := hβ.sourceIntegral
  have := hβ.targetIntegral
  have hfm : IsModification f := inferInstance
  have := hfm.sourceIntegral
  have : IsIso (β ∣_ U) := (le_isomorphismOpen_iff β U).mp hUβ
  have hUWX : β ⁻¹ᵁ U ⊔ β ⁻¹ᵁ W = ⊤ := by
    refine eq_top_iff.mpr fun x _ ↦ ?_
    have : β x ∈ U ⊔ W := by rw [hUW]; trivial
    exact TopologicalSpace.Opens.mem_sup.mpr (TopologicalSpace.Opens.mem_sup.mp this)
  have hWX : ((β ⁻¹ᵁ W : X.Opens) : Set X).Nonempty := by
    obtain ⟨y, hyW, x, rfl⟩ := β.denseRange.inter_open_nonempty W W.isOpen hW
    exact ⟨x, hyW⟩
  have hfac : inv (β ∣_ U) ≫ (β ⁻¹ᵁ U).ι ≫ β = U.ι := by
    rw [← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  have hpre : inv (β ∣_ U) ⁻¹ᵁ ((β ⁻¹ᵁ U).ι ⁻¹ᵁ (β ⁻¹ᵁ W)) = U.ι ⁻¹ᵁ W := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, Category.assoc, hfac]
  have hfX : IsIso ((f ≫ inv (β ∣_ U)) ∣_ ((β ⁻¹ᵁ U).ι ⁻¹ᵁ (β ⁻¹ᵁ W))) := by
    have h1 : IsIso (f ∣_ (inv (β ∣_ U) ⁻¹ᵁ ((β ⁻¹ᵁ U).ι ⁻¹ᵁ (β ⁻¹ᵁ W)))) := by
      rw [hpre]
      exact (le_isomorphismOpen_iff f _).mp hf
    rw [morphismRestrict_comp]
    infer_instance
  have he : IsModification (Blowups.extensionHom (β ⁻¹ᵁ W) (f ≫ inv (β ∣_ U))) :=
    Blowups.isModification_extensionHom (β ⁻¹ᵁ W) (f ≫ inv (β ∣_ U)) hUWX hWX
  refine ⟨_, Blowups.extensionHom (β ⁻¹ᵁ W) (f ≫ inv (β ∣_ U)) ≫ β, IsModification.comp _ β,
    fun O hO ↦ ?_, ?_⟩
  · have h := morphismRestrict_comp (Blowups.extensionHom (β ⁻¹ᵁ W) (f ≫ inv (β ∣_ U))) β O
    have hle : β ⁻¹ᵁ O ≤ β ⁻¹ᵁ W := fun x hx ↦ hO hx
    have : IsIso (Blowups.extensionHom (β ⁻¹ᵁ W) (f ≫ inv (β ∣_ U)) ∣_ (β ⁻¹ᵁ O)) :=
      isIso_restrict_of_le _ hle
    refine ⟨asIso (Blowups.extensionHom (β ⁻¹ᵁ W) (f ≫ inv (β ∣_ U)) ∣_ (β ⁻¹ᵁ O)), ?_⟩
    rw [h]
    rfl
  · have h := morphismRestrict_comp (Blowups.extensionHom (β ⁻¹ᵁ W) (f ≫ inv (β ∣_ U))) β U
    have h2 : IsoOver (Blowups.extensionHom (β ⁻¹ᵁ W) (f ≫ inv (β ∣_ U)) ∣_ (β ⁻¹ᵁ U))
        (f ≫ inv (β ∣_ U)) :=
      ⟨(Blowups.extensionPreimageIso (β ⁻¹ᵁ W) (f ≫ inv (β ∣_ U))).symm, by
        rw [Iso.symm_hom, Iso.inv_comp_eq]
        exact (Blowups.extensionPreimageIso_hom_comp (β ⁻¹ᵁ W) (f ≫ inv (β ∣_ U))).symm⟩
    have h3 := h2.comp (β ∣_ U)
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id, ← h] at h3
    exact h3

end Step

section Finset

variable {C : Scheme.{u}} {κ : Type*} (U W : κ → C.Opens) {Y : κ → Scheme.{u}}
  (f : ∀ k, Y k ⟶ U k)

/-- **Extension by the identity of finitely many local modifications** (`PLAN-T5.md` §2.2
step 8, node A8): let `C` be integral and, for `k` in a finite set `s`, `fₖ : Yₖ → Uₖ` a
modification of an open `Uₖ ⊆ C` which is an isomorphism over `Uₖ ∩ Wₖ`, where `Uₖ ∪ Wₖ = C`,
`Uₖ ⊆ Wₗ` for `k ≠ l` (the closed loci `C ∖ Wₖ` are disjoint from the other `Uₗ`) and the
generic point of `C` lies in every `Wₖ`. Then there is a modification `β : X → C` which is an
isomorphism over every open contained in all `Wₖ` and agrees with `fₖ` over each `Uₖ`. -/
theorem exists_extension_finset [IsIntegral C] [DecidableEq κ] (hUW : ∀ k, U k ⊔ W k = ⊤)
    (hgen : ∀ k, genericPoint C ∈ W k) (hUWl : ∀ k l, k ≠ l → U k ≤ W l)
    [∀ k, IsModification (f k)] (hf : ∀ k, (U k).ι ⁻¹ᵁ W k ≤ isomorphismOpen (f k))
    (s : Finset κ) :
    ∃ (X : Scheme.{u}) (β : X ⟶ C), IsModification β ∧
      (∀ O : C.Opens, (∀ k ∈ s, O ≤ W k) → O ≤ isomorphismOpen β) ∧
      ∀ k ∈ s, IsoOver (β ∣_ U k) (f k) := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨C, 𝟙 C, inferInstance, fun O _ ↦ ?_, fun k hk ↦ absurd hk (Finset.notMem_empty k)⟩
    rw [isomorphismOpen_eq_top]
    exact le_top
  | insert k s hks ih =>
    obtain ⟨X, β, hβ, hiso, hloc⟩ := ih
    have hUβ : U k ≤ isomorphismOpen β := hiso (U k) fun l hl ↦
      hUWl k l fun h ↦ hks (h ▸ hl)
    obtain ⟨X', β', hβ', hW', hU'⟩ := exists_extension_step β (U k) (W k) (hUW k)
      ⟨_, hgen k⟩ hUβ (f k) (hf k)
    refine ⟨X', β', hβ', fun O hO ↦ ?_, fun l hl ↦ ?_⟩
    · have hOk : O ≤ W k := hO k (Finset.mem_insert_self k s)
      have hOβ : O ≤ isomorphismOpen β := hiso O fun l hl ↦ hO l (Finset.mem_insert_of_mem hl)
      have : IsIso (β ∣_ O) := (le_isomorphismOpen_iff β O).mp hOβ
      have h := (hW' O hOk).prop (P := MorphismProperty.isomorphisms Scheme.{u})
        (inferInstanceAs (IsIso (β ∣_ O)))
      have : IsIso (β' ∣_ O) := h
      exact le_isomorphismOpen_of_isIso β' O
    · rcases Finset.mem_insert.mp hl with rfl | hl
      · exact hU'
      · have hlk : l ≠ k := fun h ↦ hks (h ▸ hl)
        exact (hW' (U l) (hUWl l k hlk)).trans (hloc l hl)

end Finset

end DeJongAlterations.StableModification.Gluing
