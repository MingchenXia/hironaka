import Hironaka.Resolution.HironakaG3RSimultaneousBlowup
import Hironaka.Blowup.BlowupTowerIsomorphism
import Hironaka.Resolution.HironakaStageCenters

set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8VisibleSwapRestriction

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupTowerIsomorphism HironakaG3RSimultaneousBlowup HironakaStageCenters
  BlowupRestrictOpen HironakaLocalPrincipalization

variable {n : ℕ} {X Y Z W Q : CMfd.{0} n}

private abbrev twice {C : Set X} {D : Set Y} {π : Y → X} {q : Z → Y}
    (hπ : IsBlowupAlong n C π) (hq : IsBlowupAlong n D q) : BlowupTower X Z :=
  .step (.step .refl C π hπ) D q hq

/-- Two choices for the same ordered disjoint pair have a strict
comparison. The terminal map is uniquely determined over the base. -/
theorem same_disjoint_pair_strict
    {C D : Set X} {π : Y → X} {q : Z → Y} {ρ : W → X} {r : Q → W}
    (hπ : IsBlowupAlong n D π) (hq : IsBlowupAlong n (π ⁻¹' C) q)
    (hρ : IsBlowupAlong n D ρ) (hr : IsBlowupAlong n (ρ ⁻¹' C) r)
    (hC : IsClosedSubmanifold n C) (hCi : interior C = ∅) (hDisj : Disjoint D C) :
    ∃ χ : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Q,
      IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) (twice hπ hq) (twice hρ hr) χ ∧
      (ρ ∘ r) ∘ χ = π ∘ q ∧
      ∀ ξ : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Q,
        (ρ ∘ r) ∘ ξ = π ∘ q → ξ = χ := by
  obtain ⟨a,b,ha,hb,hπa,_,hba,hab⟩ := BlowupUniqueness.exists_biholomorphism_over hπ hρ
  let α : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ W :=
    ⟨⟨a,b,congrFun hba,congrFun hab⟩,ha,hb⟩
  have hα : ∀ y, ρ (α y) = π y := congrFun hπa
  have hPre : α ⁻¹' (ρ ⁻¹' C) = π ⁻¹' C := by
    ext y
    change ρ (α y) ∈ C ↔ π y ∈ C
    rw [hα]
  have hr' := MarkedIdealBiholomorphism.isBlowupAlong_comp_inverse
    α.contMDiff α.symm.contMDiff α.apply_symm_apply α.symm_apply_apply hr
  rw [hPre] at hr'
  obtain ⟨f,g,hf,hg,hqf,_,hgf,hfg⟩ := BlowupUniqueness.exists_biholomorphism_over hq hr'
  let χ : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Q :=
    ⟨⟨f,g,congrFun hgf,congrFun hfg⟩,hf,hg⟩
  have hχ (z : Z) : r (χ z) = α (q z) := by
    have h := congrFun hqf z
    change α.symm (r (χ z)) = q z at h
    rw [← h,α.apply_symm_apply]
  have hProj : (ρ ∘ r) ∘ χ = π ∘ q := by
    funext z
    change ρ (r (χ z)) = π (q z)
    rw [hχ,hα]
  refine ⟨χ,?_,hProj,?_⟩
  · exact .step (.step .refl hπ hρ α hα rfl) hq hr χ hχ hPre
  · intro ξ hξ
    obtain ⟨k,_,hk⟩ := BlowupUniqueness.existsUnique_comparison
      (isBlowupAlong_union_comp hπ hC hCi hDisj hq)
      (isBlowupAlong_union_comp hρ hC hCi hDisj hr)
    have he := (hk ξ ⟨ξ.contMDiff,hξ⟩).trans (hk χ ⟨χ.contMDiff,hProj⟩).symm
    exact Diffeomorph.ext (congrFun he)

/-- Restricting the globally swapped pair gives the literal first trace
and the pulled-back second trace. Any independently chosen local swapped
pair is strictly isomorphic to that restriction, uniquely over the open. -/
theorem restrict_visible_swapped_pair
    {C D : Set X} {π : Y → X} {ρ : W → X} {r : Q → W}
    (hπ : IsBlowupAlong n C π) (hρ : IsBlowupAlong n D ρ)
    (hr : IsBlowupAlong n (ρ ⁻¹' C) r) (hDisj : Disjoint D C)
    (U : Opens X) (hCVis : ((U : Set X) ∩ C).Nonempty) (hDVis : ((U : Set X) ∩ D).Nonempty)
    {W' Q' : CMfd.{0} n} {ρ' : W' → U} {r' : Q' → W'}
    (hρ' : IsBlowupAlong n ((Subtype.val : U → X) ⁻¹' D) ρ')
    (hr' : IsBlowupAlong n (ρ' ⁻¹' ((Subtype.val : U → X) ⁻¹' C)) r') :
    let L := restrict U (twice hρ hr)
    let R := twice hρ' hr'
    StageCentres (fun _ K => K.Nonempty) L ∧ StageCentres (fun _ K => K.Nonempty) R ∧
    ∃ χ : CMfd.of (n := n) (openPreimage (twice hρ hr) U)
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Q',
      IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞) L R χ ∧
      R.proj ∘ χ = L.proj ∧
      ∀ ξ : CMfd.of (n := n) (openPreimage (twice hρ hr) U)
          ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Q',
        R.proj ∘ ξ = L.proj → ξ = χ := by
  let C' : Set U := (Subtype.val : U → X) ⁻¹' C
  let D' : Set U := (Subtype.val : U → X) ⁻¹' D
  have hC' : C'.Nonempty := by
    obtain ⟨x,hx,hxc⟩ := hCVis
    exact ⟨⟨x,hx⟩,hxc⟩
  have hD' : D'.Nonempty := by
    obtain ⟨x,hx,hxd⟩ := hDVis
    exact ⟨⟨x,hx⟩,hxd⟩
  have hDC' : Disjoint D' C' := hDisj.preimage _
  have hCgeom := isClosedSubmanifold_preimage_val hπ.1 U
  have hCint : interior C' = ∅ := by
    change interior ((Subtype.val : U → X) ⁻¹' C) = ∅
    have hTop := U.isOpen.isOpenMap_subtype_val.preimage_interior_eq_interior_preimage
      continuous_subtype_val C
    exact hTop.symm.trans ((congrArg (fun S : Set X => (Subtype.val : U → X) ⁻¹' S) hπ.2.1).trans preimage_empty)
  let P : BlowupTower X W := .step .refl D ρ hρ
  let πU : openPreimage P U → U := fun y => ⟨ρ y.val,y.property⟩
  let hπU : IsBlowupAlong n D' πU := isBlowupAlong_restrict hρ U _
  let qU : openPreimage (twice hρ hr) U → openPreimage P U :=
    fun y => ⟨r y.val,y.property⟩
  let hqU : IsBlowupAlong n (πU ⁻¹' C') qU :=
    isBlowupAlong_restrict hr (openPreimage P U) _
  refine ⟨⟨⟨trivial,hD'⟩,?_⟩,⟨⟨trivial,hD'⟩,?_⟩,?_⟩
  · exact hC'.preimage (surjective_of_isBlowupAlong hπU)
  · exact hC'.preimage (surjective_of_isBlowupAlong hρ')
  · exact same_disjoint_pair_strict (X := CMfd.of (n := n) U) (C := C') (D := D')
      hπU hqU hρ' hr' hCgeom hCint hDC'

end Hironaka.HironakaG8VisibleSwapRestriction

#print axioms Hironaka.HironakaG8VisibleSwapRestriction.restrict_visible_swapped_pair
