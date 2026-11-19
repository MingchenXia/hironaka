import Hironaka.Resolution.HironakaBaseChange
import Hironaka.Resolution.HironakaResolutionSpaceLocal

set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8StrictTransformAtlasSquare

open Hironaka.BlowupSequences BlowupTowers HironakaBaseChange
  HironakaResolutionSpaceLocal HironakaEmbeddedAnalytic BlowupRestrictOpen

variable {n : ℕ} {X Y : CMfd.{0} n}

/-- A holomorphic atlas chart, with its source as domain, is an open holomorphic embedding. -/
theorem atlas_open_holo_embedding
    (e : OpenPartialHomeomorph X (ComplexModel n))
    (he : e ∈ atlas (ComplexModel n) X) :
    let U : Opens X := ⟨e.source,e.open_source⟩
    IsOpenHoloEmbedding n (fun x : U => e x.val) := by
  dsimp only
  let U : Opens X := ⟨e.source,e.open_source⟩
  let V : Opens (ComplexModel n) := ⟨e.target,e.open_target⟩
  have hm := IsManifold.subset_maximalAtlas (I := 𝓘(ℂ,ComplexModel n)) (n := ∞) he
  have hfor : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      (fun x : U => e x.val) := by
    intro x
    exact (contMDiffAt_of_mem_maximalAtlas hm x.property).comp x contMDiff_subtype_val.contMDiffAt
  have hinv : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      (fun x : V => e.symm x.val) := by
    intro x
    exact (contMDiffAt_symm_of_mem_maximalAtlas hm x.property).comp x contMDiff_subtype_val.contMDiffAt
  let Φ : U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ V := {
    toEquiv := e.toHomeomorphSourceTarget.toEquiv
    contMDiff_toFun := by
      change ContMDiff _ _ _ (fun x : U => (⟨e x.val, e.map_source x.property⟩ : V))
      exact contMDiff_opens_mk hfor (fun x => e.map_source x.property)
    contMDiff_invFun := by
      change ContMDiff _ _ _ (fun x : V => (⟨e.symm x.val, e.map_target x.property⟩ : U))
      exact contMDiff_opens_mk hinv (fun x => e.map_target x.property) }
  exact ⟨V,Φ,fun _ => rfl⟩

/-- An exact square of holomorphic atlas coordinates computes the original
strict transform on its entire source chart. -/
theorem strict_transform_on_atlas_square
    (π : Y → X) (hπ : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π)
    (m : ComplexModel n → ComplexModel n)
    (hm : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ m)
    (e : OpenPartialHomeomorph X (ComplexModel n)) (he : e ∈ atlas (ComplexModel n) X)
    (f : OpenPartialHomeomorph Y (ComplexModel n)) (hf : f ∈ atlas (ComplexModel n) Y)
    (hMap : ∀ y ∈ f.source, π y ∈ e.source ∧ e (π y) = m (f y))
    (W : Set X) (A : Set (ComplexModel n))
    (hA : ∀ x ∈ e.source, x ∈ W ↔ e x ∈ A) :
    ∀ y ∈ f.source, y ∈ strictTransform n π W ↔ f y ∈ strictTransform n m A := by
  let U : Opens X := ⟨e.source,e.open_source⟩
  let V : Opens Y := ⟨f.source,f.open_source⟩
  let r (v : V) : U := ⟨π v.val,(hMap v.val v.property).1⟩
  have hr : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ r :=
    contMDiff_opens_mk (hπ.comp contMDiff_subtype_val) (fun v : V => (hMap v.val v.property).1)
  let eu (u : U) := e u.val
  let fv (v : V) := f v.val
  have hemb : IsOpenHoloEmbedding n eu := atlas_open_holo_embedding e he
  have hfmb : IsOpenHoloEmbedding n fv := atlas_open_holo_embedding f hf
  have hW : (Subtype.val : U → X) ⁻¹' W = eu ⁻¹' A :=
    Set.ext fun u => hA u.val u.property
  have h1 := strictTransform_preimage_eq hπ hr (isOpenHoloEmbedding_val U)
    (isOpenHoloEmbedding_val V) (fun _ => rfl) W
  have h2 := strictTransform_preimage_eq hm hr hemb hfmb
    (fun v => (hMap v.val v.property).2.symm) A
  rw [hW,h2] at h1
  intro y hy
  exact (Set.ext_iff.mp h1 ⟨y,hy⟩).symm

end Hironaka.HironakaG8StrictTransformAtlasSquare
