import Hironaka.Analytic.Unibranch.ComplexSpaceLocalEmbedding
import Hironaka.Resolution.HironakaG11InvTransitionIso

/-!
# Two local embeddings of a complex space of the same dimension are ambient-biholomorphic near a common point

Lane G11B (run 0080, round 2), G11 route steps 3--4 (`work/hironaka-resume-20261111/G11B/ROUTE-r2.md`); blueprint
`hironaka-g11-inv-local-embedding-iso.tex` (Hironaka).  Sources: the uniqueness of embeddings of a germ of complex space of a
given ambient dimension up to ambient automorphism (Grauert--Remmert); Bierstone--Milman 1997 §1.

For two local embeddings `e₁`, `e₂` of a reduced complex space `X` of the SAME ambient dimension and points `c₁`, `c₂` of
their carriers with the same image in `X`, there are open neighbourhoods `A ∋ c₁`, `B ∋ c₂` of the ambients and a
biholomorphism `Φ : A ≅ B` carrying the carrier of `e₁` exactly onto that of `e₂` and compatible with the maps to `X`
(`exists_ambient_biholomorphism`).  This is the geometric input of the comparison of two windows on an overlap: with it,
`HironakaG11InvTransport.inv_eq_on_overlap` applies to records that are restricted-equivalent after transport (e.g. the
vanishing-ideal records, `HironakaG11InvTransport.inv_vanishingRecord_eq_on_overlap`).

Proof: the holomorphic transition maps `F : e₁ → e₂`, `G : e₂ → e₁` (`LocalEmbedding.exists_contDiff_transition`) are
inverse to each other on the carriers (`LocalEmbedding.toPoint_injective`);
`HironakaG11InvTransitionIso.exists_biholomorphism_of_transitions` corrects `F` by a map vanishing on the carrier.
Sorry-free.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG11InvLocalEmbeddingIso

open Hironaka
open Hironaka.HironakaActualIntrinsicIsoPairedWindows (coordinateCarrier)
open Hironaka.HironakaG11InvTransitionIso

noncomputable section

variable {X : SourceReducedComplexSpace}

/-- **Two local embeddings of the same dimension are ambient-biholomorphic near a common point**: for local embeddings
`e₁`, `e₂` of `X` with `e₁.dim = e₂.dim` and carrier points `c₁`, `c₂` with the same image in `X`, there are opens
`A ≤ e₁.ambient` containing `c₁` and `B ≤ e₂.ambient` and a biholomorphism `Φ : A ≅ B` sending `c₁` to `c₂`, carrying the
carrier of `e₁` exactly onto that of `e₂`, and compatible with the maps to `X`. -/
theorem exists_ambient_biholomorphism (e₁ e₂ : LocalEmbedding X) (h : e₁.dim = e₂.dim)
    (c₁ : e₁.carrier) (c₂ : e₂.carrier) (hc : e₁.toPoint c₁ = e₂.toPoint c₂) :
    ∃ (A : Opens (ComplexModel e₁.dim)) (B : Opens (ComplexModel e₂.dim))
      (_ : A ≤ e₁.ambient) (_ : B ≤ e₂.ambient)
      (Φ : A ≃ₘ⟮𝓘(ℂ, ComplexModel e₁.dim), 𝓘(ℂ, ComplexModel e₂.dim)⟯ B) (hc₁ : c₁.val.val ∈ A),
      (Φ ⟨c₁.val.val, hc₁⟩ : ComplexModel e₂.dim) = c₂.val.val ∧
      (∀ x : A, (x : ComplexModel e₁.dim) ∈ coordinateCarrier e₁.carrier ↔
        (Φ x : ComplexModel e₂.dim) ∈ coordinateCarrier e₂.carrier) ∧
      ∀ (y : e₁.carrier) (hy : y.val.val ∈ A), ∃ z : e₂.carrier,
        z.val.val = (Φ ⟨y.val.val, hy⟩ : ComplexModel e₂.dim) ∧ e₂.toPoint z = e₁.toPoint y := by
  obtain ⟨W₁, hW₁, hc₁W, hW₁U, F, hF, -, hFfac⟩ :=
    LocalEmbedding.exists_contDiff_transition e₁ e₂ c₁ ⟨c₂, hc.symm⟩
  obtain ⟨W₂, hW₂, hc₂W, hW₂U, G, hG, -, hGfac⟩ :=
    LocalEmbedding.exists_contDiff_transition e₂ e₁ c₂ ⟨c₁, hc⟩
  -- the transitions are inverse on the carriers
  have hFD : ∀ x ∈ coordinateCarrier e₁.carrier ∩ W₁, F x ∈ coordinateCarrier e₂.carrier := by
    rintro _ ⟨⟨y, hy, rfl⟩, hyW⟩
    obtain ⟨z, hz, -⟩ := hFfac ⟨y, hy⟩ hyW
    exact ⟨z.val, z.property, hz⟩
  have hGC : ∀ x ∈ coordinateCarrier e₂.carrier ∩ W₂, G x ∈ coordinateCarrier e₁.carrier := by
    rintro _ ⟨⟨y, hy, rfl⟩, hyW⟩
    obtain ⟨z, hz, -⟩ := hGfac ⟨y, hy⟩ hyW
    exact ⟨z.val, z.property, hz⟩
  have hgf : ∀ x ∈ coordinateCarrier e₁.carrier ∩ W₁, F x ∈ W₂ → G (F x) = x := by
    rintro _ ⟨⟨y, hy, rfl⟩, hyW⟩ hFW
    obtain ⟨z, hz, hzp⟩ := hFfac ⟨y, hy⟩ hyW
    obtain ⟨y', hy', hy'p⟩ := hGfac z (by rw [hz]; exact hFW)
    have hyy : y' = ⟨y, hy⟩ := e₁.toPoint_injective (hy'p.trans hzp)
    rw [← hz, ← hy', hyy]
  have hfg : ∀ x ∈ coordinateCarrier e₂.carrier ∩ W₂, G x ∈ W₁ → F (G x) = x := by
    rintro _ ⟨⟨y, hy, rfl⟩, hyW⟩ hGW
    obtain ⟨z, hz, hzp⟩ := hGfac ⟨y, hy⟩ hyW
    obtain ⟨y', hy', hy'p⟩ := hFfac z (by rw [hz]; exact hGW)
    have hyy : y' = ⟨y, hy⟩ := e₂.toPoint_injective (hy'p.trans hzp)
    rw [← hz, ← hy', hyy]
  have hFc₁ : F c₁.val.val = c₂.val.val := by
    obtain ⟨z, hz, hzp⟩ := hFfac c₁ hc₁W
    have hzc : z = c₂ := e₂.toPoint_injective (hzp.trans hc)
    rw [← hz, hzc]
  -- align the dimensions
  obtain ⟨d₂, amb₂, car₂, an₂, map₂, imm₂, over₂⟩ := e₂
  dsimp only at h ⊢
  subst h
  obtain ⟨A, B, hAW, hBW, Φ, hcA, hCD, hΦF⟩ := exists_biholomorphism_of_transitions
    (SC := coordinateCarrier e₁.carrier) (SD := coordinateCarrier car₂) (c₀ := c₁.val.val) hW₁ hW₂ hF hG
    ⟨⟨c₁.val, c₁.property, rfl⟩, hc₁W⟩ (by rw [hFc₁]; exact hc₂W) hFD hGC hgf hfg
  refine ⟨A, B, fun x hx => hW₁U (hAW hx), fun x hx => hW₂U (hBW hx), Φ, hcA, ?_, hCD, fun y hy => ?_⟩
  · rw [hΦF ⟨c₁.val.val, hcA⟩ ⟨c₁.val, c₁.property, rfl⟩]
    exact hFc₁
  · obtain ⟨z, hz, hzp⟩ := hFfac y (hAW hy)
    refine ⟨z, ?_, hzp⟩
    rw [hΦF ⟨y.val.val, hy⟩ ⟨y.val, y.property, rfl⟩]
    exact hz

end

end Hironaka.Analytic.Unibranch.HironakaG11InvLocalEmbeddingIso
