import Hironaka.Analytic.Unibranch.HironakaG11InvLocalEmbeddingIso
import Hironaka.Resolution.HironakaActualSectionInitialValues
import Hironaka.Analytic.FibreDimensionLowerBound

/-!
# Stabilization of local embeddings and ambient comparison in a common dimension

Lane G11B (run 0080, round 2), G11 route step 4 (`work/hironaka-resume-20261111/G11B/ROUTE-r2.md`); blueprint
`hironaka-g11-inv-local-embedding-iso.tex` (Hironaka).  Source: every embedding of a germ is, after a product with a linear
space, ambient-isomorphic to any other one of the same dimension (Grauert--Remmert; Bierstone--Milman 1997 §1, "products
with a line" (ii)).

* `stabilize e`: the local embedding `C × 0 ⊆ Ω × ℂ` of the same open of `X` (`actualSectionSubspaceIso`), of ambient
  dimension `e.dim + 1`; `stabilizeN e r` its `r`-fold iterate, of dimension `e.dim + r`, with the same points
  (`exists_stabilizeN_point`, `stabilizeN_toPoint_mem_range`);
* **`exists_stabilized_ambient_biholomorphism`**: any two local embeddings through a common point of `X` become
  ambient-biholomorphic near that point after stabilization to a common dimension `N` (compatibly with the maps to `X`).

With the vanishing-ideal records (`HironakaG11InvTransport.inv_vanishingRecord_eq_on_overlap`) this gives the agreement of
the invariant values of any two windows of a common dimension on overlaps (the vanishing-ideal route of G11).  Sorry-free.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG11InvLocalEmbeddingStabilize

open Hironaka
open Hironaka.HironakaReducedComplexAnalyticSpaces
open Hironaka.HironakaActualAnalyticSubspace
open Hironaka.HironakaActualIntrinsicIsoPairedWindows (coordinateCarrier)
open Hironaka.HironakaActualOpenZeroSectionDifferentials
open Hironaka.HironakaActualSectionInitialValues (actualSectionSubspaceIso)
open Hironaka.HironakaRelativeNormalIdeal Hironaka.HironakaActualCentreJointJets

noncomputable section

/-- The carrier `C × 0` of the stabilized embedding is analytic. -/
theorem liftedCarrier_analytic {n : ℕ} {U : Opens (ComplexModel n)} {A : Set U}
    (hA : IsComplexAnalyticSubset (n := n) A) : IsComplexAnalyticSubset (n := n + 1) (liftedCarrier A) := by
  have h1 := Hironaka.AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage
    (projection_contMDiff U) hA
  have hnorm : ContMDiff 𝓘(ℂ, ComplexModel (n + 1)) 𝓘(ℂ, ComplexModel 1) ∞
      (fun z : productOpen U => actualJointNormalProjection n 1 z.val) :=
    (actualJointNormalProjection n 1).contMDiff.comp contMDiff_subtype_val
  have h2 := Hironaka.AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hnorm
    (Hironaka.FibreDimensionLowerBound.isComplexAnalyticSubset_singleton
      (n := 1) (0 : ComplexModel 1))
  exact h1.inter h2

variable {X : SourceReducedComplexSpace}

/-- **The stabilization** `C × 0 ⊆ Ω × ℂ` of a local embedding `C ⊆ Ω`: the same open piece of `X`, embedded in ambient
dimension one more, through the zero section (`actualSectionSubspaceIso`). -/
def stabilize (e : LocalEmbedding X) : LocalEmbedding X where
  dim := e.dim + 1
  ambient := productOpen e.ambient
  carrier := liftedCarrier e.carrier
  analytic := liftedCarrier_analytic e.analytic
  map := (actualSectionSubspaceIso e.carrier).inv ≫ e.map
  isOpenImmersion := by
    let := e.isOpenImmersion
    infer_instance
  overPoint := by
    rw [Category.assoc, e.overPoint]
    exact actualSubspaceMap_point (projection_contMDiff e.ambient) (fun _ hz => hz.1)

theorem stabilize_dim (e : LocalEmbedding X) : (stabilize e).dim = e.dim + 1 := rfl

/-- The points of the stabilization map to `X` through the projection. -/
theorem stabilize_toPoint (e : LocalEmbedding X) (z : (stabilize e).carrier) :
    (stabilize e).toPoint z = e.toPoint ⟨projection e.ambient z.val, z.property.1⟩ := rfl

/-- The zero section of a carrier point is a carrier point of the stabilization, with the same image in `X`. -/
theorem exists_stabilize_point (e : LocalEmbedding X) (c : e.carrier) :
    ∃ c' : (stabilize e).carrier, (stabilize e).toPoint c' = e.toPoint c := by
  have hmem : zeroSection e.ambient c.val ∈ liftedCarrier e.carrier := by
    refine ⟨?_, ?_⟩
    · have h : projection e.ambient (zeroSection e.ambient c.val) = c.val :=
        Subtype.ext (tangentProjection_tangentInclusion e.dim 1 c.val)
      rw [h]; exact c.property
    · change actualJointNormalProjection e.dim 1 (tangentInclusion e.dim 1 c.val.val) = 0
      exact actualJointNormalProjection_tangent _ _ _
  refine ⟨⟨zeroSection e.ambient c.val, hmem⟩, ?_⟩
  rw [stabilize_toPoint]
  congr 1
  exact Subtype.ext (Subtype.ext (tangentProjection_tangentInclusion e.dim 1 c.val))

/-- **Iterated stabilization**: `stabilizeN e r` embeds the same open piece of `X` in ambient dimension `e.dim + r`. -/
def stabilizeN (e : LocalEmbedding X) : ℕ → LocalEmbedding X
  | 0 => e
  | r + 1 => stabilize (stabilizeN e r)

theorem stabilizeN_dim (e : LocalEmbedding X) : ∀ r, (stabilizeN e r).dim = e.dim + r
  | 0 => rfl
  | r + 1 => by
    change (stabilizeN e r).dim + 1 = e.dim + (r + 1)
    rw [stabilizeN_dim e r, Nat.add_assoc]

theorem exists_stabilizeN_point (e : LocalEmbedding X) (c : e.carrier) :
    ∀ r, ∃ c' : (stabilizeN e r).carrier, (stabilizeN e r).toPoint c' = e.toPoint c
  | 0 => ⟨c, rfl⟩
  | r + 1 => by
    obtain ⟨c', hc'⟩ := exists_stabilizeN_point e c r
    obtain ⟨c'', hc''⟩ := exists_stabilize_point (stabilizeN e r) c'
    exact ⟨c'', hc''.trans hc'⟩

/-- The stabilizations see no new points of `X`. -/
theorem stabilizeN_toPoint_mem_range (e : LocalEmbedding X) :
    ∀ r (z : (stabilizeN e r).carrier), (stabilizeN e r).toPoint z ∈ range e.toPoint
  | 0, z => ⟨z, rfl⟩
  | r + 1, _ => stabilizeN_toPoint_mem_range e r _

/-- **Two local embeddings through a common point become ambient-biholomorphic after stabilization to a common
dimension**: for local embeddings `e₁`, `e₂` of `X`, carrier points `c₁`, `c₂` with the same image, and `N ≥ e₁.dim, e₂.dim`,
the stabilizations `f₁ = stabilizeN e₁ (N - e₁.dim)`, `f₂ = stabilizeN e₂ (N - e₂.dim)` (both of dimension `N`) have carrier
points `c₁'`, `c₂'` over the same point of `X` and a biholomorphism `Φ` of ambient neighbourhoods with `Φ c₁' = c₂'`, carrying
carrier onto carrier and compatible with the maps to `X`. -/
theorem exists_stabilized_ambient_biholomorphism (e₁ e₂ : LocalEmbedding X) (c₁ : e₁.carrier) (c₂ : e₂.carrier)
    (hc : e₁.toPoint c₁ = e₂.toPoint c₂) (N : ℕ) (h₁ : e₁.dim ≤ N) (h₂ : e₂.dim ≤ N) :
    (stabilizeN e₁ (N - e₁.dim)).dim = N ∧ (stabilizeN e₂ (N - e₂.dim)).dim = N ∧
    ∃ (c₁' : (stabilizeN e₁ (N - e₁.dim)).carrier) (c₂' : (stabilizeN e₂ (N - e₂.dim)).carrier),
      (stabilizeN e₁ (N - e₁.dim)).toPoint c₁' = e₁.toPoint c₁ ∧
      (stabilizeN e₂ (N - e₂.dim)).toPoint c₂' = e₂.toPoint c₂ ∧
      ∃ (A : Opens (ComplexModel (stabilizeN e₁ (N - e₁.dim)).dim))
        (B : Opens (ComplexModel (stabilizeN e₂ (N - e₂.dim)).dim))
        (_ : A ≤ (stabilizeN e₁ (N - e₁.dim)).ambient) (_ : B ≤ (stabilizeN e₂ (N - e₂.dim)).ambient)
        (Φ : A ≃ₘ⟮𝓘(ℂ, ComplexModel (stabilizeN e₁ (N - e₁.dim)).dim),
          𝓘(ℂ, ComplexModel (stabilizeN e₂ (N - e₂.dim)).dim)⟯ B) (hc₁ : c₁'.val.val ∈ A),
        (Φ ⟨c₁'.val.val, hc₁⟩ : ComplexModel _) = c₂'.val.val ∧
        (∀ x : A, (x : ComplexModel _) ∈ coordinateCarrier (stabilizeN e₁ (N - e₁.dim)).carrier ↔
          (Φ x : ComplexModel _) ∈ coordinateCarrier (stabilizeN e₂ (N - e₂.dim)).carrier) ∧
        ∀ (y : (stabilizeN e₁ (N - e₁.dim)).carrier) (hy : y.val.val ∈ A),
          ∃ z : (stabilizeN e₂ (N - e₂.dim)).carrier, z.val.val = (Φ ⟨y.val.val, hy⟩ : ComplexModel _) ∧
            (stabilizeN e₂ (N - e₂.dim)).toPoint z = (stabilizeN e₁ (N - e₁.dim)).toPoint y := by
  have hd₁ : (stabilizeN e₁ (N - e₁.dim)).dim = N := by rw [stabilizeN_dim]; omega
  have hd₂ : (stabilizeN e₂ (N - e₂.dim)).dim = N := by rw [stabilizeN_dim]; omega
  obtain ⟨c₁', hc₁'⟩ := exists_stabilizeN_point e₁ c₁ (N - e₁.dim)
  obtain ⟨c₂', hc₂'⟩ := exists_stabilizeN_point e₂ c₂ (N - e₂.dim)
  refine ⟨hd₁, hd₂, c₁', c₂', hc₁', hc₂', ?_⟩
  exact HironakaG11InvLocalEmbeddingIso.exists_ambient_biholomorphism _ _ (hd₁.trans hd₂.symm) c₁' c₂'
    (hc₁'.trans (hc.trans hc₂'.symm))

end

end Hironaka.Analytic.Unibranch.HironakaG11InvLocalEmbeddingStabilize
