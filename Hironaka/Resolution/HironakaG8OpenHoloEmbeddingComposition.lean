import Hironaka.Resolution.HironakaG8LocalTransport
import Hironaka.Resolution.HironakaBaseChange
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8OpenHoloEmbeddingComposition
noncomputable section
open BlowupTowers HironakaBaseChange HironakaG8LocalTransport MaxLocusLocal
variable {n : ℕ} {A B C : CMfd.{0} n}

/-- The composition of two actual open holomorphic embeddings is an open
holomorphic embedding, with its open image and chart constructed. -/
theorem isOpenHoloEmbedding_comp {f : B → A} {g : C → B}
    (hf : IsOpenHoloEmbedding n f) (hg : IsOpenHoloEmbedding n g) :
    IsOpenHoloEmbedding n (f ∘ g) := by
  obtain ⟨U,φ,hφ⟩ := hf
  obtain ⟨V,ψ,hψ⟩ := hg
  let V' := imageOpen (Y' := B) (Y := CMfd.of (n := n) U) φ V
  let D : Opens A := ⟨(Subtype.val : U → A) '' (V' : Set U),
    U.isOpen.isOpenMap_subtype_val _ V'.isOpen⟩
  have hBD : ∀ q : U, q ∈ V' ↔ (q : A) ∈ D := by
    intro q
    constructor
    · intro hq; exact ⟨q,hq,rfl⟩
    · rintro ⟨q',hq',heq⟩
      exact (Subtype.ext heq : q' = q) ▸ hq'
  have hDU : D ≤ U := by
    rintro x ⟨q,_,rfl⟩
    exact q.property
  let e := (ψ.trans (restrictDiffeo (Y' := B) (Y := CMfd.of (n := n) U) φ V)).trans (nestedDiffeo U V' D hBD hDU)
  refine ⟨D,e,?_⟩
  intro x
  change f (g x) = (e x : A)
  rw [hφ,hψ]
  rfl
end
end Hironaka.HironakaG8OpenHoloEmbeddingComposition
