import Hironaka.Analytic.Unibranch.HironakaG11HSMinimalWindows
import Hironaka.Resolution.HironakaG11BennettHolGerm

/-!
# Bennett's stabilization of Hilbert–Samuel functions (goal G11: the named input `HSStabilization` proved)

**`hsStabilization : HSStabilization`**: the strict pointwise order on the Hilbert–Samuel functions
`ℓ ↦ dim_ℂ O_{Y,y}/m^(ℓ+1)` of points of reduced complex spaces is well-founded (Bennett, Ann. Math. 91
(1970); Bierstone–Milman 2008 §1, property (4); Bierstone–Milman 2003, Ex. 1.11(2)).

Proof. In a strictly decreasing sequence `H_0 > H_1 > ⋯` every `H_k(1) ≤ H_0(1) =: E + 1`. At a point
with `H(1) = n + 1` there is a minimal local embedding into `ℂ^n` (lane G11B,
`HironakaG11InvMinimalLocalEmbedding.exists_minimal_localEmbedding_at`), so `H` is the Hilbert–Samuel
function of a quotient of the germ ring `O_n`, hence the counting function of a diagram in `ℕ^E`
(`HironakaG11BennettHolGerm.hilbertSamuelValue_mem_diagramFunctions`, `n ≤ E`). Strictly decreasing
sequences of such counting functions do not exist
(`HironakaG11BennettDiagram.not_strictAnti_of_mem_diagramFunctions`).

Consequently the G11 endpoints of `HironakaG11HSPhaseInduction` and `HironakaG11HSMinimalWindows` hold
without the hypothesis `hS` (`compactSingularCentreResolution_of_hsPhaseData'`,
`compactSingularCentreResolution_of_hsRecords'`): the only remaining named input of the G11
Hilbert–Samuel route is the record-level property (`HSPhaseData`, resp. `HSRecords`).
Blueprint: `hironaka-g11-resume-bennett-stabilization.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG11BennettStabilization

open Hironaka Hironaka
  HironakaG11BennettDiagram HironakaG11BennettHolGerm HironakaHolomorphicPointJets
  HironakaIntrinsicComplexAnalyticRegularLocus SourceReducedComplexSpace
  HironakaG11SingularCentreModification HironakaG11VanishingWindows
  OriginalLocalEmbeddingStalkHS HironakaG11HSPhaseInduction HironakaG11HSMinimalWindows

noncomputable section

/-- In every local embedding into `ℂ^n`, the Hilbert–Samuel function of the point is that of a quotient
of the germ ring `O_n`. -/
theorem exists_ideal_originalStalkHS_eq (Y : SourceReducedComplexSpace) (e : LocalEmbedding Y)
    (c : e.carrier) :
    ∃ I : Ideal (HolGerm (ComplexModel e.dim)), originalStalkHS Y (e.toPoint c) = hilbertSamuelValue I :=
  ⟨_, funext fun ℓ => originalStalkHS_localEmbedding_eq Y e c ℓ⟩

/-- **The Hilbert–Samuel function of a point is a diagram counting function** in `ℕ^E` as soon as
`H(1) ≤ E + 1`. -/
theorem originalStalkHS_mem_diagramFunctions (Y : SourceReducedComplexSpace) (y : Y.obj.left) {E : ℕ}
    (hE : originalStalkHS Y y 1 ≤ E + 1) : originalStalkHS Y y ∈ diagramFunctions E := by
  obtain ⟨e, hdim, ⟨c, rfl⟩, -⟩ :=
    HironakaG11InvMinimalLocalEmbedding.exists_minimal_localEmbedding_at y isOpen_univ (mem_univ y)
  obtain ⟨I, hI⟩ := exists_ideal_originalStalkHS_eq Y e c
  rw [hI]
  exact hilbertSamuelValue_mem_diagramFunctions (by omega) I

/-- **Bennett's stabilization** (Bennett 1970; BM08 §1 (4)): decreasing sequences of Hilbert–Samuel
functions of points of reduced complex spaces (pointwise order) stabilize. -/
theorem hsStabilization : HSStabilization := by
  show WellFoundedLT HSValue
  refine ⟨RelEmbedding.wellFounded_iff_isEmpty.mpr ⟨fun f => ?_⟩⟩
  let g : ℕ → ℕ → ℕ := fun k => (f k).val
  have hanti : StrictAnti g := fun a b hab => Subtype.coe_lt_coe.mpr (f.map_rel_iff.mpr hab)
  have hmem : ∀ k, g k ∈ diagramFunctions (g 0 1) := by
    intro k
    obtain ⟨Y, y, hy⟩ := (f k).property
    have hle : g k 1 ≤ g 0 1 := hanti.antitone (Nat.zero_le k) 1
    change (f k).val 1 ≤ g 0 1 at hle
    change (f k).val ∈ diagramFunctions (g 0 1)
    rw [← hy] at hle ⊢
    exact originalStalkHS_mem_diagramFunctions Y y (by omega)
  exact not_strictAnti_of_mem_diagramFunctions g hmem hanti

/-- **G11 from Hilbert–Samuel phase data** (Bennett's stabilization discharged). -/
theorem compactSingularCentreResolution_of_hsPhaseData'
    (hP : ∀ (X : SourceReducedComplexSpace) [CompactSpace X.obj.left], ¬X.IsSmooth →
      ∀ a ∈ intrinsicSingularLocus X.obj,
        (∀ x ∈ intrinsicSingularLocus X.obj,
          toLex (originalStalkHS X x) ≤ toLex (originalStalkHS X a)) →
        HSPhaseData X (originalStalkHS X a)) :
    CompactSingularCentreResolution :=
  compactSingularCentreResolution_of_hsPhaseData hsStabilization hP

/-- **G11 from records on minimal windows** (Bennett's stabilization discharged): the only remaining
input is `HSRecords` on small minimal windows. -/
theorem compactSingularCentreResolution_of_hsRecords'
    (hrec : ∀ (X : SourceReducedComplexSpace) [CompactSpace X.obj.left], ¬X.IsSmooth →
      ∀ a ∈ intrinsicSingularLocus X.obj,
        (∀ x ∈ intrinsicSingularLocus X.obj,
          toLex (originalStalkHS X x) ≤ toLex (originalStalkHS X a)) →
        ∃ Nb : X.obj.left → Set X.obj.left,
          (∀ x ∈ hsStratum X (originalStalkHS X a), IsOpen (Nb x) ∧ x ∈ Nb x) ∧
          ∀ (ι : Type) [Finite ι] (w : ι → DimEmbedding X (originalStalkHS X a 1 - 1)),
            (∀ i, ∃ x ∈ hsStratum X (originalStalkHS X a),
              range (w i).toLocalEmbedding.toPoint ⊆ Nb x) →
            HSRecords w (originalStalkHS X a)) :
    CompactSingularCentreResolution :=
  compactSingularCentreResolution_of_hsRecords hsStabilization hrec

end

end Hironaka.Analytic.Unibranch.HironakaG11BennettStabilization
