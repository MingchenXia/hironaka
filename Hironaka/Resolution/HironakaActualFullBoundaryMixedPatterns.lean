import Hironaka.Resolution.HironakaActualFullBoundaryContainmentPatterns
import Hironaka.Resolution.HironakaG34NonPureLowDim
import Hironaka.Resolution.HironakaSharpOriginalAllBoundaryCentre

/-!
# Mixed-dimensional full-boundary containment pieces

A smooth closed carrier decomposes into finitely many closed smooth pieces
classified by local dimension and containment in the original ordered boundary.
The pieces admit isolating opens, and a retained boundary on a piece cannot
introduce a sharp bad point where the full original carrier and boundary were good.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaActualFullBoundaryMixedPatterns

noncomputable section

open Hironaka.BlowupSequences BlowupTowers NormalCrossings NormalCrossingsComparison
  HironakaEmbeddedAnalytic HironakaActualFullBoundaryContainmentPatterns HironakaG34NonPureLowDim
  HironakaSharpOriginalMultiBoundaryBadLocus HironakaSharpNormalCrossingsOpenLocus
  HironakaSharpOriginalAllBoundaryCentre

universe u

variable {n : ℕ} {X : CMfd.{u} n}

/-- An original sharp bad point for the retained boundary of an open-and-closed
carrier piece is also bad for the full original carrier and boundary. -/
theorem sharpBad_subset_full_of_carrier_germs {W A : Set X} {E F : List (Set X)}
    (hW : IsClosed W) (hE : IsSNCDivisor n E) (hF : F.Sublist E) (hA : A ⊆ W)
    (hGerm : ∀ x ∈ A, ∀ᶠ y in 𝓝 x, y ∈ A ↔ y ∈ W) :
    originalSharpBadLocus (n := n) A F ⊆ originalSharpBadLocus (n := n) W E ∩ A := by
  intro x hx
  refine ⟨⟨hA hx.1, ?_⟩, hx.1⟩
  intro hNC
  obtain ⟨O, hOsub, hO, hxO⟩ := mem_nhds_iff.mp
    ((eventually_normalCrossingsAt hW hE.1 hNC).and (hGerm x hx.1))
  let U : Opens X := ⟨O, hO⟩
  let EU := E.map ((Subtype.val : U → X) ⁻¹' ·)
  let FU := F.map ((Subtype.val : U → X) ⁻¹' ·)
  have hEq : (Subtype.val : U → X) ⁻¹' A = (Subtype.val : U → X) ⁻¹' W :=
    Set.ext fun y => (hOsub y.property).2
  have hNCU : HasNormalCrossings n ((Subtype.val : U → X) ⁻¹' W) EU := by
    intro y _
    exact normalCrossingsAt_preimage_val_iff.mpr (hOsub y.property).1
  have hNCF : HasNormalCrossings n ((Subtype.val : U → X) ⁻¹' A) FU := by
    rw [hEq]
    exact hasNormalCrossings_of_forall_mem hNCU (fun _ h => (hF.map _).subset h)
  exact hx.2 (normalCrossingsAt_preimage_val_iff.mp (hNCF (⟨x, hxO⟩ : U) hx.1))

/-- The mixed-dimensional containment pieces and their isolating opens are
selected from the full original smooth carrier and SNC boundary. -/
theorem mixed_dimension_containment_patterns {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E) :
    let ι := Fin (n + 1) × Finset (Fin E.length)
    let D : Fin (n + 1) → Set X := fun d => dimPiece W d.val
    let A : ι → Set X := fun P => patternPiece (D P.1) E P.2
    (∀ d x, x ∈ D d → ∀ᶠ y in 𝓝 x, y ∈ D d ↔ y ∈ W) ∧
    (∀ d x, x ∈ D d → RegularAtDim (n := n) (D d) x d.val) ∧
    (∀ d, IsClosedSubmanifold n (D d)) ∧
    (∀ P, IsClosedSubmanifold n (A P)) ∧
    (⋃ P : ι, A P) = W ∧
    ∃ V : ι → Opens X, (∀ P, A P ⊆ V P) ∧
      ∀ P R, P ≠ R → Disjoint (V P : Set X) (A R) := by
  classical
  let ι := Fin (n + 1) × Finset (Fin E.length)
  let D : Fin (n + 1) → Set X := fun d => dimPiece W d.val
  let A : ι → Set X := fun P => patternPiece (D P.1) E P.2
  have hDgerm (d : Fin (n + 1)) (x : X) (hx : x ∈ D d) :
      ∀ᶠ y in 𝓝 x, y ∈ D d ↔ y ∈ W := by
    filter_upwards [RegularPatchNeighborhood.eventually_regularAtDim hx.2] with y hy
    exact ⟨fun h => h.1, fun h => ⟨h, hy h⟩⟩
  have hDreg (d : Fin (n + 1)) (x : X) (hx : x ∈ D d) :
      RegularAtDim (n := n) (D d) x d.val :=
    CodimOneSupport.regularAtDim_of_eventually_mem_iff ((hDgerm d x hx).mono fun _ h => h.symm) hx.2
  have hD (d : Fin (n + 1)) : IsClosedSubmanifold n (D d) :=
    ⟨isClosed_dimPiece hW d.val, fun x hx => ⟨d.val, hDreg d x hx⟩⟩
  have hAW (P : ι) : A P ⊆ W :=
    (patternPiece_subset (D P.1) E P.2).trans (dimPiece_subset W P.1.val)
  have hA (P : ι) : IsClosedSubmanifold n (A P) :=
    isClosedSubmanifold_patternPiece (hD P.1) hE (hDreg P.1) P.2
  have hCover : (⋃ P : ι, A P) = W := by
    apply Subset.antisymm
    · exact iUnion_subset hAW
    · intro x hx
      obtain ⟨k, hk⟩ := hW.2 x hx
      let d : Fin (n + 1) := ⟨k, Nat.lt_succ_of_le hk.1⟩
      have hxD : x ∈ D d := ⟨hx, hk⟩
      obtain ⟨P, hxP⟩ := mem_iUnion.mp ((iUnion_patternPiece (D d) E).symm ▸ hxD)
      exact mem_iUnion.mpr ⟨(d, P), hxP⟩
  have hDisjoint : Pairwise (fun P R : ι => Disjoint (A P) (A R)) := by
    intro P R hPR
    rcases P with ⟨d, P⟩
    rcases R with ⟨e, R⟩
    by_cases hde : d = e
    · subst e
      exact pairwise_disjoint_patternPiece (D d) E (fun h => hPR (Prod.ext rfl h))
    · apply disjoint_left.mpr
      intro x hx hy
      have hxD := patternPiece_subset (D d) E P hx
      have hyD := patternPiece_subset (D e) E R hy
      exact hde (Fin.ext (RegularPointDimension.eq_of_regularAtDim hxD.2 hyD.2))
  let V : ι → Opens X := fun P =>
    ⟨(⋃ R : {R : ι // R ≠ P}, A R.val)ᶜ,
      (isClosed_iUnion_of_finite fun R : {R : ι // R ≠ P} => (hA R.val).1).isOpen_compl⟩
  have hAV (P : ι) : A P ⊆ V P := by
    intro x hx hUnion
    obtain ⟨R, hxR⟩ := mem_iUnion.mp hUnion
    exact disjoint_left.mp (hDisjoint R.property) hxR hx
  have hSep (P R : ι) (hPR : P ≠ R) : Disjoint (V P : Set X) (A R) :=
    disjoint_left.mpr fun x hx hR => hx (mem_iUnion.mpr ⟨⟨R, Ne.symm hPR⟩, hR⟩)
  exact ⟨hDgerm, hDreg, hD, hA, hCover, V, hAV, hSep⟩

end
end Hironaka.HironakaActualFullBoundaryMixedPatterns
