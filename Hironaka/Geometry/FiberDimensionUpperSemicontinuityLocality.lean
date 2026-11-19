import Hironaka.Geometry.FiberDimensionUpperSemicontinuityClosedCover

/-!
# Noetherian closed-set induction and actual preimmersion fiber comparisons

The closed-locus criterion is proved by the native well-founded order of
closed subsets. The geometric comparison constructs the literal native
fiber map and its isomorphism from the actual residue-field map.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hironaka.Geometry.FiberDimensionUpperSemicontinuityLocality

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A Noetherian closed-set induction criterion with actual relatively open witnesses. -/
theorem isClosed_of_irreducible_closed_dichotomy
    {T : Type u} [TopologicalSpace T] [NoetherianSpace T] (E : Set T)
    (h : ∀ C : Closeds T, IsIrreducible (C : Set T) →
      (C : Set T) ⊆ E ∨ ∃ V : Set C, IsOpen V ∧ V.Nonempty ∧
        Disjoint V (Subtype.val ⁻¹' E)) : IsClosed E := by
  have hclosed (C : Closeds T) : IsClosed ((C : Set T) ∩ E) := by
    apply wellFounded_lt.induction C
    clear C
    intro C ih
    by_cases hzero : C = ⊥
    · simp [hzero]
    by_cases hpre : IsPreirreducible (C : Set T)
    · obtain hCE | ⟨V, hV, hne, hdis⟩ := h C ⟨Closeds.coe_nonempty.mpr hzero, hpre⟩
      · simpa only [Set.inter_eq_left.mpr hCE] using C.isClosed
      · obtain ⟨U, hU, hUV⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp hV
        let D : Closeds T := C ⊓ ⟨Uᶜ, hU.isClosed_compl⟩
        have hD : D < C := by
          apply inf_lt_left.mpr
          intro hCU
          obtain ⟨v, hv⟩ := hne
          have hvU : v.val ∈ U := by
            exact (congrArg (fun A : Set C ↦ v ∈ A) hUV).mpr hv
          exact hCU v.property hvU
        have hEq : (C : Set T) ∩ E = (D : Set T) ∩ E := by
          ext x
          constructor
          · rintro ⟨hxC, hxE⟩
            refine ⟨⟨hxC, ?_⟩, hxE⟩
            intro hxU
            have hxV : (⟨x, hxC⟩ : C) ∈ V := by
              rw [← hUV]
              exact hxU
            exact Set.disjoint_left.mp hdis hxV hxE
          · rintro ⟨⟨hxC, -⟩, hxE⟩
            exact ⟨hxC, hxE⟩
        rw [hEq]
        exact ih D hD
    · simp only [isPreirreducible_iff_isClosed_union_isClosed, not_forall, not_or] at hpre
      obtain ⟨A, B, hA, hB, hcover, hCA, hCB⟩ := hpre
      let A' : Closeds T := ⟨A, hA⟩
      let B' : Closeds T := ⟨B, hB⟩
      have ha := ih (C ⊓ A') (inf_lt_left.mpr hCA)
      have hb := ih (C ⊓ B') (inf_lt_left.mpr hCB)
      have hEq : (C : Set T) ∩ E =
          ((C ⊓ A' : Closeds T) : Set T) ∩ E ∪ ((C ⊓ B' : Closeds T) : Set T) ∩ E := by
        ext x
        constructor
        · rintro ⟨hxC, hxE⟩
          rcases hcover hxC with hxA | hxB
          · exact Or.inl ⟨⟨hxC, hxA⟩, hxE⟩
          · exact Or.inr ⟨⟨hxC, hxB⟩, hxE⟩
        · rintro (⟨⟨hxC, -⟩, hxE⟩ | ⟨⟨hxC, -⟩, hxE⟩)
          · exact ⟨hxC, hxE⟩
          · exact ⟨hxC, hxE⟩
      rw [hEq]
      exact ha.union hb
  simpa using hclosed ⊤

variable {X' S' X S : Scheme.{u}} {iX : X' ⟶ X} {f' : X' ⟶ S'}
  {f : X ⟶ S} {iS : S' ⟶ S}

/-- The actual native fiber map of the original Cartesian square. -/
def baseChangeFiberMap (h : IsPullback iX f' f iS) (s : S') :
    f'.fiber s ⟶ f.fiber (iS s) :=
  pullback.map _ _ _ _ iX (Spec.map (iS.residueFieldMap s)) iS h.w.symm (by simp)

/-- The actual fiber comparison is Cartesian over the original residue-field map. -/
theorem baseChangeFiberMap_isPullback (h : IsPullback iX f' f iS) (s : S') :
    IsPullback (baseChangeFiberMap h s) (f'.fiberToSpecResidueField s)
      (f.fiberToSpecResidueField (iS s)) (Spec.map (iS.residueFieldMap s)) :=
  isPullback_fiberToSpecResidueField_of_isPullback h s

/-- Actual preimmersion base changes have actual isomorphic original scheme fibers. -/
instance baseChangeFiberMap_isIso [IsPreimmersion iS]
    (h : IsPullback iX f' f iS) (s : S') : IsIso (baseChangeFiberMap h s) := by
  let : IsIso (iS.residueFieldMap s) :=
    FiberDimensionComponentLowerBoundBaseChange.residueFieldMap_isIso_of_preimmersion iS s
  exact (baseChangeFiberMap_isPullback h s).isIso_fst_of_isIso

/-- Native actual fiber dimension is unchanged by the original preimmersion base change. -/
theorem fiberDimension_eq_of_preimmersion_isPullback [IsPreimmersion iS]
    (h : IsPullback iX f' f iS) (s : S') :
    FiberDimension.fiberDimension f' s = FiberDimension.fiberDimension f (iS s) :=
  IsHomeomorph.topologicalKrullDim_eq _ (baseChangeFiberMap h s).homeomorph.isHomeomorph

end Hironaka.Geometry.FiberDimensionUpperSemicontinuityLocality
