import DeJongAlterations.Geometry.ProjectiveGraphModification
import Mathlib.Topology.Compactness.Compact

/-!
# Actual finite affine covers and their common dense open for Chow's lemma

Every chosen affine open contains its indexing point. Compactness then
extracts a finite list of nonempty affine opens covering the actual scheme.
For an integral scheme, their common open contains the actual generic point.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

namespace DeJongAlterations.Geometry.ChowLemmaAffineCover

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : Scheme.{u}}

/-- An actual finite affine cover with empty pieces discarded by construction. -/
theorem exists_finite_nonempty_affine_cover (X : Scheme.{u}) [CompactSpace X] :
    ∃ L : List X.affineOpens,
      (∀ U ∈ L, (U.1 : Set X).Nonempty) ∧
        (⨆ i : Fin L.length, (L.get i).1) = ⊤ := by
  classical
  let U : X → X.affineOpens := fun x =>
    ⟨(X.affineCover.f (X.affineCover.idx x)).opensRange, isAffineOpen_opensRange _⟩
  have hxU (x : X) : x ∈ (U x).1 := X.affineCover.covers x
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X => ((U x).1 : Set X)) (fun x => (U x).1.isOpen) (by
      intro x _
      exact Set.mem_iUnion.mpr ⟨x, hxU x⟩)
  let L : List X.affineOpens := t.toList.map U
  refine ⟨L, ?_, top_le_iff.mp ?_⟩
  · intro V hV
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hV
    exact ⟨x, hxU x⟩
  · intro x _
    have hx := ht (Set.mem_univ x)
    simp only [Set.mem_iUnion, exists_prop] at hx
    obtain ⟨a, ha, hxa⟩ := hx
    have haL : U a ∈ L := List.mem_map.mpr ⟨a, Finset.mem_toList.mpr ha, rfl⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp haL
    exact Opens.mem_iSup.mpr ⟨i, hi.symm ▸ hxa⟩

/-- The actual finite intersection of the original affine opens. -/
def commonOpen (L : List X.affineOpens) : X.Opens :=
  L.foldr (fun U V => U.1 ⊓ V) ⊤

/-- The actual common open canonically maps into every original affine patch. -/
theorem commonOpen_le_get (L : List X.affineOpens) (i : Fin L.length) :
    commonOpen L ≤ (L.get i).1 := by
  induction L with
  | nil => exact Fin.elim0 i
  | cons U L ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact inf_le_left
    · exact inf_le_right.trans (ih j)

/-- No density certificate is assumed: every original nonempty affine open contains the actual generic point. -/
theorem genericPoint_mem_commonOpen [IsIntegral X] (L : List X.affineOpens)
    (hL : ∀ U ∈ L, (U.1 : Set X).Nonempty) :
    genericPoint X ∈ commonOpen L := by
  induction L with
  | nil => trivial
  | cons U L ih =>
    constructor
    · apply ((genericPoint_spec X).mem_open_set_iff U.1.isOpen).mpr
      simpa only [Set.univ_inter] using hL U (by simp)
    · exact ih (fun V hV => hL V (by simp [hV]))

/-- The actual common open is nonempty, proved internally from its generic point. -/
theorem commonOpen_nonempty [IsIntegral X] (L : List X.affineOpens)
    (hL : ∀ U ∈ L, (U.1 : Set X).Nonempty) :
    Nonempty (commonOpen L).toScheme :=
  ⟨⟨genericPoint X, genericPoint_mem_commonOpen L hL⟩⟩

end DeJongAlterations.Geometry.ChowLemmaAffineCover
