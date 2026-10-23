/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.CurvesField.GenusEuler
import DeJongAlterations.Geometry.ProperSteinProjectiveCechSubsetNonemptyExactness

/-!
# The δ-formula for Čech complexes of diagrams

The Čech-complex form of the long exact sequence in the proof of Lemma B.1 of M. Temkin,
*Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification`, `semi-stable.tex`, lines 4416–4433).

Let `α : D₁ ⟶ D₂` be a map of diagrams `Finset ι ⥤ ModuleCat k` (in the application
`D₁(T) = Γ(U_T, 𝒪_C)`, `D₂(T) = Γ(π⁻¹U_T, 𝒪_{C̃})` for a finite affine cover `U` of `C` and the
normalization `π : C̃ → C`) which is injective on nonempty subsets with finite-dimensional
cokernels `Q(T) = D₂(T) / D₁(T)`. The termwise cokernels form a diagram `cokerDiagram α`, the
Čech complexes form a short exact sequence `0 → Č(D₁) → Č(D₂) → Č(Q) → 0`, and the Euler
characteristic of `Č(Q)` is computed from its terms:
`χ(Č(D₂)) = χ(Č(D₁)) + ∑_{T ≠ ∅} (-1)^{#T - 1} dim_k Q(T)` (`sum_homology_cech_of_injective`).
This replaces the sheaf `π_*𝒪_{C̃}/𝒪_C` and its cohomology in Temkin's argument by the explicit
termwise cokernel; no sheafification is needed.

Blueprint: `sm-curves-fields-genus.tex`, `lem:sm-cech-delta`.
-/

namespace DeJongAlterations.StableModification.CurvesField.Genus

open CategoryTheory Module Finset DeJongAlterations.Geometry.ProperSteinProjectiveCech

set_option autoImplicit false

universe u

variable {k : Type u} [Field k] {ι : Type u} [LinearOrder ι]
  {D₁ D₂ : Finset ι ⥤ ModuleCat.{u} k} (α : D₁ ⟶ D₂)

/-- The termwise cokernel `T ↦ D₂(T) / α(D₁(T))` of a map of subset diagrams. -/
noncomputable def cokerDiagram : Finset ι ⥤ ModuleCat.{u} k where
  obj T := ModuleCat.of k (D₂.obj T ⧸ LinearMap.range (α.app T).hom)
  map {S T} h := ModuleCat.ofHom (Submodule.mapQ _ _ (D₂.map h).hom (by
    rintro _ ⟨x, rfl⟩
    exact ⟨D₁.map h x, ConcreteCategory.congr_hom (α.naturality h) x⟩))
  map_id T := by
    ext x
    change Submodule.Quotient.mk ((D₂.map (𝟙 T)).hom x) = Submodule.Quotient.mk x
    rw [D₂.map_id]
    rfl
  map_comp {S T W} h h' := by
    ext x
    change Submodule.Quotient.mk ((D₂.map (h ≫ h')).hom x) =
      Submodule.Quotient.mk ((D₂.map h').hom ((D₂.map h).hom x))
    rw [D₂.map_comp]
    rfl

/-- The projection onto the cokernel diagram. -/
noncomputable def cokerDiagramπ : D₂ ⟶ cokerDiagram α where
  app T := ModuleCat.ofHom (LinearMap.range (α.app T).hom).mkQ
  naturality {S T} h := by
    ext x
    rfl

omit [LinearOrder ι] in
lemma cokerDiagram_obj (T : Finset ι) :
    (cokerDiagram α).obj T = ModuleCat.of k (D₂.obj T ⧸ LinearMap.range (α.app T).hom) := rfl

variable {α}

omit [LinearOrder ι] in
/-- On nonempty subsets, `D₁ → D₂ → Q` is short exact when `α` is injective there. -/
lemma cokerDiagram_local (hinj : ∀ T : Finset ι, T.Nonempty → Function.Injective (α.app T).hom)
    (S : Finset ι) (hS : S.Nonempty) :
    Function.Exact (α.app S).hom ((cokerDiagramπ α).app S).hom ∧
      Function.Injective (α.app S).hom ∧ Function.Surjective ((cokerDiagramπ α).app S).hom :=
  ⟨LinearMap.exact_iff.2 (Submodule.ker_mkQ _), hinj S hS, Submodule.mkQ_surjective _⟩

/-- The short exact sequence `0 → Č(D₁) → Č(D₂) → Č(Q) → 0`. -/
theorem cechCoker_shortExact
    (hinj : ∀ T : Finset ι, T.Nonempty → Function.Injective (α.app T).hom) :
    (SubsetNonemptyExactness.sequence α (cokerDiagramπ α) (cokerDiagram_local hinj)).ShortExact :=
  SubsetNonemptyExactness.sequence_shortExact α (cokerDiagramπ α) (cokerDiagram_local hinj)

section Terms

variable [Fintype ι] (D : Finset ι ⥤ ModuleCat.{u} k)

omit [LinearOrder ι] in
/-- The degree-`n` piece of the cube is the product of the values on subsets of cardinality
`n`; its dimension is the sum of their dimensions. -/
theorem finrank_subsetCechCardPiece (n : ℕ)
    (hD : ∀ T : Finset ι, T.card = n → FiniteDimensional k (D.obj T)) :
    FiniteDimensional k (subsetCechCardPiece D n) ∧
      finrank k (subsetCechCardPiece D n) =
        ∑ T ∈ univ.filter (fun T : Finset ι => T.card = n), finrank k (D.obj T) := by
  classical
  have : ∀ S : {S : Finset ι // S.card = n}, FiniteDimensional k (D.obj S.val) :=
    fun S => hD S.1 S.2
  let e := subsetCechCardProductEquiv D n
  refine ⟨Module.Finite.equiv e.symm, ?_⟩
  rw [e.finrank_eq, Module.finrank_pi_fintype]
  rw [Finset.sum_subtype (univ.filter (fun T : Finset ι => T.card = n))
    (p := fun T : Finset ι => T.card = n) (by simp)]

/-- The subset Čech complex vanishes in degrees `≥ #ι`. -/
lemma subsingleton_subsetCechComplex_X (i : ℕ) (hi : Fintype.card ι ≤ i) :
    Subsingleton ((subsetCechComplex D).X i) := by
  change Subsingleton (subsetCechCardPiece D (i + 1))
  rw [subsetCechCardPiece_eq_bot D (i + 1) (by omega)]
  infer_instance

/-- The homology of the subset Čech complex vanishes in degrees `≥ #ι`. -/
lemma subsingleton_subsetCechComplex_homology (i : ℕ) (hi : Fintype.card ι ≤ i) :
    Subsingleton ((subsetCechComplex D).homology i) := by
  have := subsingleton_subsetCechComplex_X D i hi
  have hz : Limits.IsZero ((subsetCechComplex D).X i) := ModuleCat.isZero_of_subsingleton _
  have : Limits.IsZero ((subsetCechComplex D).homology i) :=
    ShortComplex.isZero_homology_of_isZero_X₂ _ hz
  exact ModuleCat.subsingleton_of_isZero this

omit [LinearOrder ι] in
/-- Reindexing the alternating sum over degrees as a sum over nonempty subsets. -/
lemma sum_range_card_eq_sum_nonempty (d : Finset ι → ℤ) :
    ∑ i ∈ range (Fintype.card ι), (-1 : ℤ) ^ i *
        ∑ T ∈ univ.filter (fun T : Finset ι => T.card = i + 1), d T =
      ∑ T ∈ univ.filter (fun T : Finset ι => T.Nonempty), (-1 : ℤ) ^ (T.card + 1) * d T := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ.filter (fun T : Finset ι => T.Nonempty))
    (t := range (Fintype.card ι)) (g := fun T => T.card - 1)]
  · refine sum_congr rfl fun i _ => ?_
    rw [mul_sum]
    refine sum_congr ?_ fun T hT => ?_
    · ext T
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · intro h
        exact ⟨Finset.card_pos.1 (by omega), by omega⟩
      · rintro ⟨h₁, h₂⟩
        have := Finset.card_pos.2 h₁
        omega
    · simp only [mem_filter, mem_univ, true_and] at hT
      obtain ⟨h1, h2⟩ := hT
      have := Finset.card_pos.2 h1
      have hc : T.card = i + 1 := by omega
      rw [hc, pow_succ, pow_succ]
      ring
  · intro T hT
    simp only [mem_filter, mem_univ, true_and] at hT
    simp only [mem_range]
    have := Finset.card_le_univ T
    have := Finset.card_pos.2 hT
    omega

end Terms

/-- **The δ-formula for Čech complexes of diagrams.** Let `α : D₁ ⟶ D₂` be injective on nonempty
subsets, with finite-dimensional cokernels there, and let the Čech cohomology of `D₁` be
finite-dimensional. Then the Čech cohomology of `D₂` is finite-dimensional and
`χ(Č(D₂)) = χ(Č(D₁)) + ∑_{T ≠ ∅} (-1)^{#T + 1} dim_k (D₂(T) / D₁(T))`. -/
theorem sum_homology_cech_of_injective [Fintype ι]
    (hinj : ∀ T : Finset ι, T.Nonempty → Function.Injective (α.app T).hom)
    (hfin : ∀ T : Finset ι, T.Nonempty →
      FiniteDimensional k (D₂.obj T ⧸ LinearMap.range (α.app T).hom))
    [h₁ : ∀ i, FiniteDimensional k ((subsetCechComplex D₁).homology i)] :
    (∀ i, FiniteDimensional k ((subsetCechComplex D₂).homology i)) ∧
      ∑ i ∈ range (Fintype.card ι), (-1 : ℤ) ^ i *
          finrank k ((subsetCechComplex D₂).homology i) =
        ∑ i ∈ range (Fintype.card ι), (-1 : ℤ) ^ i *
            finrank k ((subsetCechComplex D₁).homology i) +
          ∑ T ∈ univ.filter (fun T : Finset ι => T.Nonempty), (-1 : ℤ) ^ (T.card + 1) *
            finrank k (D₂.obj T ⧸ LinearMap.range (α.app T).hom) := by
  classical
  have hS := cechCoker_shortExact hinj
  set S := SubsetNonemptyExactness.sequence α (cokerDiagramπ α) (cokerDiagram_local hinj)
  -- the cokernel complex has finite-dimensional terms
  have hQX : ∀ i, FiniteDimensional k ((subsetCechComplex.{u, u} (cokerDiagram α)).X i) := by
    intro i
    have : ∀ T : Finset ι, T.card = i + 1 → FiniteDimensional k ((cokerDiagram α).obj T) :=
      fun T hT => hfin T (Finset.card_pos.1 (by omega))
    exact (finrank_subsetCechCardPiece (cokerDiagram α) (i + 1) this).1
  have hQH : ∀ i, FiniteDimensional k ((subsetCechComplex.{u, u} (cokerDiagram α)).homology i) :=
    fun i => finiteDimensional_homology_of_X _ i
  have h₂ : ∀ i, FiniteDimensional k ((subsetCechComplex.{u, u} D₂).homology i) := fun i => by
    have : FiniteDimensional k (S.X₁.homology i) := h₁ i
    have : FiniteDimensional k (S.X₃.homology i) := hQH i
    exact finiteDimensional_homology_X₂ hS i
  refine ⟨h₂, ?_⟩
  have : ∀ i, FiniteDimensional k (S.X₁.homology i) := h₁
  have : ∀ i, FiniteDimensional k (S.X₂.homology i) := h₂
  have : ∀ i, FiniteDimensional k (S.X₃.homology i) := hQH
  have hsum : ∑ i ∈ range (Fintype.card ι), (-1 : ℤ) ^ i *
        finrank k ((subsetCechComplex.{u, u} D₂).homology i) =
      ∑ i ∈ range (Fintype.card ι), (-1 : ℤ) ^ i *
          finrank k ((subsetCechComplex.{u, u} D₁).homology i) +
        ∑ i ∈ range (Fintype.card ι), (-1 : ℤ) ^ i *
          finrank k ((subsetCechComplex.{u, u} (cokerDiagram α)).homology i) :=
    sum_finrank_homology_of_shortExact hS (Fintype.card ι)
      (subsingleton_subsetCechComplex_homology D₁)
  rw [hsum]
  congr 1
  have := sum_finrank_homology_eq_sum_finrank_X (subsetCechComplex.{u, u} (cokerDiagram α))
    (Fintype.card ι) (subsingleton_subsetCechComplex_X _)
  change ∑ i ∈ range (Fintype.card ι), (-1 : ℤ) ^ i *
    finrank k ((subsetCechComplex.{u, u} (cokerDiagram α)).homology i) = _
  rw [this]
  rw [← sum_range_card_eq_sum_nonempty]
  refine sum_congr rfl fun i _ => ?_
  congr 1
  have : ∀ T : Finset ι, T.card = i + 1 → FiniteDimensional k ((cokerDiagram α).obj T) :=
    fun T hT => hfin T (Finset.card_pos.1 (by omega))
  change (finrank k (subsetCechCardPiece.{u, u} (cokerDiagram α) (i + 1)) : ℤ) = _
  rw [(finrank_subsetCechCardPiece (cokerDiagram α) (i + 1) this).2]
  push_cast
  rfl

end DeJongAlterations.StableModification.CurvesField.Genus
