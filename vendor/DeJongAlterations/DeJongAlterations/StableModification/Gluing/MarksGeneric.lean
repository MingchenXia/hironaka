/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane T45B)
-/
import DeJongAlterations.StableModification.Gluing.MarksSections
import DeJongAlterations.StableModification.Blowups.TransportSection

/-!
# The generic marks are finitely many sections

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), proof of
Lemma 4.3.3 (`divlem`, T:3025–3027): "the assumptions that `K` is separably closed and `D_η` is
`K`-smooth imply that `D_η` is a union of few smooth `K`-points". Over a valuation ring `V` whose
fraction field is separably closed, and for a proper `φ : C → Spec V` whose generic marks
`D_η = D ×_C C_η` are étale over `κ(η) = Frac V`, the points of `D` over the generic point are
finitely many, and each is the generic point of a unique section `σₖ : Spec V → C`
(`exists_sections_of_etale_genericMarks`).

The generic point of `Spec V` is `⊥ : PrimeSpectrum V`; we state the result at this point (as
the generic point `genericPoint (Spec V)` equals `⊥` only propositionally,
`genericPoint_eq_bot_of_affine`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace DeJongAlterations.StableModification.Gluing.StableVal

set_option backward.isDefEq.respectTransparency false

section ResidueField

/-- The residue field of an algebraically closed field is algebraically closed. -/
theorem isAlgClosed_residueField_of_field (F : Type u) [Field F] [IsAlgClosed F] :
    IsAlgClosed (IsLocalRing.ResidueField F) := by
  have hbij : Function.Bijective (IsLocalRing.residue F) :=
    ⟨(IsLocalRing.residue F).injective, IsLocalRing.residue_surjective⟩
  exact IsAlgClosed.of_ringEquiv F _ (RingEquiv.ofBijective _ hbij)

end ResidueField

section Generic

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
  {C : Scheme.{u}} (φ : C ⟶ Spec (.of V)) [IsProper φ] (D : C.IdealSheafData)

/-- The generic point `⊥` of `Spec V`, as the point `⟨⊥, _⟩` (so that its ideal is `⊥` by
`rfl`). -/
abbrev pt₀ : Spec (.of V) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V)

omit [ValuationRing V] in
theorem genericPoint_eq_pt₀ : genericPoint (Spec (.of V)) = pt₀ :=
  (genericPoint_eq_bot_of_affine _).trans (PrimeSpectrum.ext rfl)

omit [ValuationRing V] in
theorem genericPt₀_apply' (z : Spec (.of (⊥ : Ideal V).ResidueField)) : genericPt₀ z = pt₀ :=
  (genericPt₀_apply z).trans genericPoint_eq_pt₀

/-- **The generic marks are finitely many sections** (Temkin, proof of Lemma 4.3.3, T:3025–3027).
Let `φ : C → Spec V` be proper, `D ⊆ C` closed, and assume that the residue field `κ(⊥)` of the
generic point is algebraically closed and that the generic marks `D_⊥ = D ×_C C_⊥` are étale over
`κ(⊥)`. Then there are finitely many sections `σₖ` of `φ` with pairwise distinct generic points,
which are exactly the points of `D` over the generic point. -/
theorem exists_sections_of_etale_genericMarks
    [IsAlgClosed ((Spec (.of V)).residueField pt₀)]
    (he : Etale ((DeJong.fiberMarks φ D pt₀).subschemeι ≫
      φ.fiberToSpecResidueField pt₀)) :
    ∃ (n : ℕ) (σ : Fin n → (Spec (.of V) ⟶ C)), (∀ k, σ k ≫ φ = 𝟙 _) ∧
      Function.Injective (fun k ↦ σ k pt₀) ∧
      ∀ x : C, φ x = pt₀ →
        (x ∈ (D.support : Set C) ↔ ∃ k, σ k pt₀ = x) := by
  classical
  set t₀ : Spec (.of V) := pt₀
  set Dη := DeJong.fiberMarks φ D t₀
  set p := Dη.subschemeι ≫ φ.fiberToSpecResidueField t₀
  set j := Dη.subschemeι ≫ φ.fiberι t₀
  let M : Set C := {x | φ x = t₀ ∧ x ∈ (D.support : Set C)}
  have hcond : φ.fiberι t₀ ≫ φ =
      φ.fiberToSpecResidueField t₀ ≫ (Spec (.of V)).fromSpecResidueField t₀ :=
    pullback.condition
  -- every point of `M` comes from the subscheme `Dη`
  have hM : ∀ x ∈ M, ∃ z, j z = x := by
    rintro x ⟨hx, hxD⟩
    have : x ∈ Set.range (φ.fiberι t₀) := by rw [Scheme.Hom.range_fiberι]; exact hx
    obtain ⟨y, rfl⟩ := this
    have hy : y ∈ (Dη.support : Set _) := by
      change y ∈ ((D.comap (φ.fiberι t₀)).support : Set _)
      rw [Scheme.IdealSheafData.support_comap]
      exact hxD
    rw [← Scheme.IdealSheafData.range_subschemeι] at hy
    obtain ⟨z, rfl⟩ := hy
    exact ⟨z, rfl⟩
  -- the subscheme `Dη` is finite
  let κ := (Spec (.of V)).residueField t₀
  have hsub : Subsingleton (Spec κ) := inferInstanceAs (Subsingleton (PrimeSpectrum _))
  have hfin : (Set.univ : Set Dη.subscheme).Finite := by
    have h := p.finite_preimage_singleton (IsLocalRing.closedPoint κ)
    convert h using 1
    ext z
    simp only [Set.mem_univ, Set.mem_preimage, Set.mem_singleton_iff, true_iff]
    exact Subsingleton.elim _ _
  have hMfin : M.Finite := (hfin.image j).subset fun x hx ↦ by
    obtain ⟨z, hz⟩ := hM x hx
    exact ⟨z, trivial, hz⟩
  -- each point of `M` is the generic point of a section
  have hsec : ∀ x ∈ M, ∃ σ : Spec (.of V) ⟶ C, σ ≫ φ = 𝟙 _ ∧ σ t₀ = x := by
    intro x hx
    obtain ⟨z, rfl⟩ := hM x hx
    have : IsAlgClosed (IsLocalRing.ResidueField κ) := isAlgClosed_residueField_of_field κ
    obtain ⟨s, hs, hsz⟩ := Blowups.exists_section_of_etale (V := κ) p z (Subsingleton.elim _ _)
    let P₀ := s ≫ j
    have hP₀ : P₀ ≫ φ = (Spec (.of V)).fromSpecResidueField t₀ := by
      simp only [P₀, j, Category.assoc]
      rw [hcond, ← Category.assoc Dη.subschemeι, ← Category.assoc s]
      change (s ≫ p) ≫ _ = _
      rw [hs, Category.id_comp]
    let P := Spec.map (Scheme.Spec.residueFieldIso (.of V) t₀).hom ≫ P₀
    have hP : P ≫ φ = genericPt₀ ≫ 𝟙 _ := by
      simp only [P, Category.assoc, Category.comp_id]
      rw [hP₀, ← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField, ← Category.assoc,
        ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.id_comp]
    obtain ⟨σ, ⟨hσ, hσP⟩, -⟩ := existsUnique_lift φ (𝟙 _) P hP
    refine ⟨σ, hσ, ?_⟩
    obtain ⟨w⟩ : Nonempty (Spec (.of (⊥ : Ideal V).ResidueField)) := inferInstance
    have hw : genericPt₀ w = t₀ := genericPt₀_apply' w
    calc σ t₀ = σ (genericPt₀ w) := by rw [hw]
      _ = (genericPt₀ ≫ σ) w := (Scheme.Hom.comp_apply _ _ _).symm
      _ = P w := by rw [hσP]
      _ = j (s (Spec.map (Scheme.Spec.residueFieldIso (.of V) t₀).hom w)) := rfl
      _ = j z := by
        rw [Subsingleton.elim (Spec.map (Scheme.Spec.residueFieldIso (.of V) t₀).hom w)
          (IsLocalRing.closedPoint κ), hsz]
  choose σx hσx using hsec
  have : Finite M := hMfin.to_subtype
  let e := Finite.equivFin M
  refine ⟨Nat.card M, fun k ↦ σx (e.symm k) (e.symm k).2, fun k ↦ (hσx _ (e.symm k).2).1, ?_, ?_⟩
  · intro k l hkl
    have h1 : σx (e.symm k) (e.symm k).2 t₀ = (e.symm k : C) := (hσx _ (e.symm k).2).2
    have h2 : σx (e.symm l) (e.symm l).2 t₀ = (e.symm l : C) := (hσx _ (e.symm l).2).2
    have : (e.symm k : C) = e.symm l := by rw [← h1, ← h2]; exact hkl
    exact e.symm.injective (Subtype.ext this)
  · intro x hx
    constructor
    · intro hxD
      refine ⟨e ⟨x, hx, hxD⟩, ?_⟩
      have h := (hσx _ (e.symm (e ⟨x, hx, hxD⟩)).2).2
      simp only [Equiv.symm_apply_apply] at h ⊢
      exact h
    · rintro ⟨k, rfl⟩
      rw [(hσx _ (e.symm k).2).2]
      exact (e.symm k).2.2

end Generic

end DeJongAlterations.StableModification.Gluing.StableVal
