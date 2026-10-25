/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane OM3C)
-/
import DeJongAlterations.StableModification.Cohomology.CurveHypersurface

/-!
# Two hyperplanes without common zero on a fibre over a non-local base

Blueprint `sm-projectivity-relative.tex`, `lem:sm-ltg-two-affines` (PLAN-OM3 §3 step 1). This is
Codex's `Cohomology.exists_linearForms_closedFibre` (two linear forms without common zero on the
closed fibre of a projective curve over a local ring with infinite residue field) for the fibre
over an arbitrary point `𝔭` of `Spec A` with `A ⧸ 𝔭` infinite (typically a closed point of an
affine open of the base, whose residue field is infinite):

* `exists_linearCombination_X_notMem'`: prime avoidance for linear forms, for primes `P` of
  `A[T₀, …, Tₙ]` not containing all the variables and with `P ∩ A ⊆ 𝔭`;
* `exists_linearForm_mem_basicOpen'`: finitely many points of `ℙⁿ_A` over `𝔭` lie in a common
  `D₊(f)`, `f` linear;
* `noetherianSpace_fibre`: the fibre over any point of a quasi-compact morphism of finite type is
  a Noetherian space;
* `exists_linearForms_fibre`: two linear forms whose `D₊` cover the fibre over `𝔭` of a closed
  subscheme of `ℙⁿ_A` with no chains `x ⤳ y ⤳ z` of three distinct points in that fibre.

The proofs are Codex's, with the residue field of the local ring replaced by `A ⧸ 𝔭`.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry MvPolynomial TopologicalSpace

namespace DeJongAlterations.StableModification.Projectivity

noncomputable section

open Cohomology

section LinearForms

variable {A : Type u} [CommRing A] {n : ℕ}

/-- **Prime avoidance for linear forms** over an ideal with infinite quotient: finitely many prime
ideals of `A[T₀, …, Tₙ]` not containing all the variables, whose constants lie in an ideal `𝔭`
with `A ⧸ 𝔭` infinite, avoid a common linear form. -/
theorem exists_linearCombination_X_notMem' (𝔭 : Ideal A) [Infinite (A ⧸ 𝔭)] {ι : Type*}
    (s : Finset ι) (P : ι → Ideal (MvPolynomial (Fin (n + 1)) A)) (hP : ∀ j ∈ s, (P j).IsPrime)
    (hrel : ∀ j ∈ s, ∃ i, X i ∉ P j) (hC : ∀ j ∈ s, ∀ a : A, C a ∈ P j → a ∈ 𝔭) :
    ∃ c : Fin (n + 1) → A, ∀ j ∈ s,
      Fintype.linearCombination A (fun i : Fin (n + 1) => (X i : MvPolynomial (Fin (n + 1)) A))
        c ∉ P j := by
  set lin := Fintype.linearCombination A
    (fun i : Fin (n + 1) => (X i : MvPolynomial (Fin (n + 1)) A))
  by_contra hcon
  push Not at hcon
  let W : ι → Submodule A (Fin (n + 1) → A) := fun j => ((P j).restrictScalars A).comap lin
  have hcov : ⋃ j ∈ s, (W j : Set (Fin (n + 1) → A)) = Set.univ := by
    refine Set.eq_univ_of_forall fun c => ?_
    obtain ⟨j, hj, hc⟩ := hcon c
    exact Set.mem_biUnion hj hc
  obtain ⟨j, hj, hfi⟩ := Submodule.exists_finiteIndex_of_cover hcov
  obtain ⟨i, hi⟩ := hrel j hj
  have hfin : Finite ((Fin (n + 1) → A) ⧸ (W j).toAddSubgroup) :=
    AddSubgroup.finite_quotient_of_finiteIndex
  let σ : A ⧸ 𝔭 → A := Function.surjInv Ideal.Quotient.mk_surjective
  let g : A ⧸ 𝔭 → (Fin (n + 1) → A) ⧸ (W j).toAddSubgroup :=
    fun t => QuotientAddGroup.mk (Pi.single i (σ t))
  have hg : Function.Injective g := by
    intro t t' htt'
    rw [QuotientAddGroup.eq] at htt'
    have hmem : lin (-Pi.single i (σ t) + Pi.single i (σ t')) ∈ P j := htt'
    have hlin : lin (-Pi.single i (σ t) + Pi.single i (σ t')) = C (σ t' - σ t) * X i := by
      rw [map_add, map_neg]
      simp only [lin, Fintype.linearCombination_apply_single, smul_eq_C_mul, map_sub]
      ring
    rw [hlin] at hmem
    have hCm : C (σ t' - σ t) ∈ P j := ((hP j hj).mem_or_mem hmem).resolve_right hi
    have hm := hC j hj _ hCm
    have : Ideal.Quotient.mk 𝔭 (σ t') = Ideal.Quotient.mk 𝔭 (σ t) := by
      rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
      exact hm
    simpa only [σ, Function.surjInv_eq Ideal.Quotient.mk_surjective] using this.symm
  have := Finite.of_injective g hg
  exact not_finite (A ⧸ 𝔭)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **Finitely many points of `ℙⁿ_A` over `𝔭` lie in a common `D₊(f)`, `f` linear**, when
`A ⧸ 𝔭` is infinite. -/
theorem exists_linearForm_mem_basicOpen' (𝔭 : PrimeSpectrum A) [Infinite (A ⧸ 𝔭.asIdeal)]
    {ι : Type*} (s : Finset ι) (y : ι → Proj (projectiveSpaceGrading A n))
    (hy : ∀ j ∈ s, projectiveSpaceStructure A n (y j) = 𝔭) :
    ∃ f ∈ projectiveSpaceGrading A n 1, ∀ j ∈ s,
      y j ∈ Proj.basicOpen (projectiveSpaceGrading A n) f := by
  obtain ⟨c, hc⟩ := exists_linearCombination_X_notMem' 𝔭.asIdeal s
    (fun j => (y j).asHomogeneousIdeal.toIdeal) (fun j _ => (y j).isPrime)
    (fun j _ => exists_X_notMem_asHomogeneousIdeal (y j)) (fun j hj a ha => by
      rw [← hy j hj, mem_projectiveSpaceStructure_asIdeal_iff]
      exact ha)
  exact ⟨_, linearCombination_X_mem_grading c, fun j hj => hc j hj⟩

end LinearForms

section Fibre

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {X : Scheme.{u}} {n : ℕ}

set_option backward.isDefEq.respectTransparency.types false in
/-- The fibre over any point of a quasi-compact morphism locally of finite type is a Noetherian
space. -/
theorem noetherianSpace_fibre {Z : Scheme.{u}} (p : X ⟶ Z) [LocallyOfFiniteType p]
    [QuasiCompact p] (z : Z) : NoetherianSpace (p ⁻¹' {z}) := by
  have : LocallyOfFiniteType (p.fiberToSpecResidueField z) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have : QuasiCompact (p.fiberToSpecResidueField z) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have : CompactSpace (p.fiber z) :=
    QuasiCompact.compactSpace_of_compactSpace (p.fiberToSpecResidueField z)
  have : IsLocallyNoetherian (p.fiber z) :=
    LocallyOfFiniteType.isLocallyNoetherian (p.fiberToSpecResidueField z)
  have : IsNoetherian (p.fiber z) := ⟨⟩
  exact (noetherianSpace_iff_of_homeomorph (p.fiberHomeo z)).mp inferInstance

/-- **Two hyperplanes without common zero on a fibre**: let `i : X → ℙⁿ_A` be a closed immersion
and `𝔭` a closed point of `Spec A` with `A ⧸ 𝔭` infinite, such that the fibre of `X` over `𝔭` has
no chains `x ⤳ y ⤳ z` of three distinct points. Then there are linear forms `f`, `g` such that
`X ∩ D₊(f)` and `X ∩ D₊(g)` cover the fibre over `𝔭`. -/
theorem exists_linearForms_fibre (i : X ⟶ projectiveSpace A n) [IsClosedImmersion i]
    (𝔭 : PrimeSpectrum A) (h𝔭 : IsClosed ({𝔭} : Set (PrimeSpectrum A)))
    [Infinite (A ⧸ 𝔭.asIdeal)]
    (hdim : ∀ x y z : X, (i ≫ projectiveSpaceStructure A n) x = 𝔭 →
      x ⤳ y → y ⤳ z → x = y ∨ y = z) :
    ∃ f ∈ projectiveSpaceGrading A n 1, ∃ g ∈ projectiveSpaceGrading A n 1,
      ∀ x : X, (i ≫ projectiveSpaceStructure A n) x = 𝔭 →
        x ∈ i ⁻¹ᵁ Proj.basicOpen (projectiveSpaceGrading A n) f ⊔
          i ⁻¹ᵁ Proj.basicOpen (projectiveSpaceGrading A n) g := by
  set p := i ≫ projectiveSpaceStructure A n
  have hZ : IsClosed (p ⁻¹' {𝔭}) := h𝔭.preimage p.continuous
  have := noetherianSpace_fibre p 𝔭
  obtain ⟨G, hGfin, hGZ, hG⟩ := exists_finite_specializes hZ
  obtain ⟨f, hf, hfG⟩ := exists_linearForm_mem_basicOpen' 𝔭 hGfin.toFinset
    (fun x => (i x : Proj (projectiveSpaceGrading A n))) (fun x hx => hGZ (hGfin.mem_toFinset.mp hx))
  set W : Set X := ((i ⁻¹ᵁ Proj.basicOpen (projectiveSpaceGrading A n) f : X.Opens) : Set X)ᶜ
  have hW : IsClosed W :=
    (i ⁻¹ᵁ Proj.basicOpen (projectiveSpaceGrading A n) f).isOpen.isClosed_compl
  have hGW : Disjoint G W :=
    Set.disjoint_left.mpr fun x hx hxW => hxW (hfG x (hGfin.mem_toFinset.mpr hx))
  have hfin := finite_inter_of_disjoint hZ (fun x hx y z => hdim x y z hx) hGZ hG hW hGW
  obtain ⟨g, hg, hgW⟩ := exists_linearForm_mem_basicOpen' 𝔭 hfin.toFinset
    (fun x => (i x : Proj (projectiveSpaceGrading A n)))
    (fun x hx => (hfin.mem_toFinset.mp hx).1)
  refine ⟨f, hf, g, hg, fun x hx => ?_⟩
  rw [TopologicalSpace.Opens.mem_sup]
  by_cases hxf : x ∈ i ⁻¹ᵁ Proj.basicOpen (projectiveSpaceGrading A n) f
  · exact Or.inl hxf
  · exact Or.inr (hgW x (hfin.mem_toFinset.mpr ⟨hx, hxf⟩))

end Fibre

end

end DeJongAlterations.StableModification.Projectivity
