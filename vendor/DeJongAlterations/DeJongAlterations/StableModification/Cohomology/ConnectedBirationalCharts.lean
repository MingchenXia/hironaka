/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Cohomology.CurveHypersurface

/-!
# Two affine charts near a closed fibre of a projective curve

The two-chart core of Zariski's connectedness theorem for birational morphisms
(`ConnectedBirationalCore.lean`; Temkin, *Stable modification of relative curves*,
J. Algebraic Geom. 19 (2010), proof of Lemma 4.4.2, `semi-stable.tex` line 3133) needs the
preimage of a neighbourhood of the point `x` to be covered by two affine opens. Lane COH3A proves
this over a local base (`exists_linearForms_closedFibre`, `CurveHypersurface.lean`); here the base
is an arbitrary ring `A` and the fibre is taken over a closed point `P` of `Spec A` with infinite
residue field `A ⧸ P` (blueprint `sm-cohomology-connected-birational.tex`,
`lem:sm-connbir-hyperplanes`).

## Main results

* `exists_linearCombination_X_notMem_of_infinite`, `exists_linearForm_mem_basicOpen_of_infinite`:
  prime avoidance for linear forms over a prime `p` with `A ⧸ p` infinite (the proof of COH3A's
  local statement, with the residue field replaced by `A ⧸ p`).
* `noetherianSpace_fibre`: fibres of quasi-compact morphisms locally of finite type over `Spec A`
  are Noetherian spaces.
* `exists_linearForms_fibre`: for a closed immersion `X → ℙⁿ_A` whose fibre over a closed point
  `P` has dimension at most one, two linear forms without common zero on that fibre.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry MvPolynomial TopologicalSpace

namespace DeJongAlterations.StableModification.Cohomology.ConnectedBirational

noncomputable section

section LinearForms

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {n : ℕ}

/-- **Prime avoidance for linear forms over a prime with infinite residue ring**: finitely many
prime ideals of `A[T₀, …, Tₙ]` lying over primes contained in `p` (`C a ∈ P ⇒ a ∈ p`) and not
containing all the variables avoid a common linear form, provided `A ⧸ p` is infinite. (The local
case is lane COH3A's `exists_linearCombination_X_notMem`; the proof is the same.) -/
theorem exists_linearCombination_X_notMem_of_infinite (p : Ideal A) [Infinite (A ⧸ p)]
    {ι : Type*} (s : Finset ι) (P : ι → Ideal (MvPolynomial (Fin (n + 1)) A))
    (hP : ∀ j ∈ s, (P j).IsPrime) (hrel : ∀ j ∈ s, ∃ i, X i ∉ P j)
    (hC : ∀ j ∈ s, ∀ a : A, C a ∈ P j → a ∈ p) :
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
  let σ : A ⧸ p → A := Function.surjInv Ideal.Quotient.mk_surjective
  let g : A ⧸ p → (Fin (n + 1) → A) ⧸ (W j).toAddSubgroup :=
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
    have hp := hC j hj _ hCm
    have : Ideal.Quotient.mk p (σ t') = Ideal.Quotient.mk p (σ t) := by
      rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
      exact hp
    simpa only [σ, Function.surjInv_eq Ideal.Quotient.mk_surjective] using this.symm
  have := Finite.of_injective g hg
  exact not_finite (A ⧸ p)

/-- **Finitely many points of `ℙⁿ_A` over `p` lie in a common `D₊(f)`, `f` linear**, if
`A ⧸ p` is infinite. -/
theorem exists_linearForm_mem_basicOpen_of_infinite (p : PrimeSpectrum A)
    [Infinite (A ⧸ p.asIdeal)] {ι : Type*} (s : Finset ι)
    (y : ι → Proj (projectiveSpaceGrading A n))
    (hy : ∀ j ∈ s, projectiveSpaceStructure A n (y j) = p) :
    ∃ f ∈ projectiveSpaceGrading A n 1, ∀ j ∈ s,
      y j ∈ Proj.basicOpen (projectiveSpaceGrading A n) f := by
  obtain ⟨c, hc⟩ := exists_linearCombination_X_notMem_of_infinite p.asIdeal s
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
/-- The fibre of a quasi-compact morphism locally of finite type over a point of `Spec A` is a
Noetherian space. -/
theorem noetherianSpace_fibre (p : X ⟶ Spec (CommRingCat.of A)) [LocallyOfFiniteType p]
    [QuasiCompact p] (P : PrimeSpectrum A) : NoetherianSpace (p ⁻¹' {P}) := by
  have : LocallyOfFiniteType (p.fiberToSpecResidueField P) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have : AlgebraicGeometry.IsNoetherian (p.fiber P) :=
    { __ := LocallyOfFiniteType.isLocallyNoetherian (p.fiberToSpecResidueField P) }
  exact (noetherianSpace_iff_of_homeomorph (p.fiberHomeo _)).mp inferInstance

/-- **Two hyperplanes without common zero on a closed fibre of a projective curve**: let
`i : X → ℙⁿ_A` be a closed immersion and `P` a closed point of `Spec A` with `A ⧸ P` infinite
such that the fibre over `P` has no chains `x ⤳ y ⤳ z` of three distinct points. Then there are two
linear forms `f`, `g` such that `X ∩ D₊(f)` and `X ∩ D₊(g)` cover the fibre over `P`. (The local
case is lane COH3A's `exists_linearForms_closedFibre`.) -/
theorem exists_linearForms_fibre (i : X ⟶ projectiveSpace A n) [IsClosedImmersion i]
    (P : PrimeSpectrum A) (hP : IsClosed ({P} : Set (PrimeSpectrum A)))
    [Infinite (A ⧸ P.asIdeal)]
    (hdim : ∀ x y z : X, (i ≫ projectiveSpaceStructure A n) x = P →
      x ⤳ y → y ⤳ z → x = y ∨ y = z) :
    ∃ f ∈ projectiveSpaceGrading A n 1, ∃ g ∈ projectiveSpaceGrading A n 1,
      ∀ x : X, (i ≫ projectiveSpaceStructure A n) x = P →
        x ∈ i ⁻¹ᵁ Proj.basicOpen (projectiveSpaceGrading A n) f ⊔
          i ⁻¹ᵁ Proj.basicOpen (projectiveSpaceGrading A n) g := by
  set p := i ≫ projectiveSpaceStructure A n
  have hZ : IsClosed (p ⁻¹' {P}) := hP.preimage p.continuous
  have := noetherianSpace_fibre p P
  obtain ⟨G, hGfin, hGZ, hG⟩ := exists_finite_specializes hZ
  obtain ⟨f, hf, hfG⟩ := exists_linearForm_mem_basicOpen_of_infinite P hGfin.toFinset
    (fun x => (i x : Proj (projectiveSpaceGrading A n))) (fun x hx => by
      have := hGZ (hGfin.mem_toFinset.mp hx)
      exact this)
  set W : Set X := ((i ⁻¹ᵁ Proj.basicOpen (projectiveSpaceGrading A n) f : X.Opens) : Set X)ᶜ
  have hW : IsClosed W :=
    (i ⁻¹ᵁ Proj.basicOpen (projectiveSpaceGrading A n) f).isOpen.isClosed_compl
  have hGW : Disjoint G W :=
    Set.disjoint_left.mpr fun x hx hxW => hxW (hfG x (hGfin.mem_toFinset.mpr hx))
  have hfin := finite_inter_of_disjoint hZ (fun x hx y z => hdim x y z hx) hGZ hG hW hGW
  obtain ⟨g, hg, hgW⟩ := exists_linearForm_mem_basicOpen_of_infinite P hfin.toFinset
    (fun x => (i x : Proj (projectiveSpaceGrading A n))) (fun x hx => by
      have := (hfin.mem_toFinset.mp hx).1
      exact this)
  refine ⟨f, hf, g, hg, fun x hx => ?_⟩
  rw [TopologicalSpace.Opens.mem_sup]
  by_cases hxf : x ∈ i ⁻¹ᵁ Proj.basicOpen (projectiveSpaceGrading A n) f
  · exact Or.inl hxf
  · exact Or.inr (hgW x (hfin.mem_toFinset.mpr ⟨hx, hxf⟩))

end Fibre

end

end DeJongAlterations.StableModification.Cohomology.ConnectedBirational
