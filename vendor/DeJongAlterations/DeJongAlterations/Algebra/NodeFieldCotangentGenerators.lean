import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Free

/-! # Actual three-dimensional second jets produce two original maximal-ideal generators

The original coefficient-residue map and actual second-jet dimension are the
only input data. No maximal generators, cotangent basis, or dimension certificate
are supplied, and no quadratic or geometric-node classification is asserted.
-/

noncomputable section

open IsLocalRing

namespace DeJongAlterations.Algebra.NodeFieldCotangentGenerators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
variable (K : Type u) [Field K] (C : Type v) [CommRing C] [IsLocalRing C] [Algebra K C]

/-- The actual original second-jet quotient map to the native residue field. -/
def jetResidue : (C ⧸ maximalIdeal C ^ 2) →ₗ[K] ResidueField C :=
  (Ideal.Quotient.factorₐ K (Ideal.pow_le_self (I := maximalIdeal C) two_ne_zero)).toLinearMap

/-- The native cotangent is the actual kernel of the original second-jet residue map. -/
def cotangentKernelEquiv : CotangentSpace C ≃ₗ[K] LinearMap.ker (jetResidue K C) := by
  let j := (maximalIdeal C).cotangentToQuotientSquare.restrictScalars K
  have hj : ∀ a, j a ∈ LinearMap.ker (jetResidue K C) := by
    intro a
    obtain ⟨a, rfl⟩ := (maximalIdeal C).toCotangent_surjective a
    change residue C a = 0
    exact (residue_eq_zero_iff _).mpr a.property
  refine LinearEquiv.ofBijective (j.codRestrict _ hj) ⟨?_, ?_⟩
  · intro a b hab
    exact (maximalIdeal C).cotangentToQuotientSquare_injective (congrArg Subtype.val hab)
  · intro a
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective a.val
    have hcm : c ∈ maximalIdeal C := by
      apply (residue_eq_zero_iff c).mp
      change jetResidue K C (Ideal.Quotient.mk _ c) = 0
      rw [hc]
      exact a.property
    refine ⟨(maximalIdeal C).toCotangent ⟨c, hcm⟩, ?_⟩
    apply Subtype.ext
    exact hc

/-- Actual coefficient residue bijectivity and the actual second-jet rank internally force cotangent rank two. -/
theorem cotangent_finrank
    (hres : Function.Bijective ((residue C).comp (algebraMap K C)))
    (hdim : Module.finrank K (C ⧸ maximalIdeal C ^ 2) = 3) :
    Module.finrank K (CotangentSpace C) = 2 := by
  let : Module.Finite K (C ⧸ maximalIdeal C ^ 2) :=
    Module.finite_of_finrank_pos (by rw [hdim]; omega)
  let e : K ≃ₗ[K] ResidueField C :=
    LinearEquiv.ofBijective (Algebra.linearMap K (ResidueField C)) hres
  have hr : Module.finrank K (ResidueField C) = 1 := by
    rw [← e.finrank_eq]
    exact Module.finrank_self K
  have hs : Function.Surjective (jetResidue K C) := by
    intro a
    obtain ⟨c, hc⟩ := residue_surjective a
    exact ⟨Ideal.Quotient.mk _ c, hc⟩
  have h := (jetResidue K C).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top_of_surjective _ hs, finrank_top, hr, hdim] at h
  have he := (cotangentKernelEquiv K C).finrank_eq
  omega

/-- Two internally selected and lifted cotangent basis vectors generate the WHOLE native original maximal ideal. -/
theorem exists_maximalIdeal_generators [IsNoetherianRing C]
    (hres : Function.Bijective ((residue C).comp (algebraMap K C)))
    (hdim : Module.finrank K (C ⧸ maximalIdeal C ^ 2) = 3) :
    ∃ b : Fin 2 → C, Ideal.span (Set.range b) = maximalIdeal C := by
  have hd := cotangent_finrank K C hres hdim
  let : Module.Finite K (CotangentSpace C) :=
    Module.finite_of_finrank_pos (by rw [hd]; omega)
  let B := Module.finBasisOfFinrankEq K (CotangentSpace C) hd
  choose b hb using fun i : Fin 2 => (maximalIdeal C).toCotangent_surjective (B i)
  have hspan : Submodule.span K (Set.range (fun i => (maximalIdeal C).toCotangent (b i))) = ⊤ := by
    simpa only [hb] using B.span_eq
  let L := Submodule.span C (Set.range b)
  have hle : Submodule.span K (Set.range (fun i => (maximalIdeal C).toCotangent (b i))) ≤
      (L.map (maximalIdeal C).toCotangent).restrictScalars K := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Submodule.mem_map_of_mem (Submodule.subset_span (Set.mem_range_self i))
  have hmap : L.map (maximalIdeal C).toCotangent = ⊤ := by
    apply top_unique
    intro a _
    exact hle (by rw [hspan]; trivial)
  have hL : L = ⊤ := CotangentSpace.map_eq_top_iff.mp hmap
  refine ⟨fun i => (b i : C), ?_⟩
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (b i).property
  · intro c hc
    have hle' : L ≤ Submodule.comap (maximalIdeal C).subtype
        (Ideal.span (Set.range (fun i => (b i : C)))) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact Ideal.subset_span (Set.mem_range_self i)
    exact hle' (show (⟨c, hc⟩ : maximalIdeal C) ∈ L from by rw [hL]; trivial)

end DeJongAlterations.Algebra.NodeFieldCotangentGenerators
