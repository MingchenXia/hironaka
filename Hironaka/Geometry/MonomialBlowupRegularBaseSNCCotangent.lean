import Hironaka.Algebra.RegularSmoothConverseKernel
import Hironaka.Algebra.RegularSmoothConverseConormal
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-! Original full-height generators of actual regular-local kernels have independent cotangent classes. -/

noncomputable section

open IsLocalRing TensorProduct

namespace Hironaka.Geometry.MonomialBlowupRegularBaseSNCCotangent

open Algebra.RegularSmoothConverseConormal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- Actual ideal generators span exactly the image of its intrinsic map to the maximal cotangent space. -/
theorem cotangent_span_eq_range {ι : Type*} (I : Ideal R) (hI : I ≤ maximalIdeal R)
    (t : ι → I) (hspan : Ideal.span (Set.range fun i ↦ (t i : R)) = I) :
    Submodule.span (ResidueField R)
      (Set.range fun i ↦ (maximalIdeal R).toCotangent ⟨(t i : R), hI (t i).property⟩) =
      (toMaximalCotangent I hI).range := by
  have h := congrArg (fun M : Submodule (ResidueField R) (ResidueField R ⊗[R] I) ↦
    M.map (toMaximalCotangent I hI)) (span_one_tmul_generators I t hspan)
  rw [Submodule.map_span, Submodule.map_top] at h
  simpa only [← Set.range_comp, Function.comp_def, toMaximalCotangent_tmul, one_smul] using h

/-- Specified families with the same actual ideal span have the same actual maximal cotangent span. -/
theorem cotangent_span_eq_of_ideal_span_eq {ι κ : Type*}
    (t : ι → maximalIdeal R) (b : κ → maximalIdeal R)
    (heq : Ideal.span (Set.range fun i ↦ (t i : R)) =
      Ideal.span (Set.range fun j ↦ (b j : R))) :
    Submodule.span (ResidueField R) (Set.range fun i ↦ (maximalIdeal R).toCotangent (t i)) =
      Submodule.span (ResidueField R) (Set.range fun j ↦ (maximalIdeal R).toCotangent (b j)) := by
  let I := Ideal.span (Set.range fun i ↦ (t i : R))
  have hI : I ≤ maximalIdeal R := Ideal.span_le.mpr (by
    rintro _ ⟨i, rfl⟩
    exact (t i).property)
  let t' : ι → I := fun i ↦ ⟨t i, Ideal.subset_span ⟨i, rfl⟩⟩
  let b' : κ → I := fun j ↦ ⟨b j, by
    change (b j : R) ∈ Ideal.span (Set.range fun i ↦ (t i : R))
    rw [heq]
    exact Ideal.subset_span ⟨j, rfl⟩⟩
  have ht : Ideal.span (Set.range fun i ↦ (t' i : R)) = I := rfl
  have hb : Ideal.span (Set.range fun j ↦ (b' j : R)) = I := heq.symm
  exact (cotangent_span_eq_range I hI t' ht).trans (cotangent_span_eq_range I hI b' hb).symm

end Hironaka.Geometry.MonomialBlowupRegularBaseSNCCotangent

namespace Hironaka.Geometry.MonomialBlowupRegularBaseSNCCotangent

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type*} [CommRing R] [IsRegularLocalRing R]

/-- Original specified generators of a full-height regular kernel have independent actual cotangent classes. -/
theorem original_generators_independent {ι : Type*} [Fintype ι]
    (t : ι → maximalIdeal R)
    [IsRegularLocalRing (R ⧸ Ideal.span (Set.range fun i ↦ (t i : R)))]
    (hheight : (Fintype.card ι : ℕ∞) ≤
      (Ideal.span (Set.range fun i ↦ (t i : R))).height) :
    LinearIndependent (ResidueField R) (fun i ↦ (maximalIdeal R).toCotangent (t i)) := by
  classical
  let I := Ideal.span (Set.range fun i ↦ (t i : R))
  let : IsDomain (R ⧸ I) := Algebra.RegularLocalDomain.isDomain_of_isRegularLocalRing _
  let : I.IsPrime := (Ideal.Quotient.isDomain_iff_prime I).mp inferInstance
  obtain ⟨n, b, hli, hspan⟩ :=
    Algebra.RegularSmoothConverseKernel.exists_kernel_span_independent_parameters
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hb : Ideal.span (Set.range fun j ↦ (b j : R)) = I := by
    simpa only [Ideal.mk_ker] using hspan
  have hbound : I.height ≤ n := by
    let F := Finset.univ.image (fun j ↦ (b j : R))
    have hF : Ideal.span (F : Set R) = I := by simpa [F] using hb
    have hmin : I ∈ (Ideal.span (F : Set R)).minimalPrimes := by
      rw [hF, Ideal.minimalPrimes_eq_subsingleton_self]
      exact Set.mem_singleton _
    exact (Ideal.height_le_card_of_mem_minimalPrimes_span_finset hmin).trans
      (by exact_mod_cast (Finset.card_image_le.trans_eq (Finset.card_univ.trans (Fintype.card_fin n))))
  have hcard : Fintype.card ι ≤ n := by exact_mod_cast hheight.trans hbound
  rw [linearIndependent_iff_card_le_finrank_span]
  change Fintype.card ι ≤ Module.finrank (ResidueField R)
    (Submodule.span (ResidueField R) (Set.range fun i ↦ (maximalIdeal R).toCotangent (t i)))
  rw [cotangent_span_eq_of_ideal_span_eq t b hb.symm, finrank_span_eq_card hli, Fintype.card_fin]
  exact hcard

end Hironaka.Geometry.MonomialBlowupRegularBaseSNCCotangent
