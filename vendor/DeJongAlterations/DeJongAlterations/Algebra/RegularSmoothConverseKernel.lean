/-
Copyright (c) 2026. All rights reserved.
-/
import DeJongAlterations.Algebra.RegularSmoothConverseParameters
import DeJongAlterations.Algebra.RegularLocalDomain
import DeJongAlterations.Algebra.RegularLocalSurjection

/-!
# Independent actual kernel parameters for regular local quotients

The parameter quotient is constructed from the actual map. Its genuine
regular-local domain structure and exact dimension force the remaining
surjection to be injective, identifying the actual kernel ideal.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open IsLocalRing

namespace DeJongAlterations.Algebra.RegularSmoothConverseKernel

/-- The actual kernel of a surjection between regular local rings has independent cotangent generators. -/
theorem exists_kernel_span_independent_parameters {P Q : Type*} [CommRing P] [CommRing Q]
    [IsRegularLocalRing P] [IsRegularLocalRing Q] (f : P →+* Q) (hf : Function.Surjective f) :
    ∃ (n : ℕ) (t : Fin n → maximalIdeal P),
      LinearIndependent (ResidueField P) (fun i ↦ (maximalIdeal P).toCotangent (t i)) ∧
      Ideal.span (Set.range fun i ↦ (t i : P)) = RingHom.ker f := by
  let : Algebra P Q := f.toAlgebra
  obtain ⟨n, t, hli, hC, g, hg, hgf, hdim⟩ :=
    RegularSmoothConverseParameters.exists_regular_parameter_quotient P Q hf
  let I := Ideal.span (Set.range fun i ↦ (t i : P))
  let C := P ⧸ I
  let : IsRegularLocalRing C := hC
  let : IsDomain C := RegularLocalDomain.isDomain_of_isRegularLocalRing C
  have hginj := RegularLocalSurjection.injective_of_surjective_of_ringKrullDim_le g hg hdim.le
  refine ⟨n, t, hli, ?_⟩
  change g.comp (Ideal.Quotient.mk I) = f at hgf
  rw [← hgf, RingHom.ker_comp_of_injective _ hginj]
  exact (Ideal.mk_ker).symm

end DeJongAlterations.Algebra.RegularSmoothConverseKernel
