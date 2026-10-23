import DeJongAlterations.Algebra.NodeGeometricCompletionDerivation
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.Exactness
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Kaehler.Basic

/-! The completed ORIGINAL coherent differential module, its actual completed universal
derivation, and preservation of its actual original finite relations. All constructions
are on the original algebra and native module completion. -/

noncomputable section

open TensorProduct

namespace DeJongAlterations.Algebra.NodeGeometricCompletionCoherentDifferentials

universe u

section RightExact

variable {R M N P : Type u} [CommRing R] [IsNoetherianRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P] [Module.Finite R N] (I : Ideal R)

/-- Actual completion preserves a right exact original sequence, without requiring its
original relation map to be injective. -/
theorem completion_rightExact (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Exact (AdicCompletion.map I f) (AdicCompletion.map I g) := by
  let f' : M →ₗ[R] LinearMap.ker g := f.codRestrict _ fun x =>
    (hfg (f x)).mpr ⟨x, rfl⟩
  have hf' : Function.Surjective f' := by
    intro y
    obtain ⟨x, hx⟩ := (hfg y).mp y.property
    exact ⟨x, Subtype.ext hx⟩
  have he := AdicCompletion.map_exact (I := I)
    (LinearMap.ker g).injective_subtype g.exact_subtype_ker_map hg
  have hs := AdicCompletion.map_surjective I hf'
  have hc : (AdicCompletion.map I (LinearMap.ker g).subtype).comp
      (AdicCompletion.map I f') = AdicCompletion.map I f := by
    rw [AdicCompletion.map_comp]
    rfl
  intro y
  constructor
  · intro hy
    obtain ⟨z, hz⟩ := (he y).mp hy
    obtain ⟨w, hw⟩ := hs z
    refine ⟨w, ?_⟩
    rw [← hc, LinearMap.comp_apply, hw, hz]
  · rintro ⟨z, rfl⟩
    exact (he _).mpr ⟨AdicCompletion.map I f' z, by
      rw [← hc, LinearMap.comp_apply]⟩

end RightExact

variable (K R : Type u) [CommRing K] [CommRing R] [Algebra K R] (I : Ideal R)

/-- The target is the native completion of the ORIGINAL differential module. -/
abbrev CompletedOmega := AdicCompletion I (KaehlerDifferential K R)

/-- The actual completed universal derivation of the ORIGINAL algebra. -/
def completedUniversalDerivation : Derivation K (AdicCompletion I R) (CompletedOmega K R I) :=
  NodeGeometricCompletionDerivation.completedDifferential I (KaehlerDifferential.D K R)

/-- Every original differential retains its original value in the native module completion. -/
theorem completedUniversalDerivation_original (r : R) :
    completedUniversalDerivation K R I (algebraMap R (AdicCompletion I R) r) =
      AdicCompletion.of I (KaehlerDifferential K R) (KaehlerDifferential.D K R r) :=
  NodeGeometricCompletionDerivation.completedDifferential_algebraMap I _ r

/-- The actual differential has the explicit adic one-level loss. -/
theorem completedUniversalDerivation_filtration (n : ℕ) (r : AdicCompletion I R)
    (hr : r.val (n + 1) = 0) : (completedUniversalDerivation K R I r).val n = 0 :=
  NodeGeometricCompletionDerivation.completedDifferential_filtration I _ n r hr

variable [IsNoetherianRing R] [Algebra.EssFiniteType K R]

/-- Finite presentation is deduced from the ORIGINAL essentially finite type algebra and
Noetherian original ring; it is not an output-model hypothesis. -/
theorem originalOmega_finitePresentation : Module.FinitePresentation R (KaehlerDifferential K R) :=
  Module.finitePresentation_of_finite R (KaehlerDifferential K R)

/-- The actual coherent completion comparison, with its native scalar action. -/
def completedOmegaTensorEquiv :
    AdicCompletion I R ⊗[R] (KaehlerDifferential K R) ≃ₗ[AdicCompletion I R]
      CompletedOmega K R I :=
  AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I (KaehlerDifferential K R)

/-- The comparison preserves EVERY actual original differential and completed scalar. -/
theorem completedOmegaTensorEquiv_tmul (r : AdicCompletion I R) (ω : KaehlerDifferential K R) :
    completedOmegaTensorEquiv K R I (r ⊗ₜ[R] ω) =
      r • AdicCompletion.of I (KaehlerDifferential K R) ω := rfl

/-- The ORIGINAL completed coherent differential module is finitely presented over the
actual completed original ring. -/
theorem completedOmega_finitePresentation :
    Module.FinitePresentation (AdicCompletion I R) (CompletedOmega K R I) := by
  let := originalOmega_finitePresentation K R
  exact Module.FinitePresentation.of_equiv (completedOmegaTensorEquiv K R I)

/-- Internally choose an actual finite original generator-and-relation sequence. Its actual
completed maps present the completion of the ORIGINAL coherent differential module. -/
theorem exists_original_finite_relations :
    ∃ (n m : ℕ)
      (π : (Fin n → R) →ₗ[R] KaehlerDifferential K R)
      (ρ : (Fin m → R) →ₗ[R] (Fin n → R)),
      Function.Surjective π ∧ Function.Exact ρ π ∧
      Function.Surjective (AdicCompletion.map I π) ∧
      Function.Exact (AdicCompletion.map I ρ) (AdicCompletion.map I π) := by
  let := originalOmega_finitePresentation K R
  obtain ⟨n, m, π, ρ, hπ, hρ⟩ := Module.FinitePresentation.exists_fin' R (KaehlerDifferential K R)
  exact ⟨n, m, π, ρ, hπ, hρ, AdicCompletion.map_surjective I hπ,
    completion_rightExact I ρ π hρ hπ⟩

/-- The literal cokernel of the completed ORIGINAL finite relation map is the completed
ORIGINAL differential module. The displayed projection retains all original representatives. -/
theorem exists_original_completed_cokernel :
    ∃ (n m : ℕ)
      (π : (Fin n → R) →ₗ[R] KaehlerDifferential K R)
      (ρ : (Fin m → R) →ₗ[R] (Fin n → R))
      (e : (AdicCompletion I (Fin n → R) ⧸ LinearMap.range (AdicCompletion.map I ρ))
        ≃ₗ[AdicCompletion I R] CompletedOmega K R I),
      Function.Surjective π ∧ Function.Exact ρ π ∧
      ∀ v : Fin n → R,
        e (Submodule.Quotient.mk (AdicCompletion.of I (Fin n → R) v)) =
          AdicCompletion.of I (KaehlerDifferential K R) (π v) := by
  obtain ⟨n, m, π, ρ, hπ, hρ, hπhat, hexact⟩ := exists_original_finite_relations K R I
  have hker : LinearMap.ker (AdicCompletion.map I π) =
      LinearMap.range (AdicCompletion.map I ρ) := LinearMap.exact_iff.mp hexact
  let e := (Submodule.quotEquivOfEq _ _ hker.symm).trans
    (LinearMap.quotKerEquivOfSurjective (AdicCompletion.map I π) hπhat)
  refine ⟨n, m, π, ρ, e, hπ, hρ, fun v => ?_⟩
  exact AdicCompletion.map_of I π v

end DeJongAlterations.Algebra.NodeGeometricCompletionCoherentDifferentials
