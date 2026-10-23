/-
Copyright (c) 2026. All rights reserved.
-/
import DeJongAlterations.Algebra.RegularQuotientFamily
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Algebra.RestrictScalars

/-!
# Actual kernel parameters of surjections of regular local rings

The residue cotangent map and the internally chosen parameters are constructed
from the actual surjection. No kernel-generation or dimension certificate is assumed.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open IsLocalRing Module

namespace DeJongAlterations.Algebra.RegularSmoothConverseParameters

variable {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]

local instance (priority := 0) targetCotangentModule : Module (ResidueField R) (CotangentSpace S) :=
  Module.restrictScalars (ResidueField R) (ResidueField S) (CotangentSpace S)

local instance (priority := 0) targetCotangentTower :
    IsScalarTower (ResidueField R) (ResidueField S) (CotangentSpace S) := by
  constructor
  intro a b x
  rw [Algebra.smul_def]
  change (algebraMap (ResidueField R) (ResidueField S) a * b) • x =
    algebraMap (ResidueField R) (ResidueField S) a • (b • x)
  exact mul_smul _ _ _

local instance (priority := 0) targetCotangentOwnTower : IsScalarTower S (ResidueField S) (CotangentSpace S) :=
  inferInstanceAs (IsScalarTower S (S ⧸ maximalIdeal S) (maximalIdeal S).Cotangent)

local instance (priority := 0) sourceTargetResidueTower : IsScalarTower R (ResidueField S) (CotangentSpace S) :=
  IsScalarTower.to₁₃₄ R S (ResidueField S) (CotangentSpace S)

local instance (priority := 0) sourceResidueCotangentTower : IsScalarTower R (ResidueField R) (CotangentSpace S) := by
  apply IsScalarTower.of_algebraMap_smul
  intro r x
  change algebraMap (ResidueField R) (ResidueField S) (algebraMap R (ResidueField R) r) • x = r • x
  rw [← IsScalarTower.algebraMap_apply R (ResidueField R) (ResidueField S)]
  exact IsScalarTower.algebraMap_smul (ResidueField S) r x

/-- The actual cotangent map of the given local algebra map, over its source residue field. -/
def cotangentMap : CotangentSpace R →ₗ[ResidueField R] CotangentSpace S :=
  (Ideal.mapCotangent (maximalIdeal R) (maximalIdeal S) (Algebra.ofId R S)
    (by
      change maximalIdeal R ≤ (maximalIdeal S).comap (algebraMap R S)
      rw [maximalIdeal_comap (algebraMap R S)])).extendScalarsOfSurjective residue_surjective

private theorem kernel_le_maximalIdeal : RingHom.ker (algebraMap R S) ≤ maximalIdeal R := by
  rw [← maximalIdeal_comap (algebraMap R S)]
  intro r hr
  change algebraMap R S r ∈ maximalIdeal S
  rw [RingHom.mem_ker.mp hr]
  exact Ideal.zero_mem _

private theorem maximalIdeal_comap_eq_kernel_sup :
    (maximalIdeal S).comap (algebraMap R S) = RingHom.ker (algebraMap R S) ⊔ maximalIdeal R := by
  rw [maximalIdeal_comap (algebraMap R S), sup_eq_right.mpr kernel_le_maximalIdeal]

/-- The induced map of actual cotangent spaces is surjective when the local map is surjective. -/
theorem cotangentMap_surjective (hf : Function.Surjective (algebraMap R S)) :
    Function.Surjective (cotangentMap (R := R) (S := S)) := by
  exact Ideal.mapCotangent_surjective_of_comap_eq hf maximalIdeal_comap_eq_kernel_sup

/-- Every actual cotangent kernel vector lifts to an actual element of the ring-map kernel. -/
theorem exists_kernel_lift (hf : Function.Surjective (algebraMap R S)) (v : CotangentSpace R)
    (hv : cotangentMap (R := R) (S := S) v = 0) :
    ∃ x : maximalIdeal R, algebraMap R S x = 0 ∧ (maximalIdeal R).toCotangent x = v := by
  have hv' : v ∈ (Ideal.mapCotangent (maximalIdeal R) (maximalIdeal S) (Algebra.ofId R S)
      (by
        change maximalIdeal R ≤ (maximalIdeal S).comap (algebraMap R S)
        rw [maximalIdeal_comap (algebraMap R S)])).ker := hv
  rw [Ideal.mapCotangent_ker_of_surjective hf maximalIdeal_comap_eq_kernel_sup] at hv'
  obtain ⟨x, hx, hxv⟩ := hv'
  refine ⟨x, ?_, hxv⟩
  exact RingHom.mem_ker.mp (Ideal.mem_inf.mp hx).1

/-- The actual residue-field map of a surjection is surjective. -/
theorem residueAlgebraMap_surjective (hf : Function.Surjective (algebraMap R S)) :
    Function.Surjective (algebraMap (ResidueField R) (ResidueField S)) := by
  intro y
  obtain ⟨s, rfl⟩ := residue_surjective y
  obtain ⟨r, rfl⟩ := hf s
  exact ⟨residue R r, ResidueField.algebraMap_residue r⟩

/-- The actual residue-field isomorphism preserves cotangent dimension. -/
theorem targetCotangent_finrank_eq (hf : Function.Surjective (algebraMap R S)) :
    finrank (ResidueField R) (CotangentSpace S) = finrank (ResidueField S) (CotangentSpace S) := by
  have hb : Function.Bijective (algebraMap (ResidueField R) (ResidueField S)) :=
    ⟨(algebraMap (ResidueField R) (ResidueField S)).injective, residueAlgebraMap_surjective hf⟩
  have h := Module.finrank_mul_finrank (ResidueField R) (ResidueField S) (CotangentSpace S)
  rw [Module.finrank_of_bijective_algebraMap hb, one_mul] at h
  exact h.symm

/-- Choose actual kernel elements whose cotangent classes are a basis of the actual cotangent kernel. -/
theorem exists_kernel_parameters (P Q : Type*) [CommRing P] [CommRing Q]
    [IsRegularLocalRing P] [IsRegularLocalRing Q] [Algebra P Q]
    (hf : Function.Surjective (algebraMap P Q)) :
    ∃ (n : ℕ) (t : Fin n → maximalIdeal P),
      (∀ i, algebraMap P Q (t i) = 0) ∧
      LinearIndependent (ResidueField P) (fun i ↦ (maximalIdeal P).toCotangent (t i)) ∧
      ringKrullDim Q + n = ringKrullDim P := by
  let : IsLocalHom (algebraMap P Q) := IsLocalHom.of_surjective _ hf
  let F := cotangentMap (R := P) (S := Q)
  let n := finrank (ResidueField P) F.ker
  let b := Module.finBasis (ResidueField P) F.ker
  choose t ht htclass using fun i : Fin n ↦ exists_kernel_lift hf (b i) (b i).property
  have hli : LinearIndependent (ResidueField P)
      (fun i ↦ (maximalIdeal P).toCotangent (t i)) := by
    have hb := b.linearIndependent.map' F.ker.subtype
      (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
    convert hb using 1
    · funext i
      exact htclass i
    all_goals rfl
  refine ⟨n, t, ht, hli, ?_⟩
  have h := LinearMap.finrank_range_add_finrank_ker F
  rw [LinearMap.range_eq_top.mpr (cotangentMap_surjective hf), finrank_top,
    targetCotangent_finrank_eq hf] at h
  have hcast :
      (finrank (ResidueField Q) (CotangentSpace Q) : WithBot ℕ∞) + n =
        (finrank (ResidueField P) (CotangentSpace P) : WithBot ℕ∞) := by
    exact_mod_cast h
  rwa [(IsRegularLocalRing.iff_finrank_cotangentSpace P).mp inferInstance,
    (IsRegularLocalRing.iff_finrank_cotangentSpace Q).mp inferInstance] at hcast

/-- An actual regular parameter quotient of the source still surjects onto the target with equal dimension. -/
theorem exists_regular_parameter_quotient (P Q : Type*) [CommRing P] [CommRing Q]
    [IsRegularLocalRing P] [IsRegularLocalRing Q] [Algebra P Q]
    (hf : Function.Surjective (algebraMap P Q)) :
    ∃ (n : ℕ) (t : Fin n → maximalIdeal P),
      LinearIndependent (ResidueField P) (fun i ↦ (maximalIdeal P).toCotangent (t i)) ∧
      IsRegularLocalRing (P ⧸ Ideal.span (Set.range fun i ↦ (t i : P))) ∧
      ∃ g : (P ⧸ Ideal.span (Set.range fun i ↦ (t i : P))) →+* Q,
        Function.Surjective g ∧
        g.comp (Ideal.Quotient.mk _) = algebraMap P Q ∧
        ringKrullDim (P ⧸ Ideal.span (Set.range fun i ↦ (t i : P))) = ringKrullDim Q := by
  obtain ⟨n, t, ht, hli, hdim⟩ := exists_kernel_parameters P Q hf
  let I := Ideal.span (Set.range fun i ↦ (t i : P))
  have hI : I ≤ RingHom.ker (algebraMap P Q) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact RingHom.mem_ker.mpr (ht i)
  let g := Ideal.Quotient.lift I (algebraMap P Q) hI
  have hg : Function.Surjective g := by
    intro q
    obtain ⟨p, rfl⟩ := hf q
    exact ⟨Ideal.Quotient.mk I p, rfl⟩
  refine ⟨n, t, hli, RegularQuotientFamily.isRegularLocalRing_quotient_family P t hli,
    g, hg, rfl, ?_⟩
  apply (ENat.WithBot.add_natCast_cancel (c := n)).mp
  simpa only [Fintype.card_fin] using
    (RegularQuotientFamily.ringKrullDim_quotient_family_add_card_eq P t hli).trans hdim.symm

end DeJongAlterations.Algebra.RegularSmoothConverseParameters
