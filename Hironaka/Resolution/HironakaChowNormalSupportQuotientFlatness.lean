import Hironaka.Resolution.HironakaChowNormalSupportBaseChange
import Hironaka.Resolution.HironakaChowRelativeFlatKernel
import Hironaka.Analytic.HolomorphicGermNoetherian
import Mathlib.RingTheory.Ideal.Quotient.Noetherian

/-! The actual native quotient-flat criterion for an ORIGINAL infinitesimal
support kernel. Original quotient locality/properness and the actual embedding
are derived, never supplied. Blueprint FIRST:
`hironaka-g10-normal-support-quotient-flatness.tex`. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaChowNormalSupportQuotientFlatness
noncomputable section
open HolGerm HironakaRelativeNormalIdeal HironakaChowNormalSupportProjection
  HironakaChowNormalSupportBaseChange HironakaChowRelativeFlatKernel

variable (d t : ℕ)
local notation "A" => HolGerm (ComplexModel d)
local notation "S" => HolGerm (ComplexModel (d+t))
local instance : Algebra A S := tangentAlgebra d t

variable (Delta : Set (Fin t →₀ ℕ))
local notation "N" => normalSupportSubmodule d t Delta

local instance (a : Ideal A) : Module (A ⧸ a) (normalSupportQuotient d t Delta a) :=
  (Module.isTorsionBySet_quotient_ideal_smul N a).module

local instance (a : Ideal A) :
    SMul (Ideal (A ⧸ a)) (Submodule (A ⧸ a) (normalSupportQuotient d t Delta a)) :=
  Submodule.moduleSubmodule.toSMul

/-- The canonical ORIGINAL quotient, with its native semilinear scalar square. -/
def normalSupportBaseQuotientMap (a : Ideal A) :
    N →ₛₗ[Ideal.Quotient.mk a] normalSupportQuotient d t Delta a :=
  (Module.isTorsionBySet_quotient_ideal_smul N a).semilinearMap.comp
    (a • (⊤ : Submodule A N)).mkQ

@[simp] theorem normalSupportBaseQuotientMap_mk (a : Ideal A) (n : N) :
    normalSupportBaseQuotientMap d t Delta a n = Submodule.Quotient.mk n := rfl

/-- The SAME original kernel's image, as a genuine module over A/a. -/
def normalSupportKernelImage (a : Ideal A) (K : Submodule A N) :
    Submodule (A ⧸ a) (normalSupportQuotient d t Delta a) :=
  K.map (normalSupportBaseQuotientMap d t Delta a)

theorem mem_normalSupportKernelImage_iff (a : Ideal A) (K : Submodule A N)
    (x : normalSupportQuotient d t Delta a) :
    x ∈ normalSupportKernelImage d t Delta a K ↔
      ∃ n ∈ K, (Submodule.Quotient.mk n : normalSupportQuotient d t Delta a) = x := Iff.rfl

theorem normalSupportKernelImage_eq_bot_iff (a : Ideal A) (K : Submodule A N) :
    normalSupportKernelImage d t Delta a K = ⊥ ↔ K ≤ a • (⊤ : Submodule A N) := by
  constructor
  · intro h n hn
    have hm : normalSupportBaseQuotientMap d t Delta a n ∈
        normalSupportKernelImage d t Delta a K := Submodule.mem_map_of_mem hn
    rw [h] at hm
    exact (Submodule.Quotient.mk_eq_zero _).mp hm
  · intro h
    apply eq_bot_iff.mpr
    rintro x ⟨n, hn, rfl⟩
    exact (Submodule.Quotient.mk_eq_zero _).mpr (h hn)

private theorem trace_extended_base_ideal (a : Ideal A) :
    Ideal.map (planeTrace d t).toRingHom (Ideal.map (tangentPullback d t).toRingHom a) = a := by
  rw [Ideal.map_map]
  have he : (planeTrace d t).toRingHom.comp (tangentPullback d t).toRingHom = RingHom.id A := by
    apply RingHom.ext
    exact planeTrace_tangentPullback d t
  rw [he, Ideal.map_id]

/-- Properness of the ORIGINAL ambient quotient is derived by actual trace. -/
theorem extended_base_ideal_ne_top (a : Ideal A) (ha : a ≠ ⊤) :
    Ideal.map (tangentPullback d t).toRingHom a ≠ ⊤ := by
  intro h
  have he := trace_extended_base_ideal d t a
  rw [h, Ideal.map_top] at he
  exact ha he.symm

private def quotientTrace (a : Ideal A) :
    (S ⧸ Ideal.map (tangentPullback d t).toRingHom a) →+* A ⧸ a :=
  Ideal.quotientMap a (planeTrace d t).toRingHom
    (Ideal.le_comap_of_map_le (trace_extended_base_ideal d t a).le)

private theorem quotientTrace_section (a : Ideal A) (x : A ⧸ a) :
    quotientTrace d t a
      (algebraMap (A ⧸ a) (S ⧸ Ideal.map (tangentPullback d t).toRingHom a) x) = x := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk a (planeTrace d t (tangentPullback d t x)) = Ideal.Quotient.mk a x
  rw [planeTrace_tangentPullback]

/-- The SAME original quotient algebra map reflects units by its actual
descended trace retraction; no target local-map certificate is supplied. -/
theorem original_quotient_map_isLocalHom (a : Ideal A) :
    IsLocalHom (algebraMap (A ⧸ a) (S ⧸ Ideal.map (tangentPullback d t).toRingHom a)) := by
  constructor
  intro x hx
  have h := (quotientTrace d t a).isUnit_map hx
  rwa [quotientTrace_section] at h

private theorem kernel_image_infinitesimal {R V : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup V] [Module R V] (a : Ideal R) [IsLocalRing (R ⧸ a)]
    (K : Submodule R V) (hK : K ≤ IsLocalRing.maximalIdeal R • (⊤ : Submodule R V)) :
    K.map ((Module.isTorsionBySet_quotient_ideal_smul V a).semilinearMap.comp
      (a • (⊤ : Submodule R V)).mkQ) ≤
      IsLocalRing.maximalIdeal (R ⧸ a) •
        (⊤ : Submodule (R ⧸ a) (V ⧸ a • (⊤ : Submodule R V))) := by
  have hMax : (IsLocalRing.maximalIdeal R).map (algebraMap R (R ⧸ a)) =
      IsLocalRing.maximalIdeal (R ⧸ a) :=
    IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk a) Ideal.Quotient.mk_surjective
  have hScalars : (IsLocalRing.maximalIdeal (R ⧸ a) •
        (⊤ : Submodule (R ⧸ a) (V ⧸ a • (⊤ : Submodule R V)))).restrictScalars R =
      IsLocalRing.maximalIdeal R • (⊤ : Submodule R (V ⧸ a • (⊤ : Submodule R V))) := by
    rw [← hMax, Ideal.smul_restrictScalars]
    rfl
  rintro x ⟨n, hn, rfl⟩
  change (Submodule.Quotient.mk n : V ⧸ a • (⊤ : Submodule R V)) ∈
    (IsLocalRing.maximalIdeal (R ⧸ a) •
      (⊤ : Submodule (R ⧸ a) (V ⧸ a • (⊤ : Submodule R V)))).restrictScalars R
  rw [hScalars]
  have hm := Submodule.mem_map_of_mem (f := (a • (⊤ : Submodule R V)).mkQ) (hK hn)
  rw [Submodule.map_smul''] at hm
  exact (smul_mono_right (IsLocalRing.maximalIdeal R) (show
    (⊤ : Submodule R V).map (a • (⊤ : Submodule R V)).mkQ ≤ ⊤ from le_top)) hm

/-- Actual base-quotient flatness is equivalent to containment of the SAME
ORIGINAL infinitesimal kernel in aN, for EVERY actual base ideal a. -/
theorem flat_normalSupportQuotientKernel_iff (a : Ideal A) (K : Submodule A N)
    (hK : K ≤ IsLocalRing.maximalIdeal A • (⊤ : Submodule A N)) :
    Module.Flat (A ⧸ a)
      (normalSupportQuotient d t Delta a ⧸ normalSupportKernelImage d t Delta a K) ↔
      K ≤ a • (⊤ : Submodule A N) := by
  constructor
  · intro hFlat
    by_cases ha : a = ⊤
    · subst a
      rw [Submodule.top_smul]
      exact le_top
    · let : Nontrivial (A ⧸ a) := Ideal.Quotient.nontrivial_iff.mpr ha
      let : IsLocalRing (A ⧸ a) :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk a) Ideal.Quotient.mk_surjective
      have hSa := extended_base_ideal_ne_top d t a ha
      let : Nontrivial (S ⧸ Ideal.map (tangentPullback d t).toRingHom a) :=
        Ideal.Quotient.nontrivial_iff.mpr hSa
      let : IsLocalRing (S ⧸ Ideal.map (tangentPullback d t).toRingHom a) :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.map (tangentPullback d t).toRingHom a))
          Ideal.Quotient.mk_surjective
      let : IsNoetherianRing S := isNoetherianRing_holGerm_euclidean (d+t)
      let : IsNoetherianRing (S ⧸ Ideal.map (tangentPullback d t).toRingHom a) := inferInstance
      let : IsLocalHom (algebraMap (A ⧸ a)
          (S ⧸ Ideal.map (tangentPullback d t).toRingHom a)) := original_quotient_map_isLocalHom d t a
      let : Module.Flat (A ⧸ a) (normalSupportQuotient d t Delta a) :=
        flat_normalSupportQuotient d t Delta a
      have hZero := (flat_quotient_iff_eq_bot (normalSupportKernelImage d t Delta a K)
        (normalSupportQuotientInclusion d t Delta a)
        (normalSupportQuotientInclusion_injective d t Delta a)
        (kernel_image_infinitesimal a K hK)).mp hFlat
      exact (normalSupportKernelImage_eq_bot_iff d t Delta a K).mp hZero
  · intro hContain
    let : Module.Flat (A ⧸ a) (normalSupportQuotient d t Delta a) :=
      flat_normalSupportQuotient d t Delta a
    have hZero := (normalSupportKernelImage_eq_bot_iff d t Delta a K).mpr hContain
    exact Module.Flat.of_linearEquiv
      ((normalSupportKernelImage d t Delta a K).quotEquivOfEqBot hZero)

end
end Hironaka.HironakaChowNormalSupportQuotientFlatness
