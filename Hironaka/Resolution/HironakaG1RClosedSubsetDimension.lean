import Hironaka.Resolution.HironakaG1RIntegralSchemeDimension
import Hironaka.Resolution.HironakaG1RSingularIdealSheaf
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Dimension of an irreducible closed subset, computed on any affine chart

**Main results.** Let `X` be a scheme locally of finite type over a field `k`.

* `topologicalKrullDim_eq_ringKrullDim_quotient`: for an irreducible closed `Z ⊆ X` and ANY affine
  open `U` meeting `Z`, `dim Z = dim (Γ(X, U) ⧸ I_Z(U))`, where `I_Z` is the vanishing ideal sheaf
  of `Z` (Mathlib's `Scheme.IdealSheafData.vanishingIdeal`);
* `topologicalKrullDim_closure_eq`: for a point `η` and ANY affine open `U ∋ η`,
  `dim (closure {η}) = dim (Γ(X, U) ⧸ 𝔭_η)` with `𝔭_η` the prime ideal of `η` in `Γ(X, U)`;
* `topologicalKrullDim_closure_of_isOpenImmersion`: for an open immersion `j : Y ⟶ X` and `y : Y`,
  `dim (closure {j y}) = dim (closure {y})` — the dimension of an irreducible closed subset is
  the dimension of any nonempty open part of it.

Proof: the reduced induced subscheme `Z_red` (subscheme of `I_Z`) is integral and locally of finite
type over `k`, its underlying space is `Z`, and `Γ(Z_red, Z_red ∩ U) ≅ Γ(X, U) ⧸ I_Z(U)`
(Mathlib's `subschemeObjIso`); apply `HironakaG1RIntegralSchemeDimension.topologicalKrullDim_eq_ringKrullDim`.
For a point, `I_{closure η}(U)` is the prime of `η` (vanishing ideal of a closure in `Spec`).
For open immersions, compare the charts `V ∋ y` and `j(V)` through `j.appIso V`.

Only Mathlib and lane G1's modules are imported; no named input.
Blueprint: `hironaka-g1-r-integral-scheme-dimension.tex` (node `g1r:closed-subset-dimension`).
-/

set_option autoImplicit false

open CategoryTheory TopologicalSpace

namespace Hironaka.HironakaG1RClosedSubsetDimension

open AlgebraicGeometry HironakaG1RIntegralSchemeDimension HironakaG1RSingularIdealSheaf
open Scheme.IdealSheafData

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The underlying space of the subscheme of an ideal sheaf is its support. -/
theorem topologicalKrullDim_subscheme (I : X.IdealSheafData) :
    topologicalKrullDim I.subscheme = topologicalKrullDim (I.support : Set X) :=
  rfl

/-- The reduced induced subscheme on an irreducible closed subset is integral. -/
theorem isIntegral_subscheme_vanishingIdeal (Z : Closeds X) (hZ : IsIrreducible (Z : Set X)) :
    IsIntegral (vanishingIdeal Z).subscheme := by
  have : IsReduced (vanishingIdeal Z).subscheme :=
    isReduced_subscheme_of_isRadical _ fun U ↦ by
      simp only [vanishingIdeal_ideal]
      exact PrimeSpectrum.isRadical_vanishingIdeal _
  have hirr : IsIrreducible ((vanishingIdeal Z).support : Set X) := by
    rw [coe_support_vanishingIdeal]
    exact hZ
  have : IrreducibleSpace (vanishingIdeal Z).subscheme := Subtype.irreducibleSpace hirr
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- **The dimension of an irreducible closed subset on an affine chart.** -/
theorem topologicalKrullDim_eq_ringKrullDim_quotient (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (Z : Closeds X) (hZ : IsIrreducible (Z : Set X)) {U : X.Opens}
    (hU : IsAffineOpen U) (hZU : ((Z : Set X) ∩ U).Nonempty) :
    topologicalKrullDim (Z : Set X) =
      ringKrullDim (Γ(X, U) ⧸ (vanishingIdeal Z).ideal ⟨U, hU⟩) := by
  set I := vanishingIdeal Z
  have := isIntegral_subscheme_vanishingIdeal Z hZ
  obtain ⟨x, hxZ, hxU⟩ := hZU
  have hxI : x ∈ I.support := by
    rw [← SetLike.mem_coe, coe_support_vanishingIdeal]
    exact hxZ
  have hU' : IsAffineOpen (I.subschemeι ⁻¹ᵁ U) := hU.preimage I.subschemeι
  have : Nonempty (I.subschemeι ⁻¹ᵁ U) := ⟨⟨⟨x, hxI⟩, hxU⟩⟩
  have hdim : topologicalKrullDim (Z : Set X) = topologicalKrullDim I.subscheme := by
    rw [topologicalKrullDim_subscheme, coe_support_vanishingIdeal]
  rw [hdim, topologicalKrullDim_eq_ringKrullDim (I.subschemeι ≫ f) hU']
  exact ringKrullDim_eq_of_ringEquiv (I.subschemeObjIso ⟨U, hU⟩).commRingCatIsoToRingEquiv

/-- The vanishing ideal of the closure of a point `η`, on an affine open containing `η`, is the
prime ideal of `η`. -/
theorem vanishingIdeal_closure_singleton_ideal (η : X) {U : X.Opens} (hU : IsAffineOpen U)
    (hη : η ∈ U) :
    (vanishingIdeal ⟨closure {η}, isClosed_closure⟩).ideal ⟨U, hU⟩ =
      (hU.primeIdealOf ⟨η, hη⟩).asIdeal := by
  rw [vanishingIdeal_ideal]
  have hpre : hU.fromSpec ⁻¹' {η} = {hU.primeIdealOf ⟨η, hη⟩} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hz
      apply hU.fromSpec.isOpenEmbedding.injective
      rw [hz, IsAffineOpen.fromSpec_primeIdealOf]
    · rintro rfl
      exact IsAffineOpen.fromSpec_primeIdealOf hU ⟨η, hη⟩
  have h1 : hU.fromSpec ⁻¹' closure {η} = closure {hU.primeIdealOf ⟨η, hη⟩} := by
    rw [hU.fromSpec.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
      hU.fromSpec.continuous, hpre]
    rfl
  have h2 : PrimeSpectrum.vanishingIdeal (closure {hU.primeIdealOf ⟨η, hη⟩} :
      Set (PrimeSpectrum Γ(X, U))) = (hU.primeIdealOf ⟨η, hη⟩).asIdeal := by
    rw [PrimeSpectrum.vanishingIdeal_closure, PrimeSpectrum.vanishingIdeal_singleton]
  exact (congrArg PrimeSpectrum.vanishingIdeal h1).trans h2

/-- **The dimension of the closure of a point on an affine chart**: `dim (closure {η}) =
dim (Γ(X, U) ⧸ 𝔭_η)` for every affine open `U ∋ η`. -/
theorem topologicalKrullDim_closure_eq (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (η : X)
    {U : X.Opens} (hU : IsAffineOpen U) (hη : η ∈ U) :
    topologicalKrullDim (closure {η} : Set X) =
      ringKrullDim (Γ(X, U) ⧸ (hU.primeIdealOf ⟨η, hη⟩).asIdeal) := by
  rw [← vanishingIdeal_closure_singleton_ideal η hU hη]
  exact topologicalKrullDim_eq_ringKrullDim_quotient f ⟨closure {η}, isClosed_closure⟩
    isIrreducible_singleton.closure hU ⟨η, subset_closure rfl, hη⟩

/-- Quotients by corresponding ideals along a ring isomorphism have the same dimension. -/
theorem ringKrullDim_quotient_comap_equiv {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    (Q : Ideal B) : ringKrullDim (A ⧸ Q.comap e) = ringKrullDim (B ⧸ Q) := by
  refine ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ Q e ?_)
  exact (Ideal.map_comap_of_surjective _ e.surjective Q).symm

/-- **Dimension of a point closure is local**: for an open immersion `j : Y ⟶ X` (with `X` locally
of finite type over `k`) and `y : Y`, `dim (closure {j y}) = dim (closure {y})`. -/
theorem topologicalKrullDim_closure_of_isOpenImmersion (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] (y : Y) :
    topologicalKrullDim (closure {j y} : Set X) = topologicalKrullDim (closure {y} : Set Y) := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  change Y.Opens at V
  replace hV : IsAffineOpen V := hV
  have hV' : IsAffineOpen (j ''ᵁ V) := hV.image_of_isOpenImmersion j
  have hle : V ≤ j ⁻¹ᵁ (j ''ᵁ V) := (j.preimage_image_eq V).ge
  rw [topologicalKrullDim_closure_eq f (j y) hV' (hle hyV),
    topologicalKrullDim_closure_eq (j ≫ f) y hV hyV,
    ← IsAffineOpen.comap_primeIdealOf_appLE (j ''ᵁ V) hV' V hV hle hyV]
  have e : (j.appLE (j ''ᵁ V) V hle) = (j.appIso V).hom := (j.appIso_hom' V).symm
  rw [e]
  exact ringKrullDim_quotient_comap_equiv (j.appIso V).commRingCatIsoToRingEquiv _

end Hironaka.HironakaG1RClosedSubsetDimension
