import DeJongAlterations.StableModification.Resolution.StrictifyCenter
import DeJongAlterations.Algebra.AffinePrimeDimensionMaximal
import DeJongAlterations.Geometry.RationalCoordinateMapGenericFiberOpenDimension
import DeJongAlterations.Geometry.RegularSmoothConverse
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Scheme-theoretic facts used in the strictification

* `ringKrullDim_stalk_eq_of_isClosed`: at a closed point of an integral scheme of finite type
  over a field, the local ring has the dimension of the scheme (Noether normalization, Codex's
  `Algebra.AffinePrimeDimension.maximalHeight_eq_ringKrullDim`).
* `isRegularScheme_of_closedPoints`: a scheme of finite type over a perfect field whose local
  rings at closed points are regular is regular (the regular locus is open, Codex's
  `Geometry.RegularSmoothConverse.isOpen_regularLocus`, and the scheme is Jacobson).
* `colonIdealSheaf J K`: the ideal sheaf `(J : K)`, for `K` of finite type on affine opens (here:
  a locally Noetherian scheme), with stalks `(J_x : K_x)` (`stalkIdeal_colonIdealSheaf`). It
  defines strict transforms: if `I(C) 𝒪_{X'} = (g)` is the exceptional divisor of a blowup and
  `π^* I(F) = (g^m h)`, then `(π^* I(F) : (g)^m) = (h)`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

namespace DeJongAlterations.StableModification.Resolution.Strictify

set_option backward.isDefEq.respectTransparency false

open Algebra.NodeFittingIdealSheaf

universe u

section Dimension

variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))

/-- The sections over an affine open of a scheme locally of finite type over `k` form a
`k`-algebra of finite type. -/
theorem finiteType_sectionStructure [LocallyOfFiniteType p] (U : X.affineOpens) :
    (sectionStructure p U.1).FiniteType := by
  apply RingHom.FiniteType.comp
  · exact HasRingHomProperty.appLE (P := @LocallyOfFiniteType) p inferInstance
      ⟨⊤, isAffineOpen_top _⟩ U le_top
  · exact RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).2

/-- The prime of a closed point in an affine open is maximal. -/
theorem isMaximal_primeIdealOf_of_isClosed (U : X.affineOpens) (x : X) (hxU : x ∈ U.1)
    (hx : IsClosed ({x} : Set X)) : (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal.IsMaximal := by
  rw [← PrimeSpectrum.isClosed_singleton_iff_isMaximal]
  have hpre : U.2.fromSpec ⁻¹' {x} = {U.2.primeIdealOf ⟨x, hxU⟩} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hz
      apply U.2.fromSpec.isOpenEmbedding.injective
      rw [hz]
      exact (U.2.fromSpec_primeIdealOf ⟨x, hxU⟩).symm
    · rintro rfl
      exact U.2.fromSpec_primeIdealOf ⟨x, hxU⟩
  have := hx.preimage U.2.fromSpec.continuous
  rw [hpre] at this
  exact this

/-- **Equidimensionality at closed points.** -/
theorem ringKrullDim_stalk_eq_of_isClosed [IsIntegral X] [LocallyOfFiniteType p] (x : X)
    (hx : IsClosed ({x} : Set X)) :
    ringKrullDim (X.presheaf.stalk x) = topologicalKrullDim X := by
  obtain ⟨U, hxU⟩ := exists_affineOpens_mem x
  let iA : Algebra k Γ(X, U.1) := (sectionStructure p U.1).toAlgebra
  have : Algebra.FiniteType k Γ(X, U.1) := finiteType_sectionStructure p U
  have : Nonempty U.1 := ⟨⟨x, hxU⟩⟩
  have : IsDomain Γ(X, U.1) := inferInstance
  let P := (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal
  have : P.IsMaximal := isMaximal_primeIdealOf_of_isClosed U x hxU hx
  let : Algebra Γ(X, U.1) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x) P := U.2.isLocalization_stalk ⟨x, hxU⟩
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height P (X.presheaf.stalk x),
    Algebra.AffinePrimeDimension.maximalHeight_eq_ringKrullDim k Γ(X, U.1) P,
    ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  have h1 := Geometry.FunctionFieldDimension.topologicalKrullDim_eq_of_openImmersion p U.1.ι
  rw [← h1]
  exact (U.2.isoSpec.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq).symm

end Dimension

section Regular

variable {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))

/-- Regularity at closed points suffices for schemes of finite type over a perfect field. -/
theorem isRegularScheme_of_closedPoints [LocallyOfFiniteType p]
    (h : ∀ x : X, IsClosed ({x} : Set X) → IsRegularLocalRing (X.presheaf.stalk x)) :
    IsRegularScheme X := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  have hopen := Geometry.RegularSmoothConverse.isOpen_regularLocus p
  set V := {x : X | IsRegularLocalRing (X.presheaf.stalk x)}
  have hV : Vᶜ = ∅ := by
    by_contra hne
    obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints (Set.nonempty_iff_ne_empty.mpr hne)
      hopen.isClosed_compl.isLocallyClosed
    exact hy (h y hyc)
  intro x
  by_contra hx
  have : x ∈ Vᶜ := hx
  rw [hV] at this
  exact this

end Regular

section Colon

/-- Colon ideals commute with localization, for a finitely generated divisor. -/
theorem map_colon_of_isLocalization {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (J K : Ideal R) (hK : K.FG) :
    (J.colon (K : Set R)).map (algebraMap R S) =
      (J.map (algebraMap R S)).colon ((K.map (algebraMap R S) : Ideal S) : Set S) := by
  classical
  obtain ⟨T, rfl⟩ := hK
  rw [Ideal.colon_span, Ideal.map_span, Ideal.colon_span]
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, Submodule.mem_colon]
    rintro _ ⟨k, hk, rfl⟩
    rw [smul_eq_mul, ← map_mul]
    exact Ideal.mem_map_of_mem _ (by simpa [smul_eq_mul] using (Submodule.mem_colon.mp hr) k hk)
  · intro y hy
    rw [Submodule.mem_colon] at hy
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj M y
    have hk : ∀ k ∈ T, ∃ c : M, (c : R) * (r * k) ∈ J := by
      intro k hkT
      have h1 : y * algebraMap R S k ∈ J.map (algebraMap R S) := by
        simpa [smul_eq_mul] using hy (algebraMap R S k) ⟨k, hkT, rfl⟩
      have h2 : algebraMap R S (r * k) ∈ J.map (algebraMap R S) := by
        rw [map_mul, ← hrs, mul_right_comm]
        exact Ideal.mul_mem_right _ _ h1
      obtain ⟨⟨a, m⟩, ha⟩ := (IsLocalization.mem_map_algebraMap_iff M S).mp h2
      have h3 : algebraMap R S (r * k * m) = algebraMap R S a := by
        rw [map_mul]
        exact ha
      obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists M S).mp h3
      refine ⟨c * m, ?_⟩
      have : (c : R) * (r * k * m) ∈ J := by
        rw [hc]
        exact Ideal.mul_mem_left _ _ a.property
      simpa only [Submonoid.coe_mul, mul_comm, mul_assoc, mul_left_comm] using this
    choose! c hc using hk
    let N : M := ∏ k ∈ T, c k
    have hN : (N : R) * r ∈ J.colon (T : Set R) := by
      rw [Submodule.mem_colon]
      intro k hkT
      have : (N : R) = (∏ l ∈ T.erase k, (c l : R)) * c k := by
        rw [Submonoid.coe_finsetProd, Finset.prod_erase_mul _ _ hkT]
      rw [smul_eq_mul, this]
      have := Ideal.mul_mem_left J (∏ l ∈ T.erase k, (c l : R)) (hc k hkT)
      simpa [mul_comm, mul_assoc, mul_left_comm] using this
    have hy' : y = algebraMap R S ((N : R) * r) * IsLocalization.mk' S (1 : R) (N * s) := by
      have hrs' : y * algebraMap R S s = algebraMap R S r := hrs
      rw [← IsLocalization.mk'_eq_mul_mk'_one, IsLocalization.eq_mk'_iff_mul_eq]
      rw [Submonoid.coe_mul, map_mul, map_mul]
      linear_combination (algebraMap R S N) * hrs'
    rw [hy']
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hN)

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- The colon ideal sheaf `(J : K)`. -/
def colonIdealSheaf (J K : X.IdealSheafData) : X.IdealSheafData where
  ideal U := (J.ideal U).colon (K.ideal U : Set Γ(X, U))
  map_ideal_basicOpen U f := by
    let := (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom.toAlgebra
    have : IsLocalization.Away f Γ(X, X.basicOpen f) := U.2.isLocalization_basicOpen f
    have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    rw [show (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom =
      algebraMap Γ(X, U.1) Γ(X, X.basicOpen f) from rfl,
      map_colon_of_isLocalization (Submonoid.powers f) _ _ (Ideal.fg_of_isNoetherianRing _)]
    rw [← J.map_ideal_basicOpen U f, ← K.map_ideal_basicOpen U f]
    rfl

/-- Stalks of colon ideal sheaves are colon ideals of stalks. -/
theorem stalkIdeal_colonIdealSheaf (J K : X.IdealSheafData) (x : X) :
    stalkIdeal (colonIdealSheaf J K) x =
      (stalkIdeal J x).colon ((stalkIdeal K x : Ideal (X.presheaf.stalk x)) : Set _) := by
  obtain ⟨U, hxU⟩ := exists_affineOpens_mem x
  rw [stalkIdeal_eq_map_germ _ U hxU, stalkIdeal_eq_map_germ _ U hxU,
    stalkIdeal_eq_map_germ _ U hxU]
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
  have hloc := U.2.isLocalization_stalk ⟨x, hxU⟩
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  exact map_colon_of_isLocalization (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl _ _
    (Ideal.fg_of_isNoetherianRing _)

/-- Iterated colon ideal sheaf `(J : K^m)`. -/
def colonIter (J K : X.IdealSheafData) (m : ℕ) : X.IdealSheafData :=
  (fun I ↦ colonIdealSheaf I K)^[m] J

theorem stalkIdeal_colonIter (J K : X.IdealSheafData) (m : ℕ) (x : X) :
    stalkIdeal (colonIter J K m) x = (fun I : Ideal (X.presheaf.stalk x) ↦
      I.colon ((stalkIdeal K x : Ideal (X.presheaf.stalk x)) : Set _))^[m] (stalkIdeal J x) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [colonIter, Function.iterate_succ_apply', ← colonIter, stalkIdeal_colonIdealSheaf, ih,
      Function.iterate_succ_apply']

/-- Colon by the unit ideal does nothing. -/
theorem iterate_colon_top {R : Type*} [CommRing R] (I : Ideal R) (m : ℕ) :
    (fun I : Ideal R ↦ I.colon ((⊤ : Ideal R) : Set R))^[m] I = I := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih]
    ext r
    simp

/-- Iterated colon by a principal ideal generated by a non-zero-divisor `g`, on `(g^m h)`. -/
theorem iterate_colon_span_pow_mul {R : Type*} [CommRing R] {g : R} (hg : IsSMulRegular R g)
    (h : R) (m : ℕ) :
    (fun I : Ideal R ↦ I.colon ((Ideal.span {g} : Ideal R) : Set R))^[m]
      (Ideal.span {g ^ m * h}) = Ideal.span {h} := by
  induction m generalizing h with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    have : (Ideal.span {g ^ (m + 1) * h}).colon ((Ideal.span {g} : Ideal R) : Set R) =
        Ideal.span {g ^ m * h} := by
      rw [Ideal.colon_span]
      ext r
      rw [Submodule.mem_colon_singleton, smul_eq_mul, Ideal.mem_span_singleton',
        Ideal.mem_span_singleton']
      constructor
      · rintro ⟨a, ha⟩
        refine ⟨a, hg ?_⟩
        simp only [smul_eq_mul]
        linear_combination ha
      · rintro ⟨a, rfl⟩
        exact ⟨a, by ring⟩
    rw [this, ih]

theorem le_colonIdealSheaf (J K : X.IdealSheafData) : J ≤ colonIdealSheaf J K :=
  fun _ ↦ Ideal.le_colon

theorem le_colonIter (J K : X.IdealSheafData) (m : ℕ) : J ≤ colonIter J K m := by
  induction m with
  | zero => exact le_rfl
  | succ m ih =>
    rw [colonIter, Function.iterate_succ_apply']
    exact ih.trans (le_colonIdealSheaf _ _)

end Colon

end DeJongAlterations.StableModification.Resolution.Strictify
