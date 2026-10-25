/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.CurvesField.StableDownGeometric

/-!
# Branches: points of the normalization over a point

For an integral (e.g. finite) affine morphism `π : Y → X`, an affine open `V ∋ x` with
`R = Γ(V, 𝒪_X)`, `B = Γ(π⁻¹V, 𝒪_Y)` and `𝔭` the prime of a closed point `x`, the points of the
fibre `π⁻¹(x)` correspond to the primes of `B` over `𝔭`, i.e. to the maximal ideals of the
semilocal ring `B_𝔭` (`fiberEquivPrimes`, `maximalSpectrumEquiv`, `natCard_fiber_eq_natCard_maximalSpectrum`).
For the normalization of a reduced curve these are the *branches* `x̃` of the curve at `x`
(M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010),
`references/temkin10-stable-modification/source/semi-stable.tex`, App. B, l. 4377: "`x̃ = π⁻¹(x)`");
so an ordinary double point has exactly two branches and a smooth point one
(`natCard_fiber_eq_two_of_isGeometricOrdinaryDoublePoint`, `natCard_fiber_eq_one_of_isSmoothAt`).

Blueprint: `sm-curves-fields-stabdown.tex`, `lem:sm-stabdown-branches`.
-/

namespace DeJongAlterations.StableModification.CurvesField.Genus

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace Module IsLocalRing
open DeJongAlterations.StableModification.Cohomology

set_option autoImplicit false

universe u

noncomputable section

section MaximalSpectrum

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (P : Ideal R) [P.IsMaximal]

/-- A prime of `R_P` lying over the maximal ideal `P` is the maximal ideal of `R_P`. -/
lemma eq_maximalIdeal_of_under_eq (J : Ideal (Localization.AtPrime P)) [J.IsPrime]
    (hJ : J.under R = P) : J = maximalIdeal (Localization.AtPrime P) := by
  have h : PrimeSpectrum.comap (algebraMap R (Localization.AtPrime P)) ⟨J, inferInstance⟩ =
      PrimeSpectrum.comap (algebraMap R (Localization.AtPrime P))
        ⟨maximalIdeal (Localization.AtPrime P), inferInstance⟩ := by
    ext1
    change J.under R = (maximalIdeal (Localization.AtPrime P)).under R
    rw [hJ, Localization.AtPrime.under_maximalIdeal]
  exact congrArg PrimeSpectrum.asIdeal
    (PrimeSpectrum.localization_comap_injective (Localization.AtPrime P) P.primeCompl h)

/-- The contraction to `R` of a prime of `S_P` along `R → S → S_P` is its contraction along
`R → R_P → S_P`. -/
lemma comap_comap_localization (n : Ideal (Localization (Algebra.algebraMapSubmonoid S P.primeCompl))) :
    (n.comap (algebraMap S _)).comap (algebraMap R S) =
      (n.comap (algebraMap (Localization.AtPrime P) _)).under R := by
  rw [Ideal.under, Ideal.comap_comap, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq,
    ← IsScalarTower.algebraMap_eq]

variable [Algebra.IsIntegral R S]

/-- **Maximal ideals of `S_P` are the primes of `S` over `P`** (for `S` integral over `R`, `P`
maximal). -/
def maximalSpectrumEquiv :
    MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid S P.primeCompl)) ≃
      {Q : PrimeSpectrum S // Q.asIdeal.comap (algebraMap R S) = P} := by
  let Sₚ := Localization (Algebra.algebraMapSubmonoid S P.primeCompl)
  have : Algebra.IsIntegral (Localization.AtPrime P) Sₚ :=
    ⟨isIntegral_localization (M := P.primeCompl) (Rₘ := Localization.AtPrime P) (Sₘ := Sₚ)⟩
  refine Equiv.ofBijective (fun n => ⟨PrimeSpectrum.comap (algebraMap S Sₚ)
      ⟨n.asIdeal, n.isMaximal.isPrime⟩, ?_⟩) ⟨fun n n' h => ?_, fun Q => ?_⟩
  · change (n.asIdeal.comap (algebraMap S Sₚ)).comap (algebraMap R S) = P
    rw [comap_comap_localization]
    have hmax : (n.asIdeal.comap (algebraMap (Localization.AtPrime P) Sₚ)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal n.asIdeal
    rw [IsLocalRing.eq_maximalIdeal hmax, Localization.AtPrime.under_maximalIdeal]
  · have h' := congrArg Subtype.val h
    have := PrimeSpectrum.localization_comap_injective Sₚ
      (Algebra.algebraMapSubmonoid S P.primeCompl) h'
    exact MaximalSpectrum.ext (congrArg PrimeSpectrum.asIdeal this)
  · obtain ⟨Q, hQ⟩ := Q
    have hdisj : Disjoint ((Algebra.algebraMapSubmonoid S P.primeCompl : Submonoid S) : Set S)
        Q.asIdeal := by
      rw [Set.disjoint_left]
      rintro _ ⟨a, ha, rfl⟩ hQa
      have : a ∈ Q.asIdeal.comap (algebraMap R S) := hQa
      rw [hQ] at this
      exact ha this
    obtain ⟨n, hn⟩ : Q ∈ Set.range (PrimeSpectrum.comap (algebraMap S Sₚ)) := by
      rw [PrimeSpectrum.localization_comap_range Sₚ (Algebra.algebraMapSubmonoid S P.primeCompl)]
      exact hdisj
    have hunder : (n.asIdeal.comap (algebraMap (Localization.AtPrime P) Sₚ)).under R = P := by
      rw [← comap_comap_localization]
      have : n.asIdeal.comap (algebraMap S Sₚ) = Q.asIdeal := congrArg PrimeSpectrum.asIdeal hn
      rw [this, hQ]
    have hJ := eq_maximalIdeal_of_under_eq P _ hunder
    have hnmax : n.asIdeal.IsMaximal := by
      refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap
        (R := Localization.AtPrime P) n.asIdeal ?_
      rw [hJ]
      infer_instance
    exact ⟨⟨n.asIdeal, hnmax⟩, Subtype.ext hn⟩

end MaximalSpectrum

section Fibre

variable {X Y : Scheme.{u}} (π : Y ⟶ X) (V : X.Opens) (hV : IsAffineOpen V)
  (x : X) (hx : x ∈ V)

/-- **Points of the fibre are the primes over the prime of the point**: for an affine morphism
`π`, an affine open `V ∋ x`, `R = Γ(V)`, `B = Γ(π⁻¹V)`, the points of `π⁻¹(x)` correspond to the
primes `Q` of `B` with `Q ∩ R = 𝔭_x`. -/
def fiberEquivPrimes [IsAffineHom π] :
    letI := (π.app V).hom.toAlgebra
    ↥(π ⁻¹' {x}) ≃ {Q : PrimeSpectrum Γ(Y, π ⁻¹ᵁ V) //
      Q.asIdeal.comap (algebraMap Γ(X, V) Γ(Y, π ⁻¹ᵁ V)) = (hV.primeIdealOf ⟨x, hx⟩).asIdeal} := by
  letI := (π.app V).hom.toAlgebra
  have hV' : IsAffineOpen (π ⁻¹ᵁ V) := hV.preimage π
  have hmem : ∀ y : Y, π y = x → y ∈ π ⁻¹ᵁ V := fun y hy => by
    change π y ∈ V
    rw [hy]
    exact hx
  have hcomap : ∀ (y : Y) (hy : y ∈ π ⁻¹ᵁ V),
      (hV'.primeIdealOf ⟨y, hy⟩).asIdeal.comap (algebraMap Γ(X, V) Γ(Y, π ⁻¹ᵁ V)) =
        (hV.primeIdealOf ⟨π y, hy⟩).asIdeal := fun y hy => by
    have h := IsAffineOpen.comap_primeIdealOf_appLE (f := π) V hV (π ⁻¹ᵁ V) hV' le_rfl hy
    rw [Scheme.Hom.appLE_eq_app] at h
    exact congrArg PrimeSpectrum.asIdeal h
  refine
    { toFun := fun y => ⟨hV'.primeIdealOf ⟨y.1, hmem y.1 y.2⟩, ?_⟩
      invFun := fun Q => ⟨hV'.fromSpec Q.1, ?_⟩
      left_inv := fun y => ?_
      right_inv := fun Q => ?_ }
  · rw [hcomap]
    have : π y.1 = x := y.2
    congr 2
    exact Subtype.ext this
  · obtain ⟨Q, hQ⟩ := Q
    have hQV : hV'.fromSpec Q ∈ π ⁻¹ᵁ V := fromSpec_mem hV' Q
    have h1 := hcomap _ hQV
    rw [primeIdealOf_fromSpec hV' Q, hQ] at h1
    have h2 : hV.primeIdealOf ⟨π (hV'.fromSpec Q), hQV⟩ = hV.primeIdealOf ⟨x, hx⟩ :=
      PrimeSpectrum.ext h1.symm
    have h3 := congrArg hV.fromSpec h2
    rwa [hV.fromSpec_primeIdealOf, hV.fromSpec_primeIdealOf] at h3
  · apply Subtype.ext
    exact hV'.fromSpec_primeIdealOf _
  · apply Subtype.ext
    exact primeIdealOf_fromSpec hV' Q.1

/-- **Branches are maximal ideals**: for an integral affine morphism `π` and a closed point `x`,
`#π⁻¹(x)` is the number of maximal ideals of the semilocal ring `Γ(π⁻¹V)_𝔭` over `x`. -/
theorem natCard_fiber_eq_natCard_maximalSpectrum [IsIntegralHom π] (hxc : IsClosed {x}) :
    letI := (π.app V).hom.toAlgebra
    Nat.card ↥(π ⁻¹' {x}) = Nat.card (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid
      Γ(Y, π ⁻¹ᵁ V) (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl))) := by
  let _ := (π.app V).hom.toAlgebra
  have : Algebra.IsIntegral Γ(X, V) Γ(Y, π ⁻¹ᵁ V) := ⟨π.isIntegral_app V hV⟩
  have : (hV.primeIdealOf ⟨x, hx⟩).asIdeal.IsMaximal :=
    hV.primeIdealOf_isMaximal_of_isClosed ⟨x, hx⟩ hxc
  exact Nat.card_congr ((fiberEquivPrimes π V hV x hx).trans
    (maximalSpectrumEquiv (hV.primeIdealOf ⟨x, hx⟩).asIdeal).symm)

end Fibre

section Branches

variable {X : Scheme.{u}} [IsAffineHom (pullback.diagonal (terminal.from X))]
  [Finite (genericPoints X)] {k : Type u} [Field k] (q : X ⟶ Spec (.of k))
  [LocallyOfFiniteType q]

/-- **An ordinary double point has two branches**: `#π⁻¹(z) = 2` for the normalization `π` of a
reduced curve and an ordinary double point `z` (Temkin, App. B, l. 4382–4383). -/
theorem natCard_fiber_eq_two_of_isGeometricOrdinaryDoublePoint [IsReduced X]
    (hdim : topologicalKrullDim X ≤ 1) (z : X) (hzc : IsClosed {z}) (hzg : z ∉ genericPoints X)
    (hnode : Geometry.IsGeometricOrdinaryDoublePoint q z) :
    Nat.card ↥(normalizationPointsMap (genericPoints X) ⁻¹' {z}) = 2 := by
  have : IsFinite (normalizationPointsMap (genericPoints X)) :=
    isFinite_normalizationPointsMap (S := genericPoints X) q
  obtain ⟨_, ⟨V, hV, rfl⟩, hzV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  rw [natCard_fiber_eq_natCard_maximalSpectrum _ V hV z hzV hzc]
  exact (deltaInvariant_eq_one_of_isGeometricOrdinaryDoublePoint q hdim z hzc hzg hnode).2 V hV hzV

/-- **A smooth point has one branch**: `#π⁻¹(z) = 1` for the normalization `π` of a reduced curve
and a closed point `z`, not generic, at which the curve is smooth. -/
theorem natCard_fiber_eq_one_of_isSmoothAt [IsReduced X] [LocallyOfFinitePresentation q]
    (hdim : topologicalKrullDim X ≤ 1) (z : X) (hzc : IsClosed {z}) (hzg : z ∉ genericPoints X)
    (hsm : DeJong.IsSmoothAt q z) :
    Nat.card ↥(normalizationPointsMap (genericPoints X) ⁻¹' {z}) = 1 := by
  have : IsFinite (normalizationPointsMap (genericPoints X)) :=
    isFinite_normalizationPointsMap (S := genericPoints X) q
  obtain ⟨_, ⟨V, hV, rfl⟩, hzV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  rw [natCard_fiber_eq_natCard_maximalSpectrum _ V hV z hzV hzc]
  exact (deltaInvariant_eq_zero_of_isSmoothAt q hdim z hzc hzg hsm).2 V hV hzV

omit [Finite (genericPoints X)] in
include q in
/-- **The branches of the normalization in a disjoint union of point sets**: for `S = S₁ ⊔ S₂`,
the fibre of `π_S` over `z` is the disjoint union of those of `π_{S₁}` and `π_{S₂}`. -/
theorem natCard_fiber_normalizationPoints_union (S S₁ S₂ : Set X) [Finite S] [Finite S₁]
    [Finite S₂] (hS : S = S₁ ∪ S₂) (hd : Disjoint S₁ S₂) (z : X) :
    Nat.card ↥(normalizationPointsMap S ⁻¹' {z}) =
      Nat.card ↥(normalizationPointsMap S₁ ⁻¹' {z}) +
        Nat.card ↥(normalizationPointsMap S₂ ⁻¹' {z}) := by
  have hf : ∀ T : Set X, [Finite T] → (normalizationPointsMap T ⁻¹' {z}).Finite := fun T _ => by
    have : IsFinite (normalizationPointsMap T) := isFinite_normalizationPointsMap (S := T) q
    exact (normalizationPointsMap T).finite_preimage_singleton z
  subst hS
  obtain ⟨e⟩ := nonempty_isColimit_binaryCofanMk_of_isCompl _ _ (isCompl_opensRange_pointsIncl hd)
  obtain ⟨jU, jV, _, _, hjU, hjV, hdisj, hcov⟩ := exists_normalization_split
    (pointsMap X (S₁ ∪ S₂)) _ _ (pointsMap X S₁) (pointsMap X S₂)
    (pointsIncl_pointsMap _) (pointsIncl_pointsMap _) e
  have hset : normalizationPointsMap (S₁ ∪ S₂) ⁻¹' {z} =
      jU '' (normalizationPointsMap S₁ ⁻¹' {z}) ∪ jV '' (normalizationPointsMap S₂ ⁻¹' {z}) := by
    ext w
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_image]
    constructor
    · intro hw
      have : w ∈ jU.opensRange ⊔ jV.opensRange := by rw [hcov]; trivial
      rcases Opens.mem_sup.1 this with ⟨a, rfl⟩ | ⟨b, rfl⟩
      · left
        refine ⟨a, ?_, rfl⟩
        have hw' : (jU ≫ (pointsMap X (S₁ ∪ S₂)).fromNormalization) a = z := hw
        rwa [hjU] at hw'
      · right
        refine ⟨b, ?_, rfl⟩
        have hw' : (jV ≫ (pointsMap X (S₁ ∪ S₂)).fromNormalization) b = z := hw
        rwa [hjV] at hw'
    · rintro (⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩)
      · have ha' : (jU ≫ (pointsMap X (S₁ ∪ S₂)).fromNormalization) a = z := by
          rw [hjU]
          exact ha
        exact ha'
      · have hb' : (jV ≫ (pointsMap X (S₁ ∪ S₂)).fromNormalization) b = z := by
          rw [hjV]
          exact hb
        exact hb'
  have hdisj' : Disjoint (jU '' (normalizationPointsMap S₁ ⁻¹' {z}))
      (jV '' (normalizationPointsMap S₂ ⁻¹' {z})) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, -, rfl⟩ ⟨b, -, hb⟩
    have hmem : jU a ∈ jU.opensRange ⊓ jV.opensRange := ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
    rw [disjoint_iff.1 hdisj] at hmem
    exact hmem
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq, hset,
    Set.ncard_union_eq hdisj' ((hf S₁).image _) ((hf S₂).image _),
    Set.ncard_image_of_injective _ jU.isOpenEmbedding.injective,
    Set.ncard_image_of_injective _ jV.isOpenEmbedding.injective]

omit [Finite (genericPoints X)] in
include q in
/-- **The branches over a finite set of points**: `#π_T⁻¹(z) = ∑_{v ∈ T} #π_v⁻¹(z)`. -/
theorem natCard_fiber_normalizationPoints_eq_sum (T : Finset X) (z : X) :
    Nat.card ↥(normalizationPointsMap (T : Set X) ⁻¹' {z}) =
      ∑ v ∈ T, Nat.card ↥(normalizationPointsMap ({v} : Set X) ⁻¹' {z}) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    have : IsEmpty (pointsScheme X ((∅ : Finset X) : Set X)) := by
      refine ⟨fun w => ?_⟩
      have := pointsMap_mem w
      simp at this
    have : IsEmpty (normalizationPoints ((∅ : Finset X) : Set X)) := isEmpty_normalization _
    rw [Nat.card_eq_zero]
    left
    exact ⟨fun w => isEmptyElim w.1⟩
  | insert a T ha ih =>
    have hS : ((insert a T : Finset X) : Set X) = {a} ∪ (T : Set X) := by
      rw [Finset.coe_insert, Set.insert_eq]
    have hd : Disjoint ({a} : Set X) (T : Set X) := by
      rw [Set.disjoint_singleton_left]
      exact_mod_cast ha
    rw [natCard_fiber_normalizationPoints_union q _ _ _ hS hd z, ih, Finset.sum_insert ha]

omit [Finite (genericPoints X)] in
include q in
/-- **A point lies on a component iff a branch of that component lies over it**: `z` is in the
closure of `v` iff the normalization `π_v : X̃_v → X` of the component of `v` has a point over `z`
(`π_v` is finite, hence closed, with dense image in `closure {v}`). -/
theorem mem_closure_iff_nonempty_fiber (v z : X) :
    z ∈ closure {v} ↔ (normalizationPointsMap ({v} : Set X) ⁻¹' {z}).Nonempty := by
  have : IsFinite (normalizationPointsMap ({v} : Set X)) :=
    isFinite_normalizationPointsMap (S := ({v} : Set X)) q
  constructor
  · intro hz
    have hcl : IsClosed (Set.range (normalizationPointsMap ({v} : Set X))) :=
      (normalizationPointsMap ({v} : Set X)).isClosedMap.isClosed_range
    have hv : v ∈ Set.range (normalizationPointsMap ({v} : Set X)) := by
      let η : ({v} : Set X) := ⟨v, rfl⟩
      obtain ⟨y⟩ : Nonempty (Spec (X.residueField v)) := inferInstance
      refine ⟨(pointsMap X {v}).toNormalization (pointsι η y), ?_⟩
      change ((pointsMap X {v}).toNormalization ≫ (pointsMap X {v}).fromNormalization)
        (pointsι η y) = v
      rw [Scheme.Hom.toNormalization_fromNormalization, pointsMap_ι_apply]
    obtain ⟨w, hw⟩ := (closure_minimal (Set.singleton_subset_iff.2 hv) hcl) hz
    exact ⟨w, hw⟩
  · rintro ⟨w, hw⟩
    have := range_normalizationPointsMap_subset ({v} : Set X) ⟨w, rfl⟩
    rw [hw] at this
    exact this

end Branches

end

end DeJongAlterations.StableModification.CurvesField.Genus
