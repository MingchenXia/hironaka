/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.CurvesField.OrdinaryCompletionBranches
import DeJongAlterations.StableModification.CurvesField.Delta
import DeJongAlterations.Algebra.CompletionRegularityAscent
import DeJongAlterations.Algebra.RegularLocalDomain
import Mathlib.RingTheory.LocalProperties.Reduced

/-!
# Ordinary double points and smooth points through the δ-invariant

Let `A = 𝒪_{C,x}` be the local ring of a reduced curve at a closed point and `B` its normalization
(the semilocal ring `𝒪_{C̃,x̃}`). M. Temkin, *Stable modification of relative curves*, J. Algebraic
Geom. 19 (2010) (`references/temkin10-stable-modification/source/semi-stable.tex`, App. B,
l. 4381–4397) defines `x` to be an ordinary double point if `Â ≅ k[[u, v]]/(uv)` and characterizes
ordinary points by `g(x) = |x̃| - 1`, with `g(x) = δ(A) = dim_k B/A`. This file proves the two cases
of this characterization used in Corollary B.2 for the source curve `C'` (blueprint
`lem:sm-ordinary-completion`, directions "completed ⇒ gluing" for `n = 1, 2`):

* `delta_eq_one_of_formalNode`, `card_maximalSpectrum_eq_two_of_formalNode`: **if `Â ≅ k[[u, v]]/(uv)`
  then `δ(A) = 1` and `B` has exactly two maximal ideals** (`x` has two branches); consequently,
  the residue fields being `k`, `A` is the gluing ring of `B`
  (`Genus.eq_gluing_of_isGeometricOrdinaryDoublePoint` at the scheme level);
* `algebraMap_surjective_of_isIntegrallyClosed`: **if `A` is an integrally closed domain (a smooth
  point), then `A = B`**, so `δ(A) = 0` and `x` has one branch.

The normalization `B` enters through the properties used: `B` is a finite `A`-algebra containing `A`,
there is a conductor element `s ∈ 𝔪_A` (`s B ⊆ A`) which is a non-zero-divisor on `B`, and `B` is
integrally closed in an `A`-algebra `L ⊇ B` in which `s` is invertible (for the normalization of a
reduced curve, `L` is the product of the residue fields at the generic points).

## The argument for the node

Let `φ : k[[u, v]]/(uv) → k[[t]] × k[[t]]` be the branch embedding (`OrdinaryCompletionBranches`),
whose image has codimension one, and `β : A → Â ≅ k[[u, v]]/(uv) → k[[t]] × k[[t]]`. Both
components of `β(s)` are nonzero (`s` is a non-zero-divisor of the flat `Â`). Since `k[[t]]` is
integrally closed, `b ↦ β(s b) / β(s)` is a ring map `Ψ : B → k[[t]] × k[[t]]` extending `β`
(`exists_ringHom_mul_eq`). If `Ψ(b) ∈ im φ`, then `s b ∈ s Â ∩ A = s A` (faithful flatness), so
`b ∈ A`. Hence `B/A` embeds into `(k[[t]] × k[[t]]) / im φ`, and `δ(A) ≤ 1`. If `A = B`, then `A`
is integrally closed in `L`; this makes `A_s` a field and `A` a discrete valuation ring, hence
regular, so `Â` is regular, hence a domain, which `k[[u, v]]/(uv)` is not
(`rangeIn_ne_top_of_formalNode`).
So `δ(A) = 1`, `B/A → (k[[t]] × k[[t]]) / im φ` is bijective, and taking constant terms gives a
surjection `B → k × k` (`node_quotient`): `B` has two maximal ideals; it has at most
`δ(A) + 1 = 2` (`CurvesField.card_le_delta_add_one`).

Blueprint: `sm-curves-fields-stabdown.tex`, `lem:sm-conductor-division`,
`lem:sm-formal-node-not-normal`, `lem:sm-ordinary-completion-node`,
`lem:sm-ordinary-completion-smooth`.
-/

namespace DeJongAlterations.StableModification.CurvesField.OrdinaryCompletion

open IsLocalRing Module
open DeJongAlterations.Algebra.NodeGeometricCompletionFormalUV
open DeJongAlterations.Algebra.CompletionRegularityBasics

set_option autoImplicit false

universe u v w

noncomputable section

section Conductor

/-! ### Division by a conductor element -/

variable {A : Type v} {B : Type w} [CommRing A] [CommRing B] [Algebra A B]
  (hAB : Function.Injective (algebraMap A B)) {s : A}
  (hsB : ∀ b : B, ∃ a : A, s • b = algebraMap A B a)

/-- The element `s b ∈ A` for a conductor element `s` (`s B ⊆ A`). -/
def numer (b : B) : A := (hsB b).choose

lemma algebraMap_numer (b : B) : algebraMap A B (numer hsB b) = s • b :=
  (hsB b).choose_spec.symm

include hAB

lemma numer_add (b b' : B) : numer hsB (b + b') = numer hsB b + numer hsB b' :=
  hAB (by rw [map_add, algebraMap_numer, algebraMap_numer, algebraMap_numer, smul_add])

lemma numer_zero : numer hsB (0 : B) = 0 :=
  hAB (by rw [algebraMap_numer, smul_zero, map_zero])

lemma numer_one : numer hsB (1 : B) = s :=
  hAB (by rw [algebraMap_numer, Algebra.smul_def, mul_one])

lemma numer_mul (b b' : B) : s * numer hsB (b * b') = numer hsB b * numer hsB b' :=
  hAB (by
    rw [map_mul, map_mul, algebraMap_numer, algebraMap_numer, algebraMap_numer, Algebra.smul_def,
      Algebra.smul_def, Algebra.smul_def]
    ring)

lemma numer_algebraMap (a : A) : numer hsB (algebraMap A B a) = s * a :=
  hAB (by rw [algebraMap_numer, Algebra.smul_def, map_mul])

/-- **Division by a conductor element in an integrally closed domain.** Let `s B ⊆ A` and let
`γ : A → R` be a ring map into an integrally closed domain with `γ(s) ≠ 0`. If `B` is integral over
`A`, then `b ↦ γ(s b) / γ(s)` is a ring map `Ψ : B → R` extending `γ`. -/
theorem exists_ringHom_mul_eq [Algebra.IsIntegral A B] {R : Type*} [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] (γ : A →+* R) (hγ : γ s ≠ 0) :
    ∃ Ψ : B →+* R, (∀ a, Ψ (algebraMap A B a) = γ a) ∧ ∀ b, γ s * Ψ b = γ (numer hsB b) := by
  let F := FractionRing R
  have hinj : Function.Injective (algebraMap R F) := IsFractionRing.injective R F
  have hs : algebraMap R F (γ s) ≠ 0 := fun h => hγ (hinj (h.trans (map_zero _).symm))
  let Θ : B →+* F :=
    { toFun := fun b => algebraMap R F (γ (numer hsB b)) / algebraMap R F (γ s)
      map_one' := by rw [numer_one hAB, div_self hs]
      map_mul' := fun b b' => by
        have key : algebraMap R F (γ (numer hsB (b * b'))) * algebraMap R F (γ s) =
            algebraMap R F (γ (numer hsB b)) * algebraMap R F (γ (numer hsB b')) := by
          simp only [← map_mul]
          rw [mul_comm, numer_mul hAB]
        rw [div_mul_div_comm, div_eq_div_iff hs (mul_ne_zero hs hs), ← key]
        ring
      map_zero' := by rw [numer_zero hAB, map_zero, map_zero, zero_div]
      map_add' := fun b b' => by rw [numer_add hAB, map_add, map_add, add_div] }
  have hΘ : ∀ a, Θ (algebraMap A B a) = algebraMap R F (γ a) := fun a => by
    change algebraMap R F (γ (numer hsB _)) / _ = _
    rw [numer_algebraMap hAB, map_mul, map_mul, mul_div_cancel_left₀ _ hs]
  have hcomp : (algebraMap R F).comp γ = Θ.comp (algebraMap A B) := by
    ext a
    exact (hΘ a).symm
  have hint : ∀ b, ∃ y : R, algebraMap R F y = Θ b := fun b =>
    IsIntegrallyClosed.isIntegral_iff.1
      (IsIntegral.map_of_comp_eq γ Θ hcomp (Algebra.IsIntegral.isIntegral b))
  let e : R ≃+* (algebraMap R F).range :=
    RingEquiv.ofBijective (algebraMap R F).rangeRestrict
      ⟨fun x y h => hinj (congrArg Subtype.val h), (algebraMap R F).rangeRestrict_surjective⟩
  let Ψ : B →+* R := e.symm.toRingHom.comp
    (Θ.codRestrict (algebraMap R F).range fun b => (hint b).imp fun _ h => h)
  have hΨ : ∀ b, algebraMap R F (Ψ b) = Θ b := fun b => by
    have : e (Ψ b) = ⟨Θ b, (hint b).imp fun _ h => h⟩ := e.apply_symm_apply _
    exact congrArg Subtype.val this
  refine ⟨Ψ, fun a => hinj (by rw [hΨ, hΘ]), fun b => hinj ?_⟩
  rw [map_mul, hΨ]
  change _ * (algebraMap R F (γ (numer hsB b)) / _) = _
  rw [mul_div_cancel₀ _ hs]

include hsB in
/-- **A smooth point has one branch**: if `A` is an integrally closed domain, `s ≠ 0`, `s B ⊆ A`
and `s` is a non-zero-divisor on the integral `A`-algebra `B ⊇ A`, then `A = B`. -/
theorem algebraMap_surjective_of_isIntegrallyClosed [IsDomain A] [IsIntegrallyClosed A]
    [Algebra.IsIntegral A B] (hs : s ≠ 0) (hreg : ∀ b : B, s • b = 0 → b = 0) :
    Function.Surjective (algebraMap A B) := by
  obtain ⟨Ψ, -, hΨ⟩ := exists_ringHom_mul_eq hAB hsB (RingHom.id A) hs
  intro b
  refine ⟨Ψ b, ?_⟩
  have h := hreg (b - algebraMap A B (Ψ b)) (by
    have h1 := hΨ b
    simp only [RingHom.id_apply] at h1
    rw [smul_sub, ← algebraMap_numer hsB b, ← h1, map_mul, Algebra.smul_def, sub_self])
  exact (sub_eq_zero.1 h).symm

end Conductor

section Lower

/-! ### `A` is not integrally closed in `L` at a node -/

variable {k : Type u} [Field k] {A : Type v} [CommRing A] [Algebra k A] [IsLocalRing A]
  [IsNoetherianRing A]

/-- An idempotent element is integral. -/
lemma isIntegral_of_isIdempotentElem {R S : Type*} [CommRing R] [Nontrivial R] [CommRing S]
    [Algebra R S] {x : S}
    (hx : IsIdempotentElem x) : IsIntegral R x := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.X, ?_, ?_⟩
  · exact (Polynomial.monic_X_pow 2).sub_of_left (by
      rw [Polynomial.degree_X, Polynomial.degree_X_pow]
      exact_mod_cast one_lt_two)
  · rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X, pow_two, hx.eq, sub_self]

/-- A nilpotent element is integral. -/
lemma isIntegral_of_isNilpotent {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {x : S}
    (hx : IsNilpotent x) : IsIntegral R x := by
  obtain ⟨n, hn⟩ := hx
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    have : Subsingleton S := subsingleton_of_zero_eq_one (by rw [← hn, pow_zero])
    rw [Subsingleton.elim x 0]
    exact isIntegral_zero
  · exact IsIntegral.of_pow hpos (by rw [hn]; exact isIntegral_zero)

/-- An idempotent of a local ring is `0` or `1`. -/
lemma eq_zero_or_eq_one_of_isIdempotentElem {R : Type*} [CommRing R] [IsLocalRing R] {a : R}
    (ha : IsIdempotentElem a) : a = 0 ∨ a = 1 := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self a with h | h
  · right
    obtain ⟨u, rfl⟩ := h
    have : (u : R) * u = u * 1 := by rw [mul_one]; exact ha.eq
    exact u.isUnit.mul_left_cancel this
  · left
    obtain ⟨u, hu⟩ := h
    have h1 : (1 - a) * a = 0 := by rw [sub_mul, one_mul, ha.eq, sub_self]
    rw [← hu] at h1
    exact (Units.mul_right_eq_zero u).1 h1

/-- **At a node, `A` is not integrally closed in any `A`-algebra `L ⊇ A` in which an element
`s ∈ 𝔪_A` becomes invertible.** If it were, `A_s` would be a field (it is reduced, zero-dimensional
and has no nontrivial idempotents) and `A` an integrally closed domain of dimension one, i.e. a
discrete valuation ring; then `A` and its completion are regular, so `Â` is a domain, but
`k[[u, v]]/(uv)` is not. -/
theorem false_of_isIntegrallyClosedIn_of_formalNode [Ring.KrullDimLE 1 A]
    (e : Completion A ≃ₐ[k] FormalUV k) {s : A} (hs : s ∈ maximalIdeal A) {L : Type w}
    [CommRing L] [Algebra A L] (hAL : Function.Injective (algebraMap A L))
    (hsL : IsUnit (algebraMap A L s))
    (hint : ∀ y : L, IsIntegral A y → ∃ a : A, algebraMap A L a = y) : False := by
  -- `s` is a non-zero-divisor
  have hsnz : s ∈ nonZeroDivisors A := by
    refine mem_nonZeroDivisors_iff_right.2 fun a ha => hAL ?_
    rw [map_zero]
    have h : algebraMap A L a * algebraMap A L s = 0 := by rw [← map_mul, ha, map_zero]
    exact (hsL.mul_left_eq_zero).1 h
  let As := Localization.Away s
  have hinjA : Function.Injective (algebraMap A As) :=
    IsLocalization.injective As (Submonoid.powers_le.2 hsnz)
  let j : As →+* L := IsLocalization.Away.lift s hsL
  have hj : ∀ a, j (algebraMap A As a) = algebraMap A L a := fun a =>
    IsLocalization.lift_eq _ a
  have hjinj : Function.Injective j := by
    refine (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers s) j).2 fun x y => ?_
    rw [hj, hj]
    exact ⟨fun h => by rw [hinjA h], fun h => by rw [hAL h]⟩
  have hintAs : ∀ y : As, IsIntegral A y → ∃ a : A, algebraMap A As a = y := by
    intro y hy
    have hcomp : (algebraMap A L).comp (RingHom.id A) = j.comp (algebraMap A As) := by
      ext a
      exact (hj a).symm
    obtain ⟨a, ha⟩ := hint (j y) (IsIntegral.map_of_comp_eq (RingHom.id A) j hcomp hy)
    exact ⟨a, hjinj (by rw [hj, ha])⟩
  have : Nontrivial L := hAL.nontrivial
  have hnt : Nontrivial As := j.domain_nontrivial
  -- `A` is reduced: `nil(A) = s · nil(A)`, then Nakayama
  have hred : IsReduced A := by
    have hN : nilradical A = ⊥ := by
      refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal A) (nilradical A)
        (IsNoetherian.noetherian _) ?_ (IsLocalRing.maximalIdeal_le_jacobson _)
      intro n hn
      have hy : IsNilpotent (IsLocalization.mk' As n (⟨s, Submonoid.mem_powers s⟩ :
          Submonoid.powers s)) := by
        obtain ⟨m, hm⟩ := (mem_nilradical.1 hn)
        refine ⟨m, ?_⟩
        rw [← IsLocalization.mk'_pow, hm, IsLocalization.mk'_zero]
      obtain ⟨a, ha⟩ := hintAs _ (isIntegral_of_isNilpotent hy)
      have hna : n = a * s := by
        rw [eq_comm, IsLocalization.mk'_eq_iff_eq_mul] at ha
        exact hinjA (by rw [ha, map_mul])
      have hanil : a ∈ nilradical A :=
        mem_nilradical.2 ((IsNilpotent.map_iff hinjA).1 (ha ▸ hy))
      rw [hna, mul_comm, Ideal.smul_eq_mul]
      exact Ideal.mul_mem_mul hs hanil
    refine ⟨fun x hx => ?_⟩
    have : x ∈ nilradical A := hx
    rw [hN] at this
    exact this
  have : IsReduced As := inferInstanceAs (IsReduced (Localization (Submonoid.powers s)))
  -- `A_s` is zero-dimensional
  have hdim0 : Ring.KrullDimLE 0 As := by
    refine Ring.KrullDimLE.mk₀ fun P hP => ?_
    obtain ⟨M, hM, hPM⟩ := Ideal.exists_le_maximal P hP.ne_top
    have hsM : s ∉ M.comap (algebraMap A As) := fun h =>
      hM.ne_top (Ideal.eq_top_of_isUnit_mem _ h (IsLocalization.Away.algebraMap_isUnit s))
    have hqM : (M.comap (algebraMap A As)).IsPrime := Ideal.comap_isPrime _ M
    have hmin : M.comap (algebraMap A As) ∈ minimalPrimes A := by
      rcases Ring.krullDimLE_one_iff.1 inferInstance _ hqM with h | h
      · exact h
      · exact absurd ((IsLocalRing.eq_maximalIdeal h) ▸ hs) hsM
    have hle : P.comap (algebraMap A As) ≤ M.comap (algebraMap A As) := Ideal.comap_mono hPM
    have heq : P.comap (algebraMap A As) = M.comap (algebraMap A As) :=
      le_antisymm hle (hmin.2 ⟨Ideal.comap_isPrime _ P, bot_le⟩ hle)
    have heq' : Ideal.under A P = Ideal.under A M := heq
    have : P = M := by
      rw [← IsLocalization.map_under (Submonoid.powers s) As P,
        ← IsLocalization.map_under (Submonoid.powers s) As M, heq']
    exact this ▸ hM
  have hart : IsArtinianRing As :=
    isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.2 ⟨inferInstance, hdim0⟩
  -- `A_s` has no nontrivial idempotents, hence is local, hence a field
  have hloc : IsLocalRing As := by
    classical
    refine IsLocalRing.of_unique_max_ideal ?_
    obtain ⟨M, hM⟩ := Ideal.exists_maximal As
    refine ⟨M, hM, fun N hN => ?_⟩
    by_contra hNM
    let E := IsArtinianRing.equivPi As
    let I₁ : MaximalSpectrum As := ⟨M, hM⟩
    let I₂ : MaximalSpectrum As := ⟨N, hN⟩
    have hI : I₁ ≠ I₂ := fun h => hNM (congrArg MaximalSpectrum.asIdeal h).symm
    let x : As := E.symm (Pi.single I₁ 1)
    have hx : IsIdempotentElem x := by
      change x * x = x
      rw [← map_mul]
      congr 1
      ext I
      by_cases hI' : I = I₁
      · subst hI'
        simp
      · simp [hI']
    obtain ⟨a, ha⟩ := hintAs x (isIntegral_of_isIdempotentElem hx)
    have hia : IsIdempotentElem a := hinjA (by rw [map_mul, ha]; exact hx.eq)
    have hEx : E x = Pi.single I₁ 1 := E.apply_symm_apply _
    rcases eq_zero_or_eq_one_of_isIdempotentElem hia with h0 | h1
    · have h0' : E x I₁ = 0 := by rw [← ha, h0, map_zero, map_zero]; rfl
      rw [hEx, Pi.single_eq_same] at h0'
      have : Nontrivial (As ⧸ I₁.asIdeal) := Ideal.Quotient.nontrivial_iff.2 hM.ne_top
      exact one_ne_zero h0'
    · have h1' : E x I₂ = 1 := by rw [← ha, h1, map_one, map_one]; rfl
      rw [hEx, Pi.single_eq_of_ne hI.symm] at h1'
      have : Nontrivial (As ⧸ I₂.asIdeal) := Ideal.Quotient.nontrivial_iff.2 hN.ne_top
      exact zero_ne_one h1'
  have hfield : IsField As := IsArtinianRing.isField_of_isReduced_of_isLocalRing As
  let : Field As := hfield.toField
  -- `A` is an integrally closed domain
  have hdom : IsDomain A := hinjA.isDomain (algebraMap A As)
  have hic : IsIntegrallyClosed A := by
    rw [isIntegrallyClosed_iff (FractionRing A)]
    intro x hx
    let g : FractionRing A →+* As := IsFractionRing.lift hinjA
    have hg : ∀ a, g (algebraMap A (FractionRing A) a) = algebraMap A As a := fun a =>
      IsFractionRing.lift_algebraMap hinjA a
    have hcomp : (algebraMap A As).comp (RingHom.id A) = g.comp (algebraMap A (FractionRing A)) := by
      ext a
      exact (hg a).symm
    obtain ⟨a, ha⟩ := hintAs (g x) (IsIntegral.map_of_comp_eq (RingHom.id A) g hcomp hx)
    exact ⟨a, g.injective (by rw [hg, ha])⟩
  have hnf : ¬ IsField A := by
    intro h
    have hm : maximalIdeal A = ⊥ := (IsLocalRing.isField_iff_maximalIdeal_eq).1 h
    have : s = 0 := by rw [← Ideal.mem_bot, ← hm]; exact hs
    exact (nonZeroDivisors.ne_zero hsnz) this
  -- so `A` is a discrete valuation ring, hence regular
  have hdvr : IsDiscreteValuationRing A := by
    have key := (IsDiscreteValuationRing.TFAE A hnf).out 0 3
    refine key.2 ⟨hic, maximalIdeal A,
      ⟨fun h => hnf ((IsLocalRing.isField_iff_maximalIdeal_eq).2 h), inferInstance⟩, ?_⟩
    rintro P ⟨hP, hPp⟩
    exact IsLocalRing.eq_maximalIdeal (hPp.isMaximal_of_ne_bot hP)
  have hreg : IsRegularLocalRing A := inferInstance
  have : IsRegularLocalRing (Completion A) :=
    DeJongAlterations.Algebra.CompletionRegularityAscent.isRegularLocalRing_completion A
  have : IsDomain (Completion A) :=
    DeJongAlterations.Algebra.RegularLocalDomain.isDomain_of_isRegularLocalRing (Completion A)
  exact not_isDomain_formalUV (e.symm.toMulEquiv.isDomain)

end Lower

section Node

/-! ### The node: `δ(A) ≤ 1` and the two branches -/

variable {k : Type u} [Field k] {A : Type v} [CommRing A] [Algebra k A] [IsLocalRing A]
  [IsNoetherianRing A]

variable (e : Completion A ≃ₐ[k] FormalUV k)

/-- The two formal branches of `A` at a node: `A → Â ≅ k[[u, v]]/(uv) → k[[t]] × k[[t]]`. -/
def nodeBranches : A →ₐ[k] PowerSeries k × PowerSeries k :=
  (branchMap k).comp (e.toAlgHom.comp (IsScalarTower.toAlgHom k A (Completion A)))

omit [IsNoetherianRing A] in
lemma nodeBranches_apply (a : A) :
    nodeBranches e a = branchMap k (e (algebraMap A (Completion A) a)) := rfl

lemma nodeBranches_injective : Function.Injective (nodeBranches e) :=
  branchMap_injective.comp (e.injective.comp (algebraMap_injective A))

/-- The constant term of the branches of `a`: the residue class of `a` in `k`. -/
def nodeResidue (a : A) : k := PowerSeries.constantCoeff (nodeBranches e a).1

omit [IsNoetherianRing A] in
lemma nodeResidue_snd (a : A) :
    PowerSeries.constantCoeff (nodeBranches e a).2 = nodeResidue e a :=
  (constantCoeff_branchMap_fst_eq_snd _).symm

/-- The residue as a ring map `A → k`. -/
def nodeResidueHom : A →+* k :=
  (PowerSeries.constantCoeff.comp (RingHom.fst _ _)).comp (nodeBranches e).toRingHom

omit [IsNoetherianRing A] in
lemma nodeResidueHom_apply (a : A) : nodeResidueHom e a = nodeResidue e a := rfl

omit [IsNoetherianRing A] in
lemma nodeResidue_algebraMap (c : k) : nodeResidue e (algebraMap k A c) = c := by
  rw [nodeResidue, AlgHom.commutes]
  simp

omit [IsNoetherianRing A] in
/-- **`a ∈ 𝔪_A` iff its branches have constant term `0`.** -/
lemma mem_maximalIdeal_iff_nodeResidue_eq_zero (a : A) :
    a ∈ maximalIdeal A ↔ nodeResidue e a = 0 := by
  have hsurj : Function.Surjective (nodeResidueHom e) := fun c =>
    ⟨algebraMap k A c, nodeResidue_algebraMap e c⟩
  rw [← IsLocalRing.ker_eq_maximalIdeal (nodeResidueHom e) hsurj, RingHom.mem_ker,
    nodeResidueHom_apply]

omit [IsNoetherianRing A] in
lemma sub_algebraMap_nodeResidue_mem (a : A) :
    a - algebraMap k A (nodeResidue e a) ∈ maximalIdeal A := by
  rw [mem_maximalIdeal_iff_nodeResidue_eq_zero e, ← nodeResidueHom_apply e, map_sub,
    nodeResidueHom_apply e, nodeResidueHom_apply e, nodeResidue_algebraMap e, sub_self]

variable {B : Type w} [CommRing B] [Algebra A B] [Algebra k B] [IsScalarTower k A B]
  [Module.Finite A B]

/-- The image of `A` in `B` as a `k`-subalgebra. -/
abbrev rangeIn (k A B : Type*) [Field k] [CommRing A] [Algebra k A] [CommRing B] [Algebra A B]
    [Algebra k B] [IsScalarTower k A B] : Subalgebra k B :=
  (IsScalarTower.toAlgHom k A B).range

/-- **The quotient `B / A` at a node.** Let `Â ≅ k[[u, v]]/(uv)`, let `B ⊇ A` be a finite `A`-algebra
and `s ∈ A` with `s B ⊆ A`, a non-zero-divisor on `B`. Then `B / A` has dimension at most one over
`k`, and if `B ≠ A`, there is a surjective ring map `B → k × k` (the values at the two branches)
restricting to the residue map on `A`. -/
theorem node_quotient (hAB : Function.Injective (algebraMap A B)) {s : A}
    (hsB : ∀ b : B, ∃ a : A, s • b = algebraMap A B a) (hreg : ∀ b : B, s • b = 0 → b = 0) :
    FiniteDimensional k (B ⧸ Subalgebra.toSubmodule (rangeIn k A B)) ∧
      finrank k (B ⧸ Subalgebra.toSubmodule (rangeIn k A B)) ≤ 1 ∧
      (rangeIn k A B ≠ ⊤ → ∃ χ : B →+* k × k, Function.Surjective χ ∧
        ∀ a : A, χ (algebraMap A B a) = (nodeResidue e a, nodeResidue e a)) := by
  -- `s` is a non-zero-divisor of `A` and of `Â`
  have hsnz : s ∈ nonZeroDivisors A := by
    refine mem_nonZeroDivisors_iff_right.2 fun a ha => hAB ?_
    rw [map_zero]
    refine hreg _ ?_
    rw [Algebra.smul_def, ← map_mul, mul_comm, ha, map_zero]
  have hŝ : ∀ x : Completion A, algebraMap A (Completion A) s * x = 0 → x = 0 := by
    intro x hx
    have := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Completion A) hsnz
    exact this (show s • x = s • (0 : Completion A) by rw [smul_zero, Algebra.smul_def, hx])
  have hβne : ∀ i : Fin 2,
      (if i = 0 then (nodeBranches e s).1 else (nodeBranches e s).2) ≠ 0 := by
    intro i hi
    let c : FormalUV k := coordinate k i
    have hc : branchMap k c = if i = 0 then (PowerSeries.X, 0) else (0, PowerSeries.X) := by
      fin_cases i
      · exact branchMap_coordinate_zero
      · exact branchMap_coordinate_one
    have h1 : branchMap k (e (algebraMap A (Completion A) s) * c) = 0 := by
      rw [map_mul, ← nodeBranches_apply, hc]
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue, if_true] at hi ⊢
        ext1 <;> simp [hi]
      · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, if_false] at hi ⊢
        ext1 <;> simp [hi]
    have h2 : e (algebraMap A (Completion A) s) * c = 0 :=
      branchMap_injective (h1.trans (map_zero _).symm)
    have h3 : e.symm c = 0 := hŝ _ (by
      apply e.injective
      rw [map_mul, AlgEquiv.apply_symm_apply, map_zero, h2])
    have h4 : c = 0 := by rw [← e.apply_symm_apply c, h3, map_zero]
    have h5 := congrArg (branchMap k) h4
    rw [hc, map_zero] at h5
    fin_cases i
    · simpa using congrArg Prod.fst h5
    · simpa using congrArg Prod.snd h5
  have hβ0 : (nodeBranches e s).1 ≠ 0 := by simpa using hβne 0
  have hβ1 : (nodeBranches e s).2 ≠ 0 := by simpa using hβne 1
  set β := nodeBranches e
  obtain ⟨Ψ₀, hΨ₀a, hΨ₀⟩ := exists_ringHom_mul_eq hAB hsB
    ((RingHom.fst _ _).comp β.toRingHom) hβ0
  obtain ⟨Ψ₁, hΨ₁a, hΨ₁⟩ := exists_ringHom_mul_eq hAB hsB
    ((RingHom.snd _ _).comp β.toRingHom) hβ1
  let Ψ : B →+* PowerSeries k × PowerSeries k := Ψ₀.prod Ψ₁
  have hΨa : ∀ a, Ψ (algebraMap A B a) = β a := fun a => Prod.ext (hΨ₀a a) (hΨ₁a a)
  have hΨ : ∀ b, β s * Ψ b = β (numer hsB b) := fun b => Prod.ext (hΨ₀ b) (hΨ₁ b)
  have hΨk : ∀ c : k, Ψ (algebraMap k B c) = algebraMap k _ c := fun c => by
    rw [IsScalarTower.algebraMap_apply k A B, hΨa, AlgHom.commutes]
  let Ψl : B →ₗ[k] PowerSeries k × PowerSeries k :=
    { toFun := Ψ
      map_add' := map_add Ψ
      map_smul' := fun c b => by
        rw [Algebra.smul_def, map_mul, hΨk, RingHom.id_apply, Algebra.smul_def] }
  set W := LinearMap.range (branchMap k).toLinearMap
  let T : B →ₗ[k] (PowerSeries k × PowerSeries k) ⧸ W := W.mkQ ∘ₗ Ψl
  have hA : Subalgebra.toSubmodule (rangeIn k A B) ≤ LinearMap.ker T := by
    rintro _ ⟨a, rfl⟩
    rw [LinearMap.mem_ker]
    change W.mkQ (Ψ (algebraMap A B a)) = 0
    rw [hΨa, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨e (algebraMap A (Completion A) a), rfl⟩
  have hker : LinearMap.ker T ≤ Subalgebra.toSubmodule (rangeIn k A B) := by
    intro b hb
    rw [LinearMap.mem_ker] at hb
    change W.mkQ (Ψ b) = 0 at hb
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hb
    obtain ⟨y, hy⟩ := hb
    change branchMap k y = Ψ b at hy
    have h1 : branchMap k (e (algebraMap A (Completion A) (numer hsB b))) =
        branchMap k (e (algebraMap A (Completion A) s) * y) := by
      rw [map_mul, hy, ← nodeBranches_apply, ← nodeBranches_apply, hΨ]
    have h2 : algebraMap A (Completion A) (numer hsB b) =
        algebraMap A (Completion A) s * e.symm y := by
      apply e.injective
      rw [map_mul, AlgEquiv.apply_symm_apply]
      exact branchMap_injective h1
    have h3 : numer hsB b ∈ Ideal.span {s} := by
      rw [← comap_map A (Ideal.span {s}), Ideal.mem_comap, h2]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self s))
    obtain ⟨a', ha'⟩ := Ideal.mem_span_singleton'.1 h3
    refine ⟨a', ?_⟩
    have h4 := hreg (b - algebraMap A B a') (by
      rw [smul_sub, ← algebraMap_numer hsB b, ← ha', map_mul, Algebra.smul_def, mul_comm,
        sub_self])
    exact (sub_eq_zero.1 h4).symm
  have hkerT : LinearMap.ker T = Subalgebra.toSubmodule (rangeIn k A B) := le_antisymm hker hA
  let T' := (Subalgebra.toSubmodule (rangeIn k A B)).liftQ T hA
  have hT'inj : Function.Injective T' := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ hker
  obtain ⟨hfdW, hrkW⟩ := finrank_quotient_range_branchMap_le_one (K := k)
  have hrkW' : finrank k ((PowerSeries k × PowerSeries k) ⧸ W) ≤ 1 := hrkW
  have hfdW' : FiniteDimensional k ((PowerSeries k × PowerSeries k) ⧸ W) := hfdW
  have hfd : FiniteDimensional k (B ⧸ Subalgebra.toSubmodule (rangeIn k A B)) :=
    Module.Finite.of_injective T' hT'inj
  have hrk : finrank k (B ⧸ Subalgebra.toSubmodule (rangeIn k A B)) ≤ 1 :=
    (LinearMap.finrank_le_finrank_of_injective hT'inj).trans hrkW'
  refine ⟨hfd, hrk, fun hne => ?_⟩
  -- `B ≠ A`: then `T'` is bijective
  have hnt : Nontrivial (B ⧸ Subalgebra.toSubmodule (rangeIn k A B)) := by
    refine Submodule.Quotient.nontrivial_iff.2 fun h => hne ?_
    exact Subalgebra.toSubmodule_injective (h.trans Algebra.top_toSubmodule.symm)
  have hpos : 0 < finrank k (B ⧸ Subalgebra.toSubmodule (rangeIn k A B)) := finrank_pos
  have hrk1 : finrank k (B ⧸ Subalgebra.toSubmodule (rangeIn k A B)) =
      finrank k ((PowerSeries k × PowerSeries k) ⧸ W) := by
    have := LinearMap.finrank_le_finrank_of_injective hT'inj
    omega
  have hT'surj : Function.Surjective T' :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrk1).1 hT'inj
  have hTsurj : ∀ w, ∃ b, Ψ b - w ∈ W := by
    intro w
    obtain ⟨q, hq⟩ := hT'surj (W.mkQ w)
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    refine ⟨b, ?_⟩
    have : W.mkQ (Ψ b) = W.mkQ w := hq
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at this
    exact this
  -- the constant terms of the two branches
  let ρ : PowerSeries k × PowerSeries k →+* k × k :=
    (PowerSeries.constantCoeff.comp (RingHom.fst _ _)).prod
      (PowerSeries.constantCoeff.comp (RingHom.snd _ _))
  have hρβ : ∀ a, ρ (β a) = (nodeResidue e a, nodeResidue e a) := fun a =>
    Prod.ext rfl (nodeResidue_snd e a)
  have hρW : ∀ w ∈ W, ρ w = (PowerSeries.constantCoeff w.1, PowerSeries.constantCoeff w.1) := by
    rintro _ ⟨y, rfl⟩
    exact Prod.ext rfl (constantCoeff_branchMap_fst_eq_snd y).symm
  refine ⟨ρ.comp Ψ, fun c => ?_, fun a => by rw [RingHom.comp_apply, hΨa, hρβ]⟩
  obtain ⟨b, hb⟩ := hTsurj (PowerSeries.C c.1, PowerSeries.C c.2)
  set d := PowerSeries.constantCoeff (Ψ b - (PowerSeries.C c.1, PowerSeries.C c.2)).1
  refine ⟨b - algebraMap k B d, ?_⟩
  have h1 := hρW _ hb
  rw [map_sub] at h1
  rw [RingHom.comp_apply, map_sub, map_sub, hΨk]
  have h2 : ρ (algebraMap k (PowerSeries k × PowerSeries k) d) = (d, d) := by
    ext <;> simp [ρ]
  have h3 : ρ (PowerSeries.C c.1, PowerSeries.C c.2) = c := by
    ext <;> simp [ρ]
  rw [h2]
  rw [h3] at h1
  rw [sub_eq_iff_eq_add.1 h1]
  ext <;> simp [d]

omit [IsLocalRing A] [IsNoetherianRing A] [Module.Finite A B] in
/-- `s` is a non-zero-divisor on `B` if `B` embeds into an `A`-algebra in which `s` is a unit. -/
lemma smul_eq_zero_of_isUnit {L : Type*} [CommRing L] [Algebra A L] {ι : B →ₐ[A] L}
    (hι : Function.Injective ι) {s : A} (hsL : IsUnit (algebraMap A L s)) (b : B) (h : s • b = 0) :
    b = 0 := by
  apply hι
  rw [map_zero]
  have : algebraMap A L s * ι b = 0 := by rw [← Algebra.smul_def, ← map_smul, h, map_zero]
  exact (hsL.mul_right_eq_zero).1 this

omit [Module.Finite A B] in
include e in
/-- **At a node, `B ≠ A`**: under the hypotheses of `node_quotient` and if `B` is integrally closed
in an `A`-algebra `L ⊇ B` in which `s ∈ 𝔪_A` is invertible. -/
theorem rangeIn_ne_top_of_formalNode [Ring.KrullDimLE 1 A]
    (hAB : Function.Injective (algebraMap A B)) {s : A} (hs : s ∈ maximalIdeal A)
    {L : Type*} [CommRing L] [Algebra A L] (ι : B →ₐ[A] L) (hι : Function.Injective ι)
    (hsL : IsUnit (algebraMap A L s)) (hint : ∀ y : L, IsIntegral A y → y ∈ ι.range) :
    rangeIn k A B ≠ ⊤ := by
  intro htop
  have hsurj : ∀ b : B, ∃ a : A, algebraMap A B a = b := fun b => by
    have : b ∈ rangeIn k A B := htop ▸ Algebra.mem_top
    obtain ⟨a, ha⟩ := this
    exact ⟨a, ha⟩
  refine false_of_isIntegrallyClosedIn_of_formalNode e hs (L := L) ?_ hsL fun y hy => ?_
  · rw [← ι.comp_algebraMap]
    exact hι.comp hAB
  · obtain ⟨b, rfl⟩ := hint y hy
    obtain ⟨a, rfl⟩ := hsurj b
    exact ⟨a, (ι.commutes a).symm⟩

include e in
/-- **An ordinary double point has `δ = 1`** (Temkin, App. B, l. 4392–4393, the case `n = 2`):
if `Â ≅ k[[u, v]]/(uv)`, `B ⊇ A` is a finite `A`-algebra with a conductor element `s ∈ 𝔪_A`
(`s B ⊆ A`), and `B` is integrally closed in an `A`-algebra `L ⊇ B` in which `s` is invertible
(e.g. the normalization), then `dim_k B / A = 1`. -/
theorem delta_eq_one_of_formalNode [Ring.KrullDimLE 1 A]
    (hAB : Function.Injective (algebraMap A B)) {s : A} (hs : s ∈ maximalIdeal A)
    (hsB : ∀ b : B, ∃ a : A, s • b = algebraMap A B a)
    {L : Type*} [CommRing L] [Algebra A L] (ι : B →ₐ[A] L) (hι : Function.Injective ι)
    (hsL : IsUnit (algebraMap A L s)) (hint : ∀ y : L, IsIntegral A y → y ∈ ι.range) :
    FiniteDimensional k (B ⧸ Subalgebra.toSubmodule (rangeIn k A B)) ∧
      delta k (rangeIn k A B) = 1 := by
  obtain ⟨hfd, hrk, -⟩ := node_quotient e hAB hsB (smul_eq_zero_of_isUnit hι hsL)
  have hne := rangeIn_ne_top_of_formalNode e hAB hs ι hι hsL hint
  have hnt : Nontrivial (B ⧸ Subalgebra.toSubmodule (rangeIn k A B)) := by
    refine Submodule.Quotient.nontrivial_iff.2 fun h => hne ?_
    exact Subalgebra.toSubmodule_injective (h.trans Algebra.top_toSubmodule.symm)
  have hpos : 0 < finrank k (B ⧸ Subalgebra.toSubmodule (rangeIn k A B)) := finrank_pos
  exact ⟨hfd, by unfold delta; omega⟩

include e in
/-- **An ordinary double point has two branches** (Temkin, App. B, l. 4382–4383): under the
hypotheses of `delta_eq_one_of_formalNode`, `B` has exactly two maximal ideals, the kernels of the
two components of a surjection `B → k × k` which restricts to the residue map on `A`. -/
theorem card_maximalSpectrum_eq_two_of_formalNode [Ring.KrullDimLE 1 A]
    (hAB : Function.Injective (algebraMap A B)) {s : A} (hs : s ∈ maximalIdeal A)
    (hsB : ∀ b : B, ∃ a : A, s • b = algebraMap A B a)
    {L : Type*} [CommRing L] [Algebra A L] (ι : B →ₐ[A] L) (hι : Function.Injective ι)
    (hsL : IsUnit (algebraMap A L s)) (hint : ∀ y : L, IsIntegral A y → y ∈ ι.range) :
    Nat.card (MaximalSpectrum B) = 2 := by
  obtain ⟨-, -, hχ⟩ := node_quotient e hAB hsB (smul_eq_zero_of_isUnit hι hsL)
  obtain ⟨hfd, hδ⟩ := delta_eq_one_of_formalNode e hAB hs hsB ι hι hsL hint
  have hne := rangeIn_ne_top_of_formalNode e hAB hs ι hι hsL hint
  obtain ⟨χ, hχs, hχa⟩ := hχ hne
  have hχk : ∀ c : k, χ (algebraMap k B c) = (c, c) := fun c => by
    rw [IsScalarTower.algebraMap_apply k A B, hχa, nodeResidue_algebraMap]
  have hχsmul : ∀ (c : k) (b : B), χ (c • b) = (c * (χ b).1, c * (χ b).2) := fun c b => by
    rw [Algebra.smul_def, map_mul, hχk]
    rfl
  obtain ⟨b₀, hb₀⟩ := hχs (1, 0)
  set Q := Subalgebra.toSubmodule (rangeIn k A B)
  have hb₀ne : Submodule.Quotient.mk (p := Q) b₀ ≠ 0 := by
    intro h
    rw [Submodule.Quotient.mk_eq_zero] at h
    obtain ⟨a, ha⟩ := h
    have := congrArg χ ha
    change χ (algebraMap A B a) = χ b₀ at this
    rw [hχa, hb₀] at this
    have h1 := congrArg Prod.fst this
    have h2 := congrArg Prod.snd this
    simp only at h1 h2
    rw [h2] at h1
    exact zero_ne_one h1
  have hdecomp : ∀ x : B, ∃ (a : A) (c : k), x = algebraMap A B a + c • b₀ := by
    intro x
    have hδ' : finrank k (B ⧸ Q) = 1 := hδ
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hb₀ne).1 hδ' (Submodule.Quotient.mk x)
    rw [← Submodule.Quotient.mk_smul, eq_comm, Submodule.Quotient.eq] at hc
    obtain ⟨a, ha⟩ := hc
    exact ⟨a, c, by rw [← sub_eq_iff_eq_add]; exact ha.symm⟩
  -- `b₀ (b₀ - 1) ∈ 𝔪_A B`
  obtain ⟨a₀, c₀, h₀⟩ := hdecomp (b₀ * (b₀ - 1))
  have hχ0 : χ (b₀ * (b₀ - 1)) = 0 := by
    rw [map_mul, map_sub, map_one, hb₀]
    ext <;> simp
  rw [h₀, map_add, hχa, hχsmul, hb₀] at hχ0
  have hr₀ : nodeResidue e a₀ = 0 := by simpa using congrArg Prod.snd hχ0
  have hc₀ : c₀ = 0 := by
    have := congrArg Prod.fst hχ0
    simp only [Prod.fst_add, Prod.fst_zero, hr₀, zero_add, mul_one] at this
    exact this
  rw [hc₀, zero_smul, add_zero] at h₀
  have ha₀ : a₀ ∈ maximalIdeal A := (mem_maximalIdeal_iff_nodeResidue_eq_zero e a₀).2 hr₀
  -- the two maximal ideals
  let χ₁ : B →+* k := (RingHom.fst k k).comp χ
  let χ₂ : B →+* k := (RingHom.snd k k).comp χ
  have hχ₁ : Function.Surjective χ₁ := fun c => by
    obtain ⟨b, hb⟩ := hχs (c, 0)
    exact ⟨b, by simp [χ₁, hb]⟩
  have hχ₂ : Function.Surjective χ₂ := fun c => by
    obtain ⟨b, hb⟩ := hχs (0, c)
    exact ⟨b, by simp [χ₂, hb]⟩
  have hn₁ : (RingHom.ker χ₁).IsMaximal := RingHom.ker_isMaximal_of_surjective χ₁ hχ₁
  have hn₂ : (RingHom.ker χ₂).IsMaximal := RingHom.ker_isMaximal_of_surjective χ₂ hχ₂
  have hb₀₁ : b₀ ∉ RingHom.ker χ₁ := by
    rw [RingHom.mem_ker]
    simp [χ₁, hb₀]
  have hb₀₂ : b₀ ∈ RingHom.ker χ₂ := by
    rw [RingHom.mem_ker]
    simp [χ₂, hb₀]
  have hint' : Algebra.IsIntegral A B := inferInstance
  have hmax : ∀ n : MaximalSpectrum B, n = ⟨_, hn₁⟩ ∨ n = ⟨_, hn₂⟩ := by
    intro n
    have hcomap : n.asIdeal.comap (algebraMap A B) = maximalIdeal A :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal n.asIdeal)
    have hmem : ∀ a ∈ maximalIdeal A, algebraMap A B a ∈ n.asIdeal := fun a ha => by
      rw [← Ideal.mem_comap, hcomap]
      exact ha
    have hprod : b₀ * (b₀ - 1) ∈ n.asIdeal := h₀ ▸ hmem a₀ ha₀
    rcases n.isMaximal.isPrime.mem_or_mem hprod with h | h
    · right
      refine MaximalSpectrum.ext (hn₂.eq_of_le n.isMaximal.ne_top fun x hx => ?_).symm
      obtain ⟨a, c, rfl⟩ := hdecomp x
      rw [RingHom.mem_ker] at hx
      simp [χ₂, hχa, hχsmul, hb₀] at hx
      refine n.asIdeal.add_mem (hmem a ((mem_maximalIdeal_iff_nodeResidue_eq_zero e a).2 hx)) ?_
      rw [Algebra.smul_def]
      exact n.asIdeal.mul_mem_left _ h
    · left
      refine MaximalSpectrum.ext (hn₁.eq_of_le n.isMaximal.ne_top fun x hx => ?_).symm
      obtain ⟨a, c, rfl⟩ := hdecomp x
      rw [RingHom.mem_ker] at hx
      simp [χ₁, hχa, hχsmul, hb₀] at hx
      have hx' : algebraMap A B a + c • b₀ =
          algebraMap A B (a + algebraMap k A c) + c • (b₀ - 1) := by
        rw [map_add, ← IsScalarTower.algebraMap_apply, smul_sub, Algebra.smul_def c (1 : B),
          mul_one]
        ring
      rw [hx']
      have hr : nodeResidue e (a + algebraMap k A c) = 0 := by
        have : nodeResidue e (a + algebraMap k A c) = nodeResidue e a + c := by
          rw [← nodeResidueHom_apply, map_add, nodeResidueHom_apply, nodeResidueHom_apply,
            nodeResidue_algebraMap]
        rw [this, hx]
      refine n.asIdeal.add_mem (hmem _ ((mem_maximalIdeal_iff_nodeResidue_eq_zero e _).2 hr)) ?_
      rw [Algebra.smul_def]
      exact n.asIdeal.mul_mem_left _ h
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨_, hn₁⟩, ⟨_, hn₂⟩, fun h => hb₀₁ ?_, ?_⟩
  · have : RingHom.ker χ₁ = RingHom.ker χ₂ := congrArg MaximalSpectrum.asIdeal h
    rw [this]
    exact hb₀₂
  · ext n
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact hmax n

end Node

section Smooth

/-! ### Smooth points -/

variable {k : Type u} [Field k] {A : Type v} [CommRing A] [Algebra k A] [IsLocalRing A]
  {B : Type w} [CommRing B] [Algebra A B] [Algebra k B] [IsScalarTower k A B]
  [Algebra.IsIntegral A B]

/-- **A smooth point has `δ = 0` and one branch**: if `A` is an integrally closed local domain, and
`B ⊇ A` is integral with a conductor element `s ≠ 0` which is a non-zero-divisor on `B`, then
`B = A`; so `δ(A) = 0` and `B` has exactly one maximal ideal. -/
theorem delta_eq_zero_of_isIntegrallyClosed [IsDomain A] [IsIntegrallyClosed A]
    (hAB : Function.Injective (algebraMap A B)) {s : A} (hs : s ≠ 0)
    (hsB : ∀ b : B, ∃ a : A, s • b = algebraMap A B a) (hreg : ∀ b : B, s • b = 0 → b = 0) :
    rangeIn k A B = ⊤ ∧ delta k (rangeIn k A B) = 0 ∧ Nat.card (MaximalSpectrum B) = 1 := by
  have hsurj := algebraMap_surjective_of_isIntegrallyClosed hAB hsB hs hreg
  have htop : rangeIn k A B = ⊤ := by
    refine eq_top_iff.2 fun b _ => ?_
    obtain ⟨a, rfl⟩ := hsurj b
    exact ⟨a, rfl⟩
  refine ⟨htop, ?_, ?_⟩
  · unfold delta
    rw [htop, Algebra.top_toSubmodule]
    exact finrank_zero_of_subsingleton
  · have : Nontrivial B := hAB.nontrivial
    have : IsLocalRing B := IsLocalRing.of_surjective' (algebraMap A B) hsurj
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun n n' => MaximalSpectrum.ext ?_⟩, ⟨⟨maximalIdeal B, inferInstance⟩⟩⟩
    rw [IsLocalRing.eq_maximalIdeal n.isMaximal, IsLocalRing.eq_maximalIdeal n'.isMaximal]

/-- A one-dimensional Noetherian local ring whose maximal ideal is generated by one element (a
smooth point of a curve) is a discrete valuation ring, hence an integrally closed domain. -/
theorem isDomain_isIntegrallyClosed_of_spanFinrank_le_one [IsNoetherianRing A]
    (hdim : ringKrullDim A = 1) (h : (maximalIdeal A).spanFinrank ≤ 1) :
    IsDomain A ∧ IsIntegrallyClosed A := by
  have : IsRegularLocalRing A :=
    IsRegularLocalRing.of_spanFinrank_maximalIdeal_le A (by rw [hdim]; exact_mod_cast h)
  have : IsDomain A := DeJongAlterations.Algebra.RegularLocalDomain.isDomain_of_isRegularLocalRing A
  have hnf : ¬ IsField A := by
    intro hf
    let : Field A := hf.toField
    have : ringKrullDim A = 0 := ringKrullDim_eq_zero_of_field A
    rw [hdim] at this
    exact one_ne_zero this
  have hne : maximalIdeal A ≠ ⊥ := fun h => hnf ((IsLocalRing.isField_iff_maximalIdeal_eq).2 h)
  have hfg : (maximalIdeal A).FG := IsNoetherian.noetherian _
  have h1 : (maximalIdeal A).spanFinrank = 1 := by
    have h0 : (maximalIdeal A).spanFinrank ≠ 0 := fun h0 =>
      hne ((Submodule.spanFinrank_eq_zero_iff_eq_bot hfg).1 h0)
    omega
  have hp : (maximalIdeal A).IsPrincipal := ((Submodule.spanFinrank_eq_one_iff _).1 h1).1
  have key := (IsDiscreteValuationRing.TFAE A hnf).out 0 4
  have : IsDiscreteValuationRing A := key.2 hp
  exact ⟨inferInstance, inferInstance⟩

end Smooth

section Regular

/-- **A regular local ring of dimension at most one is an integrally closed domain** (a field
or a discrete valuation ring); this applies to the local ring at a smooth point of a curve. -/
theorem isDomain_isIntegrallyClosed_of_isRegularLocalRing {A : Type v} [CommRing A]
    [IsRegularLocalRing A] [Ring.KrullDimLE 1 A] : IsDomain A ∧ IsIntegrallyClosed A := by
  have hdom : IsDomain A := DeJongAlterations.Algebra.RegularLocalDomain.isDomain_of_isRegularLocalRing A
  have hreg := (isRegularLocalRing_iff A).1 inferInstance
  have hle : ringKrullDim A ≤ 1 := Ring.krullDimLE_iff.1 inferInstance
  have hn : (maximalIdeal A).spanFinrank ≤ 1 := by
    rw [← hreg] at hle
    exact_mod_cast hle
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hn with h0 | h1
  · -- dimension zero: `𝔪 = 0`, `A` is a field
    have hfg : (maximalIdeal A).FG := IsNoetherian.noetherian _
    have hbot : maximalIdeal A = ⊥ := (Submodule.spanFinrank_eq_zero_iff_eq_bot hfg).1 h0
    have hf : IsField A := (IsLocalRing.isField_iff_maximalIdeal_eq).2 hbot
    let : Field A := hf.toField
    exact ⟨hdom, inferInstance⟩
  · have hdim : ringKrullDim A = 1 := by rw [← hreg, h1]; rfl
    exact isDomain_isIntegrallyClosed_of_spanFinrank_le_one hdim h1.le

end Regular

end

end DeJongAlterations.StableModification.CurvesField.OrdinaryCompletion
