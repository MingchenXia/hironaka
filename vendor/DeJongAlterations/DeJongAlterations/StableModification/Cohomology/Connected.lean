/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.Geometry.ProjectiveSpaceBaseChange
import DeJongAlterations.StableModification.Cohomology.ConnectedStep
import DeJongAlterations.StableModification.Cohomology.PullbackQcoh
import DeJongAlterations.StableModification.Valuation.SepClosed
import DeJongAlterations.StableModification.ValuationRing.FibreDimension
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Zariski's connectedness theorem over a valuation ring of finite height

Let `V` be a valuation ring with finitely many prime ideals (finite height) such that the fraction
field of `V ⧸ 𝔭` is separably closed for every prime `𝔭` (this holds for every valuation ring with
separably closed fraction field, e.g. the valuation rings of `K^s` in Temkin's method, whose
residue fields at nonzero primes are even algebraically closed). If `f : X → Spec V` is
projective and flat and the generic fibre is connected, then **every fibre of `f` is connected**
(`isPreconnected_fiber_of_isProjectiveOver`, blueprint `thm:sm-zariski-connected`). For `X`
irreducible the generic fibre is an open subset of `X`, hence connected
(`isPreconnected_fiber_of_irreducibleSpace`).

This is the form of Zariski's connectedness theorem used by Temkin, *Stable modification of
relative curves*, J. Algebraic Geom. 19 (2010), in the proof of Lemma 4.4.2 (`semi-stable.tex`
lines 3125–3131: "Applying the Zariski connectedness theorem, we obtain that the `S`-fibers of
`C'` are connected (…) `C'` comes from a curve defined over a noetherian base"). Temkin reduces
to a noetherian base by approximation; we argue directly over `V`.

## The argument

By well-founded induction on the (finite, totally ordered) set of primes: the generic fibre is
connected by hypothesis. For a prime `𝔮 ≠ 0` let `𝔭` be the prime just below `𝔮`, and
`W = (V ⧸ 𝔭)_𝔮`, a valuation ring with exactly two primes. The base change
`X_W = X ×_V Spec W → X` is a preimmersion (`Spec W → Spec V` is a closed immersion followed by a
localization), so its fibres over the two points of `Spec W` are homeomorphic to the fibres of
`X` over `𝔭` and `𝔮` (`isPreconnected_preimage_bcSnd_iff`). The generic fibre of `X_W` is the
basic open set where `c ∈ 𝔮 ∖ 𝔭` is invertible; by induction it is connected, so the ring of
functions on it has no nontrivial idempotents (`eq_zero_or_eq_one_of_isPreconnected`); being
integral over the separably closed field `Frac (V ⧸ 𝔭)`, every such function is a constant up to
nilpotents and `p`-th powers (`exists_pow_sub_isNilpotent_of_isIntegral`). This is the hypothesis
of the height-one step `isPreconnected_closedFibre_of_heightOne` (`ConnectedStep.lean`), which
gives the connectedness of the closed fibre of `X_W`, i.e. of the fibre of `X` over `𝔮`.

## Main results

* `isProjectiveOver_bcSnd`: projectivity is stable under base change of the coefficient ring.
* `isPreconnected_preimage_bcSnd_iff`: fibres of a base change along a preimmersion.
* `eq_zero_or_eq_one_of_isPreconnected`: functions on a connected open have trivial idempotents.
* `exists_isNilpotent_of_isPreconnected_generic` (blueprint `lem:sm-conn-generic`).
* `isPreconnected_fiber_of_adjacent` (the inductive step).
* `isPreconnected_fiber_of_isProjectiveOver`, `isConnected_fiber_of_isProjectiveOver` (blueprint
  `thm:sm-zariski-connected`) and `isPreconnected_fiber_of_irreducibleSpace`,
  `isConnected_fiber_of_irreducibleSpace` (blueprint `cor:sm-zariski-irreducible`);
  `nonempty_fiber_of_flat`: flat universally closed morphisms from a nonempty scheme are
  surjective.
* `isSepClosed_fractionRing_quotient`: the separable closedness hypothesis holds for valuation
  rings with separably closed fraction field.
* `bijective_structureCoeff_closedFibre`, `finrank_cechCohomology_zero_closedFibre` (blueprint
  `cor:sm-h0-closed-fibre`): a connected reduced closed fibre over an algebraically closed residue
  field has only constant functions (`h⁰ = 1`, also in the Čech form of
  `exists_eulerChar_fibre_valuation`).

## Not proved here

The second use of Zariski's theorem in Temkin's proof of Lemma 4.4.2 (line 3133, "`Z` is
connected because otherwise `C` is not normal at `x`"), connectedness of the fibres of a proper
birational morphism onto a normal curve over a valuation ring, is not proved in this file; it does
not follow from the results here and a genus count (blueprint remark `rem:sm-conn-birational`).
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Limits
open DeJongAlterations.Geometry.ProjectiveSpaceBaseChange
open DeJongAlterations.Geometry.BlowupProjectiveEmbedding

namespace DeJongAlterations.StableModification.Cohomology.Connected

noncomputable section

set_option backward.isDefEq.respectTransparency false

section BaseChange

/-- **Projectivity is stable under base change** of the coefficient ring: if `X → Spec A` is a
closed subscheme of `ℙⁿ_A`, then `X ×_A Spec B` is a closed subscheme of `ℙⁿ_B`. -/
theorem isProjectiveOver_bcSnd {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of A)} (hp : IsProjectiveOver p) :
    IsProjectiveOver (bcSnd φ p) := by
  obtain ⟨n, i, hi, hcomp⟩ := hp
  have H := isPullback_projectiveCoefficientMap φ n
  let j : pullback p (Spec.map (CommRingCat.ofHom φ)) ⟶ projectiveSpace B n :=
    H.lift (bcFst φ p ≫ i) (bcSnd φ p) (by rw [Category.assoc, hcomp]; exact pullback.condition)
  have hj : j ≫ projectiveSpaceStructure B n = bcSnd φ p := H.lift_snd _ _ _
  have hj' : j ≫ projectiveCoefficientMap φ n = bcFst φ p ≫ i := H.lift_fst _ _ _
  have S : IsPullback (bcFst φ p) j i (projectiveCoefficientMap φ n) := by
    refine IsPullback.of_bot ?_ hj'.symm H
    rw [hj, hcomp]
    exact IsPullback.of_hasPullback p (Spec.map (CommRingCat.ofHom φ))
  have : IsClosedImmersion i := hi
  have : IsClosedImmersion j :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) S inferInstance
  exact ⟨n, j, this, hj⟩

/-- The image of the fibre of a base change `X ×_A Spec B` over `Q ∈ Spec B` is the fibre of `X`
over the image of `Q`. -/
theorem bcFst_image_preimage_singleton {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of A)) (Q : Spec (CommRingCat.of B)) :
    bcFst φ p '' (bcSnd φ p ⁻¹' {Q}) = p ⁻¹' {Spec.map (CommRingCat.ofHom φ) Q} := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hz ⊢
    rw [← hz, ← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  · intro hx
    obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback x Q hx
    exact ⟨z, hz2, hz1⟩

/-- **Fibres of a base change along a preimmersion** (blueprint `lem:sm-conn-fibre-base-change`):
if `Spec B → Spec A` is a preimmersion, the fibre of `X ×_A Spec B` over `Q` is homeomorphic to the
fibre of `X` over the image of `Q`; in particular one is preconnected iff the other is. -/
theorem isPreconnected_preimage_bcSnd_iff {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    [IsPreimmersion (Spec.map (CommRingCat.ofHom φ))] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of A)) (Q : Spec (CommRingCat.of B)) :
    _root_.IsPreconnected (bcSnd φ p ⁻¹' {Q}) ↔
      _root_.IsPreconnected (p ⁻¹' {Spec.map (CommRingCat.ofHom φ) Q}) := by
  rw [← bcFst_image_preimage_singleton, (bcFst φ p).isEmbedding.isInducing.isPreconnected_image]

end BaseChange

section Idempotents

/-- **Functions on a connected open have trivial idempotents**: if `U ⊆ Y` is a preconnected open
subset of a scheme, `0` and `1` are the only idempotents of `Γ(Y, U)`. -/
theorem eq_zero_or_eq_one_of_isPreconnected {Y : Scheme.{u}} {U : Y.Opens}
    (hU : _root_.IsPreconnected (U : Set Y)) {e : Γ(Y, U)} (he : IsIdempotentElem e) :
    e = 0 ∨ e = 1 := by
  have hcov : (U : Set Y) ⊆ (Y.basicOpen e : Set Y) ∪ Y.basicOpen (1 - e) := by
    intro x hx
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (Y.presheaf.germ U x hx e) with h | h
    · left
      exact (Y.mem_basicOpen e x hx).mpr h
    · right
      rw [SetLike.mem_coe, Y.mem_basicOpen _ x hx, map_sub, map_one]
      exact h
  have hdisj : (U : Set Y) ∩ ((Y.basicOpen e : Set Y) ∩ Y.basicOpen (1 - e)) = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, SetLike.mem_coe, Set.mem_empty_iff_false, iff_false, not_and]
    intro hx h1 h2
    rw [Y.mem_basicOpen e x hx] at h1
    rw [Y.mem_basicOpen _ x hx] at h2
    have := h1.mul h2
    rw [← map_mul, mul_sub, mul_one, he.eq, sub_self, map_zero] at this
    exact not_isUnit_zero this
  rcases (isPreconnected_iff_subset_of_disjoint.mp hU) _ _ (Y.basicOpen e).isOpen
      (Y.basicOpen (1 - e)).isOpen hcov hdisj with h | h
  · right
    apply TopCat.Presheaf.section_ext Y.sheaf U
    intro x hx
    have hu := (Y.mem_basicOpen e x hx).mp (h hx)
    change Y.presheaf.germ U x hx e = Y.presheaf.germ U x hx 1
    rw [map_one]
    exact (IsIdempotentElem.iff_eq_one_of_isUnit hu).mp (he.map _)
  · left
    apply TopCat.Presheaf.section_ext Y.sheaf U
    intro x hx
    have hu := (Y.mem_basicOpen (1 - e) x hx).mp (h hx)
    have h1 := (IsIdempotentElem.iff_eq_one_of_isUnit hu).mp ((he.one_sub).map _)
    change Y.presheaf.germ U x hx e = Y.presheaf.germ U x hx 0
    rw [map_zero]
    rw [map_sub, map_one, sub_eq_self] at h1
    exact h1

end Idempotents

section Generic

variable {W : Type u} [CommRing W] [IsDomain W] [ValuationRing W]

/-- **Functions on a connected generic fibre are constants up to nilpotents** (blueprint
`lem:sm-conn-generic`). Let `W` be a valuation ring with exactly two primes, `c ≠ 0` in the
maximal ideal, `κ` a separably closed fraction field of `W`, and `f : X → Spec W` flat and proper
with preconnected generic fibre. Then every global function `g` of `X` satisfies
`b g ^ m - a` nilpotent for some `m ≥ 1` and `a, b ∈ W`, `b ≠ 0`. -/
theorem exists_isNilpotent_of_isPreconnected_generic
    (hW : ∀ P : Ideal W, P.IsPrime → P = ⊥ ∨ P = IsLocalRing.maximalIdeal W) {c : W}
    (hc0 : c ≠ 0) (hcm : c ∈ IsLocalRing.maximalIdeal W) (κ : Type u) [Field κ] [Algebra W κ]
    [IsFractionRing W κ] [IsSepClosed κ] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of W))
    [Flat f] [IsProper f] (hgen : _root_.IsPreconnected (f ⁻¹' {(⊥ : PrimeSpectrum W)}))
    (g : Γ(X, ⊤)) :
    ∃ m : ℕ, 0 < m ∧ ∃ a b : W, b ≠ 0 ∧
      IsNilpotent (structureCoeff f b * g ^ m - structureCoeff f a) := by
  classical
  let U : X.Opens := X.basicOpen (structureCoeff f c)
  -- the generic fibre is the basic open set of `c`
  have hUset : (U : Set X) = f ⁻¹' {(⊥ : PrimeSpectrum W)} := by
    have h1 : U = f ⁻¹ᵁ (Spec (CommRingCat.of W)).basicOpen ((Scheme.ΓSpecIso _).inv c) := by
      rw [Scheme.preimage_basicOpen]
      rfl
    rw [h1, basicOpen_eq_of_affine]
    ext x
    change c ∉ (f x).asIdeal ↔ f x = (⊥ : PrimeSpectrum W)
    constructor
    · intro hx
      rcases hW _ (f x).isPrime with h | h
      · exact PrimeSpectrum.ext h
      · exact absurd (h ▸ hcm) hx
    · intro hx
      rw [hx]
      exact fun h => hc0 (Ideal.mem_bot.mp h)
  have hidem : ∀ e : Γ(X, U), IsIdempotentElem e → e = 0 ∨ e = 1 := fun e he =>
    eq_zero_or_eq_one_of_isPreconnected (hUset ▸ hgen) he
  -- `Γ(X, U)` is the localization of `Γ(X, 𝒪_X)` at `c`
  have : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have hloc : IsLocalization.Away (structureCoeff f c) Γ(X, U) :=
    isLocalization_basicOpen_of_qcqs isCompact_univ isQuasiSeparated_univ _
  let ρ := algebraMap Γ(X, ⊤) Γ(X, U)
  let σW : W →+* Γ(X, U) := ρ.comp (structureCoeff f)
  have hσW : ∀ w : W, w ≠ 0 → IsUnit (σW w) := by
    intro w hw
    obtain ⟨n, z, hz⟩ := exists_dvd_pow_of_ne_zero hW hcm hw
    have hcu : IsUnit (σW c) := IsLocalization.Away.algebraMap_isUnit (structureCoeff f c)
    have : IsUnit (σW w * σW z) := by rw [← map_mul, ← hz, map_pow]; exact hcu.pow n
    exact isUnit_of_mul_isUnit_left this
  let σκ : κ →+* Γ(X, U) := IsLocalization.lift (M := nonZeroDivisors W) (g := σW)
    (fun w => hσW w (nonZeroDivisors.ne_zero w.2))
  have hσκ : ∀ w : W, σκ (algebraMap W κ w) = σW w := fun w => IsLocalization.lift_eq _ _
  let _ : Algebra κ Γ(X, U) := σκ.toAlgebra
  -- integrality over `κ`
  have hint : (structureCoeff f).IsIntegral := by
    have h := isIntegral_appTop_of_universallyClosed f
    have h' : (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom.IsIntegral :=
      RingHom.isIntegral_of_surjective _
        (Scheme.ΓSpecIso (CommRingCat.of W)).commRingCatIsoToRingEquiv.symm.surjective
    exact RingHom.IsIntegral.trans _ _ h' h
  have hxint : IsIntegral κ (ρ g) := by
    obtain ⟨P, hPm, hP⟩ := hint g
    refine ⟨P.map (algebraMap W κ), hPm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomp : (algebraMap κ Γ(X, U)).comp (algebraMap W κ) = ρ.comp (structureCoeff f) := by
      ext w
      exact hσκ w
    rw [hcomp, ← Polynomial.hom_eval₂, hP, map_zero]
  obtain ⟨m, hm, l, hl⟩ := exists_pow_sub_isNilpotent_of_isIntegral hidem hxint
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := W) l
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  refine ⟨m, hm, a, b, hb0, ?_⟩
  -- the restriction to `U` is nilpotent
  have hres : IsNilpotent (ρ (structureCoeff f b * g ^ m - structureCoeff f a)) := by
    have hbκ : algebraMap W κ b ≠ 0 := fun h =>
      hb0 (IsFractionRing.injective W κ (h.trans (map_zero _).symm))
    have hal : algebraMap W κ a = algebraMap W κ b * l := by
      rw [← hab, mul_div_cancel₀ _ hbκ]
    have heq : ρ (structureCoeff f b * g ^ m - structureCoeff f a) =
        σκ (algebraMap W κ b) * ((ρ g) ^ m - algebraMap κ Γ(X, U) l) := by
      rw [map_sub, map_mul, map_pow, mul_sub]
      change σW b * ρ g ^ m - σW a = σκ (algebraMap W κ b) * ρ g ^ m - σκ (algebraMap W κ b) * σκ l
      rw [← map_mul, ← hal, hσκ, hσκ]
    rw [heq]
    obtain ⟨k, hk⟩ := hl
    exact ⟨k, by rw [mul_pow, hk, mul_zero]⟩
  -- hence nilpotent on `X`, since `c` is a nonzerodivisor
  obtain ⟨k, hk⟩ := hres
  rw [← map_pow, IsLocalization.map_eq_zero_iff (Submonoid.powers (structureCoeff f c))] at hk
  obtain ⟨⟨_, j, rfl⟩, hj⟩ := hk
  refine ⟨k, eq_zero_of_structureCoeff_mul_eq_zero f (pow_ne_zero j hc0) _ ?_⟩
  rw [map_pow]
  exact hj

end Generic

section Induction

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]

/-- **The inductive step** (blueprint `thm:sm-zariski-connected`): let `𝔭 < 𝔮` be primes of the
valuation ring `V` with no prime strictly between them and `Frac (V ⧸ 𝔭)` separably closed, and
`f : X → Spec V` projective and flat. If the fibre over `𝔭` is preconnected, so is the fibre over
`𝔮`. -/
theorem isPreconnected_fiber_of_adjacent {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of V))
    (hf : IsProjectiveOver f) [Flat f] {p q : PrimeSpectrum V} (hpq : p < q)
    (hadj : ∀ r : PrimeSpectrum V, p ≤ r → r ≤ q → r = p ∨ r = q)
    (hsep : IsSepClosed (FractionRing (V ⧸ p.asIdeal)))
    (hp : _root_.IsPreconnected (f ⁻¹' {p})) : _root_.IsPreconnected (f ⁻¹' {q}) := by
  classical
  -- the valuation ring `W = (V ⧸ 𝔭)_𝔮` with two primes
  have hker : RingHom.ker (Ideal.Quotient.mk p.asIdeal) ≤ q.asIdeal := by
    rw [Ideal.mk_ker]
    exact hpq.le
  let Q : Ideal (V ⧸ p.asIdeal) := q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)
  have hQ : Q.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  have : ValuationRing (V ⧸ p.asIdeal) :=
    Function.Surjective.valuationRing (Ideal.Quotient.mk p.asIdeal) Ideal.Quotient.mk_surjective
  have : ValuationRing (Localization.AtPrime Q) :=
    { toPreValuationRing := ValuationRing.preValuationRing_of_isLocalization Q.primeCompl }
  let W := Localization.AtPrime Q
  let φ : V →+* W := algebraMap V W
  have hφ : φ = (algebraMap (V ⧸ p.asIdeal) W).comp (Ideal.Quotient.mk p.asIdeal) :=
    IsScalarTower.algebraMap_eq V (V ⧸ p.asIdeal) W
  have hcomap : ∀ J : Ideal W, J.comap φ =
      (J.comap (algebraMap (V ⧸ p.asIdeal) W)).comap (Ideal.Quotient.mk p.asIdeal) := by
    intro J
    rw [hφ, Ideal.comap_comap]
  have hcomap_inj : Function.Injective (Ideal.comap φ) := by
    intro J J' h
    rw [hcomap, hcomap] at h
    have h' := Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective h
    rw [← IsLocalization.map_under Q.primeCompl W J, ← IsLocalization.map_under Q.primeCompl W J']
    exact congrArg (Ideal.map (algebraMap (V ⧸ p.asIdeal) W)) h'
  have hbot : (⊥ : Ideal W).comap φ = p.asIdeal := by
    rw [hcomap, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).mp
      (IsLocalization.injective W Q.primeCompl_le_nonZeroDivisors), ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker]
  have hmax : (IsLocalRing.maximalIdeal W).comap φ = q.asIdeal := by
    rw [hcomap]
    change ((IsLocalRing.maximalIdeal (Localization.AtPrime Q)).under (V ⧸ p.asIdeal)).comap _ = _
    rw [Localization.AtPrime.under_maximalIdeal, Ideal.comap_map_of_surjective _
      Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
      sup_eq_left.mpr hpq.le]
  have hW : ∀ P : Ideal W, P.IsPrime → P = ⊥ ∨ P = IsLocalRing.maximalIdeal W := by
    intro P hP
    have hle1 : p ≤ ⟨P.comap φ, Ideal.IsPrime.comap φ⟩ := by
      intro x hx
      have hx' : x ∈ (⊥ : Ideal W).comap φ := by rw [hbot]; exact hx
      exact Ideal.comap_mono bot_le hx'
    have hle2 : (⟨P.comap φ, Ideal.IsPrime.comap φ⟩ : PrimeSpectrum V) ≤ q := by
      intro x hx
      have hx' : x ∈ (IsLocalRing.maximalIdeal W).comap φ :=
        Ideal.comap_mono (IsLocalRing.le_maximalIdeal hP.ne_top) hx
      rw [hmax] at hx'
      exact hx'
    rcases hadj _ hle1 hle2 with h | h
    · left
      apply hcomap_inj
      rw [hbot]
      exact congrArg PrimeSpectrum.asIdeal h
    · right
      apply hcomap_inj
      rw [hmax]
      exact congrArg PrimeSpectrum.asIdeal h
  obtain ⟨c, hcq, hcp⟩ := SetLike.exists_of_lt (show p.asIdeal < q.asIdeal from hpq)
  have hc0 : φ c ≠ 0 := by
    intro h
    apply hcp
    rw [← hbot]
    exact h
  have hcm : φ c ∈ IsLocalRing.maximalIdeal W := by
    have : c ∈ (IsLocalRing.maximalIdeal W).comap φ := by rw [hmax]; exact hcq
    exact this
  -- the base change and its fibres
  have hpre : IsPreimmersion (Spec.map (CommRingCat.ofHom φ)) := by
    have e : Spec.map (CommRingCat.ofHom φ) =
        Spec.map (CommRingCat.ofHom (algebraMap (V ⧸ p.asIdeal) W)) ≫
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk p.asIdeal)) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← hφ]
    rw [e]
    have := IsPreimmersion.of_isLocalization (R := V ⧸ p.asIdeal) Q.primeCompl (S := W)
    have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk p.asIdeal))) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    infer_instance
  have hpt_bot : Spec.map (CommRingCat.ofHom φ) (⊥ : PrimeSpectrum W) = p := by
    apply PrimeSpectrum.ext
    exact hbot
  have hpt_max : Spec.map (CommRingCat.ofHom φ) (IsLocalRing.closedPoint W) = q := by
    apply PrimeSpectrum.ext
    exact hmax
  have hf' : IsProjectiveOver (bcSnd φ f) := isProjectiveOver_bcSnd φ hf
  have : IsProper (bcSnd φ f) := hf'.isProper
  have hgen' : _root_.IsPreconnected (bcSnd φ f ⁻¹' {(⊥ : PrimeSpectrum W)}) := by
    rw [isPreconnected_preimage_bcSnd_iff φ f, hpt_bot]
    exact hp
  have hG := exists_isNilpotent_of_isPreconnected_generic hW hc0 hcm
    (FractionRing (V ⧸ p.asIdeal)) (bcSnd φ f) hgen'
  have h := isPreconnected_closedFibre_of_heightOne (bcSnd φ f) hf' hW hc0 hcm hG
  rw [isPreconnected_preimage_bcSnd_iff φ f, hpt_max] at h
  exact h

/-- **Zariski's connectedness theorem over a valuation ring of finite height** (blueprint
`thm:sm-zariski-connected`): let `V` be a valuation ring with finitely many primes such that
`Frac (V ⧸ 𝔭)` is separably closed for every prime `𝔭`, and `f : X → Spec V` projective and flat.
If the generic fibre is preconnected, every fibre is preconnected. -/
theorem isPreconnected_fiber_of_isProjectiveOver [Finite (PrimeSpectrum V)]
    (hsep : ∀ p : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ p.asIdeal)))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of V)) (hf : IsProjectiveOver f) [Flat f]
    (hgen : _root_.IsPreconnected (f ⁻¹' {(⊥ : PrimeSpectrum V)})) (q : PrimeSpectrum V) :
    _root_.IsPreconnected (f ⁻¹' {q}) := by
  classical
  induction q using WellFoundedLT.induction with
  | _ q ih =>
    by_cases hq : q = ⊥
    · rw [hq]
      exact hgen
    -- the prime just below `q`
    have hne : {r : PrimeSpectrum V | r < q}.Nonempty := ⟨⊥, bot_lt_iff_ne_bot.mpr hq⟩
    obtain ⟨p, hpmax⟩ := (Set.toFinite {r : PrimeSpectrum V | r < q}).exists_maximal hne
    have hpq : p < q := hpmax.1
    have hadj : ∀ r : PrimeSpectrum V, p ≤ r → r ≤ q → r = p ∨ r = q := by
      intro r hpr hrq
      rcases hrq.lt_or_eq with h | h
      · left
        exact (hpmax.eq_of_le h hpr).symm
      · right
        exact h
    exact isPreconnected_fiber_of_adjacent f hf hpq hadj (hsep p) (ih p hpq)

omit [ValuationRing V] in
/-- The generic point of `Spec V` is open when `V` has finitely many primes. -/
theorem isOpen_singleton_bot [Finite (PrimeSpectrum V)] :
    IsOpen ({(⊥ : PrimeSpectrum V)} : Set (PrimeSpectrum V)) := by
  classical
  have h : ({(⊥ : PrimeSpectrum V)} : Set (PrimeSpectrum V)) =
      (⋃ r ∈ {r : PrimeSpectrum V | r ≠ ⊥}, PrimeSpectrum.zeroLocus (r.asIdeal : Set V))ᶜ := by
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq,
      PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, exists_prop, not_exists, not_and]
    constructor
    · rintro rfl r hr hle
      exact hr (le_bot_iff.mp hle)
    · intro h
      by_contra hx
      exact h x hx le_rfl
  rw [h, isOpen_compl_iff]
  exact (Set.toFinite _).isClosed_biUnion fun r _ => PrimeSpectrum.isClosed_zeroLocus _

/-- **Zariski's connectedness theorem, irreducible form** (blueprint
`cor:sm-zariski-irreducible`): if moreover `X` is irreducible, every fibre of `f` is
preconnected. -/
theorem isPreconnected_fiber_of_irreducibleSpace [Finite (PrimeSpectrum V)]
    (hsep : ∀ p : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ p.asIdeal)))
    {X : Scheme.{u}} [IrreducibleSpace X] (f : X ⟶ Spec (CommRingCat.of V))
    (hf : IsProjectiveOver f) [Flat f] (q : PrimeSpectrum V) :
    _root_.IsPreconnected (f ⁻¹' {q}) := by
  refine isPreconnected_fiber_of_isProjectiveOver hsep f hf ?_ q
  have hopen : IsOpen (f ⁻¹' {(⊥ : PrimeSpectrum V)}) :=
    isOpen_singleton_bot.preimage f.continuous
  exact ((IrreducibleSpace.isIrreducible_univ X).isPreirreducible.open_subset hopen
    (Set.subset_univ _)).isPreconnected

omit [ValuationRing V] in
/-- **Fibres of a flat universally closed morphism are nonempty**: if `X` is nonempty and
`f : X → Spec V` is flat and universally closed, `f` is surjective. (The image is closed and
stable under generization, so it contains the generic point and its closure.) -/
theorem nonempty_fiber_of_flat {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of V)) [Flat f]
    [UniversallyClosed f] [Nonempty X] (q : PrimeSpectrum V) : (f ⁻¹' {q}).Nonempty := by
  obtain ⟨x⟩ := ‹Nonempty X›
  have hbot : (⊥ : PrimeSpectrum V) ⤳ f x :=
    (PrimeSpectrum.le_iff_specializes _ _).mp bot_le
  obtain ⟨x', -, hx'⟩ := Flat.generalizingMap f hbot
  have hq : (⊥ : PrimeSpectrum V) ⤳ q := (PrimeSpectrum.le_iff_specializes _ _).mp bot_le
  have hmem : q ∈ Set.range f :=
    hq.mem_closed f.isClosedMap.isClosed_range ⟨x', hx'⟩
  obtain ⟨y, hy⟩ := hmem
  exact ⟨y, hy⟩

/-- **Zariski's connectedness theorem, connected form** (blueprint `thm:sm-zariski-connected`):
for `X` nonempty, projective and flat over `V` with preconnected generic fibre, every fibre is
connected. -/
theorem isConnected_fiber_of_isProjectiveOver [Finite (PrimeSpectrum V)]
    (hsep : ∀ p : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ p.asIdeal)))
    {X : Scheme.{u}} [Nonempty X] (f : X ⟶ Spec (CommRingCat.of V)) (hf : IsProjectiveOver f)
    [Flat f] (hgen : _root_.IsPreconnected (f ⁻¹' {(⊥ : PrimeSpectrum V)})) (q : PrimeSpectrum V) :
    _root_.IsConnected (f ⁻¹' {q}) := by
  have : IsProper f := hf.isProper
  exact ⟨nonempty_fiber_of_flat f q, isPreconnected_fiber_of_isProjectiveOver hsep f hf hgen q⟩

/-- **Connected fibres of an irreducible projective flat scheme** (blueprint
`cor:sm-zariski-irreducible`): if `X` is irreducible, projective and flat over `V`, every fibre of
`f` is connected. -/
theorem isConnected_fiber_of_irreducibleSpace [Finite (PrimeSpectrum V)]
    (hsep : ∀ p : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ p.asIdeal)))
    {X : Scheme.{u}} [IrreducibleSpace X] (f : X ⟶ Spec (CommRingCat.of V))
    (hf : IsProjectiveOver f) [Flat f] (q : PrimeSpectrum V) :
    _root_.IsConnected (f ⁻¹' {q}) := by
  have : IsProper f := hf.isProper
  have : Nonempty X := (IrreducibleSpace.isIrreducible_univ X).nonempty.to_subtype.map Subtype.val
  exact ⟨nonempty_fiber_of_flat f q, isPreconnected_fiber_of_irreducibleSpace hsep f hf q⟩

end Induction

section SepClosed

/-- Separable closedness is invariant under ring isomorphisms of fields. -/
theorem isSepClosed_of_ringEquiv {k k' : Type*} [Field k] [Field k'] (e : k ≃+* k')
    [IsSepClosed k] : IsSepClosed k' := by
  refine IsSepClosed.of_exists_root k' fun p _ hirr hsep => ?_
  let P : Polynomial k := p.map e.symm.toRingHom
  have hP : P.Separable := hsep.map
  have hdeg : P.degree ≠ 0 := by
    rw [Polynomial.degree_map]
    exact (Polynomial.degree_pos_of_irreducible hirr).ne'
  obtain ⟨x, hx⟩ := IsSepClosed.exists_root P hdeg hP
  refine ⟨e x, ?_⟩
  have hPe : P.map e.toRingHom = p := by
    simp only [P, Polynomial.map_map, RingEquiv.toRingHom_eq_coe]
    rw [show (e : k →+* k').comp (e.symm : k' →+* k) = RingHom.id k' by ext; simp,
      Polynomial.map_id]
  rw [← hPe, Polynomial.eval_map]
  change Polynomial.eval₂ (e : k →+* k') ((e : k →+* k') x) P = 0
  rw [Polynomial.eval₂_hom, hx.eq_zero, map_zero]

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]

/-- **Residue fields of a valuation ring with separably closed fraction field**: if the fraction
field `K` of the valuation ring `V` is separably closed, so is the fraction field of `V ⧸ 𝔭` for
every prime `𝔭` (it is the residue field of the valuation ring `V_𝔭`, whose fraction field is
`K`; `Valuation.isSepClosed_residueField`). This supplies the hypothesis of
`isPreconnected_fiber_of_isProjectiveOver` for the valuation rings of Temkin's method. -/
theorem isSepClosed_fractionRing_quotient (K : Type u) [Field K] [Algebra V K]
    [IsFractionRing V K] [IsSepClosed K] (p : PrimeSpectrum V) :
    IsSepClosed (FractionRing (V ⧸ p.asIdeal)) := by
  have : ValuationRing (Localization.AtPrime p.asIdeal) :=
    { toPreValuationRing := ValuationRing.preValuationRing_of_isLocalization p.asIdeal.primeCompl }
  have : IsSepClosed (FractionRing V) :=
    isSepClosed_of_ringEquiv (FractionRing.algEquiv V K).symm.toRingEquiv
  have h1 : IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal)) :=
    Valuation.isSepClosed_residueField (Localization.AtPrime p.asIdeal) (FractionRing V)
  have h2 : IsSepClosed p.asIdeal.ResidueField := h1
  exact isSepClosed_of_ringEquiv
    (FractionRing.algEquiv (V ⧸ p.asIdeal) p.asIdeal.ResidueField).symm.toRingEquiv

end SepClosed

section ClosedFibre

/-- **Functions on a connected reduced closed fibre are constants** (blueprint
`cor:sm-h0-closed-fibre`; "`h⁰(C'_t) = 1`", Temkin, proof of Lemma 4.4.2, `semi-stable.tex`
line 3127): let `R` be a local ring with algebraically closed residue field `κ` and
`f : X → Spec R` universally closed. If the closed fibre is connected and the scheme-theoretic
closed fibre `X_κ = X ×_R Spec κ` is reduced, the structure map `κ → Γ(X_κ, 𝒪)` is bijective. -/
theorem bijective_structureCoeff_closedFibre {R : Type u} [CommRing R] [IsLocalRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [UniversallyClosed f]
    (hconn : _root_.IsConnected (f ⁻¹' {IsLocalRing.closedPoint R}))
    [IsReduced (pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))] :
    Function.Bijective (structureCoeff (bcSnd (IsLocalRing.residue R) f)) := by
  classical
  let T : Scheme.{u} := pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))
  have hrange : Set.range (bcFst (IsLocalRing.residue R) f) =
      f ⁻¹' {IsLocalRing.closedPoint R} := by
    apply range_bcFst_quotient f (I := IsLocalRing.maximalIdeal R)
    · intro P hP
      apply PrimeSpectrum.ext
      exact le_antisymm (IsLocalRing.le_maximalIdeal P.isPrime.ne_top) hP
    · exact le_rfl
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hpre : _root_.IsPreconnected (Set.univ : Set T) := by
    rw [← (bcFst (IsLocalRing.residue R) f).isEmbedding.isInducing.isPreconnected_image,
      Set.image_univ, hrange]
    exact hconn.isPreconnected
  have hne : Nonempty T := by
    obtain ⟨y, hy⟩ := hconn.nonempty
    rw [← hrange] at hy
    obtain ⟨z, -⟩ := hy
    exact ⟨z⟩
  have : PreconnectedSpace T := ⟨hpre⟩
  have hcs : ConnectedSpace T := ⟨hne⟩
  have hidem :=
    ((DeJongAlterations.Geometry.ProperSteinGlobalIdempotents.connectedSpace_iff_idempotents
      T).mp hcs).2
  have hnt : Nontrivial Γ(T, ⊤) := by
    obtain ⟨z⟩ := hne
    exact (T.presheaf.germ ⊤ z trivial).hom.domain_nontrivial
  let _ : Algebra (IsLocalRing.ResidueField R) Γ(T, ⊤) :=
    (structureCoeff (bcSnd (IsLocalRing.residue R) f)).toAlgebra
  have hint : (structureCoeff (bcSnd (IsLocalRing.residue R) f)).IsIntegral := by
    have h := isIntegral_appTop_of_universallyClosed (bcSnd (IsLocalRing.residue R) f)
    have h' : (Scheme.ΓSpecIso (CommRingCat.of (IsLocalRing.ResidueField R))).inv.hom.IsIntegral :=
      RingHom.isIntegral_of_surjective _ (Scheme.ΓSpecIso
        (CommRingCat.of (IsLocalRing.ResidueField R))).commRingCatIsoToRingEquiv.symm.surjective
    exact RingHom.IsIntegral.trans _ _ h' h
  refine ⟨(structureCoeff (bcSnd (IsLocalRing.residue R) f)).injective, fun y => ?_⟩
  obtain ⟨l, hl⟩ := exists_sub_isNilpotent_of_isIntegral (F := IsLocalRing.ResidueField R) hidem
    (hint y)
  exact ⟨l, (sub_eq_zero.mp hl.eq_zero).symm⟩

/-- **`h⁰ = 1` for a connected reduced closed fibre, Čech form** (blueprint
`cor:sm-h0-closed-fibre`): under the hypotheses of `bijective_structureCoeff_closedFibre`, for
every covering family `U` of opens of `X`, the degree-zero Čech cohomology of the pulled-back
structure sheaf on the closed fibre `X_κ` (for the cover `q⁻¹ U`) is one-dimensional over `κ`. This
is the form of `h⁰(X_κ, 𝒪) = 1` matching `ProjectiveCoordinates.exists_eulerChar_fibre_valuation`
(Temkin, proof of Lemma 4.4.2, `semi-stable.tex` lines 3127–3131). -/
theorem finrank_cechCohomology_zero_closedFibre {R : Type u} [CommRing R] [IsLocalRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [UniversallyClosed f]
    (hconn : _root_.IsConnected (f ⁻¹' {IsLocalRing.closedPoint R}))
    [IsReduced (pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))]
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤) :
    Module.finrank (IsLocalRing.ResidueField R)
      (cechCohomology ((Scheme.Modules.pullback (bcFst (IsLocalRing.residue R) f)).obj
        (unitModule X)) (fun j => bcFst (IsLocalRing.residue R) f ⁻¹ᵁ U j)
        (structureCoeff (bcSnd (IsLocalRing.residue R) f)) 0) = 1 := by
  let T : Scheme.{u} := pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))
  have hcov : ⨆ j, bcFst (IsLocalRing.residue R) f ⁻¹ᵁ U j = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hU, Scheme.Hom.preimage_top]
  let e1 := cechCohomologyZeroIso
    ((Scheme.Modules.pullback (bcFst (IsLocalRing.residue R) f)).obj (unitModule X))
    (structureCoeff (bcSnd (IsLocalRing.residue R) f)) hcov
  let E := pullbackUnitIso (bcFst (IsLocalRing.residue R) f)
  let e2 : sectionsModuleCat
      ((Scheme.Modules.pullback (bcFst (IsLocalRing.residue R) f)).obj (unitModule X))
      (structureCoeff (bcSnd (IsLocalRing.residue R) f)) ⊤ le_top ≅
      sectionsModuleCat (unitModule T) (structureCoeff (bcSnd (IsLocalRing.residue R) f)) ⊤
        le_top :=
    { hom := sectionsMap _ E.hom ⊤ le_top
      inv := sectionsMap _ E.inv ⊤ le_top
      hom_inv_id := by rw [← sectionsMap_comp, E.hom_inv_id, sectionsMap_id]
      inv_hom_id := by rw [← sectionsMap_comp, E.inv_hom_id, sectionsMap_id] }
  have hbij := bijective_structureCoeff_closedFibre f hconn
  let L : IsLocalRing.ResidueField R →ₗ[IsLocalRing.ResidueField R]
      sectionsModuleCat (unitModule T) (structureCoeff (bcSnd (IsLocalRing.residue R) f)) ⊤
        le_top :=
    { toFun := fun l => (show Γ(T, ⊤) from structureCoeff (bcSnd (IsLocalRing.residue R) f) l)
      map_add' := fun l l' => map_add _ l l'
      map_smul' := fun r l => by
        change structureCoeff (bcSnd (IsLocalRing.residue R) f) (r * l) =
          sectionsRingHom (structureCoeff (bcSnd (IsLocalRing.residue R) f)) (le_top : ⊤ ≤ ⊤) r *
            structureCoeff (bcSnd (IsLocalRing.residue R) f) l
        rw [map_mul]
        congr 1
        exact (presheaf_map_self_apply _ _).symm }
  have hL : Function.Bijective L := hbij
  rw [← (e2.symm ≪≫ e1).toLinearEquiv.finrank_eq, ← (LinearEquiv.ofBijective L hL).finrank_eq,
    Module.finrank_self]

end ClosedFibre

end

end DeJongAlterations.StableModification.Cohomology.Connected
