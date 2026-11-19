/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Hironaka.Scheme.BlowUp.Transform.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
import Hironaka.Algebra.Local.Regular
import Hironaka.Scheme.BlowUp.InverseImage
import Hironaka.Scheme.BlowUp.InvertibleSheaf
import Hironaka.Scheme.BlowUp.Transform

/-!
# The principal case of the weak transform

For principal ideals the weak and strict transforms coincide [Hau14, Remark 6.9]. Here `I^g`
is the weak transform `(I* : E^N)` with `N` the exceptional order, the largest `N` with `E^N ∣ I*`
[Hir64, Ch. 0, §5, p. 142], and `Iˢ = ⋃ᵢ (I* : Eⁱ)` the strict transform, for `I* = I.comap π`
the total transform of a locally principal `I` and `E` the (invertible) ideal of the exceptional
divisor `F = V(E)`. Hauser's setting is a regular ambient scheme with a regular centre, so that
`F` is regular and irreducible; `weakTransformAlong_eq_strictTransformAlong_of_locally_principal'`
states the result under exactly these hypotheses, and
`weakTransformAlong_eq_strictTransformAlong_of_locally_principal` under the one the proof uses,
the integrality of `F`. The auxiliary lemmas (the integrality of a regular irreducible closed
subscheme, the primality of its ideal on a chart, and `I ≤ E ^ c → E ^ c ∣ I` for invertible `E`)
are used for the components of normal crossings divisors
(`Hironaka.Resolution.Algebraic.Snc.ComponentStalks`), the order along the exceptional divisor
(`Hironaka.Scheme.IdealSheaf.Order.Exceptional`) and hypersurfaces of maximal contact
(`Hironaka.Resolution.Algebraic.MaximalContact.AgreeOnBlowUp`).

## The argument

Write `N` for the exceptional order. Since `(I* : Eⁱ)` increases with `i` and `(I* : Eⁱ) ⊆ Iˢ`
for every `i`, everything reduces to the single inequality `(I* : E^(N+1)) ⊆ (I* : E^N)`: it gives
`(I* : E^(N+i)) = (I* : E^N)` for all `i` by `colon_colon`, hence `Iˢ = (I* : E^N)`.

On an affine chart `U'` of the blow-up over an affine `U` of `X` with `I(U) = (f)` and
`E(U') = (e)`, `e` a nonzerodivisor (`E` is invertible), the total transform is `(f*)` with
`f* = π♯ f` (`ideal_comap_of_le`), and the inequality reads: `u e^(N+1) ∈ (f*) ⇒ u e^N ∈ (f*)`.

* If `U'` misses `F`, then `E(U') = Γ(U')`, `e` is a unit and there is nothing to prove.
* If `U'` meets `F` and the exceptional order is attained (`E^N ∣ I*`, `E^(N+1) ∤ I*`), then
  `f* = e^N g` with `e ∤ g` and the ring form of the strict transform, `f* = h^k f^s`
  [Hau14, Definition 6.2], applies once `e` is *prime* in `Γ(U')`: from `u e^(N+1) = v e^N g`
  cancel `e^N`, so `e ∣ v g`, `e ∣ v`, `v = e w`, `u = w g` and `u e^N = w f*`.
* If every power of `E` divides `I*` (so `N = 0`, the supremum in `ℕ` of an unbounded set being
  `0`), then `f*` is divisible by every power of `e`; on the Noetherian ring `Γ(U')` the chain
  `(f*) : eⁱ` stabilizes and yields `(1 - a e) f* = 0` for some `a`, whence `(f* : e) = (f*)`.

Two facts carry the hypotheses of the statement:

1. **`e` is prime.** `F = V(E)` is irreducible and its stalks are regular local rings, hence
   domains, so `F` is reduced and therefore integral. Then `Γ(F ∩ U')` is a domain and
   `E(U') = ker (Γ(U') → Γ(F ∩ U'))` (Mathlib `ker_subschemeι_app`) is a prime ideal.
2. **Constancy of the exceptional order along `F`.** If `e^(N+1) ∣ f*` on one chart meeting `F`,
   then `E^(N+1) ∣ I*` everywhere: any other chart `U''` meeting `F` meets it in a nonempty open of
   the irreducible `F`, and on a common smaller chart `V` the divisibility says that the restriction
   of `g` (from `f* = e^N g` on `U''`) lies in `E(V)`, i.e. vanishes on `F ∩ V`; on the integral
   `F` a section vanishing on a nonempty open vanishes (`map_injective_of_isIntegral`), so
   `g ∈ E(U'')` and `e^(N+1) ∣ f*` on `U''`. Charts missing `F` divide trivially.

Fact (2) says that the order of `f*` along `F` is its order at the generic point of `F`; the
argument above reads this on sections (the generic point is not named). The regularity of the
ambient scheme, part of Hauser's setting, is not among the hypotheses of the theorems here; the
regularity of `F` enters only through the reducedness of `F`.

## Conventions

The transforms are `strictTransformAlong π E I`, `controlledTransformAlong π E I c`,
`exceptionalOrderAlong π E I = sSup {c | E ^ c ∣ I.comap π}` (`0` when unbounded), and
`weakTransformAlong π E I`, the controlled transform with the exceptional order as control.
Invertibility is `IsInvertible` (locally a nonzerodivisor generator). Integrality of a scheme is
Mathlib's `IsIntegral`.
-/

public section

universe u

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry

/-! ### Ring lemmas -/

section Ring

variable {A : Type*} [CommRing A]

/-- Two generators of one principal ideal: if one is a nonzerodivisor, so is the other. -/
theorem mem_nonZeroDivisors_of_span_singleton_eq {a b : A} (ha : a ∈ nonZeroDivisors A)
    (h : Ideal.span {a} = Ideal.span {b}) : b ∈ nonZeroDivisors A := by
  have hab : b ∣ a := Ideal.mem_span_singleton.mp (h ▸ Ideal.mem_span_singleton_self a)
  have hba : a ∣ b := Ideal.mem_span_singleton.mp (h.symm ▸ Ideal.mem_span_singleton_self b)
  obtain ⟨u, hu⟩ := hab
  obtain ⟨v, hv⟩ := hba
  have h1 : a * (v * u - 1) = 0 := by
    rw [mul_sub, mul_one, ← mul_assoc, ← hv, ← hu, sub_self]
  have hvu : v * u = 1 := sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp ha).1 _ h1)
  have hvunit : IsUnit v := ⟨Units.mkOfMulEqOne v u hvu, rfl⟩
  rw [hv]
  exact mul_mem ha hvunit.mem_nonZeroDivisors

/-- The ring form of the strict transform of a principal ideal [Hau14, Definition 6.2] at a chart
meeting the divisor: for a prime nonzerodivisor `e` and `f = eᴺ g` with `e ∤ g`,
`(f : eᴺ⁺¹) ⊆ (f : eᴺ)`. -/
theorem mul_pow_mem_span_of_mul_pow_succ_mem {e f : A} (he : e ∈ nonZeroDivisors A) (hp : Prime e)
    {N : ℕ} (hN : e ^ N ∣ f) (hN' : ¬ e ^ (N + 1) ∣ f) {u : A}
    (hu : u * e ^ (N + 1) ∈ Ideal.span {f}) : u * e ^ N ∈ Ideal.span {f} := by
  obtain ⟨g, rfl⟩ := hN
  have hg : ¬ e ∣ g := fun ⟨w, hw⟩ => hN' ⟨w, by rw [hw, pow_succ, mul_assoc]⟩
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton.mp hu
  have h1 : e ^ N * (u * e) = e ^ N * (g * v) := by
    rw [← mul_assoc, ← mul_assoc, ← hv, pow_succ]; ring
  have h2 : u * e = g * v := (mul_cancel_left_mem_nonZeroDivisors (pow_mem he N)).mp h1
  have hv' : e ∣ v := (hp.dvd_or_dvd ⟨u, by rw [← h2, mul_comm]⟩).resolve_left hg
  obtain ⟨w, rfl⟩ := hv'
  have h3 : u = g * w := (mul_cancel_right_mem_nonZeroDivisors he).mp (by rw [h2]; ring)
  rw [Ideal.mem_span_singleton]
  exact ⟨w, by rw [h3]; ring⟩

/-- Chain form of Krull's intersection theorem, as needed for an unbounded exceptional order: in a
Noetherian ring, if the nonzerodivisor `e` has every power dividing `f`, then `(f : e) = (f)`. -/
theorem mem_span_of_mul_mem_of_forall_pow_dvd [IsNoetherianRing A] {e f : A}
    (he : e ∈ nonZeroDivisors A) (hf : ∀ i, e ^ i ∣ f) {u : A}
    (hu : u * e ∈ Ideal.span {f}) : u ∈ Ideal.span {f} := by
  let c : ℕ →o Ideal A :=
    ⟨fun i => (Ideal.span {f}).colon {e ^ i}, fun i j hij x hx => by
      rw [Submodule.mem_colon_singleton, smul_eq_mul] at hx ⊢
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
      rw [pow_add, ← mul_assoc]
      exact Ideal.mul_mem_right _ _ hx⟩
  obtain ⟨k, hk⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance c
  obtain ⟨g, hg⟩ := hf (k + 1)
  have hgk : g ∈ c k := by
    rw [hk (k + 1) (Nat.le_succ k)]
    change g ∈ (Ideal.span {f}).colon {e ^ (k + 1)}
    rw [Submodule.mem_colon_singleton, smul_eq_mul, hg, mul_comm]
    exact Ideal.mem_span_singleton_self _
  change g ∈ (Ideal.span {f}).colon {e ^ k} at hgk
  rw [Submodule.mem_colon_singleton, smul_eq_mul, Ideal.mem_span_singleton] at hgk
  obtain ⟨b, hb⟩ := hgk
  have h1 : e ^ k * g = e ^ k * (e * g * b) := by
    rw [hg] at hb
    calc e ^ k * g = g * e ^ k := mul_comm _ _
      _ = e ^ (k + 1) * g * b := hb
      _ = e ^ k * (e * g * b) := by ring
  have h2 : g = e * g * b := (mul_cancel_left_mem_nonZeroDivisors (pow_mem he k)).mp h1
  have hf0 : (1 - e * b) * f = 0 := by
    rw [hg]
    calc (1 - e * b) * (e ^ (k + 1) * g) = e ^ (k + 1) * (g - e * g * b) := by ring
      _ = 0 := by rw [← h2, sub_self, mul_zero]
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton.mp hu
  have h3 : (u - u * (e * b)) * e = 0 := by
    calc (u - u * (e * b)) * e = (1 - e * b) * (u * e) := by ring
      _ = (1 - e * b) * f * v := by rw [hv, mul_assoc]
      _ = 0 := by rw [hf0, zero_mul]
  have h4 : u = u * (e * b) := sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp he).2 _ h3)
  rw [Ideal.mem_span_singleton]
  refine ⟨v * b, ?_⟩
  calc u = u * (e * b) := h4
    _ = u * e * b := by ring
    _ = f * v * b := by rw [hv]
    _ = f * (v * b) := by ring

end Ring

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (E : X.IdealSheafData)

/-! ### Sections of an ideal sheaf whose closed subscheme is integral -/

/-- The closed subscheme `V(E)` is integral when it is irreducible and its stalks are regular local
rings (regular local rings are domains, so `V(E)` is reduced). -/
theorem isIntegral_subscheme_of_isRegularLocalRing_stalk [IrreducibleSpace E.subscheme]
    (h : ∀ z : E.subscheme, IsRegularLocalRing (E.subscheme.presheaf.stalk z)) :
    IsIntegral E.subscheme := by
  have : ∀ z : E.subscheme, _root_.IsReduced (E.subscheme.presheaf.stalk z) := fun z => by
    have := h z
    infer_instance
  have : IsReduced E.subscheme := isReduced_of_isReduced_stalk E.subscheme
  exact isIntegral_of_irreducibleSpace_of_isReduced E.subscheme

/-- An affine open missing `V(E)` has `E(U) = Γ(U)`. -/
theorem ideal_eq_top_of_forall_notMem (U : X.affineOpens)
    (h : ∀ z : E.subscheme, E.subschemeι z ∉ U.1) : E.ideal U = ⊤ := by
  by_contra hne
  obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal _ hne
  have hU : IsAffineOpen U.1 := U.2
  let q : PrimeSpectrum Γ(X, U) := ⟨Q, hQ.isPrime⟩
  have hmem : hU.fromSpec q ∈ U.1 := by
    have : q ∈ hU.fromSpec ⁻¹ᵁ U.1 := by rw [hU.fromSpec_preimage_self]; trivial
    exact this
  have hsupp' : hU.fromSpec q ∈ E.support := by
    rw [mem_support_iff_of_mem hmem, fromSpec_mem_zeroLocus_iff]
    exact hle
  have hsupp : hU.fromSpec q ∈ Set.range E.subschemeι := by
    rw [range_subschemeι]; exact hsupp'
  obtain ⟨z, hz⟩ := hsupp
  exact h z (hz ▸ hmem)

variable [IsIntegral E.subscheme]

/-- On an affine open meeting the integral closed subscheme `V(E)`, the ideal `E(U)` is prime: it
is the kernel of `Γ(U) → Γ(V(E) ∩ U)` and the target is a domain. -/
theorem isPrime_ideal_of_isIntegral_subscheme (U : X.affineOpens) {z : E.subscheme}
    (hz : E.subschemeι z ∈ U.1) : (E.ideal U).IsPrime := by
  have : Nonempty (E.subschemeι ⁻¹ᵁ U.1) := ⟨⟨z, hz⟩⟩
  rw [← E.ker_subschemeι_app U]
  exact RingHom.ker_isPrime _

/-- On the integral closed subscheme `V(E)`, a section vanishing on a nonempty open vanishes: if
the restriction of `g ∈ Γ(U)` to an affine `V ≤ U` meeting `V(E)` lies in `E(V)`, then
`g ∈ E(U)`. -/
theorem mem_ideal_of_map_mem_of_isIntegral_subscheme {U V : X.affineOpens} (h : V ≤ U)
    {z : E.subscheme} (hz : E.subschemeι z ∈ V.1) {g : Γ(X, U)}
    (hg : (X.presheaf.map (homOfLE h).op).hom g ∈ E.ideal V) : g ∈ E.ideal U := by
  have : Nonempty (E.subschemeι ⁻¹ᵁ V.1) := ⟨⟨z, hz⟩⟩
  have h' : E.subschemeι ⁻¹ᵁ V.1 ≤ E.subschemeι ⁻¹ᵁ U.1 := fun _ hx => h hx
  rw [← E.ker_subschemeι_app U, RingHom.mem_ker]
  rw [← E.ker_subschemeι_app V, RingHom.mem_ker] at hg
  have hres : (E.subscheme.presheaf.map (homOfLE h').op).hom ((E.subschemeι.app U.1).hom g) =
      (E.subschemeι.app V.1).hom ((X.presheaf.map (homOfLE h).op).hom g) := by
    change (E.subschemeι.app U.1 ≫ E.subscheme.presheaf.map (homOfLE h').op) g =
      (X.presheaf.map (homOfLE h).op ≫ E.subschemeι.app V.1) g
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, Scheme.Hom.app_eq_appLE,
      Scheme.Hom.map_appLE]
  apply map_injective_of_isIntegral E.subscheme (homOfLE h')
  change (E.subscheme.presheaf.map (homOfLE h').op).hom _ = _
  rw [hres, hg, map_zero]

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry

open Scheme.IdealSheafData

open AlgebraicGeometry.Scheme

variable {B X : Scheme.{u}} (π : B ⟶ X) (E : B.IdealSheafData) (J : X.IdealSheafData)

/-! ### Divisibility by powers of an invertible ideal sheaf -/

/-- `E ^ c ∣ I` implies `I ≤ E ^ c`. -/
theorem le_pow_of_pow_dvd {I E : B.IdealSheafData} {c : ℕ} (h : E ^ c ∣ I) : I ≤ E ^ c := by
  obtain ⟨K, rfl⟩ := h
  exact IdealSheafData.mul_le_self_left _ _

/-- For an invertible `E`, `I ≤ E ^ c` implies `E ^ c ∣ I` (with quotient `(I : E ^ c)`). -/
theorem pow_dvd_of_le_pow_of_isInvertible {I E : B.IdealSheafData} (hE : E.IsInvertible) {c : ℕ}
    (h : I ≤ E ^ c) : E ^ c ∣ I := by
  refine ⟨I.colon (E ^ c), le_antisymm ?_ (by rw [mul_comm]; exact IdealSheafData.colon_mul_le _ _)⟩
  have hE' := hE
  choose U hxU e he hEe using hE'
  refine IdealSheafData.le_of_iSup_eq_top U
    (top_le_iff.mp fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxU x⟩) fun x => ?_
  rw [IdealSheafData.ideal_mul, Pi.mul_apply,
    IdealSheafData.ideal_colon_of_isInvertible _ _ (IdealSheafData.isInvertible_pow hE c) (U x),
    IdealSheafData.ideal_pow, Pi.pow_apply, hEe x, Ideal.span_singleton_pow, Ideal.colon_span]
  intro s hs
  have hs' : s ∈ Ideal.span {e x ^ c} := by
    have := h (U x) hs
    rwa [IdealSheafData.ideal_pow, Pi.pow_apply, hEe x, Ideal.span_singleton_pow] at this
  obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton.mp hs'
  refine Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) ?_
  rw [Submodule.mem_colon_singleton, smul_eq_mul, mul_comm]
  exact hs

/-- Divisibility on a chart restricts to smaller affine opens. -/
theorem ideal_le_pow_of_le {I K : B.IdealSheafData} {U V : B.affineOpens} (h : V ≤ U) {c : ℕ}
    (hU : I.ideal U ≤ K.ideal U ^ c) : I.ideal V ≤ K.ideal V ^ c := by
  rw [← I.map_ideal h, ← K.map_ideal h, ← Ideal.map_pow]
  exact Ideal.map_mono hU

/-- The charts used below: an affine open `U` of `X` around `π b` on which the locally principal
`J` is principal, and an affine open `U' ∋ b` of `B` inside `π⁻¹U` on which the invertible `E` is
generated by a nonzerodivisor. -/
theorem exists_chart_of_locally_principal (hE : E.IsInvertible)
    (hJ : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ ∃ f : Γ(X, U), J.ideal U = Ideal.span {f})
    (b : B) : ∃ (U : X.affineOpens) (U' : B.affineOpens) (f : Γ(X, U)),
      J.ideal U = Ideal.span {f} ∧ b ∈ U'.1 ∧ U'.1 ≤ π ⁻¹ᵁ U.1 ∧
        ∃ e ∈ nonZeroDivisors Γ(B, U'), E.ideal U' = Ideal.span {e} := by
  obtain ⟨U, hxU, f, hf⟩ := hJ (π b)
  obtain ⟨W, hbW, e₀, he₀, hEW⟩ := hE b
  obtain ⟨_, ⟨V, hV, rfl⟩, hbV, hVU⟩ := B.isBasis_affineOpens.exists_subset_of_mem_open
    (show b ∈ (π ⁻¹ᵁ U.1 : Set B) from hxU) (π ⁻¹ᵁ U.1).2
  have hVU' : V ≤ π ⁻¹ᵁ U.1 := hVU
  have hW : IsAffineOpen W.1 := W.2
  obtain ⟨s, hsle, hbs⟩ := hW.exists_basicOpen_le (V := W.1 ⊓ V) ⟨b, ⟨hbW, hbV⟩⟩ hbW
  obtain ⟨e, he, hEe⟩ := IdealSheafData.exists_regular_generator_affineBasicOpen E W he₀ hEW s
  exact ⟨U, B.affineBasicOpen s, f, hf, hbs, (hsle.trans inf_le_right).trans hVU', e, he, hEe⟩

/-- Principality on every affine open gives principality on an affine neighbourhood of every point,
the hypothesis of `weakTransformAlong_eq_strictTransformAlong_of_locally_principal`. -/
theorem locally_principal_of_forall_principal
    (hJ : ∀ U : X.affineOpens, ∃ f : Γ(X, U), J.ideal U = Ideal.span {f}) (x : X) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧ ∃ f : Γ(X, U), J.ideal U = Ideal.span {f} :=
  let ⟨U, hxU⟩ := IdealSheafData.exists_affineOpens_mem x
  ⟨U, hxU, hJ U⟩

/-! ### Constancy of the exceptional order along an integral exceptional divisor -/

variable [IsIntegral E.subscheme]

/-- Constancy of the exceptional order, chart to chart: on a chart `U'` of `B` over an
affine `U` of `X` with `J(U) = (f)`, `E(U') = (e)`, `e` a nonzerodivisor and `eᴺ ∣ π♯ f`, if the
total transform is divisible by `E ^ (N + 1)` on a smaller affine `V` meeting `V(E)`, then it is
divisible by `E ^ (N + 1)` on `U'`. -/
theorem ideal_comap_le_pow_succ_of_le (U : X.affineOpens) (U' : B.affineOpens)
    (hle : U'.1 ≤ π ⁻¹ᵁ U.1) {e : Γ(B, U')}
    (hEe : E.ideal U' = Ideal.span {e}) {f : Γ(X, U)} (hf : J.ideal U = Ideal.span {f}) {N : ℕ}
    (hN : (J.comap π).ideal U' ≤ E.ideal U' ^ N) (V : B.affineOpens) (hV : V ≤ U')
    {z : E.subscheme} (hz : E.subschemeι z ∈ V.1)
    (heV : ∃ e' ∈ nonZeroDivisors Γ(B, V), E.ideal V = Ideal.span {e'})
    (h : (J.comap π).ideal V ≤ E.ideal V ^ (N + 1)) :
    (J.comap π).ideal U' ≤ E.ideal U' ^ (N + 1) := by
  set φ := π.appLE U.1 U'.1 hle with hφ
  have hJ' : (J.comap π).ideal U' = Ideal.span {φ.hom f} := by
    rw [IdealSheafData.ideal_comap_of_le J π U U' hle, hf, Ideal.map_span, Set.image_singleton]
  rw [hJ', hEe, Ideal.span_singleton_pow, Ideal.span_singleton_le_span_singleton] at hN ⊢
  obtain ⟨g, hg⟩ := hN
  set res : Γ(B, U') →+* Γ(B, V) := (B.presheaf.map (homOfLE hV).op).hom with hres
  have hEV : E.ideal V = Ideal.span {res e} := by
    rw [← E.map_ideal hV, hEe, Ideal.map_span, Set.image_singleton]
  have hresE : res e ∈ nonZeroDivisors Γ(B, V) := by
    obtain ⟨e', he', hEe'⟩ := heV
    exact mem_nonZeroDivisors_of_span_singleton_eq he' (hEe'.symm.trans hEV)
  have hmem : res (φ.hom f) ∈ (J.comap π).ideal V := by
    rw [← (J.comap π).map_ideal hV]
    exact Ideal.mem_map_of_mem _ (hJ' ▸ Ideal.mem_span_singleton_self _)
  have h1 := h hmem
  rw [hEV, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h1
  obtain ⟨h', hh'⟩ := h1
  rw [hg, map_mul, map_pow] at hh'
  have h2 : res g = res e * h' := by
    refine (mul_cancel_left_mem_nonZeroDivisors (pow_mem hresE N)).mp ?_
    rw [hh', pow_succ]; ring
  have h3 : g ∈ E.ideal U' :=
    E.mem_ideal_of_map_mem_of_isIntegral_subscheme hV hz
      (by rw [hEV, Ideal.mem_span_singleton, h2]; exact dvd_mul_right _ _)
  rw [hEe, Ideal.mem_span_singleton] at h3
  obtain ⟨w, hw⟩ := h3
  exact ⟨w, by rw [hg, hw, pow_succ]; ring⟩

/-- Constancy of the exceptional order along an integral divisor: for `J` locally principal, `E`
invertible with `V(E)` integral and `J* ≤ E ^ N`, if `E ^ (N + 1)` divides the total transform on
one affine open meeting `V(E)`, it divides it everywhere. -/
theorem comap_le_pow_succ_of_chart (hE : E.IsInvertible)
    (hJ : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ ∃ f : Γ(X, U), J.ideal U = Ideal.span {f}) {N : ℕ}
    (hN : J.comap π ≤ E ^ N) (U₀ : B.affineOpens) {z₀ : E.subscheme}
    (hz₀ : E.subschemeι z₀ ∈ U₀.1) (h₀ : (J.comap π).ideal U₀ ≤ E.ideal U₀ ^ (N + 1)) :
    J.comap π ≤ E ^ (N + 1) := by
  classical
  choose U U' f hf hbU' hle e he hEe using
    exists_chart_of_locally_principal π E J hE hJ
  refine IdealSheafData.le_of_iSup_eq_top U'
    (top_le_iff.mp fun b _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨b, hbU' b⟩) fun b => ?_
  rw [IdealSheafData.ideal_pow, Pi.pow_apply]
  by_cases hz : ∃ z : E.subscheme, E.subschemeι z ∈ (U' b).1
  · obtain ⟨z₁, hz₁⟩ := hz
    -- the two affine opens meet `V(E)` in nonempty opens of the irreducible `V(E)`
    obtain ⟨z, hz₀', hz₁'⟩ := nonempty_preirreducible_inter
      (E.subschemeι ⁻¹ᵁ U₀.1).isOpen (E.subschemeι ⁻¹ᵁ (U' b).1).isOpen
      ⟨z₀, hz₀⟩ ⟨z₁, hz₁⟩
    -- a common smaller chart on which `E` has a nonzerodivisor generator
    obtain ⟨W, hzW, e₀, he₀, hEW⟩ := hE (E.subschemeι z)
    have hW : IsAffineOpen W.1 := W.2
    obtain ⟨s, hsle, hzs⟩ :=
      hW.exists_basicOpen_le (V := W.1 ⊓ (U₀.1 ⊓ (U' b).1)) ⟨E.subschemeι z, ⟨hzW, hz₀', hz₁'⟩⟩ hzW
    have hV₀ : B.affineBasicOpen s ≤ U₀ := (hsle.trans inf_le_right).trans inf_le_left
    have hV₁ : B.affineBasicOpen s ≤ U' b := (hsle.trans inf_le_right).trans inf_le_right
    have hNb : (J.comap π).ideal (U' b) ≤ E.ideal (U' b) ^ N := by
      have := hN (U' b)
      rwa [IdealSheafData.ideal_pow, Pi.pow_apply] at this
    exact ideal_comap_le_pow_succ_of_le π E J (U b) (U' b) (hle b) (hEe b) (hf b) hNb
      (B.affineBasicOpen s) hV₁ hzs
      (IdealSheafData.exists_regular_generator_affineBasicOpen E W he₀ hEW s)
      (ideal_le_pow_of_le hV₀ h₀)
  · rw [E.ideal_eq_top_of_forall_notMem (U' b) fun z hz' => hz ⟨z, hz'⟩, Ideal.top_pow]
    exact le_top

/-! ### The principal case -/

/-- **For principal ideals the weak and strict transforms coincide** [Hau14, Remark 6.9]: along
`π : B ⟶ X` with `B` locally Noetherian, `E` an invertible ideal sheaf on `B` whose closed
subscheme is integral and `J` locally principal on `X` (principal on an affine neighbourhood of
every point), the weak transform of `J` is its strict transform. -/
theorem weakTransformAlong_eq_strictTransformAlong_of_locally_principal [IsLocallyNoetherian B]
    (hE : E.IsInvertible)
    (hJ : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ ∃ f : Γ(X, U), J.ideal U = Ideal.span {f}) :
    J.weakTransformAlong π E = J.strictTransformAlong π E := by
  classical
  set N := exceptionalOrderAlong π E J with hNdef
  -- the key inequality `(J* : E^(N+1)) ≤ (J* : E^N)`, checked on a cover by charts
  have key : (J.comap π).colon (E ^ (N + 1)) ≤ (J.comap π).colon (E ^ N) := by
    choose U U' f hf hbU' hle e he hEe using
      exists_chart_of_locally_principal π E J hE hJ
    refine IdealSheafData.le_of_iSup_eq_top U'
      (top_le_iff.mp fun b _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨b, hbU' b⟩) fun b => ?_
    set φ := π.appLE (U b).1 (U' b).1 (hle b) with hφ
    have hJ' : (J.comap π).ideal (U' b) = Ideal.span {φ.hom (f b)} := by
      rw [IdealSheafData.ideal_comap_of_le J π (U b) (U' b) (hle b), hf b, Ideal.map_span,
        Set.image_singleton]
    -- `E ^ c ∣ J*` gives `e ^ c ∣ π♯ f` on the chart
    have hdvd : ∀ c, E ^ c ∣ J.comap π → e b ^ c ∣ φ.hom (f b) := fun c hc => by
      have := le_pow_of_pow_dvd hc (U' b)
      rw [hJ', IdealSheafData.ideal_pow, Pi.pow_apply, hEe b, Ideal.span_singleton_pow] at this
      exact Ideal.span_singleton_le_span_singleton.mp this
    have hEpow := IdealSheafData.isInvertible_pow hE
    rw [IdealSheafData.ideal_colon_of_isInvertible _ _ (hEpow _) (U' b),
      IdealSheafData.ideal_colon_of_isInvertible _ _ (hEpow _) (U' b), hJ']
    simp only [IdealSheafData.ideal_pow, Pi.pow_apply, hEe b, Ideal.span_singleton_pow,
      Ideal.colon_span]
    intro u hu
    rw [Submodule.mem_colon_singleton, smul_eq_mul] at hu ⊢
    by_cases hbdd : BddAbove {c : ℕ | E ^ c ∣ J.comap π}
    · -- the exceptional order is attained: `E ^ N ∣ J*` and `E ^ (N + 1) ∤ J*`
      have hmem : E ^ N ∣ J.comap π :=
        Nat.sSup_mem ⟨0, show E ^ 0 ∣ J.comap π by rw [pow_zero]; exact one_dvd _⟩ hbdd
      have hmax : ¬ E ^ (N + 1) ∣ J.comap π := fun h =>
        Nat.not_succ_le_self N (le_csSup hbdd h)
      by_cases hz : ∃ z : E.subscheme, E.subschemeι z ∈ (U' b).1
      · -- the chart meets `V(E)`: `e` is prime and `e ^ (N + 1) ∤ π♯ f` by constancy
        obtain ⟨z, hz⟩ := hz
        have : Nonempty (U' b).1 := ⟨⟨_, hz⟩⟩
        have hne : e b ≠ 0 := fun h0 =>
          one_ne_zero ((mem_nonZeroDivisors_iff.mp (he b)).1 1 (by rw [h0, zero_mul]))
        have hprime : Prime (e b) := (Ideal.span_singleton_prime hne).mp
          (by rw [← hEe b]; exact E.isPrime_ideal_of_isIntegral_subscheme (U' b) hz)
        refine mul_pow_mem_span_of_mul_pow_succ_mem (he b) hprime (hdvd N hmem)
          (fun hd => hmax ?_) hu
        refine pow_dvd_of_le_pow_of_isInvertible hE ?_
        refine comap_le_pow_succ_of_chart π E J hE hJ (le_pow_of_pow_dvd hmem) (U' b) hz ?_
        rw [hJ', hEe b, Ideal.span_singleton_pow]
        exact Ideal.span_singleton_le_span_singleton.mpr hd
      · -- the chart misses `V(E)`: `e` is a unit
        have htop := E.ideal_eq_top_of_forall_notMem (U' b) fun z hz' => hz ⟨z, hz'⟩
        rw [hEe b, Ideal.span_singleton_eq_top] at htop
        rw [pow_succ, ← mul_assoc] at hu
        exact (Ideal.mul_unit_mem_iff_mem _ htop).mp hu
    · -- every power of `E` divides `J*`: `N = 0` and `(J* : E) = J*` on the Noetherian chart
      have hN0 : N = 0 := Nat.sSup_of_not_bddAbove hbdd
      have hall : ∀ c, e b ^ c ∣ φ.hom (f b) := fun c => by
        obtain ⟨y, hy, hcy⟩ := not_bddAbove_iff.mp hbdd c
        exact hdvd c ((pow_dvd_pow E hcy.le).trans hy)
      rw [hN0, pow_zero, mul_one]
      rw [hN0, zero_add, pow_one] at hu
      have := IsLocallyNoetherian.component_noetherian (U' b)
      exact mem_span_of_mul_mem_of_forall_pow_dvd (he b) hall hu
  -- all colons are bounded by the `N`-th one
  have hall : ∀ i, (J.comap π).colon (E ^ i) ≤ (J.comap π).colon (E ^ N) := by
    have hstep : ∀ m, (J.comap π).colon (E ^ (N + m)) ≤ (J.comap π).colon (E ^ N) := by
      intro m
      induction m with
      | zero => exact le_rfl
      | succ m ih =>
        calc (J.comap π).colon (E ^ (N + (m + 1)))
            = ((J.comap π).colon (E ^ (N + m))).colon E := by
              rw [IdealSheafData.colon_colon, ← Nat.add_assoc, pow_succ]
          _ ≤ ((J.comap π).colon (E ^ N)).colon E := IdealSheafData.colon_mono_left _ _ E ih
          _ = (J.comap π).colon (E ^ (N + 1)) := by rw [IdealSheafData.colon_colon, pow_succ]
          _ ≤ (J.comap π).colon (E ^ N) := key
    intro i
    rcases le_or_gt i N with h | h
    · exact IdealSheafData.colon_pow_mono _ _ h
    · have := hstep (i - N)
      rwa [Nat.add_sub_cancel' h.le] at this
  change (J.comap π).colon (E ^ N) = (J.comap π).saturate E
  exact le_antisymm (IdealSheafData.colon_pow_le_saturate _ _ N) (iSup_le hall)

omit [IsIntegral E.subscheme] in
/-- The principal case of the weak transform in Hauser's setting [Hau14, Remark 6.9]: the
exceptional divisor `V(E)` regular (stalks regular local rings) and irreducible. -/
theorem weakTransformAlong_eq_strictTransformAlong_of_locally_principal' [IsLocallyNoetherian B]
    (hE : E.IsInvertible)
    (hF : ∀ z : E.subscheme, IsRegularLocalRing (E.subscheme.presheaf.stalk z))
    [IrreducibleSpace E.subscheme]
    (hJ : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ ∃ f : Γ(X, U), J.ideal U = Ideal.span {f}) :
    J.weakTransformAlong π E = J.strictTransformAlong π E :=
  have := E.isIntegral_subscheme_of_isRegularLocalRing_stalk hF
  weakTransformAlong_eq_strictTransformAlong_of_locally_principal π E J hE hJ

end AlgebraicGeometry
