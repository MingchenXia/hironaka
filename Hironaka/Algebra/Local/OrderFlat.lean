/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.Defs
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Hironaka.Algebra.Local.CompletionMap
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.Localization

/-!
# The order under local homomorphisms reflecting the powers of the maximal ideal

The order of an ideal does not drop under a local homomorphism `φ : A → B` (`ord_le_ord_map`,
`Hironaka/Algebra/Local/Order.lean`). It is preserved when `φ` reflects the powers of the maximal
ideal, `φ⁻¹(𝔪_Bʳ) ⊆ 𝔪_Aʳ` for every `r` (`OrdFaithful φ`; the reverse inclusion holds for every
local map): then `J B ⊆ 𝔪_Bʳ` forces `J ⊆ 𝔪_Aʳ`, so `ord_B (J B) ≤ ord_A J`
(`ord_map_le_of_ordFaithful`) and `ord_B (J B) = ord_A J` (`ord_map_eq_of_ordFaithful`). The
property is stable under composition, transports along isomorphisms, and descends from `ψ ∘ φ` to
`φ` when `ψ` is local (`OrdFaithful.of_comp`).

The main instance is the étale case: a flat local map with `𝔪_A B = 𝔪_B` reflects the powers of
the maximal ideal (`ordFaithful_of_flat_of_map_maximalIdeal_eq`), since `𝔪_Bʳ = 𝔪_Aʳ B` and
`𝔪_Aʳ B ∩ A = 𝔪_Aʳ`, a flat local map being faithfully flat (Mathlib's
`Module.FaithfullyFlat.of_flat_of_isLocalHom` and `Ideal.comap_map_eq_self_of_faithfullyFlat`);
hence `ord_B (J B) = ord_A J` (`ord_map_eq_of_flat_of_map_maximalIdeal_eq`). Flatness alone does
not suffice: `k[t]_{(t)} → k[y]_{(y)}`, `t ↦ y²`, is flat and local and doubles the order. Two
convenient forms: for a flat `A`-algebra `D` and a prime `Q = 𝔪_A D`, the map `A → D_Q` reflects
the powers of the maximal ideal (`ordFaithful_algebraMap_atPrime_of_flat`), and so does the
localization of a bijective ring map at a prime (`ordFaithful_localRingHom_of_bijective`).

This is the algebra behind the statement of [Hau03, Appendix A] that the order is invariant
"with respect to smooth morphisms". The polynomial and smooth cases are
`Hironaka/Algebra/Local/OrderPolynomial.lean` and `Hironaka/Algebra/Local/OrderSmooth.lean`; the
transport of the bound of [Kol07, Lemma 61] along the chart-ring map is
`Hironaka/Algebra/Local/ChartOrderFaithful.lean`; the flat case is used in
`Hironaka/Scheme/BlowUpSequence/BaseChangeOrder.lean` and the vocabulary in
`Hironaka/Scheme/IdealSheaf/Order/Smooth.lean`.
-/

@[expose] public section

namespace IsLocalRing

open IsLocalRing

variable {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]

/-- A ring map `φ : A → B` of local rings reflects the powers of the maximal ideal:
`φ⁻¹(𝔪_Bʳ) ⊆ 𝔪_Aʳ` for every `r`. -/
def OrdFaithful (φ : A →+* B) : Prop :=
  ∀ r : ℕ, (maximalIdeal B ^ r).comap φ ≤ maximalIdeal A ^ r

theorem OrdFaithful.comap_pow_eq {φ : A →+* B} [IsLocalHom φ] (h : OrdFaithful φ) (r : ℕ) :
    (maximalIdeal B ^ r).comap φ = maximalIdeal A ^ r :=
  le_antisymm (h r) ((Ideal.le_comap_map).trans (Ideal.comap_mono
    ((Ideal.map_pow _ _ _).le.trans (Ideal.pow_right_mono (map_maximalIdeal_le φ) r))))

/-- `ord_B (J B) ≤ ord_A J` when `φ` reflects the powers of the maximal ideal. -/
theorem ord_map_le_of_ordFaithful {φ : A →+* B} (h : OrdFaithful φ) (J : Ideal A) :
    ord (J.map φ) ≤ ord J := by
  rw [← ENat.forall_natCast_le_iff_le]
  intro r hr
  rw [le_ord_iff] at hr ⊢
  exact (Ideal.le_comap_map).trans ((Ideal.comap_mono hr).trans (h r))

/-- `ord_B (J B) = ord_A J` for a local `φ` reflecting the powers of the maximal ideal. -/
theorem ord_map_eq_of_ordFaithful {φ : A →+* B} [IsLocalHom φ] (h : OrdFaithful φ) (J : Ideal A) :
    ord (J.map φ) = ord J :=
  le_antisymm (ord_map_le_of_ordFaithful h J) (ord_le_ord_map φ J)

theorem OrdFaithful.comp {C : Type*} [CommRing C] [IsLocalRing C] {φ : A →+* B} {ψ : B →+* C}
    (hφ : OrdFaithful φ) (hψ : OrdFaithful ψ) : OrdFaithful (ψ.comp φ) := fun r => by
  rw [← Ideal.comap_comap]
  exact (Ideal.comap_mono (hψ r)).trans (hφ r)

/-- An isomorphism of local rings reflects the powers of the maximal ideal (through its inverse,
a local map). -/
theorem OrdFaithful.of_ringEquiv (e : A ≃+* B) : OrdFaithful (e : A →+* B) := fun r x hx => by
  rw [Ideal.mem_comap] at hx
  have h1 : (maximalIdeal B ^ r).map (e.symm : B →+* A) ≤ maximalIdeal A ^ r := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono (map_maximalIdeal_le (e.symm : B →+* A)) r
  have h2 := h1 (Ideal.mem_map_of_mem (e.symm : B →+* A) hx)
  simpa using h2

/-- Composition with an isomorphism on the target. -/
theorem OrdFaithful.comp_ringEquiv {C : Type*} [CommRing C] [IsLocalRing C] {φ : A →+* B}
    (h : OrdFaithful φ) (e : B ≃+* C) : OrdFaithful ((e : B →+* C).comp φ) :=
  h.comp (OrdFaithful.of_ringEquiv e)

/-- Composition with an isomorphism on the source. -/
theorem OrdFaithful.ringEquiv_comp {C : Type*} [CommRing C] [IsLocalRing C] {φ : B →+* C}
    (h : OrdFaithful φ) (e : A ≃+* B) : OrdFaithful (φ.comp (e : A →+* B)) :=
  (OrdFaithful.of_ringEquiv e).comp h

theorem OrdFaithful.congr {φ ψ : A →+* B} (h : OrdFaithful φ) (e : φ = ψ) : OrdFaithful ψ :=
  e ▸ h

/-- If `ψ ∘ φ` reflects the powers of the maximal ideal and `ψ` is local, so does `φ`:
`φ⁻¹(𝔪_Bʳ) ⊆ (ψ ∘ φ)⁻¹(𝔪_Cʳ) ⊆ 𝔪_Aʳ`. -/
theorem OrdFaithful.of_comp {C : Type*} [CommRing C] [IsLocalRing C] {φ : A →+* B} {ψ : B →+* C}
    [IsLocalHom ψ] (h : OrdFaithful (ψ.comp φ)) : OrdFaithful φ := fun r => by
  refine le_trans ?_ (h r)
  rw [← Ideal.comap_comap]
  refine Ideal.comap_mono ?_
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  exact Ideal.pow_right_mono (map_maximalIdeal_le ψ) r

/-- The localization of a bijective ring map at a prime reflects the powers of the maximal ideal:
it is inverted by the localization of the inverse map, a local map (`OrdFaithful.of_comp`). -/
theorem ordFaithful_localRingHom_of_bijective {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Bijective f) {p : Ideal R} [p.IsPrime] (q : Ideal S) [q.IsPrime]
    (hpq : p = q.comap f) : OrdFaithful (Localization.localRingHom p q f hpq) := by
  let e := RingEquiv.ofBijective f hf
  have hfe : f.comp (e.symm : S →+* R) = RingHom.id S := RingHom.ext fun s => e.apply_symm_apply s
  have hqp : q = p.comap (e.symm : S →+* R) := by
    rw [hpq, Ideal.comap_comap, hfe, Ideal.comap_id]
  have := Localization.isLocalHom_localRingHom q p (e.symm : S →+* R) hqp
  refine OrdFaithful.of_comp (ψ := Localization.localRingHom q p (e.symm : S →+* R) hqp) ?_
  have : (Localization.localRingHom q p (e.symm : S →+* R) hqp).comp
      (Localization.localRingHom p q f hpq) = RingHom.id _ := by
    refine IsLocalization.ringHom_ext p.primeCompl (RingHom.ext fun r => ?_)
    simp only [RingHom.comp_apply, Localization.localRingHom_to_map, RingHom.id_apply]
    congr 1
    exact e.symm_apply_apply r
  rw [this]
  exact fun r => (Ideal.comap_id _).le

/-- The étale case: a flat local map `A → B` with `𝔪_A B = 𝔪_B` reflects the powers of the
maximal ideal, since `𝔪_Bʳ = 𝔪_Aʳ B` and `𝔪_Aʳ B ∩ A = 𝔪_Aʳ` for the faithfully flat `A → B`. -/
theorem ordFaithful_of_flat_of_map_maximalIdeal_eq [Algebra A B] [Module.Flat A B]
    [IsLocalHom (algebraMap A B)] (h : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) :
    OrdFaithful (algebraMap A B) := fun r => by
  have : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  rw [← h, ← Ideal.map_pow, Ideal.comap_map_eq_self_of_faithfullyFlat]

/-- For a flat local map `A → B` with `𝔪_A B = 𝔪_B`, `ord_B (J B) = ord_A J`. -/
theorem ord_map_eq_of_flat_of_map_maximalIdeal_eq [Algebra A B] [Module.Flat A B]
    [IsLocalHom (algebraMap A B)] (h : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B)
    (J : Ideal A) : ord (J.map (algebraMap A B)) = ord J :=
  ord_map_eq_of_ordFaithful (ordFaithful_of_flat_of_map_maximalIdeal_eq h) J

/-- A flat `A`-algebra `D` and a prime `Q = 𝔪_A D` of `D`: `A → D_Q` is flat and local with
`𝔪_A D_Q = Q D_Q = 𝔪_{D_Q}`, hence reflects the powers of the maximal ideal.  (The shape of both
cases of the one-variable polynomial case in `Hironaka/Algebra/Local/OrderPolynomial.lean`: `D =
A[X]` with `Q = 𝔪_A A[X]`, and `D = A[X]/(G)` for a monic `G`.) -/
theorem ordFaithful_algebraMap_atPrime_of_flat {D : Type*} [CommRing D] [Algebra A D]
    [Module.Flat A D] (Q : Ideal D) [Q.IsPrime]
    (hQ : Q = (maximalIdeal A).map (algebraMap A D)) :
    OrdFaithful (algebraMap A (Localization.AtPrime Q)) := by
  have : IsLocalHom (algebraMap A (Localization.AtPrime Q)) := ⟨fun a ha => by
    rw [IsScalarTower.algebraMap_apply A D (Localization.AtPrime Q),
      IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime Q) Q] at ha
    by_contra h
    refine ha ?_
    rw [hQ]
    exact Ideal.mem_map_of_mem _ ((mem_maximalIdeal a).mpr (mem_nonunits_iff.mpr h))⟩
  refine ordFaithful_of_flat_of_map_maximalIdeal_eq ?_
  rw [IsScalarTower.algebraMap_eq A D (Localization.AtPrime Q), ← Ideal.map_map, ← hQ,
    Localization.AtPrime.map_eq_maximalIdeal]

end IsLocalRing
