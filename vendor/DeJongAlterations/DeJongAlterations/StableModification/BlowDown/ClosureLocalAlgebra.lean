/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.BlowDown.NumericalDescentAlgebra

/-!
# The local structure of a nodal curve at a point of the closed fibre: algebra

Let `R` be a ring with a prime `𝔭` and `A` a local `R`-algebra (a local ring of a nodal curve over
`R` at a point over `𝔭`). `LocalStructure R A 𝔭` records the two properties of `A` used for the
closure of a component of the generic fibre in Temkin's proof of Lemma 4.4.4 (M. Temkin, *Stable
modification of relative curves*, J. Algebraic Geom. 19 (2010), T:3164–3166):

* `reduced`: for every minimal prime `P` of `A`, the fibre `A / (P + 𝔭A)` of the component `P` is
  reduced if the fibre `A / 𝔭A` is;
* `node`: if a minimal prime `P` is not contained in some prime `w ⊇ 𝔭A` (a branch of the fibre
  lies on another component), then `P` is contained in a prime `n` over the generic point
  (`n ∩ R = 0`) whose local ring `A_n` is not a domain and which contains a second minimal prime
  (a node of the generic fibre on the component `P` and on another component).

This file proves the general facts used to establish it: `LocalStructure.of_isDomain` (an integral
local ring has it, trivially), transport along isomorphisms (`LocalStructure.of_algEquiv`), and
the behaviour of minimal primes under (faithfully) flat maps.

Blueprint: `sm-blow-down-unconditional.tex`, `def:sm-bdu-local-structure`.
-/

noncomputable section

open IsLocalRing

namespace DeJongAlterations.StableModification.BlowDown.ClosureLocal

universe u

set_option autoImplicit false

section MinimalPrimes

variable {A A' : Type*} [CommRing A] [CommRing A'] [Algebra A A']

/-- Over a faithfully flat algebra, every minimal prime is the contraction of a minimal prime. -/
theorem exists_mem_minimalPrimes_comap_eq [Module.FaithfullyFlat A A'] {P : Ideal A}
    (hP : P ∈ minimalPrimes A) :
    ∃ Q ∈ minimalPrimes A', Q.comap (algebraMap A A') = P := by
  have : P.IsPrime := hP.1.1
  obtain ⟨Q₀, hQ₀, hQ₀P⟩ := Ideal.exists_isPrime_liesOver_of_faithfullyFlat (B := A') P
  obtain ⟨Q, hQ, hQQ₀⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal A')) (J := Q₀) bot_le
  refine ⟨Q, hQ, ?_⟩
  have : Q.IsPrime := hQ.1.1
  have hle : Q.comap (algebraMap A A') ≤ P := by
    rw [hQ₀P.over]
    exact Ideal.comap_mono hQQ₀
  exact le_antisymm hle (hP.2 ⟨Ideal.comap_isPrime _ _, bot_le⟩ hle)

/-- Over a flat algebra (going down), the contraction of a minimal prime is minimal. -/
theorem comap_mem_minimalPrimes [Module.Flat A A'] {Q : Ideal A'} (hQ : Q ∈ minimalPrimes A') :
    Q.comap (algebraMap A A') ∈ minimalPrimes A := by
  have : Q.IsPrime := hQ.1.1
  refine ⟨⟨Ideal.comap_isPrime _ _, bot_le⟩, fun p hp hpQ => ?_⟩
  have : p.IsPrime := hp.1
  have : Q.LiesOver (Q.comap (algebraMap A A')) := ⟨rfl⟩
  obtain ⟨Q', hQ'Q, hQ', hQ'p⟩ := Ideal.exists_ideal_le_liesOver_of_le (S := A') (p := p)
    (q := Q.comap (algebraMap A A')) Q hpQ
  have hQQ' : Q ≤ Q' := hQ.2 ⟨hQ', bot_le⟩ hQ'Q
  rw [hQ'p.over]
  exact Ideal.comap_mono hQQ'

end MinimalPrimes

section Structure

variable (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] (𝔭 : Ideal R)

/-- **The local structure of a nodal curve at a point over `𝔭`** (blueprint
`def:sm-bdu-local-structure`): the fibres over `𝔭` of the components through the point are
reduced (if the fibre of `A` is), and a component through a point whose fibre over `𝔭` has a
branch off the component carries a point over the generic point of `R` lying on two components. -/
structure LocalStructure : Prop where
  reduced : ∀ P ∈ minimalPrimes A, IsReduced (A ⧸ 𝔭.map (algebraMap R A)) →
    IsReduced (A ⧸ (P ⊔ 𝔭.map (algebraMap R A)))
  node : ∀ P ∈ minimalPrimes A, ∀ w : Ideal A, w.IsPrime → 𝔭.map (algebraMap R A) ≤ w → ¬ P ≤ w →
    ∃ (n : Ideal A) (_ : n.IsPrime), P ≤ n ∧ n.comap (algebraMap R A) = ⊥ ∧
      ¬ IsDomain (Localization.AtPrime n) ∧ ∃ P₂ ∈ minimalPrimes A, P₂ ≠ P ∧ P₂ ≤ n

variable {R A 𝔭}

/-- **A domain has the local structure**: its only minimal prime is `0`. -/
theorem LocalStructure.of_isDomain [IsDomain A] : LocalStructure R A 𝔭 where
  reduced P hP h := by
    rw [IsDomain.minimalPrimes_eq_singleton_bot] at hP
    rw [Set.mem_singleton_iff.mp hP, bot_sup_eq]
    exact h
  node P hP w _ _ hPw := by
    rw [IsDomain.minimalPrimes_eq_singleton_bot] at hP
    exact absurd (Set.mem_singleton_iff.mp hP ▸ bot_le) hPw

/-- **The local structure is invariant under isomorphisms of `R`-algebras.** -/
theorem LocalStructure.of_algEquiv {A' : Type*} [CommRing A'] [Algebra R A'] (e : A ≃ₐ[R] A')
    (h : LocalStructure R A 𝔭) : LocalStructure R A' 𝔭 := by
  set f : A ≃+* A' := e.toRingEquiv
  have hmem : ∀ (I : Ideal A) (x : A'), x ∈ I.map (f : A →+* A') ↔ f.symm x ∈ I := by
    intro I x
    rw [Ideal.map_comap_of_equiv f, Ideal.mem_comap]
  have hmap : ∀ I : Ideal R, (I.map (algebraMap R A)).map (f : A →+* A') =
      I.map (algebraMap R A') := by
    intro I
    rw [Ideal.map_map]
    congr 1
    ext r
    exact e.commutes r
  have hcomap : ∀ P' : Ideal A', (P'.comap (f : A →+* A')).map (f : A →+* A') = P' := fun P' =>
    Ideal.map_comap_of_surjective _ f.surjective P'
  have hmin : ∀ P' ∈ minimalPrimes A', P'.comap (f : A →+* A') ∈ minimalPrimes A := by
    intro P' hP'
    have : P'.IsPrime := hP'.1.1
    refine ⟨⟨Ideal.comap_isPrime _ _, bot_le⟩, fun p hp hpP => ?_⟩
    have : p.IsPrime := hp.1
    have hp' : (p.map (f : A →+* A')).IsPrime := Ideal.map_isPrime_of_equiv f
    have hle : p.map (f : A →+* A') ≤ P' := by
      rw [Ideal.map_le_iff_le_comap]
      exact hpP
    have := hP'.2 ⟨hp', bot_le⟩ hle
    intro x hx
    have hx' : f x ∈ p.map (f : A →+* A') := this hx
    rw [hmem] at hx'
    simpa using hx'
  refine ⟨fun P' hP' hred => ?_, fun P' hP' w' hw' h𝔭w hPw => ?_⟩
  · set P := P'.comap (f : A →+* A')
    have hred0 : IsReduced (A ⧸ 𝔭.map (algebraMap R A)) := by
      let g : A ⧸ 𝔭.map (algebraMap R A) ≃+* A' ⧸ 𝔭.map (algebraMap R A') :=
        Ideal.quotientEquiv _ _ f (hmap 𝔭).symm
      exact isReduced_of_injective g.toRingHom g.injective
    have hP := h.reduced P (hmin P' hP') hred0
    let g : A ⧸ (P ⊔ 𝔭.map (algebraMap R A)) ≃+* A' ⧸ (P' ⊔ 𝔭.map (algebraMap R A')) :=
      Ideal.quotientEquiv _ _ f (by rw [Ideal.map_sup, hcomap, hmap])
    exact isReduced_of_injective g.symm.toRingHom g.symm.injective
  · set P := P'.comap (f : A →+* A')
    set w := w'.comap (f : A →+* A')
    have : w.IsPrime := Ideal.comap_isPrime _ _
    have h𝔭w' : 𝔭.map (algebraMap R A) ≤ w := by
      rw [← Ideal.map_le_iff_le_comap, hmap]
      exact h𝔭w
    have hPw' : ¬ P ≤ w := fun hle => hPw (by
      rw [← hcomap P', ← hcomap w']
      exact Ideal.map_mono hle)
    obtain ⟨n, hn, hPn, hnR, hreg, P₂, hP₂, hP₂P, hP₂n⟩ := h.node P (hmin P' hP') w this h𝔭w' hPw'
    have hn' : (n.map (f : A →+* A')).IsPrime := Ideal.map_isPrime_of_equiv f
    have hcm : ∀ I : Ideal A, (I.map (f : A →+* A')).comap (f : A →+* A') = I := by
      intro I
      ext x
      rw [Ideal.mem_comap, hmem]
      simp
    refine ⟨n.map (f : A →+* A'), hn', ?_, ?_, fun hreg' => ?_, P₂.map (f : A →+* A'), ?_, ?_,
      Ideal.map_mono hP₂n⟩
    · rw [← hcomap P']
      exact Ideal.map_mono hPn
    · ext r
      rw [Ideal.mem_comap, hmem, Ideal.mem_bot]
      have : f.symm (algebraMap R A' r) = algebraMap R A r := by
        rw [show algebraMap R A' r = f (algebraMap R A r) from (e.commutes r).symm]
        exact f.symm_apply_apply _
      rw [this, ← Ideal.mem_comap, hnR, Ideal.mem_bot]
    · have hM : n.primeCompl.map f.toMonoidHom = (n.map (f : A →+* A')).primeCompl := by
        ext y
        simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff, hmem]
        constructor
        · rintro ⟨x, hx, rfl⟩ hmem'
          exact hx (by simpa using hmem')
        · intro hy
          exact ⟨f.symm y, hy, by simp⟩
      let eL : Localization.AtPrime n ≃+* Localization.AtPrime (n.map (f : A →+* A')) :=
        IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime n)
          (Localization.AtPrime (n.map (f : A →+* A'))) f hM
      exact hreg (eL.injective.isDomain eL.toRingHom)
    · have : P₂.IsPrime := hP₂.1.1
      have hp' : (P₂.map (f : A →+* A')).IsPrime := Ideal.map_isPrime_of_equiv f
      refine ⟨⟨hp', bot_le⟩, fun q hq hqP => ?_⟩
      have : q.IsPrime := hq.1
      have hle := hP₂.2 ⟨Ideal.comap_isPrime (f : A →+* A') q, bot_le⟩
        (by rw [← hcm P₂]; exact Ideal.comap_mono hqP)
      rw [← hcomap q]
      exact Ideal.map_mono hle
    · intro heq
      apply hP₂P
      rw [← hcm P₂, heq]

end Structure

end DeJongAlterations.StableModification.BlowDown.ClosureLocal
