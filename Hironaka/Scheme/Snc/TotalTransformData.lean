/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
import Hironaka.Scheme.Snc.ParameterSubset
import Hironaka.Scheme.Snc.TrivialTotalTransform

/-!
# The shape of the total transform at a point of the exceptional divisor

Hauser's chart computation (the proof of [Hau14, Proposition 5.3]; [Hau14, Proposition 5.4 (7)])
reads the total transform of an snc divisor at a point `x'` of the exceptional divisor `F` of a
smooth blow-up in coordinates `y` at `x'` for which `F = (y_j)`: the total transform of a component
containing the centre is `(y_c · y_j)` — or `(y_j)` for the component whose coordinate is the chart
coordinate — and that of a transversal component is `(y_c)`; a component not through `x'` has total
transform `(1)`. Its strict transform is the saturation `⋃_k (T : F^k)`, which divides out the
exceptional factor: `(y_c y_j) : y_j^∞ = (y_c)`, `(y_j) : y_j^∞ = (1)`.

This module isolates that shape as a predicate on a local ring, `TotalTransformData F T` — a regular
system of parameters `z` with `F = (z_j)` and each `T i` of one of the four shapes, the parameter
indices of the components through the point being distinct and different from `j` — proves that the
predicate transports along ring isomorphisms (how the chart computation reaches the stalk
`𝒪_{B,x'}`, `Hironaka.Scheme.Snc.TotalTransformOnCentre`), and computes the saturations in a regular
local ring: the strict transform of a component through `x'` is the prime `(z_a)`, that of a
component missing `x'` (or of the component with `c = j`, [Hau14, Definition 6.2]) is `(1)`. The
assembly into Kollár's conditions (1)–(3) for the total transform
(`exists_snc_data_totalTransform_of_mem_support` of `Hironaka.Scheme.Snc.TotalTransformSnc`) then
only reads off the indices.

**Why the saturations hold.** `(z_a)` is prime for a member of a regular system of parameters (the
quotient is regular, hence a domain), and `z_j ∉ (z_a)` for `a ≠ j` (distinct members are
independent modulo `𝔪²`). Hence `z_a z_j ∣ r z_j^k` forces `z_a ∣ r`, so `(z_a z_j) : z_j^k ⊆ (z_a)`
for every `k`, with equality of the union at `k = 1`; `(z_a) : z_j^k = (z_a)` since `(z_a)` is a
prime not containing `z_j`; and `(z_j) : z_j = (1)`.

Sources: [Hau14, Proposition 5.3] (the proof); [Hau14, Proposition 5.4 (7); Definition 6.2];
[Kol07, Definition 24].
-/

@[expose] public section

universe u v w

open IsLocalRing Ideal

namespace AlgebraicGeometry

section Data

variable {S : Type u} [CommRing S] [IsLocalRing S] {ι : Type v}

/-- The shape of the total transform at a point `x'` of the exceptional divisor (the proof of
[Hau14, Proposition 5.3]): the stalk is a regular local ring with a regular system of parameters
`z`, the exceptional divisor has stalk `(z_j)`, and the total transform `T i` of each component is
`(z_{a i} · z_j)` (a component containing the centre, through `x'`), `(z_{a i})` (a transversal
component through `x'`), `(z_j)` (the component of the chart coordinate) or `(1)` (a component
missing `x'`); the indices `a i` of the components through `x'` are different from `j` and distinct
(the index of a component missing `x'` is irrelevant and may be taken to be `j`). -/
def TotalTransformData (F : Ideal S) (T : ι → Ideal S) : Prop :=
  IsRegularLocalRing S ∧ ∃ (m : ℕ) (z : Fin m → S),
    (span (Set.range z) = maximalIdeal S ∧ (m : WithBot ℕ∞) = ringKrullDim S) ∧
    ∃ (j : Fin m) (a : ι → Fin m), F = span {z j} ∧
      (∀ i i', a i ≠ j → a i' ≠ j → a i = a i' → i = i') ∧
      ∀ i, (a i ≠ j ∧ (T i = span {z (a i) * z j} ∨ T i = span {z (a i)})) ∨
        T i = span {z j} ∨ T i = ⊤

/-- The maximal ideal transports along a ring isomorphism of local rings. -/
theorem map_maximalIdeal_ringEquiv {S' : Type w} [CommRing S'] [IsLocalRing S'] (e : S ≃+* S') :
    (maximalIdeal S').map e.symm = maximalIdeal S := by
  rw [Ideal.map_symm]
  exact IsLocalRing.eq_maximalIdeal
    (Ideal.comap_isMaximal_of_surjective e e.surjective (K := maximalIdeal S'))

/-- The total-transform shape transports along a ring isomorphism `e : S ≃ S'` carrying the
ideals `F`, `T i` to `F'`, `T' i`. -/
theorem TotalTransformData.of_ringEquiv {S' : Type w} [CommRing S'] [IsLocalRing S']
    (e : S ≃+* S') {F : Ideal S} {T : ι → Ideal S} {F' : Ideal S'} {T' : ι → Ideal S'}
    (hF : F.map e = F') (hT : ∀ i, (T i).map e = T' i)
    (h : TotalTransformData F' T') : TotalTransformData F T := by
  obtain ⟨hreg, m, z', ⟨hspan, hdim⟩, j, a, hF', hinj, hshape⟩ := h
  have hback : ∀ (I : Ideal S) (I' : Ideal S'), I.map e = I' → I = I'.map e.symm := by
    intro I I' hI
    rw [Ideal.map_symm, ← hI, Ideal.comap_map_of_bijective _ e.bijective]
  have hspan' : ∀ b : S', (span {b}).map e.symm = span {e.symm b} := fun b => by
    rw [Ideal.map_span, Set.image_singleton]
  refine ⟨IsRegularLocalRing.of_ringEquiv e.symm, m, e.symm ∘ z', ⟨?_, ?_⟩, j, a, ?_, hinj, ?_⟩
  · rw [Set.range_comp, ← Ideal.map_span, hspan, map_maximalIdeal_ringEquiv e]
  · rw [hdim]
    exact ringKrullDim_eq_of_ringEquiv e.symm
  · rw [hback F F' hF, hF', hspan']
    rfl
  · intro i
    rw [hback (T i) (T' i) (hT i)]
    rcases hshape i with ⟨hne, hi | hi⟩ | hi | hi
    · exact Or.inl ⟨hne, Or.inl (by rw [hi, hspan', map_mul]; rfl)⟩
    · exact Or.inl ⟨hne, Or.inr (by rw [hi, hspan']; rfl)⟩
    · exact Or.inr (Or.inl (by rw [hi, hspan']; rfl))
    · exact Or.inr (Or.inr (by rw [hi, Ideal.map_top]))

end Data

section Saturation

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] {m : ℕ} {z : Fin m → R}
  (hz : span (Set.range z) = maximalIdeal R) (hn : (m : WithBot ℕ∞) = ringKrullDim R)
include hz hn

/-- `z_j ∉ (z_a)` for distinct members of a regular system of parameters. -/
theorem notMem_span_singleton_of_ne {a j : Fin m} (haj : a ≠ j) : z j ∉ span {z a} := by
  have h := notMem_span_image_of_notMem hz.symm hn (s := {a}) (j := j)
    (by simpa using fun h => haj h.symm)
  rwa [Finset.coe_singleton, Set.image_singleton] at h

/-- [Hau14, Proposition 5.4 (7)]: `(z_a z_j) : z_j^∞ = (z_a)` for `a ≠ j` — the saturation divides
out the exceptional factor. -/
theorem iSup_colon_pow_span_singleton_mul {a j : Fin m} (haj : a ≠ j) :
    (⨆ k : ℕ, (span {z a * z j}).colon (↑(span {z j} ^ k) : Set R)) = span {z a} := by
  have hprime := isPrime_span_singleton_of_parameters hz.symm hn a
  have hnot := notMem_span_singleton_of_ne hz hn haj
  refine le_antisymm (iSup_le fun k => fun r hr => ?_) (le_iSup_of_le 1 fun r hr => ?_)
  · rw [Submodule.mem_colon] at hr
    have h := hr (z j ^ k) (Ideal.pow_mem_pow (mem_span_singleton_self (z j)) k)
    rw [smul_eq_mul, mem_span_singleton] at h
    rw [mem_span_singleton]
    have h1 : z a ∣ r * z j ^ k := (dvd_mul_right (z a) (z j)).trans h
    rcases (hprime.mem_or_mem (mem_span_singleton.mpr h1)) with h2 | h2
    · exact mem_span_singleton.mp h2
    · exact absurd (hprime.mem_of_pow_mem k h2) hnot
  · rw [Submodule.mem_colon]
    intro s hs
    rw [pow_one, SetLike.mem_coe, mem_span_singleton] at hs
    obtain ⟨t, rfl⟩ := hs
    rw [smul_eq_mul, mem_span_singleton]
    obtain ⟨u, rfl⟩ := mem_span_singleton.mp hr
    exact ⟨u * t, by ring⟩

/-- The proof of [Hau14, Proposition 5.3]: `(z_a) : z_j^∞ = (z_a)` for `a ≠ j` — a transversal
component is unchanged by the saturation. -/
theorem iSup_colon_pow_span_singleton_of_ne {a j : Fin m} (haj : a ≠ j) :
    (⨆ k : ℕ, (span {z a}).colon (↑(span {z j} ^ k) : Set R)) = span {z a} := by
  have h : ∀ k : ℕ, (span {z a}).colon (↑(span {z j} ^ k) : Set R) = span {z a} := fun k =>
    Ideal.colon_pow_eq_self_of_isPrime (isPrime_span_singleton_of_parameters hz.symm hn a)
      (fun h => notMem_span_singleton_of_ne hz hn haj (h (mem_span_singleton_self _))) k
  exact le_antisymm (iSup_le fun k => (h k).le) (le_iSup_of_le 0 (h 0).ge)

end Saturation

section SaturationGeneral

variable {R : Type u} [CommRing R]

/-- `(z_j) : z_j^∞ = (1)`: the component of the chart coordinate dies ([Hau14, Definition 6.2]). -/
theorem iSup_colon_pow_span_singleton_self (g : R) :
    (⨆ k : ℕ, (span {g} : Ideal R).colon (↑(span {g} ^ k) : Set R)) = ⊤ :=
  top_le_iff.mp (le_iSup_of_le 1 (by rw [pow_one, Ideal.colon_coe_self]))

/-- The saturation of the unit ideal is the unit ideal. -/
theorem iSup_colon_pow_top (J : Ideal R) :
    (⨆ k : ℕ, (⊤ : Ideal R).colon (↑(J ^ k) : Set R)) = ⊤ :=
  top_le_iff.mp (le_iSup_of_le 0 fun _ _ => Submodule.mem_colon.mpr fun _ _ => trivial)

end SaturationGeneral

section Assembly

variable {S : Type u} [CommRing S] [IsLocalRing S] {ι : Type v} {F : Ideal S} {T : ι → Ideal S}

/-- The strict transforms read off the total-transform shape: the saturation `⋃ₖ (T i : F^k)` is
`(z_{a i})` for a component through `x'` (its index `a i ≠ j`) and `(1)` otherwise. -/
theorem TotalTransformData.iSup_colon_eq (h : TotalTransformData F T) :
    IsRegularLocalRing S ∧ ∃ (m : ℕ) (z : Fin m → S),
      (span (Set.range z) = maximalIdeal S ∧ (m : WithBot ℕ∞) = ringKrullDim S) ∧
      ∃ (j : Fin m) (a : ι → Fin m), F = span {z j} ∧
        (∀ i i', a i ≠ j → a i' ≠ j → a i = a i' → i = i') ∧
        ∀ i, (a i ≠ j ∧ (⨆ k : ℕ, (T i).colon (↑(F ^ k) : Set S)) = span {z (a i)}) ∨
          (⨆ k : ℕ, (T i).colon (↑(F ^ k) : Set S)) = ⊤ := by
  obtain ⟨hreg, m, z, ⟨hspan, hdim⟩, j, a, hF, hinj, hshape⟩ := h
  refine ⟨hreg, m, z, ⟨hspan, hdim⟩, j, a, hF, hinj, fun i => ?_⟩
  rw [hF]
  rcases hshape i with ⟨hne, hi | hi⟩ | hi | hi
  · exact Or.inl ⟨hne, by rw [hi]; exact iSup_colon_pow_span_singleton_mul hspan hdim hne⟩
  · exact Or.inl ⟨hne, by rw [hi]; exact iSup_colon_pow_span_singleton_of_ne hspan hdim hne⟩
  · exact Or.inr (by rw [hi]; exact iSup_colon_pow_span_singleton_self (z j))
  · exact Or.inr (by rw [hi]; exact iSup_colon_pow_top _)

end Assembly

end AlgebraicGeometry
