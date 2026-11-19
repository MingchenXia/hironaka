/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.Snc.TotalTransformOffCentre
public import Hironaka.Scheme.Snc.SmoothDivisor
import Hironaka.Algebra.Local.Regular
import Hironaka.Algebra.Local.RegularSystem
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUp.Transform
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.IdealSheaf.StalkLe
import Hironaka.Scheme.Smooth.AdaptedCoordinates
import Hironaka.Scheme.Snc.Family
import Hironaka.Scheme.Snc.HasSncWith
import Hironaka.Scheme.Snc.TotalTransformOnCentre
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The total transform is snc: Kollár's conditions and the strict transforms

The total-transform theorem of [Hau14, Proposition 5.3] in the unfolded form — families of ideal
sheaves with the snc data as explicit hypotheses, the family `(π_*^{-1} E^i, F)` as
`totalTransformFamily`; the forms on the predicates `IsSnc`, `HasSncWith`, `IsSncAt`,
`totalTransform`, `strictTransform` and `exceptionalDivisor` are in
`Hironaka.Scheme.Snc.TotalTransformChartComputation`:

* at a point `x'` of the exceptional divisor `F`, Kollár's conditions (1)–(3) for the family
  `(π_*^{-1} E^i, F)` (`exists_snc_data_totalTransform_of_mem_support`), read off
  `TotalTransformData` at `x'` (`exists_totalTransformData_of_mem_support` of
  `Hironaka.Scheme.Snc.TotalTransformOnCentre`) and the saturations `(T : F^∞)` of
  `TotalTransformData.iSup_colon_eq` — the strict transform of a component through `x'` is the
  coordinate hyperplane `(z_a)`, the exceptional divisor is `(z_j)`, the other members miss `x'`;
* at a point `x' ∈ F` over `x` with snc coordinates `z` at `x` (`D_x = (z_c)`,
  `Z_x = (z_l : l ∈ s)`): for `c ∉ s` the strict transform of `D` has stalk `(π^* z_c)`
  (`stalkIdeal_strictTransformAlong_of_notMem`) and contains the fibre over `Z ∩ D`
  (`mem_support_strictTransformAlong_iff_of_notMem`); for `c ∈ s`, `π^* z_c = u e` for a generator
  `e` of `F_{x'}` and the strict transform has stalk `(u)`
  (`exists_stalkIdeal_strictTransformAlong_eq_span_of_mem`); where `π^* z_c` itself generates
  `F_{x'}` the strict transform misses `x'`
  (`notMem_support_strictTransformAlong_of_stalkIdeal_eq`);
* every member of the total transform is a smooth divisor (`isSmoothDivisor_totalTransformFamily`),
  from the snc data at every point (on and off `F`) and `isSmoothDivisor_of_snc_data` of
  `Hironaka.Scheme.Snc.Family`.

**Why the lemmas hold.** At `x' ∈ F` the total transform of `D` is `π^*(D_x) = (π^* z_c)`, and
`TotalTransformData` says it is `(z'_a z'_j)`, `(z'_a)`, `(z'_j)` or `(1)` in a regular system of
parameters `z'` of `𝒪_{B,x'}` with `F_{x'} = (z'_j)`. Whether `D` contains `Z` near `x` — `c ∈ s`,
by `span_singleton_le_span_image_iff` — decides between the shapes contained in `F_{x'}` (the first
and third) and the others, because a total transform inside the exceptional ideal comes from a
component containing the centre (the containment clause of
`exists_totalTransformData_of_mem_support`), and conversely `D_x ⊆ Z_x` gives `π^*(D_x) ⊆ F_{x'}`.
The saturations then compute the strict transforms (`TotalTransformData.iSup_colon_eq`), and two
generators of a principal ideal of a domain differ by a unit (Mathlib's
`Ideal.span_singleton_eq_span_singleton`).

Sources: [Hau14, Proposition 5.3] (the proof); [Hau14, Proposition 5.4; Definition 6.2];
[Hau03, Appendix C]; [Kol07, Definition 24; Definition 25].
-/

public section

universe u

open AlgebraicGeometry CategoryTheory IsLocalRing Ideal Scheme.IdealSheafData _root_.Algebra

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}}

section Saturation

variable (Z D : X.IdealSheafData) (x' : blowUp Z)

/-- The stalk of the strict transform is the saturation of the stalk of the total transform by the
powers of the stalk of the exceptional ideal. -/
theorem stalkIdeal_strictTransformAlong_eq_iSup :
    (D.strictTransformAlong (blowUpπ Z) (Z.comap (blowUpπ Z))).stalkIdeal x' =
      ⨆ i : ℕ, ((D.comap (blowUpπ Z)).stalkIdeal x').colon
        (↑((Z.comap (blowUpπ Z)).stalkIdeal x' ^ i) : Set ((blowUp Z).presheaf.stalk x')) :=
  stalkIdeal_saturate_of_isInvertible _ (blowUp.isInvertible_comap_π Z) x'

/-- The strict transform contains the total transform, so its support lies over the support of
`D`. -/
theorem π_mem_support_of_mem_support_strictTransformAlong
    (h : x' ∈ (D.strictTransformAlong (blowUpπ Z) (Z.comap (blowUpπ Z))).support) :
    blowUpπ Z x' ∈ D.support := by
  have hle : D.comap (blowUpπ Z) ≤ D.strictTransformAlong (blowUpπ Z) (Z.comap (blowUpπ Z)) :=
    le_saturate _ _
  have h' := (mem_support_iff_stalkIdeal_le_maximalIdeal (D.comap (blowUpπ Z)) x').mpr
    ((stalkIdeal_mono hle x').trans
      ((mem_support_iff_stalkIdeal_le_maximalIdeal _ x').mp h))
  exact (mem_support_comap_iff' D _ x').mp h'

end Saturation

section OnCentre

variable [PerfectField k] (f : X ⟶ Spec (.of k)) [Smooth f] {ι : Type*} [Finite ι]
  (E : ι → X.IdealSheafData) (Z : X.IdealSheafData)
  (hZ : ∀ x ∈ Z.support, ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk x),
    (span (Set.range z) = maximalIdeal (X.presheaf.stalk x) ∧
      (n : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk x)) ∧
    (∃ c : {i : ι // x ∈ (E i).support} → Fin n, Function.Injective c ∧
      ∀ i, (E i.1).stalkIdeal x = span {z (c i)}) ∧
    ∃ s : Finset (Fin n), Z.stalkIdeal x = span (z '' ↑s))

include f hZ

/-- The proof of [Hau14, Proposition 5.3] and [Hau14, Proposition 5.4] ([Hau03, Appendix C]):
**Kollár's conditions (1)–(3) for `(π_*^{-1} E^i, F)` at a point `x'` of `F`** — the stalk is
regular with a regular system of parameters `z'`; `F` takes the coordinate `z'_j`, the strict
transform of a component through `x'` takes its own coordinate `z'_{a i}`, and the assignment is
injective. -/
theorem exists_snc_data_totalTransform_of_mem_support (x' : blowUp Z)
    (hx' : x' ∈ (Z.comap (blowUpπ Z)).support) :
    IsRegularLocalRing ((blowUp Z).presheaf.stalk x') ∧
    ∃ (m : ℕ) (z : Fin m → (blowUp Z).presheaf.stalk x'),
      (span (Set.range z) = maximalIdeal ((blowUp Z).presheaf.stalk x') ∧
        (m : WithBot ℕ∞) = ringKrullDim ((blowUp Z).presheaf.stalk x')) ∧
      ∃ c' : {k : ι ⊕ PUnit.{u + 1} // x' ∈ (totalTransformFamily Z E k).support} → Fin m,
        Function.Injective c' ∧ ∀ k, (totalTransformFamily Z E k.1).stalkIdeal x' =
          span {z (c' k)} := by
  classical
  have hdata := (exists_totalTransformData_of_mem_support f E Z hZ x' hx').1
  have hsat := hdata.iSup_colon_eq
  obtain ⟨hreg, m, z, hz, j, a, hF, hinj, hshape⟩ := hsat
  -- the stalks of the members of the total transform
  have hstalk : ∀ i, (totalTransformFamily Z E (Sum.inl i)).stalkIdeal x' =
      ⨆ n : ℕ, (((E i).comap (blowUpπ Z)).stalkIdeal x').colon
        (↑((Z.comap (blowUpπ Z)).stalkIdeal x' ^ n) : Set ((blowUp Z).presheaf.stalk x')) :=
    fun i => stalkIdeal_strictTransformAlong_eq_iSup Z (E i) x'
  have hFstalk : ∀ u : PUnit.{u + 1}, (totalTransformFamily Z E (Sum.inr u)).stalkIdeal x' =
      span {z j} := fun _ => hF
  -- a member through `x'` is a strict transform with a parameter, or `F`
  have hthrough : ∀ i, x' ∈ (totalTransformFamily Z E (Sum.inl i)).support →
      a i ≠ j ∧ (totalTransformFamily Z E (Sum.inl i)).stalkIdeal x' = span {z (a i)} := by
    intro i hi
    have hle := (mem_support_iff_stalkIdeal_le_maximalIdeal _ x').mp hi
    rcases hshape i with ⟨hne, hi'⟩ | hi'
    · exact ⟨hne, (hstalk i).trans hi'⟩
    · exfalso
      have : (⊤ : Ideal ((blowUp Z).presheaf.stalk x')) ≤ maximalIdeal _ :=
        ((hstalk i).trans hi').symm.le.trans hle
      exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp this)
  let c' : {k : ι ⊕ PUnit.{u + 1} // x' ∈ (totalTransformFamily Z E k).support} → Fin m :=
    fun k => match k with
      | ⟨Sum.inl i, _⟩ => a i
      | ⟨Sum.inr _, _⟩ => j
  refine ⟨hreg, m, z, hz, c', ?_, ?_⟩
  · rintro ⟨k₁, h₁⟩ ⟨k₂, h₂⟩ heq
    match k₁, h₁, k₂, h₂, heq with
    | Sum.inl i₁, h₁, Sum.inl i₂, h₂, heq =>
      exact Subtype.ext (congrArg Sum.inl
        (hinj i₁ i₂ (hthrough i₁ h₁).1 (hthrough i₂ h₂).1 heq))
    | Sum.inl i₁, h₁, Sum.inr u, _, heq => exact absurd heq (hthrough i₁ h₁).1
    | Sum.inr u, _, Sum.inl i₂, h₂, heq => exact absurd heq.symm (hthrough i₂ h₂).1
    | Sum.inr u₁, _, Sum.inr u₂, _, _ => rfl
  · rintro ⟨k, hk⟩
    match k, hk with
    | Sum.inl i, hi => exact (hthrough i hi).2
    | Sum.inr u, _ => exact hFstalk u

/-- The local rings of `B_Z X` are regular (on `F` from the chart shape, off `F` from those of
`X`). -/
theorem isRegularLocalRing_stalk_blowUp' (x' : blowUp Z) :
    IsRegularLocalRing ((blowUp Z).presheaf.stalk x') := by
  by_cases hx' : x' ∈ (Z.comap (blowUpπ Z)).support
  · exact (exists_totalTransformData_of_mem_support f E Z hZ x' hx').1.1
  · have := isIso_stalkMap_π_of_notMem_support Z hx'
    have := isRegularLocalRing_stalk f (blowUpπ Z x')
    exact IsRegularLocalRing.of_ringEquiv (stalkMapπEquiv Z hx')

end OnCentre

section Stalk

variable (Z D : X.IdealSheafData) (x' : blowUp Z) {n : ℕ}
  {z : Fin n → X.presheaf.stalk (blowUpπ Z x')} {c : Fin n}

/-- The total transform of `D = (z_c = 0)` at `x'` is `(π^* z_c)`. -/
theorem stalkIdeal_comap_π_eq (hc : D.stalkIdeal (blowUpπ Z x') = span {z c}) :
    (D.comap (blowUpπ Z)).stalkIdeal x' = span {(blowUpπ Z).stalkMap x' (z c)} := by
  rw [stalkIdeal_comap, hc, Ideal.map_span, Set.image_singleton]

/-- `π^*` is a local homomorphism: `π^* z_c ∈ 𝔪_{x'}` for `z_c ∈ 𝔪_x`. -/
theorem stalkMap_mem_maximalIdeal_of_mem
    (hcz : z c ∈ maximalIdeal (X.presheaf.stalk (blowUpπ Z x'))) :
    (blowUpπ Z).stalkMap x' (z c) ∈ maximalIdeal ((blowUp Z).presheaf.stalk x') :=
  (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr fun hu =>
    mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hcz)
      (isUnit_of_map_unit ((blowUpπ Z).stalkMap x').hom _ hu))

/-- Saturations of equal ideals by equal ideals agree. -/
theorem iSup_colon_congr {S : Type*} [CommRing S] {T F T' F' : Ideal S} (hT : T = T')
    (hF : F = F') :
    (⨆ m : ℕ, T.colon (↑(F ^ m) : Set S)) = ⨆ m : ℕ, T'.colon (↑(F' ^ m) : Set S) := by
  subst hT
  subst hF
  rfl

/-- [Hau14, Definition 6.2]: where `π^* z_c` generates the exceptional ideal, the strict transform
of `D = (z_c = 0)` misses `x'`: `(π^* z_c) : (π^* z_c)^∞ = (1)`. -/
theorem notMem_support_strictTransformAlong_of_stalkIdeal_eq
    (hc : D.stalkIdeal (blowUpπ Z x') = span {z c})
    (he : (Z.comap (blowUpπ Z)).stalkIdeal x' = span {(blowUpπ Z).stalkMap x' (z c)}) :
    x' ∉ (D.strictTransformAlong (blowUpπ Z) (Z.comap (blowUpπ Z))).support := by
  intro h
  have hle := (mem_support_iff_stalkIdeal_le_maximalIdeal _ x').mp h
  have htop : (D.strictTransformAlong (blowUpπ Z) (Z.comap (blowUpπ Z))).stalkIdeal x' = ⊤ :=
    (stalkIdeal_strictTransformAlong_eq_iSup Z D x').trans
      ((iSup_colon_congr (stalkIdeal_comap_π_eq Z D x' hc) he).trans
        (iSup_colon_pow_span_singleton_self _))
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp (htop.symm.le.trans hle))

end Stalk

section

variable [PerfectField k] (f : X ⟶ Spec (.of k)) [Smooth f] {ι : Type*} [Finite ι]
  (E : ι → X.IdealSheafData) (Z : X.IdealSheafData)
  (hZ : ∀ x ∈ Z.support, ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk x),
    (span (Set.range z) = maximalIdeal (X.presheaf.stalk x) ∧
      (n : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk x)) ∧
    (∃ c : {i : ι // x ∈ (E i).support} → Fin n, Function.Injective c ∧
      ∀ i, (E i.1).stalkIdeal x = span {z (c i)}) ∧
    ∃ s : Finset (Fin n), Z.stalkIdeal x = span (z '' ↑s))
  (i : ι) (x' : blowUp Z) (hx' : x' ∈ (Z.comap (blowUpπ Z)).support) {n : ℕ}
  {z : Fin n → X.presheaf.stalk (blowUpπ Z x')}
  (hz : span (Set.range z) = maximalIdeal (X.presheaf.stalk (blowUpπ Z x')) ∧
    (n : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk (blowUpπ Z x')))
  {s : Finset (Fin n)} (hs : Z.stalkIdeal (blowUpπ Z x') = span (z '' ↑s)) {c : Fin n}
  (hc : (E i).stalkIdeal (blowUpπ Z x') = span {z c})

include f hZ hx' hz hs hc

/-- The proof of [Hau14, Proposition 5.3]: for `c ∉ s` — the component transversal to `Z` — the
strict transform has stalk `(π^* z_c)`: its total transform has the shape `(z'_a)` of a coordinate
hyperplane, unchanged by the saturation. -/
theorem stalkIdeal_strictTransformAlong_of_notMem (hcs : c ∉ s) :
    ((E i).strictTransformAlong (blowUpπ Z) (Z.comap (blowUpπ Z))).stalkIdeal x' =
      span {(blowUpπ Z).stalkMap x' (z c)} := by
  classical
  have hreg : IsRegularLocalRing (X.presheaf.stalk (blowUpπ Z x')) :=
    isRegularLocalRing_stalk f _
  have hdata := exists_totalTransformData_of_mem_support f E Z hZ x' hx'
  obtain ⟨hshape, hcont⟩ := hdata
  have hT0 := stalkIdeal_comap_π_eq Z (E i) x' hc
  -- the total transform is not contained in the exceptional ideal
  have hnotle : ¬ ((E i).comap (blowUpπ Z)).stalkIdeal x' ≤
      (Z.comap (blowUpπ Z)).stalkIdeal x' :=
    fun hle => hcs ((stalkIdeal_le_stalkIdeal_iff_mem hz hs hc).mp (hcont i hle))
  obtain ⟨hreg', m', z'', hz'', j', a', hF', -, hshape''⟩ := hshape
  rw [stalkIdeal_strictTransformAlong_eq_iSup, ← hT0]
  rcases hshape'' i with ⟨hne, hT | hT⟩ | hT | hT
  · -- `(z'_a z'_j) ⊆ (z'_j)`: excluded
    have hT' : ((E i).comap (blowUpπ Z)).stalkIdeal x' = span {z'' (a' i) * z'' j'} := hT
    exact absurd (hT'.le.trans ((Ideal.span_le.mpr (Set.singleton_subset_iff.mpr
      (Ideal.mul_mem_left _ _ (mem_span_singleton_self _)))).trans hF'.symm.le)) hnotle
  · -- the transversal shape: the saturation is the ideal itself
    have hT' : ((E i).comap (blowUpπ Z)).stalkIdeal x' = span {z'' (a' i)} := hT
    exact (iSup_colon_congr hT' hF').trans
      ((iSup_colon_pow_span_singleton_of_ne hz''.1 hz''.2 hne).trans hT'.symm)
  · -- `(z'_j)`: excluded
    have hT' : ((E i).comap (blowUpπ Z)).stalkIdeal x' = span {z'' j'} := hT
    exact absurd (hT'.le.trans hF'.symm.le) hnotle
  · -- `(1)`: excluded, `π^* z_c ∈ 𝔪_{x'}`
    have hT' : ((E i).comap (blowUpπ Z)).stalkIdeal x' = ⊤ := hT
    have hmem := stalkMap_mem_maximalIdeal_of_mem Z x' (c := c)
      (x_mem_maximalIdeal_of_span_eq z hz.1.symm c)
    have hunit := Ideal.span_singleton_eq_top.mp (hT0.symm.trans hT')
    exact absurd hunit (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hmem))

/-- The strict transform of a component transversal to `Z` contains the whole fibre over `Z ∩ D` —
`x'` lies on it iff `x = π(x')` lies on `D`. -/
theorem mem_support_strictTransformAlong_iff_of_notMem (hcs : c ∉ s) :
    x' ∈ ((E i).strictTransformAlong (blowUpπ Z) (Z.comap (blowUpπ Z))).support ↔
      blowUpπ Z x' ∈ (E i).support := by
  have hreg : IsRegularLocalRing (X.presheaf.stalk (blowUpπ Z x')) :=
    isRegularLocalRing_stalk f _
  refine ⟨π_mem_support_of_mem_support_strictTransformAlong Z (E i) x', fun _ => ?_⟩
  refine (mem_support_iff_stalkIdeal_le_maximalIdeal _ x').mpr ?_
  refine (stalkIdeal_strictTransformAlong_of_notMem f E Z hZ i x' hx' hz hs hc hcs).le.trans ?_
  rw [Ideal.span_le, Set.singleton_subset_iff]
  exact stalkMap_mem_maximalIdeal_of_mem Z x' (c := c)
    (x_mem_maximalIdeal_of_span_eq z hz.1.symm c)

/-- [Hau14, Proposition 5.4 (7); Definition 6.2]: for `c ∈ s` — the component containing `Z` near
`x` — and a generator `e` of the exceptional ideal at `x'`, `π^* z_c = u e` and the strict transform
has stalk `(u)`: the total transform has the shape `(z'_a z'_j)` (then `u` is `z'_a` up to a unit)
or `(z'_j)` (then `u` is a unit and the strict transform misses `x'`). -/
theorem exists_stalkIdeal_strictTransformAlong_eq_span_of_mem (hcs : c ∈ s)
    {e : (blowUp Z).presheaf.stalk x'} (he : (Z.comap (blowUpπ Z)).stalkIdeal x' = span {e}) :
    ∃ u : (blowUp Z).presheaf.stalk x', (blowUpπ Z).stalkMap x' (z c) = u * e ∧
      ((E i).strictTransformAlong (blowUpπ Z) (Z.comap (blowUpπ Z))).stalkIdeal x' =
        span {u} := by
  classical
  have hreg : IsRegularLocalRing (X.presheaf.stalk (blowUpπ Z x')) :=
    isRegularLocalRing_stalk f _
  have hdata := exists_totalTransformData_of_mem_support f E Z hZ x' hx'
  obtain ⟨hshape, -⟩ := hdata
  have hT0 := stalkIdeal_comap_π_eq Z (E i) x' hc
  -- the total transform lies in the exceptional ideal
  have hle : ((E i).comap (blowUpπ Z)).stalkIdeal x' ≤ (Z.comap (blowUpπ Z)).stalkIdeal x' := by
    rw [stalkIdeal_comap, stalkIdeal_comap]
    exact Ideal.map_mono ((stalkIdeal_le_stalkIdeal_iff_mem hz hs hc).mpr hcs)
  obtain ⟨hreg', m', z'', hz'', j', a', hF', -, hshape''⟩ := hshape
  have hsat := stalkIdeal_strictTransformAlong_eq_iSup Z (E i) x'
  -- `e` and `z'_j` generate the same ideal
  obtain ⟨u, hu⟩ : Associated (z'' j') e :=
    Ideal.span_singleton_eq_span_singleton.mp (hF'.symm.trans he)
  rcases hshape'' i with ⟨hne, hT | hT⟩ | hT | hT
  · -- `(z'_a z'_j)`: `u = z'_a` up to a unit
    have hT' : ((E i).comap (blowUpπ Z)).stalkIdeal x' = span {z'' (a' i) * z'' j'} := hT
    obtain ⟨w, hw⟩ : Associated (z'' (a' i) * z'' j') ((blowUpπ Z).stalkMap x' (z c)) :=
      Ideal.span_singleton_eq_span_singleton.mp (hT'.symm.trans hT0)
    refine ⟨z'' (a' i) * ↑w * ↑u⁻¹, ?_, ?_⟩
    · have hzj : z'' j' = e * ↑u⁻¹ := (Units.eq_mul_inv_iff_mul_eq u).mpr hu
      rw [← hw, hzj]
      ring
    · rw [hsat, iSup_colon_congr hT' hF',
        iSup_colon_pow_span_singleton_mul hz''.1 hz''.2 hne,
        Ideal.span_singleton_mul_right_unit (Units.isUnit u⁻¹) (z'' (a' i) * ↑w),
        Ideal.span_singleton_mul_right_unit (Units.isUnit w) (z'' (a' i))]
  · -- `(z'_a)`: excluded by `T ⊆ F`
    have hT' : ((E i).comap (blowUpπ Z)).stalkIdeal x' = span {z'' (a' i)} := hT
    exfalso
    have hmem := (hT'.symm.le.trans (hle.trans hF'.le)) (mem_span_singleton_self _)
    exact notMem_span_singleton_of_ne hz''.1 hz''.2 hne.symm hmem
  · -- `(z'_j)`: `u` is a unit, the strict transform dies
    have hT' : ((E i).comap (blowUpπ Z)).stalkIdeal x' = span {z'' j'} := hT
    obtain ⟨w, hw⟩ : Associated ((blowUpπ Z).stalkMap x' (z c)) e :=
      Ideal.span_singleton_eq_span_singleton.mp (hT0.symm.trans (hT'.trans (hF'.symm.trans he)))
    refine ⟨↑w⁻¹, ?_, ?_⟩
    · rw [← hw, mul_comm _ (↑w : (blowUp Z).presheaf.stalk x'), Units.inv_mul_cancel_left]
    · rw [hsat, iSup_colon_congr hT' hF', iSup_colon_pow_span_singleton_self]
      exact (Ideal.span_singleton_eq_top.mpr (Units.isUnit _)).symm
  · -- `(1)`: excluded, `π^* z_c ∈ 𝔪_{x'}`
    have hT' : ((E i).comap (blowUpπ Z)).stalkIdeal x' = ⊤ := hT
    exfalso
    have hmem := stalkMap_mem_maximalIdeal_of_mem Z x' (c := c)
      (x_mem_maximalIdeal_of_span_eq z hz.1.symm c)
    have hunit := Ideal.span_singleton_eq_top.mp (hT0.symm.trans hT')
    exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hmem) hunit

end

section SmoothDivisor

variable [PerfectField k] (f : X ⟶ Spec (.of k)) [Smooth f] {ι : Type*} [Finite ι]
  (E : ι → X.IdealSheafData) (Z : X.IdealSheafData)
  (hE : ∀ x : X, ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk x),
    (span (Set.range z) = maximalIdeal (X.presheaf.stalk x) ∧
      (n : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk x)) ∧
    ∃ c : {i : ι // x ∈ (E i).support} → Fin n, Function.Injective c ∧
      ∀ i, (E i.1).stalkIdeal x = span {z (c i)})
  (hZ : ∀ x ∈ Z.support, ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk x),
    (span (Set.range z) = maximalIdeal (X.presheaf.stalk x) ∧
      (n : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk x)) ∧
    (∃ c : {i : ι // x ∈ (E i).support} → Fin n, Function.Injective c ∧
      ∀ i, (E i.1).stalkIdeal x = span {z (c i)}) ∧
    ∃ s : Finset (Fin n), Z.stalkIdeal x = span (z '' ↑s))

include f hE hZ

/-- Kollár's conditions (1)–(3) for `(π_*^{-1} E^i, F)` at every point of `B_Z X` (on `F` from the
chart shape, off `F` from the data of `X`). -/
theorem exists_snc_data_totalTransform (x' : blowUp Z) :
    ∃ (m : ℕ) (z : Fin m → (blowUp Z).presheaf.stalk x'),
      (span (Set.range z) = maximalIdeal ((blowUp Z).presheaf.stalk x') ∧
        (m : WithBot ℕ∞) = ringKrullDim ((blowUp Z).presheaf.stalk x')) ∧
      ∃ c' : {k : ι ⊕ PUnit.{u + 1} // x' ∈ (totalTransformFamily Z E k).support} → Fin m,
        Function.Injective c' ∧ ∀ k, (totalTransformFamily Z E k.1).stalkIdeal x' =
          span {z (c' k)} := by
  by_cases hx' : x' ∈ (Z.comap (blowUpπ Z)).support
  · exact (exists_snc_data_totalTransform_of_mem_support f E Z hZ x' hx').2
  · obtain ⟨n, z, ⟨hspan, hdim⟩, c, hcinj, hc⟩ := hE (blowUpπ Z x')
    have h := exists_snc_data_totalTransform_of_notMem_support Z E hx' hspan.symm hdim c hcinj hc
    exact ⟨n, fun i => (blowUpπ Z).stalkMap x' (z i), ⟨h.1.1.symm, h.1.2⟩, h.2⟩

/-- [Hau14, Proposition 5.3]: every member of the total transform — the strict transforms of the
components and the exceptional divisor — is a smooth divisor of `B_Z X` (`IsSmoothDivisor`):
regular, and generated at every point by a coordinate of a regular system of parameters. -/
theorem isSmoothDivisor_totalTransformFamily (k : ι ⊕ PUnit.{u + 1}) :
    IsSmoothDivisor (totalTransformFamily Z E k) := by
  have hX : ∀ x' : blowUp Z, IsRegularLocalRing ((blowUp Z).presheaf.stalk x') :=
    isRegularLocalRing_stalk_blowUp' f E Z hZ
  have hsnc := exists_snc_data_totalTransform f E Z hE hZ
  refine isSmoothDivisor_of_snc_data (totalTransformFamily Z E) (fun k' => ?_) hsnc hX k
  refine isRegular_subscheme_of_isRegularLocalRing_quotient _ fun w hw => ?_
  have := hX w
  obtain ⟨n, z, hz, c, -, hc⟩ := hsnc w
  have h := hc ⟨k', hw⟩
  refine isRegularLocalRing_quotient_stalkIdeal_of_eq_span hz (s := {c ⟨k', hw⟩}) ?_
  rw [h, Finset.coe_singleton, Set.image_singleton]

end SmoothDivisor

end AlgebraicGeometry
