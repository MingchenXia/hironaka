/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane T45A)
-/
import DeJongAlterations.StableModification.BlowDown.ClosedLocus

/-!
# Local models around the bad points (PLAN-T5 node A7)

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), proof of
Lemma 4.4.2 (T:3115–3118: "since `V` is closed in `C̄`, we can extend `f` trivially") and
Proposition 4.5.1 (T:3243–3266); `PLAN-T5.md` §2.2 step 7. Given finitely many bad points `Σ` of
the normalized refinement `N` (node A6) and local modifications `τᵢ : Bᵢ → Oᵢ` with finite loci
`Zᵢ`, we choose, for each closed point `x ∈ Σ`, an open `Uₓ ∋ x` inside some `Oⱼ₍ₓ₎` and the part
`Tₓ = {t ∈ Zⱼ₍ₓ₎ | t ⤳ x}` of the locus through `x`, such that the `Tₓ` are closed in `N`,
pairwise disjoint, cover `Σ`, and `Uₓ` meets no other `T_y`. These are the data of the extension
by the identity (node A8, `Gluing.Extension`).

Closedness of `Tₓ` in `N` (and not only in `Oⱼ₍ₓ₎`) is the point of ERRATA T11: over a valuation
ring with separably closed residue fields the closure of an algebraic point of a proper `V`-scheme
consists of generizations of its unique closed point
(`BlowDown.specializes_of_specializes_of_isAlgebraicAt`, lane T44A).

## Main results

* `isClosed_of_finite_of_specializes`: a finite set stable under specialization is closed.
* `eq_of_specializes_of_isAlgebraicAt`: an algebraic point specializes to at most one closed point.
* `exists_localModels`: the local data `(Uₓ, Tₓ)` (node A7).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Topology

universe u

namespace DeJongAlterations.StableModification.Gluing

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Topology

variable {X : Type*} [TopologicalSpace X]

/-- A finite set stable under specialization is closed. -/
theorem isClosed_of_finite_of_specializes {S : Set X} (hS : S.Finite)
    (h : ∀ s ∈ S, ∀ z, s ⤳ z → z ∈ S) : IsClosed S := by
  have hS' : S = ⋃ s ∈ S, closure {s} := by
    ext z
    constructor
    · intro hz
      exact Set.mem_biUnion hz (subset_closure rfl)
    · intro hz
      obtain ⟨s, hs, hz⟩ := Set.mem_iUnion₂.mp hz
      exact h s hs z (specializes_iff_mem_closure.mpr hz)
  rw [hS']
  exact hS.isClosed_biUnion fun _ _ ↦ isClosed_closure

end Topology

section LocalModels

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
  (hsep : ∀ p : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ p.asIdeal)))
  {N : Scheme.{u}} (pN : N ⟶ Spec (CommRingCat.of V)) [IsProper pN]

include hsep in
/-- Over a valuation ring with separably closed residue fields, an algebraic point specializes to
at most one closed point (`BlowDown.specializes_of_specializes_of_isAlgebraicAt`). -/
theorem eq_of_specializes_of_isAlgebraicAt {t x y : N} (htx : t ⤳ x) (hty : t ⤳ y)
    (hx : IsClosed ({x} : Set N)) (hy : IsClosed ({y} : Set N))
    (ht : ValCurves.IsAlgebraicAt pN t) : x = y := by
  have hyx : y ⤳ x := BlowDown.specializes_of_specializes_of_isAlgebraicAt hsep pN htx hx ht hty
  have h := specializes_iff_mem_closure.mp hyx
  rw [hy.closure_eq] at h
  exact h

variable {ι : Type*} (O : ι → N.Opens) (Z : ι → Set N) (Bad : Set N)

include hsep in
/-- **Local models around the bad points** (`PLAN-T5.md` §2.2 step 7, node A7; Temkin, proof of
Lemma 4.4.2, T:3115–3118, with ERRATA T11). Let `N` be proper over a valuation ring `V` all of whose
residue fields `Frac(V/𝔭)` are separably closed, covered by opens `Oᵢ`, and let `Zᵢ ⊆ Oᵢ` be finite
sets of algebraic points, closed in `Oᵢ` (the loci of local modifications `Bᵢ → Oᵢ`), and `Σ` a
finite closed set with `Σ ∩ Oᵢ ⊆ Zᵢ`. Index by the closed points `x ∈ Σ`, choose `Oⱼ₍ₓ₎ ∋ x` and
put `Tₓ = {t ∈ Zⱼ₍ₓ₎ | t ⤳ x}` and `Uₓ = Oⱼ₍ₓ₎ ∖ (Zⱼ₍ₓ₎ ∖ Tₓ) ∖ ⋃_{y ≠ x} T_y`. Then the `Tₓ`
are closed in `N` (closures of algebraic points are local), `Tₓ ⊆ Uₓ ⊆ Oⱼ₍ₓ₎`, `Uₓ` meets no
`T_y`, `y ≠ x`, the `Tₓ` cover `Σ`, and `Uₓ ∩ Zⱼ₍ₓ₎ ⊆ Tₓ`. -/
theorem exists_localModels (hO : ⨆ i, O i = ⊤)
    (hZc : ∀ i, IsClosed (((↑) : O i → N) ⁻¹' Z i)) (hZf : ∀ i, (Z i).Finite)
    (hZa : ∀ i, ∀ t ∈ Z i, ValCurves.IsAlgebraicAt pN t) (hBad : IsClosed Bad) (hBadf : Bad.Finite)
    (hBadZ : ∀ i, Bad ∩ O i ⊆ Z i) :
    ∃ (κ : Type u) (_ : Finite κ) (j : κ → ι) (U : κ → N.Opens) (T : κ → Set N),
      (∀ k, IsClosed (T k)) ∧ (∀ k, T k ⊆ U k) ∧ (∀ k, U k ≤ O (j k)) ∧
      (∀ k l, k ≠ l → Disjoint (U k : Set N) (T l)) ∧ Bad ⊆ ⋃ k, T k ∧
      (∀ k, (U k : Set N) ∩ Z (j k) ⊆ T k) ∧ (∀ k, T k ⊆ Z (j k)) ∧ (∀ k, (T k).Nonempty) := by
  classical
  have : CompactSpace N := QuasiCompact.compactSpace_of_compactSpace pN
  let κ := {x : N // x ∈ Bad ∧ IsClosed ({x} : Set N)}
  have hκ : Finite κ := (hBadf.subset fun x (hx : x ∈ Bad ∧ _) ↦ hx.1).to_subtype
  have hmemO : ∀ x : N, ∃ i, x ∈ O i := fun x ↦ by
    have hx : x ∈ (⊤ : N.Opens) := trivial
    rw [← hO] at hx
    exact TopologicalSpace.Opens.mem_iSup.mp hx
  choose j hj using fun k : κ ↦ hmemO k.1
  let T : κ → Set N := fun k ↦ {t | t ∈ Z (j k) ∧ t ⤳ k.1}
  have hTO : ∀ k, T k ⊆ O (j k) := fun k t ht ↦ ht.2.mem_open (O (j k)).isOpen (hj k)
  have hTf : ∀ k, (T k).Finite := fun k ↦ (hZf (j k)).subset fun t ht ↦ ht.1
  have hTspec : ∀ k, ∀ t ∈ T k, ∀ z, t ⤳ z → z ∈ T k := by
    intro k t ht z htz
    have hzx : z ⤳ k.1 := BlowDown.specializes_of_specializes_of_isAlgebraicAt hsep pN ht.2
      k.2.2 (hZa _ t ht.1) htz
    have hzO : z ∈ O (j k) := hzx.mem_open (O (j k)).isOpen (hj k)
    have hsp : (⟨t, hTO k ht⟩ : O (j k)) ⤳ ⟨z, hzO⟩ :=
      Topology.IsInducing.subtypeVal.specializes_iff.mp htz
    exact ⟨hsp.mem_closed (hZc (j k)) ht.1, hzx⟩
  have hTc : ∀ k, IsClosed (T k) := fun k ↦ isClosed_of_finite_of_specializes (hTf k) (hTspec k)
  have hTdisj : ∀ k l, k ≠ l → Disjoint (T k) (T l) := by
    intro k l hkl
    rw [Set.disjoint_left]
    intro t htk htl
    exact hkl (Subtype.ext (eq_of_specializes_of_isAlgebraicAt hsep pN htk.2 htl.2 k.2.2 l.2.2
      (hZa _ t htk.1)))
  -- `Oⱼ ∖ (Zⱼ ∖ T)` is open
  have hR : ∀ k, IsOpen ((O (j k) : Set N) \ (Z (j k) \ T k)) := by
    intro k
    have hc : IsClosed (((↑) : O (j k) → N) ⁻¹' (Z (j k) \ T k)) := by
      refine isClosed_of_finite_of_specializes
        (((hZf (j k)).sdiff).preimage Subtype.val_injective.injOn) ?_
      rintro ⟨s, hsO⟩ ⟨hsZ, hsT⟩ ⟨z, hzO⟩ hsz
      refine ⟨hsz.mem_closed (hZc (j k)) hsZ, fun hzT ↦ hsT ⟨hsZ, ?_⟩⟩
      exact (Topology.IsInducing.subtypeVal.specializes_iff.mpr hsz).trans hzT.2
    have he : (O (j k) : Set N) \ (Z (j k) \ T k) =
        Subtype.val '' ((((↑) : O (j k) → N) ⁻¹' (Z (j k) \ T k))ᶜ) := by
      ext z
      constructor
      · rintro ⟨hzO, hz⟩
        exact ⟨⟨z, hzO⟩, hz, rfl⟩
      · rintro ⟨⟨z, hzO⟩, hz, rfl⟩
        exact ⟨hzO, hz⟩
    rw [he]
    exact (O (j k)).isOpen.isOpenMap_subtype_val _ hc.isOpen_compl
  have hUo : ∀ k, IsOpen (((O (j k) : Set N) \ (Z (j k) \ T k)) \ ⋃ l ∈ {l | l ≠ k}, T l) :=
    fun k ↦ (hR k).sdiff ((Set.toFinite _).isClosed_biUnion fun l _ ↦ hTc l)
  let U : κ → N.Opens := fun k ↦ ⟨_, hUo k⟩
  have hU : ∀ k z, z ∈ U k ↔ (z ∈ O (j k) ∧ z ∉ Z (j k) \ T k) ∧ ∀ l, l ≠ k → z ∉ T l := by
    intro k z
    change z ∈ ((O (j k) : Set N) \ (Z (j k) \ T k)) \ ⋃ l ∈ {l | l ≠ k}, T l ↔ _
    simp only [Set.mem_sdiff, Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, SetLike.mem_coe]
  refine ⟨κ, hκ, j, U, T, hTc, fun k t ht ↦ ?_, fun k z hz ↦ ((hU k z).mp hz).1.1,
    fun k l hkl ↦ ?_, fun σ hσ ↦ ?_, fun k t ⟨htU, htZ⟩ ↦ ?_, fun k t ht ↦ ht.1, fun k ↦ ?_⟩
  · exact (hU k t).mpr ⟨⟨hTO k ht, fun h ↦ h.2 ht⟩, fun l hlk htl ↦
      Set.disjoint_left.mp (hTdisj k l hlk.symm) ht htl⟩
  · rw [Set.disjoint_left]
    intro t htU htT
    exact ((hU k t).mp htU).2 l hkl.symm htT
  · obtain ⟨x, hx, hxc⟩ := isClosed_closure.exists_closed_singleton
      (⟨σ, subset_closure rfl⟩ : (closure {σ}).Nonempty)
    have hxBad : x ∈ Bad := hBad.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hσ) hx
    let k : κ := ⟨x, hxBad, hxc⟩
    have hσx : σ ⤳ x := specializes_iff_mem_closure.mpr hx
    have hσO : σ ∈ O (j k) := hσx.mem_open (O (j k)).isOpen (hj k)
    exact Set.mem_iUnion.mpr ⟨k, hBadZ (j k) ⟨hσ, hσO⟩, hσx⟩
  · by_contra htT
    exact ((hU k t).mp htU).1.2 ⟨htZ, htT⟩
  · exact ⟨k.1, hBadZ (j k) ⟨k.2.1, hj k⟩, specializes_refl _⟩

end LocalModels

end DeJongAlterations.StableModification.Gluing
