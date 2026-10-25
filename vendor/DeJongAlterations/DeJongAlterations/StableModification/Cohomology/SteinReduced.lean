/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Cohomology.SteinFinite

/-!
# Reduced closed fibres of `Spec π_* 𝒪_B` over a valuation ring

Let `V` be a valuation ring with maximal ideal `𝔪` and `q : X → Spec V` flat, and `W₀ ⊆ X` a
quasi-compact open. If the closed fibre of every affine open `W ⊆ W₀` is reduced, i.e.
`𝔪 Γ(W, 𝒪_X)` is a radical ideal of `Γ(W, 𝒪_X)`, then `𝔪 Γ(W₀, 𝒪_X)` is a radical ideal
(`isRadical_map_maximalIdeal_sections`; for `W₀ = X`:
`isRadical_map_maximalIdeal_globalSections`): the closed fibre of `Spec Γ(W₀, 𝒪_X)` is reduced.
The hypothesis holds when the closed fibre `X_k` is a reduced scheme
(`isRadical_map_maximalIdeal_of_isReduced`, from `Γ(W_k, 𝒪) = Γ(W, 𝒪) / 𝔪`,
`mem_map_maximalIdeal_of_closedFibre_eq_zero`), which gives the form used for
`Spec π_* 𝒪_B` (`isRadical_map_maximalIdeal_preimage_of_isReduced`).

Applied to `X = π⁻¹U` for a projective `π : B → Y` with `B` flat over `V` with reduced fibres and
`U ⊆ Y` affine (`SteinProjective.lean`), this says that the finite `𝒪_Y`-algebra `π_* 𝒪_B` has
reduced closed fibre: the second half of `thm:sm-stein-finite-valuation` (plan
`PLAN-SM-GEOM.md`, S8, which replaces Temkin's use of the reduced fibre theorem, Temkin, *Stable
modification of relative curves*, J. Algebraic Geom. 19 (2010), Lemma 4.4.1, `semi-stable.tex`
lines 3089–3104).

## The argument (plan S8)

If `s^n ∈ 𝔪 Γ(X, 𝒪)`, then on each member `W_j` of a finite affine cover `s|_{W_j} ∈ 𝔪 Γ(W_j, 𝒪)`
by the hypothesis, so `s|_{W_j} = t_j b_j` with `t_j ∈ 𝔪` (in a valuation ring a finite sum
`∑ tᵢ yᵢ` is `t ∑ (tᵢ / t) yᵢ` for the `tᵢ` of least valuation, `exists_eq_mul_of_mem_map`).
The finitely many `t_j` have a common divisor `t` among them (`exists_dvd_of_finset`); writing
`t_j = t u_j`, the local functions `u_j b_j` agree on overlaps because `𝒪_X` has no `V`-torsion
(`eq_zero_of_mul_eq_zero_of_flat`), so they glue to `b` with `s = t b ∈ 𝔪 Γ(X, 𝒪)`.

Blueprint: `sm-cohomology-stein.tex`, `lem:sm-val-ideal-element`, `lem:sm-closed-fibre-kernel`,
`thm:sm-stein-reduced`.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry IsLocalRing TopologicalSpace

namespace DeJongAlterations.StableModification.Cohomology

noncomputable section

section Algebra

variable {V : Type*} [CommRing V] [IsDomain V] [ValuationRing V]

/-- **Common divisors in a valuation ring**: finitely many elements `t i` satisfying a property `P`
(also satisfied by `0`) have a common divisor which satisfies `P` (one of them, or `0` for the
empty family). -/
theorem exists_dvd_of_finset {ι : Type*} (s : Finset ι) (t : ι → V) (P : V → Prop)
    (hP : ∀ i ∈ s, P (t i)) (hP₀ : P 0) : ∃ t₀, P t₀ ∧ ∀ i ∈ s, t₀ ∣ t i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, hP₀, by simp⟩
  | insert j s hj ih =>
    obtain ⟨t₀, hPt₀, hdvd⟩ := ih fun i hi => hP i (Finset.mem_insert_of_mem hi)
    rcases ValuationRing.dvd_total t₀ (t j) with h | h
    · refine ⟨t₀, hPt₀, fun i hi => ?_⟩
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact h
      · exact hdvd i hi
    · refine ⟨t j, hP j (Finset.mem_insert_self j s), fun i hi => ?_⟩
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact dvd_rfl
      · exact h.trans (hdvd i hi)

variable {S : Type*} [CommRing S] (c : V →+* S)

/-- **Elements of an extended ideal over a valuation ring**: every element of the extension
`I S` of an ideal `I` of a valuation ring along `c : V → S` is a single product `c t * y` with
`t ∈ I`. -/
theorem exists_eq_mul_of_mem_map {I : Ideal V} {x : S} (hx : x ∈ I.map c) :
    ∃ t ∈ I, ∃ y, x = c t * y := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, ht, rfl⟩ := hx
    exact ⟨t, ht, 1, (mul_one _).symm⟩
  | zero => exact ⟨0, I.zero_mem, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨t₁, ht₁, y₁, rfl⟩ := hx
    obtain ⟨t₂, ht₂, y₂, rfl⟩ := hy
    rcases ValuationRing.dvd_total t₁ t₂ with ⟨w, rfl⟩ | ⟨w, rfl⟩
    · exact ⟨t₁, ht₁, y₁ + c w * y₂, by rw [map_mul]; ring⟩
    · exact ⟨t₂, ht₂, c w * y₁ + y₂, by rw [map_mul]; ring⟩
  | smul a x _ hx =>
    obtain ⟨t, ht, y, rfl⟩ := hx
    exact ⟨t, ht, a * y, by rw [smul_eq_mul]; ring⟩

end Algebra

section Scheme

set_option backward.isDefEq.respectTransparency false

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]

omit [IsDomain V] [ValuationRing V] in
private lemma map_map_apply {X : Scheme.{u}} {U W W' : X.Opens} (h₁ : W ≤ U) (h₂ : W' ≤ W)
    (x : Γ(X, U)) :
    X.presheaf.map (homOfLE h₂).op (X.presheaf.map (homOfLE h₁).op x) =
      X.presheaf.map (homOfLE (h₂.trans h₁)).op x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- **Reduced closed fibre of the ring of functions on a quasi-compact open** (blueprint
`thm:sm-stein-reduced`): let `q : X → Spec V` be flat over a valuation ring `V` and `W₀ ⊆ X` a
quasi-compact open. If `𝔪 Γ(W, 𝒪_X)` is a radical ideal for every affine open `W ⊆ W₀` (the
closed fibre of `W₀` is reduced), then `𝔪 Γ(W₀, 𝒪_X)` is a radical ideal:
`Γ(W₀, 𝒪_X) ⊗_V k` is reduced. -/
theorem isRadical_map_maximalIdeal_sections {X : Scheme.{u}}
    (q : X ⟶ Spec (CommRingCat.of V)) [Flat q] {W₀ : X.Opens} (hW₀ : IsCompact (W₀ : Set X))
    (hred : ∀ W : X.Opens, IsAffineOpen W → W ≤ W₀ →
      (Ideal.map (sectionsRingHom (structureCoeff q) (le_top : W ≤ ⊤))
        (maximalIdeal V)).IsRadical) :
    (Ideal.map (sectionsRingHom (structureCoeff q) (le_top : W₀ ≤ ⊤))
      (maximalIdeal V)).IsRadical := by
  intro s hs
  obtain ⟨n, hn⟩ := hs
  set c := structureCoeff q
  have hres : ∀ (W : X.Opens) (hW : W ≤ W₀),
      (X.presheaf.map (homOfLE hW).op).hom.comp (sectionsRingHom c (le_top : W₀ ≤ ⊤)) =
        sectionsRingHom c (le_top : W ≤ ⊤) := by
    intro W hW
    ext a
    exact map_map_apply (le_top : W₀ ≤ ⊤) hW (c a)
  let ι := {W : X.affineOpens // (W : X.Opens) ≤ W₀}
  obtain ⟨F, hF⟩ := hW₀.elim_finite_subcover
    (fun W : ι => ((W.1 : X.Opens) : Set X)) (fun W => W.1.1.isOpen) (fun x hx => by
      obtain ⟨W, hW, hxW, hWle⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp
        X.isBasis_affineOpens) hx
      exact Set.mem_iUnion.mpr ⟨⟨⟨W, hW⟩, hWle⟩, hxW⟩)
  have hloc : ∀ W : ι, X.presheaf.map (homOfLE W.2).op s ∈
      Ideal.map (sectionsRingHom c (le_top : (W.1 : X.Opens) ≤ ⊤)) (maximalIdeal V) := by
    intro W
    refine hred W.1 W.1.2 W.2 ⟨n, ?_⟩
    rw [← map_pow, ← hres W.1 W.2, ← Ideal.map_map]
    exact Ideal.mem_map_of_mem _ hn
  choose t ht y hy using fun W : ι => exists_eq_mul_of_mem_map _ (hloc W)
  obtain ⟨t₀, ht₀, hdvd⟩ := exists_dvd_of_finset F t (· ∈ maximalIdeal V) (fun W _ => ht W)
    (maximalIdeal V).zero_mem
  choose! w hw using hdvd
  let U : F → X.Opens := fun W => W.1.1.1
  have hcover : W₀ ≤ iSup U := by
    intro x hx
    obtain ⟨W, hW, hxW⟩ := Set.mem_iUnion₂.mp (hF hx)
    exact Opens.mem_iSup.mpr ⟨⟨W, hW⟩, hxW⟩
  let z : ∀ W : F, Γ(X, U W) := fun W =>
    sectionsRingHom c (le_top : U W ≤ ⊤) (w W.1) * y W.1
  have hsz : ∀ W : F, X.presheaf.map (homOfLE W.1.2).op s =
      X.presheaf.map (homOfLE (le_top : U W ≤ ⊤)).op (c t₀) * z W := by
    intro W
    rw [hy W.1, hw W.1 W.2, map_mul]
    simp only [z, sectionsRingHom, RingHom.comp_apply]
    ring
  by_cases h0 : t₀ = 0
  · have : s = 0 := by
      refine X.sheaf.eq_of_locally_eq' U W₀ (fun W => homOfLE W.1.2) hcover s 0 fun W => ?_
      change X.presheaf.map (homOfLE W.1.2).op s = X.presheaf.map (homOfLE W.1.2).op 0
      simp only [hsz W, h0, map_zero, zero_mul]
    rw [this]
    exact Ideal.zero_mem _
  · have ha : (Scheme.ΓSpecIso (CommRingCat.of V)).inv t₀ ≠ 0 := fun h => h0 (by
      have := congrArg (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom h
      rw [map_zero] at this
      rw [← this, ← CommRingCat.comp_apply, Iso.inv_hom_id]
      rfl)
    have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 U z := by
      intro W W'
      apply eq_of_sub_eq_zero
      apply eq_zero_of_mul_eq_zero_of_flat q ha
      change X.presheaf.map (homOfLE le_top).op (c t₀) * _ = 0
      rw [mul_sub]
      apply sub_eq_zero.mpr
      have e₁ : ∀ (A : X.Opens) (hA : U W ⊓ U W' ≤ A) (hA' : A ≤ W₀) (zA : Γ(X, A))
          (hzA : X.presheaf.map (homOfLE hA').op s =
            X.presheaf.map (homOfLE (le_top : A ≤ ⊤)).op (c t₀) * zA),
          X.presheaf.map (homOfLE le_top).op (c t₀) * X.presheaf.map (homOfLE hA).op zA =
            X.presheaf.map (homOfLE (hA.trans hA')).op s := by
        intro A hA hA' zA hzA
        rw [← map_map_apply hA' hA s, hzA, map_mul, map_map_apply]
      exact (e₁ _ inf_le_left W.1.2 _ (hsz W)).trans (e₁ _ inf_le_right W'.1.2 _ (hsz W')).symm
    obtain ⟨g', hg, -⟩ := X.sheaf.existsUnique_gluing' U W₀ (fun W => homOfLE W.1.2) hcover z
      hcompat
    let g : Γ(X, W₀) := g'
    have : s = sectionsRingHom c (le_top : W₀ ≤ ⊤) t₀ * g := by
      refine X.sheaf.eq_of_locally_eq' U W₀ (fun W => homOfLE W.1.2) hcover _ _ fun W => ?_
      change X.presheaf.map (homOfLE W.1.2).op s =
        X.presheaf.map (homOfLE W.1.2).op (sectionsRingHom c (le_top : W₀ ≤ ⊤) t₀ * g)
      rw [map_mul, hsz W]
      congr 1
      · exact (map_map_apply (le_top : W₀ ≤ ⊤) W.1.2 (c t₀)).symm
      · exact (hg W).symm
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ht₀)

/-- **Reduced closed fibre of the ring of global functions**: the case `W₀ = X` of
`isRadical_map_maximalIdeal_sections`, for `X` quasi-compact. -/
theorem isRadical_map_maximalIdeal_globalSections {X : Scheme.{u}}
    (q : X ⟶ Spec (CommRingCat.of V)) [Flat q] [CompactSpace X]
    (hred : ∀ W : X.Opens, IsAffineOpen W →
      (Ideal.map (sectionsRingHom (structureCoeff q) (le_top : W ≤ ⊤))
        (maximalIdeal V)).IsRadical) :
    (Ideal.map (sectionsRingHom (structureCoeff q) (le_top : (⊤ : X.Opens) ≤ ⊤))
      (maximalIdeal V)).IsRadical :=
  isRadical_map_maximalIdeal_sections q isCompact_univ fun W hW _ => hred W hW

/-- **Reduced closed fibre of `π_* 𝒪_B`** (blueprint `thm:sm-stein-reduced`, S8): for a
quasi-compact `π : B → Y` over `pY : Y → Spec V` with `B` flat over the valuation ring `V`, and
an affine (more generally quasi-compact) open `U ⊆ Y` such that the affine opens of `B` inside
`π⁻¹U` have reduced closed fibres, the ideal `𝔪 Γ(π⁻¹U, 𝒪_B)` is radical: the closed fibre of
`Spec Γ(π⁻¹U, 𝒪_B)` (the restriction of `Spec π_* 𝒪_B`, `SteinFinite.lean`) is reduced. -/
theorem isRadical_map_maximalIdeal_preimage {B Y : Scheme.{u}} (π : B ⟶ Y)
    (pY : Y ⟶ Spec (CommRingCat.of V)) [Flat (π ≫ pY)] [QuasiCompact π] {U : Y.Opens}
    (hU : IsCompact (U : Set Y))
    (hred : ∀ W : B.Opens, IsAffineOpen W → W ≤ π ⁻¹ᵁ U →
      (Ideal.map (sectionsRingHom (structureCoeff (π ≫ pY)) (le_top : W ≤ ⊤))
        (maximalIdeal V)).IsRadical) :
    (Ideal.map (sectionsRingHom (structureCoeff (π ≫ pY)) (le_top : π ⁻¹ᵁ U ≤ ⊤))
      (maximalIdeal V)).IsRadical :=
  isRadical_map_maximalIdeal_sections (π ≫ pY) (π.isCompact_preimage hU) hred

end Scheme

section ClosedFibre

set_option backward.isDefEq.respectTransparency false

variable {V : Type u} [CommRing V] [IsLocalRing V] {X : Scheme.{u}}
  (p : X ⟶ Spec (CommRingCat.of V))

/-- **Kernel of the restriction to the closed fibre**: for an affine open `W ⊆ X` over a local
ring `V`, a function on `W` which vanishes on the closed fibre `W_k = W ×_V k` lies in
`𝔪 Γ(W, 𝒪_X)` (because `Γ(W_k, 𝒪) = Γ(W, 𝒪) ⊗_V k = Γ(W, 𝒪) / 𝔪`, lane COH2's
`isPushout_baseChange_sections`). -/
theorem mem_map_maximalIdeal_of_closedFibre_eq_zero {W : X.Opens} (hW : IsAffineOpen W)
    (s : Γ(X, W))
    (hs : (bcFst (residue V) p).appLE W (bcFst (residue V) p ⁻¹ᵁ W) le_rfl s = 0) :
    s ∈ Ideal.map (sectionsRingHom (structureCoeff p) (le_top : W ≤ ⊤)) (maximalIdeal V) := by
  have H := isPushout_baseChange_sections (residue V) p hW
  let A := Γ(X, W)
  let S' := Γ(pullback p (Spec.map (CommRingCat.ofHom (residue V))), bcFst (residue V) p ⁻¹ᵁ W)
  let fA : CommRingCat.of V ⟶ Γ(X, W) :=
    (Scheme.ΓSpecIso (CommRingCat.of V)).inv ≫ p.appLE ⊤ W le_top
  let fk : CommRingCat.of (ResidueField V) ⟶ S' :=
    (Scheme.ΓSpecIso (CommRingCat.of (ResidueField V))).inv ≫
      (bcSnd (residue V) p).appLE ⊤ (bcFst (residue V) p ⁻¹ᵁ W) le_top
  let g : Γ(X, W) ⟶ S' := (bcFst (residue V) p).appLE W (bcFst (residue V) p ⁻¹ᵁ W) le_rfl
  let : Algebra V A := fA.hom.toAlgebra
  let : Algebra (ResidueField V) S' := fk.hom.toAlgebra
  let : Algebra A S' := g.hom.toAlgebra
  let : Algebra V S' := (g.hom.comp fA.hom).toAlgebra
  have : IsScalarTower V A S' := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower V (ResidueField V) S' := IsScalarTower.of_algebraMap_eq' (by
    have := congrArg CommRingCat.Hom.hom H.w
    simp only [CommRingCat.hom_comp] at this
    exact this.symm)
  have hpush : Algebra.IsPushout V (ResidueField V) A S' :=
    CommRingCat.isPushout_iff_isPushout.mp H
  have hfA : fA.hom = sectionsRingHom (structureCoeff p) (le_top : W ≤ ⊤) := by
    ext a
    simp [fA, sectionsRingHom, structureCoeff, Scheme.Hom.appLE]
  rw [← hfA]
  change s ∈ Ideal.map (algebraMap V A) (maximalIdeal V)
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  apply (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A (maximalIdeal V)).injective
  rw [map_zero, Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk]
  apply hpush.symm.out.equiv.injective
  rw [map_zero, IsBaseChange.equiv_tmul]
  simp only [AlgHom.toLinearMap_apply, map_one]
  rw [Algebra.smul_def, mul_one]
  exact hs

/-- **Reduced closed fibre, affine form**: if the closed fibre `X_k = X ×_V k` is reduced, then
`𝔪 Γ(W, 𝒪_X)` is a radical ideal for every affine open `W ⊆ X`. -/
theorem isRadical_map_maximalIdeal_of_isReduced {W : X.Opens} (hW : IsAffineOpen W)
    [IsReduced (pullback p (Spec.map (CommRingCat.ofHom (residue V))))] :
    (Ideal.map (sectionsRingHom (structureCoeff p) (le_top : W ≤ ⊤))
      (maximalIdeal V)).IsRadical := by
  intro s ⟨n, hn⟩
  apply mem_map_maximalIdeal_of_closedFibre_eq_zero p hW
  have H := isPushout_baseChange_sections (residue V) p hW
  let g := (bcFst (residue V) p).appLE W (bcFst (residue V) p ⁻¹ᵁ W) le_rfl
  have hker : Ideal.map (sectionsRingHom (structureCoeff p) (le_top : W ≤ ⊤)) (maximalIdeal V) ≤
      RingHom.ker g.hom := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have hw := congrArg (fun f => f.hom a) H.w
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hw
    have hres : residue V a = 0 := (residue_eq_zero_iff a).mpr ha
    have hfA : sectionsRingHom (structureCoeff p) (le_top : W ≤ ⊤) a =
        (p.appLE ⊤ W le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a) := by
      simp [sectionsRingHom, structureCoeff, Scheme.Hom.appLE]
    rw [hfA]
    change g.hom _ = 0
    rw [← hw, hres, map_zero, map_zero]
  have hnil : IsNilpotent (g.hom s) := ⟨n, by rw [← map_pow]; exact hker hn⟩
  exact hnil.eq_zero

end ClosedFibre

section Stein

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]

/-- **Reduced closed fibre of `π_* 𝒪_B`** (blueprint `thm:sm-stein-reduced`, S8): for a
quasi-compact `π : B → Y` over `pY : Y → Spec V` with `B` flat over the valuation ring `V` with
reduced closed fibre `B_k`, and a quasi-compact (e.g. affine) open `U ⊆ Y`, the ideal
`𝔪 Γ(π⁻¹U, 𝒪_B)` is radical: `Γ(π⁻¹U, 𝒪_B) ⊗_V k` is reduced, i.e. the finite `𝒪_Y`-algebra
`π_* 𝒪_B` (`isFinite_fromNormalization_of_isRelativelyProjective`) has reduced closed
fibre. -/
theorem isRadical_map_maximalIdeal_preimage_of_isReduced {B Y : Scheme.{u}} (π : B ⟶ Y)
    (pY : Y ⟶ Spec (CommRingCat.of V)) [Flat (π ≫ pY)] [QuasiCompact π]
    [IsReduced (pullback (π ≫ pY) (Spec.map (CommRingCat.ofHom (residue V))))] {U : Y.Opens}
    (hU : IsCompact (U : Set Y)) :
    (Ideal.map (sectionsRingHom (structureCoeff (π ≫ pY)) (le_top : π ⁻¹ᵁ U ≤ ⊤))
      (maximalIdeal V)).IsRadical :=
  isRadical_map_maximalIdeal_preimage π pY hU fun _ hW _ =>
    isRadical_map_maximalIdeal_of_isReduced (π ≫ pY) hW

end Stein

end

end DeJongAlterations.StableModification.Cohomology
