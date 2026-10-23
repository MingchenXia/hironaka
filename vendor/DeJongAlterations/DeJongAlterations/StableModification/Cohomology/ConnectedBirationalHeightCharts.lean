/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Cohomology.ConnectedBirational

/-!
# Zariski connectedness over the generizations of a point of the modification locus

Let `V` be a valuation ring with finitely many primes, `pY : Y → Spec V` of finite presentation,
quasi-compact and separated, with `Y` integral, normal and of relative dimension one, and
`π : B → Y` birational and projective relative to `pY` with `B` integral and flat over `V`. For a
point `z` of the modification locus `Σ = center π` with infinite residue field, **the preimage
under `π` of the set `Σ_z` of generizations of `z` in `Σ` is preconnected**
(`isPreconnected_preimage_generizations`, blueprint `thm:sm-connbirh-generizations`, chapter
`sm-cohomology-connected-birational-height.tex`).

This is lane COH3D's two-chart Zariski connectedness
(`ConnectedBirational.isPreconnected_preimage_zeroLocus_of_twoCharts_birational`), applied on a
neighbourhood of `z` in which `Σ_z` is cut out by finitely many functions. Unlike lane COH3D's
`isConnected_preimage_singleton_of_isIso`, the point `z` need not be closed in `Y` (it is closed in
the open complement `U₀` of the closure of `Σ ∖ Σ_z`) and the vanishing locus contains all of
`Σ_z`, not just `z` (M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19
(2010), `references/temkin10-stable-modification/source/semi-stable.tex`, proof of Lemma 4.4.2,
T:3133; blueprint remark `rem:sm-connbir-generizations`).

## Main results

* `isClosed_singleton_of_forall_specializes`, `infinite_quotient_of_isClosed`,
  `isClosed_singleton_toSpecΓ_of_isClosed`: closedness of a point inside an open.
* `exists_twoCharts_of_forall_specializes`: two affine charts over a neighbourhood of a point
  which is closed in an open (lane COH3D's `exists_twoCharts` for points closed in `Y`).
* `eq_or_eq_of_specializes_of_fiberTrdeg_le_one'`: the fibre of a modification of a relative curve
  over any point contains no chain of three distinct points.
* `exists_finset_zeroLocus_eq`: a closed subset of an affine open is cut out by finitely many
  functions over a valuation ring of finite height.
* `isPreconnected_preimage_generizations` (blueprint `thm:sm-connbirh-generizations`).
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Limits

namespace DeJongAlterations.StableModification.Cohomology.ConnectedBirationalHeight

open ConnectedBirational Geometry.ModificationCenter

noncomputable section

set_option backward.isDefEq.respectTransparency false

section Shrink

attribute [local instance] MvPolynomial.gradedAlgebra

variable {V : Type u} [CommRing V]
variable {B Y : Scheme.{u}} (π : B ⟶ Y) (pY : Y ⟶ Spec (CommRingCat.of V))

omit [CommRing V] in
/-- A point `x` without proper specialization in an open `U'` is closed in every open `U ≤ U'`
containing it. -/
theorem isClosed_singleton_of_forall_specializes {U' U : Y.Opens} (hUU' : U ≤ U') {x : Y}
    (hxU : x ∈ U) (hx : ∀ w ∈ U', x ⤳ w → w = x) :
    IsClosed ({(⟨x, hxU⟩ : U)} : Set U) := by
  refine closure_subset_iff_isClosed.mp fun w hw => ?_
  have h : (⟨x, hxU⟩ : U) ⤳ w := specializes_iff_mem_closure.mpr hw
  have h' : x ⤳ w.1 := h.map continuous_subtype_val
  exact Subtype.ext (hx w.1 (hUU' w.2) h')

omit [CommRing V] in
/-- The image in `Spec Γ(Y, U)` of a point closed in the affine open `U` is closed. -/
theorem isClosed_singleton_toSpecΓ_of_isClosed {U : Y.Opens} (hU : IsAffineOpen U) {x : Y}
    (hxU : x ∈ U) (hclU : IsClosed ({(⟨x, hxU⟩ : U)} : Set U)) :
    IsClosed ({U.toSpecΓ ⟨x, hxU⟩} : Set (PrimeSpectrum Γ(Y, U))) := by
  have h := hU.isoSpec.hom.homeomorph.isClosedMap _ hclU
  rwa [Set.image_singleton] at h

omit [CommRing V] in
/-- If `x` is closed in the affine open `U`, its residue field is `Γ(U) ⧸ 𝔭ₓ`; in particular this
quotient is infinite if the residue field is. -/
theorem infinite_quotient_of_isClosed {U : Y.Opens} (hU : IsAffineOpen U) {x : Y} (hxU : x ∈ U)
    (hclU : IsClosed ({(⟨x, hxU⟩ : U)} : Set U)) [Infinite (Y.residueField x)] :
    Infinite (Γ(Y, U) ⧸ (U.toSpecΓ ⟨x, hxU⟩).asIdeal) := by
  set P := U.toSpecΓ ⟨x, hxU⟩
  have hclP : IsClosed ({P} : Set (PrimeSpectrum Γ(Y, U))) :=
    isClosed_singleton_toSpecΓ_of_isClosed hU hxU hclU
  have hmax : P.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal P).mp hclP
  have e₁ : Function.Bijective (U.ι.residueFieldMap ⟨x, hxU⟩) :=
    ConcreteCategory.bijective_of_isIso _
  have e₂ : Function.Bijective (hU.isoSpec.hom.residueFieldMap ⟨x, hxU⟩) :=
    ConcreteCategory.bijective_of_isIso _
  have e₃ : Function.Bijective (Scheme.Spec.residueFieldIso (CommRingCat.of Γ(Y, U)) P).hom :=
    ConcreteCategory.bijective_of_isIso _
  have e₄ := P.asIdeal.bijective_algebraMap_quotient_residueField
  have : Infinite (Y.residueField (U.ι ⟨x, hxU⟩)) := ‹Infinite (Y.residueField x)›
  have : Infinite (U.toScheme.residueField ⟨x, hxU⟩) := Infinite.of_injective _ e₁.1
  have : Infinite ((Spec (CommRingCat.of Γ(Y, U))).residueField P) :=
    Infinite.of_surjective _ e₂.2
  have : Infinite P.asIdeal.ResidueField := Infinite.of_injective _ e₃.1
  exact Infinite.of_surjective _ e₄.2

/-- **Two affine charts over a neighbourhood of a point closed in an open** (blueprint
`lem:sm-connbirh-charts`). Let `π : B → Y` be projective relative to `pY`, `U' ⊆ Y` open and
`x ∈ U'` a point with infinite residue field and no proper specialization in `U'`, such that the
fibre `π⁻¹(x)` contains no chain `b ⤳ b' ⤳ b''` of three distinct points. Then `U'` contains an
affine open `U ∋ x` such that `π⁻¹U` is the union of two affine opens. -/
theorem exists_twoCharts_of_forall_specializes (hπ : DeJong.IsRelativelyProjective pY π) (x : Y)
    [Infinite (Y.residueField x)] (U' : Y.Opens) (hxU' : x ∈ U')
    (hx : ∀ w ∈ U', x ⤳ w → w = x)
    (hdim : ∀ b b' b'' : B, π b = x → π b' = x → π b'' = x → b ⤳ b' → b' ⤳ b'' →
      b = b' ∨ b' = b'') :
    ∃ U : Y.Opens, IsAffineOpen U ∧ x ∈ U ∧ U ≤ U' ∧
      ∃ W₁ W₂ : B.Opens, IsAffineOpen W₁ ∧ IsAffineOpen W₂ ∧ W₁ ⊔ W₂ = π ⁻¹ᵁ U := by
  classical
  obtain ⟨U₀, hU₀, hxU₀, hU₀U'⟩ := exists_isAffineOpen_mem_and_subset hxU'
  obtain ⟨n, i, hi, hcomp⟩ := id hπ
  have hproj := Cohomology.isProjectiveOver_morphismRestrict_toSpecΓ π pY i hcomp hU₀
  have : IsProper (π ∣_ U₀ ≫ U₀.toSpecΓ) := hproj.isProper
  obtain ⟨m, j, hj, hjcomp⟩ := hproj
  set P := U₀.toSpecΓ ⟨x, hxU₀⟩ with hPdef
  have hclU₀ := isClosed_singleton_of_forall_specializes hU₀U' hxU₀ hx
  have hinf := infinite_quotient_of_isClosed hU₀ hxU₀ hclU₀
  have hclP := isClosed_singleton_toSpecΓ_of_isClosed hU₀ hxU₀ hclU₀
  have hinj : Function.Injective U₀.toSpecΓ := hU₀.isoSpec.hom.homeomorph.injective
  have hpt : ∀ a : (π ⁻¹ᵁ U₀).toScheme,
      (π ∣_ U₀ ≫ U₀.toSpecΓ) a = U₀.toSpecΓ ⟨π a.1, a.2⟩ := by
    intro a
    rw [Scheme.Hom.comp_apply]
    congr 1
    exact Subtype.ext (morphismRestrict_base_coe π U₀ a)
  have hfib : ∀ a : (π ⁻¹ᵁ U₀).toScheme, (π ∣_ U₀ ≫ U₀.toSpecΓ) a = P → π a.1 = x := by
    intro a ha
    rw [hpt] at ha
    exact congrArg Subtype.val (hinj ha)
  have hdim' : ∀ a b c : (π ⁻¹ᵁ U₀).toScheme,
      (j ≫ projectiveSpaceStructure Γ(Y, U₀) m) a = P → a ⤳ b → b ⤳ c → a = b ∨ b = c := by
    intro a b c ha hab hbc
    rw [hjcomp] at ha
    have hax := hfib a ha
    have hab' : a.1 ⤳ b.1 := hab.map (π ⁻¹ᵁ U₀).ι.continuous
    have hbc' : b.1 ⤳ c.1 := hbc.map (π ⁻¹ᵁ U₀).ι.continuous
    have hbx : π b.1 = x := hx _ (hU₀U' b.2) (hax ▸ hab'.map π.continuous)
    have hcx : π c.1 = x := hx _ (hU₀U' c.2) (hbx ▸ hbc'.map π.continuous)
    rcases hdim a.1 b.1 c.1 hax hbx hcx hab' hbc' with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  obtain ⟨f, hf, g, hg, hcovP⟩ := exists_linearForms_fibre j P hclP hdim'
  let O : (π ⁻¹ᵁ U₀).toScheme.Opens :=
    j ⁻¹ᵁ Proj.basicOpen (projectiveSpaceGrading Γ(Y, U₀) m) f ⊔
      j ⁻¹ᵁ Proj.basicOpen (projectiveSpaceGrading Γ(Y, U₀) m) g
  have hWc : IsClosed ((π ∣_ U₀ ≫ U₀.toSpecΓ) '' (O : Set (π ⁻¹ᵁ U₀).toScheme)ᶜ) :=
    (π ∣_ U₀ ≫ U₀.toSpecΓ).isClosedMap _ O.isOpen.isClosed_compl
  have hPWc : P ∉ (π ∣_ U₀ ≫ U₀.toSpecΓ) '' (O : Set (π ⁻¹ᵁ U₀).toScheme)ᶜ := by
    rintro ⟨a, ha, haP⟩
    apply ha
    have := hcovP a (by rw [hjcomp]; exact haP)
    exact this
  obtain ⟨_, ⟨h, rfl⟩, hPh, hhsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hPWc
      hWc.isOpen_compl
  refine ⟨Y.basicOpen h, hU₀.basicOpen h, ?_, (Y.basicOpen_le h).trans hU₀U', ?_⟩
  · rw [mem_basicOpen_iff_notMem_toSpecΓ h hxU₀]
    exact hPh
  let ι₀ := (π ⁻¹ᵁ U₀).ι
  have hres : ∀ A : B.Opens, A ≤ π ⁻¹ᵁ U₀ → IsAffineOpen A →
      IsAffineOpen (A ⊓ π ⁻¹ᵁ Y.basicOpen h) := by
    intro A hA hAff
    have e : A ⊓ π ⁻¹ᵁ Y.basicOpen h =
        B.basicOpen (B.presheaf.map (homOfLE hA).op (π.app U₀ h)) := by
      rw [Scheme.basicOpen_res, Scheme.preimage_basicOpen]
    rw [e]
    exact hAff.basicOpen _
  have hAf := (isAffineOpen_preimage_basicOpen j f hf one_pos).image_of_isOpenImmersion ι₀
  have hAg := (isAffineOpen_preimage_basicOpen j g hg one_pos).image_of_isOpenImmersion ι₀
  refine ⟨_, _, hres _ (Scheme.Opens.ι_image_le _ _) hAf, hres _ (Scheme.Opens.ι_image_le _ _) hAg,
    le_antisymm (sup_le inf_le_right inf_le_right) ?_⟩
  intro b hb
  have hbU₀ : b ∈ π ⁻¹ᵁ U₀ := Y.basicOpen_le h hb
  let b' : (π ⁻¹ᵁ U₀).toScheme := ⟨b, hbU₀⟩
  have hfb : (π ∣_ U₀ ≫ U₀.toSpecΓ) b' ∈ PrimeSpectrum.basicOpen h := by
    rw [hpt, PrimeSpectrum.mem_basicOpen, ← mem_basicOpen_iff_notMem_toSpecΓ]
    exact hb
  have hbO : b' ∈ O := by
    by_contra hc
    exact hhsub hfb ⟨b', hc, rfl⟩
  rcases Opens.mem_sup.mp hbO with h1 | h1
  · exact Opens.mem_sup.mpr (Or.inl ⟨⟨b', h1, rfl⟩, hb⟩)
  · exact Opens.mem_sup.mpr (Or.inr ⟨⟨b', h1, rfl⟩, hb⟩)

/-- **Fibres of a modification of a relative curve** (over an arbitrary point): if the generic point
of `Y` has transcendence degree at most one over `Spec V` and `π` is a modification, the fibre of
`π` over any point contains no chain `b ⤳ b' ⤳ b''` of three distinct points. -/
theorem eq_or_eq_of_specializes_of_fiberTrdeg_le_one' [IsIntegral B] [IsIntegral Y]
    [IsModification π]
    (hcurve : ValuationRing.fiberTrdeg pY (genericPoint Y) ≤ 1) [IsDomain V] [ValuationRing V]
    {x : Y} (b b' b'' : B) (hb : π b = x) (hb' : π b' = x) (hb'' : π b'' = x) (h₁ : b ⤳ b')
    (h₂ : b' ⤳ b'') : b = b' ∨ b' = b'' := by
  by_contra hne
  push Not at hne
  have e₁ := ValCurves.one_add_fiberTrdeg_le_of_specializes (π ≫ pY) h₁ hne.1
    (by rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hb, hb'])
  have e₂ := ValCurves.one_add_fiberTrdeg_le_of_specializes (π ≫ pY) h₂ hne.2
    (by rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hb', hb''])
  have e₀ := ValCurves.fiberTrdeg_le_one pY hcurve π b
  have h0 : ValuationRing.fiberTrdeg (π ≫ pY) b' = 0 :=
    ValCurves.Cardinal.eq_zero_of_one_add_le_one (e₁.trans e₀)
  rw [h0] at e₂
  have : (1 : Cardinal) ≤ 0 := le_self_add.trans e₂
  exact absurd this (by simp)

/-- **Closed subsets are cut out by finitely many functions** over a valuation ring of finite
height: if `Y` is locally of finite type over `V` with `Spec V` finite, `K ⊆ Y` is closed and
`U₀ ⊆ Y` is an affine open, there are finitely many functions on `U₀` whose common zero locus in
`U₀` is `K ∩ U₀`. -/
theorem exists_finset_zeroLocus_eq [LocallyOfFiniteType pY] [Finite (PrimeSpectrum V)]
    {K : Set Y} (hK : IsClosed K) {U₀ : Y.Opens} (hU₀ : IsAffineOpen U₀) :
    ∃ s₀ : Finset Γ(Y, U₀), ∀ y ∈ U₀, (∀ q ∈ s₀, y ∉ Y.basicOpen q) ↔ y ∈ K := by
  classical
  have : IsAffine U₀.toScheme := hU₀
  have := noetherianSpace_of_finite (U₀.ι ≫ pY)
  have hc : IsCompact (U₀.ι '' {w : U₀ | w.1 ∉ K}) :=
    (NoetherianSpace.isCompact _).image U₀.ι.continuous
  let T := {q : Γ(Y, U₀) // (Y.basicOpen q : Set Y) ⊆ Kᶜ}
  have hcover : U₀.ι '' {w : U₀ | w.1 ∉ K} ⊆ ⋃ q : T, (Y.basicOpen q.1 : Set Y) := by
    rintro _ ⟨⟨y, hy⟩, hyK, rfl⟩
    let O : Y.Opens := ⟨Kᶜ, hK.isOpen_compl⟩
    obtain ⟨q, hqO, hyq⟩ := hU₀.exists_basicOpen_le (V := O) ⟨y, hyK⟩ hy
    exact Set.mem_iUnion.mpr ⟨⟨q, hqO⟩, hyq⟩
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover (fun q : T => (Y.basicOpen q.1 : Set Y))
    (fun q => (Y.basicOpen q.1).isOpen) hcover
  refine ⟨t.image Subtype.val, fun y hy => ⟨fun h => ?_, ?_⟩⟩
  · by_contra hyK
    have hmem : y ∈ U₀.ι '' {w : U₀ | w.1 ∉ K} := ⟨⟨y, hy⟩, hyK, rfl⟩
    obtain ⟨q, hq, hyq⟩ := Set.mem_iUnion₂.mp (ht hmem)
    exact h q.1 (Finset.mem_image_of_mem _ hq) hyq
  · intro hyK q hq hyq
    obtain ⟨q', -, rfl⟩ := Finset.mem_image.mp hq
    exact q'.2 hyq hyK

end Shrink

section Generizations

attribute [local instance] MvPolynomial.gradedAlgebra

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
variable {B Y : Scheme.{u}} (π : B ⟶ Y) (pY : Y ⟶ Spec (CommRingCat.of V))
  [IsIntegral B] [IsIntegral Y] [LocallyOfFinitePresentation pY] [Flat (π ≫ pY)]
  [QuasiCompact pY] [IsSeparated pY]

/-- **Zariski connectedness over the generizations of a point of the modification locus**
(blueprint `thm:sm-connbirh-generizations`). Let `V` be a valuation ring with finitely many
primes, `pY : Y → Spec V` of finite presentation, quasi-compact and separated with `Y` integral,
normal and of relative dimension at most one, and `π : B → Y` birational and projective relative
to `pY` with `B` integral and flat over `V`. Let `z` be a point of the modification locus
`center π` with infinite residue field. Then the preimage of the set of generizations of `z` in
`center π` is preconnected. -/
theorem isPreconnected_preimage_generizations [Finite (PrimeSpectrum V)]
    (hπ : DeJong.IsRelativelyProjective pY π) (hY : IsNormalScheme Y)
    (hbir : Scheme.BirationalOver π (𝟙 Y))
    (hcurve : ValuationRing.fiberTrdeg pY (genericPoint Y) ≤ 1) (z : Y) (hz : z ∈ center π)
    [Infinite (Y.residueField z)] :
    _root_.IsPreconnected (π ⁻¹' {y | y ∈ center π ∧ y ⤳ z}) := by
  classical
  have := isModification_of_isRelativelyProjective π pY hπ hbir
  have : Finite (Spec (CommRingCat.of V)) := inferInstanceAs (Finite (PrimeSpectrum V))
  have hfin : (center π : Set Y).Finite := ValCurves.finite_center pY hY hcurve π
  set S : Set Y := (center π : Set Y) with hSdef
  set G : Set Y := {y | y ∈ center π ∧ y ⤳ z} with hGdef
  -- an open neighbourhood `U₀` of `z` with `S ∩ U₀ = G`
  set K := closure (S \ G)
  have hK : K = ⋃ w ∈ S \ G, closure {w} := by
    rw [← (hfin.subset Set.sdiff_subset).closure_biUnion (fun w => ({w} : Set Y)),
      Set.biUnion_of_singleton]
  have hGK : ∀ y ∈ G, y ∉ K := by
    intro y hy
    rw [hK, Set.mem_iUnion₂]
    rintro ⟨w, ⟨hwS, hwG⟩, hyw⟩
    exact hwG ⟨hwS, (specializes_iff_mem_closure.mpr hyw).trans hy.2⟩
  have hzG : z ∈ G := ⟨hz, specializes_rfl⟩
  let U₀ : Y.Opens := ⟨Kᶜ, isClosed_closure.isOpen_compl⟩
  have hzU₀ : z ∈ U₀ := hGK z hzG
  have hSU₀ : ∀ y ∈ U₀, y ∈ S → y ∈ G := by
    intro y hy hyS
    by_contra hyG
    exact hy (subset_closure ⟨hyS, hyG⟩)
  have hzcl : ∀ w ∈ U₀, z ⤳ w → w = z := by
    intro w hw hzw
    have hwS : w ∈ S := hzw.mem_closed (center π).isClosed hz
    exact (hzw.antisymm (hSU₀ w hw hwS).2).eq.symm
  -- two affine charts
  obtain ⟨U, hU, hzU, hUU₀, W₁, W₂, hW₁, hW₂, hcov⟩ :=
    exists_twoCharts_of_forall_specializes π pY hπ z U₀ hzU₀ hzcl
      (fun b b' b'' hb hb' hb'' h₁ h₂ =>
        eq_or_eq_of_specializes_of_fiberTrdeg_le_one' π pY hcurve b b' b'' hb hb' hb'' h₁ h₂)
  have : Nonempty U := ⟨⟨z, hzU⟩⟩
  have hGU : ∀ y ∈ G, y ∈ U := fun y hy => hy.2.mem_open U.isOpen hzU
  -- `S ∩ U` is cut out by finitely many functions
  obtain ⟨s, hs⟩ := exists_finset_zeroLocus_eq pY (center π).isClosed hU
  have hs' : ∀ q ∈ s, IsAffineOpen (π ⁻¹ᵁ Y.basicOpen q) := by
    intro q hq
    have hle : Y.basicOpen q ≤ isomorphismOpen π := by
      intro y hy
      by_contra hyS
      exact ((hs y (Y.basicOpen_le q hy)).mpr hyS) q hq hy
    have : IsIso (π ∣_ Y.basicOpen q) := (le_isomorphismOpen_iff π _).mp hle
    have : IsAffine (Y.basicOpen q).toScheme := hU.basicOpen q
    exact IsAffine.of_isIso (π ∣_ Y.basicOpen q)
  -- every prime containing `s` is contained in the prime of `z`
  set m := (U.toSpecΓ ⟨z, hzU⟩).asIdeal
  have hsm : ∀ P : Ideal Γ(Y, U), P.IsPrime → (s : Set Γ(Y, U)) ⊆ P → P ≤ m := by
    intro P hP hsP
    obtain ⟨⟨y, hy⟩, hyP⟩ := hU.isoSpec.hom.homeomorph.surjective ⟨P, hP⟩
    have hyP' : U.toSpecΓ ⟨y, hy⟩ = ⟨P, hP⟩ := hyP
    have hyS : y ∈ S := by
      refine (hs y hy).mp fun q hq => ?_
      rw [mem_basicOpen_iff_notMem_toSpecΓ q hy, hyP', not_not]
      exact hsP hq
    have hyz : (⟨y, hy⟩ : U) ⤳ ⟨z, hzU⟩ :=
      Topology.IsInducing.subtypeVal.specializes_iff.mp (hSU₀ y (hUU₀ hy) hyS).2
    have h := (PrimeSpectrum.le_iff_specializes _ _).mpr (hyz.map U.toSpecΓ.continuous)
    rw [hyP'] at h
    exact h
  have h := isPreconnected_preimage_zeroLocus_of_twoCharts_birational π pY hπ hY hbir hU W₁ W₂
    hW₁ hW₂ hcov s hs' m (U.toSpecΓ ⟨z, hzU⟩).isPrime.ne_top hsm
  have hset : {b : B | ∃ hb : π b ∈ U,
      U.toSpecΓ ⟨π b, hb⟩ ∈ PrimeSpectrum.zeroLocus (s : Set Γ(Y, U))} = π ⁻¹' G := by
    ext b
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    constructor
    · rintro ⟨hb, hbs⟩
      refine hSU₀ (π b) (hUU₀ hb) ((hs (π b) hb).mp fun q hq => ?_)
      rw [mem_basicOpen_iff_notMem_toSpecΓ q hb, not_not]
      exact hbs hq
    · intro hb
      have hbU := hGU (π b) hb
      refine ⟨hbU, fun q hq => ?_⟩
      have := (hs (π b) hbU).mpr hb.1 q hq
      rw [mem_basicOpen_iff_notMem_toSpecΓ q hbU, not_not] at this
      exact this
  rw [hset] at h
  exact h

end Generizations

end

end DeJongAlterations.StableModification.Cohomology.ConnectedBirationalHeight
