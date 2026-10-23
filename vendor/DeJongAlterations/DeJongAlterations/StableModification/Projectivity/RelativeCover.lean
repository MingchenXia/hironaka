/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane OM3C)
-/
import DeJongAlterations.StableModification.Projectivity.RelativeCoverProj
import DeJongAlterations.StableModification.Projectivity.RelativeCoverLinear
import DeJongAlterations.StableModification.Projectivity.RelativeFibre

/-!
# Two affines around a fibre (`lem:sm-ltg-two-affines`)

Blueprint `sm-projectivity-relative.tex`, `lem:sm-ltg-two-affines` (PLAN-OM3 §3 step 1). Let
`β : X ⟶ Y` be proper and projective relative to `W' ⟶ Y ⟶ Spec R` over an open `W' ⊆ Y`, and
let `y ∈ W'` be a closed point with infinite residue field whose fibre has dimension at most one.
Then there are an affine open `W ∋ y` inside `W'` and affine opens `U₀`, `U₁` of `X` with affine
intersection and `U₀ ∪ U₁ = β⁻¹ W` (`exists_twoAffines`).

Proof: over an affine `W₀ ∋ y`, `β⁻¹ W₀` is a closed subscheme of `ℙⁿ_{Γ(Y, W₀)}`
(`isProjectiveOver_morphismRestrict_of_le`); two linear forms `ℓ₀`, `ℓ₁` have no common zero on
the fibre over `y` (`exists_linearForms_fibre`; the residue field `Γ(Y, W₀) ⧸ 𝔭_y = κ(y)` is
infinite, `infinite_quotient_toSpecΓ`); the common zero locus is closed, so its image avoids a
basic open `W = D(g) ∋ y`, and `U_i = β⁻¹ W ∩ D₊(ℓ_i)` are affine.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Limits

namespace DeJongAlterations.StableModification.Projectivity

noncomputable section

open DeJong Cohomology

variable {X Y : Scheme.{u}}

/-! ### The residue field of a closed point of an affine open -/

section Residue

variable {W : Y.Opens} (hW : IsAffineOpen W) {y : Y} (hy : y ∈ W)

/-- A function on `W` lies in the prime of `y` iff it vanishes at `y`. -/
lemma mem_toSpecΓ_asIdeal_iff (a : Γ(Y, W)) :
    a ∈ (W.toSpecΓ ⟨y, hy⟩).asIdeal ↔ y ∉ Y.basicOpen a := by
  have h := congrArg (fun U : W.toScheme.Opens => (⟨y, hy⟩ : W.toScheme) ∈ U)
    (Scheme.Opens.toSpecΓ_preimage_basicOpen W a)
  simp only [eq_iff_iff] at h
  rw [← not_iff_not, not_not]
  exact (PrimeSpectrum.mem_basicOpen _ _).symm.trans h

/-- The kernel of the residue map at `y` is the prime of `y`. -/
lemma ker_fibreResidue : RingHom.ker (fibreResidue y hy).hom = (W.toSpecΓ ⟨y, hy⟩).asIdeal := by
  ext a
  rw [RingHom.mem_ker, mem_toSpecΓ_asIdeal_iff hy]
  have hpt : Nonempty (Spec (Y.residueField y)) :=
    ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨pt⟩ := hpt
  have hb : (Spec (Y.residueField y)).basicOpen (fibreResidue y hy a) =
      Y.fromSpecResidueField y ⁻¹ᵁ Y.basicOpen a := by
    rw [fibreResidue, Scheme.basicOpen_appLE, top_inf_eq]
  constructor
  · intro h0 hya
    have : pt ∈ (Spec (Y.residueField y)).basicOpen (fibreResidue y hy a) := by
      rw [hb]
      change Y.fromSpecResidueField y pt ∈ Y.basicOpen a
      rw [Scheme.fromSpecResidueField_apply]
      exact hya
    rw [h0, Scheme.basicOpen_zero] at this
    exact this
  · intro hya
    by_contra h0
    set r := fibreResidue y hy a
    let φ := (Scheme.ΓSpecIso (CommRingCat.of (Y.residueField y))).commRingCatIsoToRingEquiv
    have hφr : φ r ≠ 0 := fun h => h0 (φ.injective (h.trans (map_zero φ).symm))
    have hunit : IsUnit r := by
      have : IsUnit (φ.symm (φ r)) := (Ne.isUnit hφr).map φ.symm
      rwa [RingEquiv.symm_apply_apply] at this
    have : pt ∈ (Spec (Y.residueField y)).basicOpen r := by
      rw [Scheme.basicOpen_of_isUnit _ hunit]
      trivial
    rw [hb] at this
    apply hya
    have := this
    change Y.fromSpecResidueField y pt ∈ Y.basicOpen a at this
    rwa [Scheme.fromSpecResidueField_apply] at this

include hW in
/-- **The residue field of a closed point**: for a closed point `y` of an affine open `W` with
infinite residue field, `Γ(Y, W) ⧸ 𝔭_y` is infinite. -/
lemma infinite_quotient_toSpecΓ (hcl : IsClosed ({y} : Set Y)) [Infinite (Y.residueField y)] :
    Infinite (Γ(Y, W) ⧸ (W.toSpecΓ ⟨y, hy⟩).asIdeal) := by
  let e₁ := RingHom.quotientKerEquivOfSurjective (surjective_fibreResidue y hW hy hcl)
  let e₂ := Ideal.quotEquivOfEq (ker_fibreResidue hy)
  let e₃ := (Scheme.ΓSpecIso (CommRingCat.of (Y.residueField y))).commRingCatIsoToRingEquiv
  exact Infinite.of_injective (fun t : Y.residueField y => e₂ (e₁.symm (e₃.symm t)))
    (fun _ _ h => e₃.symm.injective (e₁.symm.injective (e₂.injective h)))

end Residue

/-! ### Dimension of a fibre -/

/-- **Dimension of a fibre over a closed point**: if the fibre over a closed point `y` has
topological Krull dimension at most one, there are no chains `x ⤳ x' ⤳ x''` of three distinct
points of `X` starting over `y`. -/
theorem eq_or_eq_of_topologicalKrullDim_fiber_le_one' (β : X ⟶ Y) {y : Y}
    (hy : IsClosed ({y} : Set Y)) (hdim : topologicalKrullDim (β.fiber y) ≤ 1) (x x' x'' : X)
    (hx : β x = y) (hxy : x ⤳ x') (hyz : x' ⤳ x'') : x = x' ∨ x' = x'' := by
  have hy' : β x' = y := (hxy.map β.continuous).mem_closed hy hx
  have hz : β x'' = y := (hyz.map β.continuous).mem_closed hy hy'
  by_contra h
  push Not at h
  let e := (β.fiberHomeo y).symm
  have hi : Topology.IsInducing (Subtype.val : (β ⁻¹' {y} : Set X) → X) :=
    Topology.IsInducing.subtypeVal
  have hxy' : e ⟨x, hx⟩ ⤳ e ⟨x', hy'⟩ := (hi.specializes_iff.mp hxy).map e.continuous
  have hyz' : e ⟨x', hy'⟩ ⤳ e ⟨x'', hz⟩ := (hi.specializes_iff.mp hyz).map e.continuous
  have hne₁ : e ⟨x'', hz⟩ ≠ e ⟨x', hy'⟩ := fun h' => h.2 (congrArg Subtype.val (e.injective h')).symm
  have hne₂ : e ⟨x', hy'⟩ ≠ e ⟨x, hx⟩ := fun h' => h.1 (congrArg Subtype.val (e.injective h')).symm
  have h2 := two_le_krullDim_of_specializes hyz' hxy' hne₁ hne₂
  rw [← Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints] at h2
  exact absurd (h2.trans hdim) (by decide)

/-! ### The two affines -/

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R]

/-- **Two affines around a fibre** (blueprint `lem:sm-ltg-two-affines`). -/
theorem exists_twoAffines (pY : Y ⟶ Spec (.of R)) (β : X ⟶ Y) [IsProper β] {W' : Y.Opens}
    (hW' : IsRelativelyProjective (W'.ι ≫ pY) (β ∣_ W')) {y : Y} (hyW' : y ∈ W')
    (hy : IsClosed ({y} : Set Y)) [Infinite (Y.residueField y)]
    (hdim : topologicalKrullDim (β.fiber y) ≤ 1) :
    ∃ W : Y.Opens, IsAffineOpen W ∧ y ∈ W ∧ W ≤ W' ∧ ∃ U₀ U₁ : X.Opens, IsAffineOpen U₀ ∧
      IsAffineOpen U₁ ∧ IsAffineOpen (U₀ ⊓ U₁) ∧ U₀ ⊔ U₁ = β ⁻¹ᵁ W := by
  obtain ⟨W₀, hW₀, hyW₀, hW₀W'⟩ := exists_isAffineOpen_mem_and_subset hyW'
  obtain ⟨n, j, hj, hjs⟩ := isProjectiveOver_morphismRestrict_of_le pY β hW' hW₀ hW₀W'
  have : IsClosedImmersion j := hj
  set A := Γ(Y, W₀)
  set π₀ := β ∣_ W₀ ≫ W₀.toSpecΓ with hπ₀
  set ι₀ := (β ⁻¹ᵁ W₀).ι with hι₀
  set 𝔭 : PrimeSpectrum A := W₀.toSpecΓ ⟨y, hyW₀⟩ with h𝔭
  have : Infinite (A ⧸ 𝔭.asIdeal) := infinite_quotient_toSpecΓ hW₀ hyW₀ hy
  -- `𝔭` is a closed point
  have h𝔭cl : IsClosed ({𝔭} : Set (PrimeSpectrum A)) := by
    rw [PrimeSpectrum.isClosed_singleton_iff_isMaximal]
    let e₃ := (Scheme.ΓSpecIso (CommRingCat.of (Y.residueField y))).commRingCatIsoToRingEquiv
    have hsurj : Function.Surjective (e₃.toRingHom.comp (fibreResidue y hyW₀).hom) :=
      e₃.surjective.comp (surjective_fibreResidue y hW₀ hyW₀ hy)
    have hker : RingHom.ker (e₃.toRingHom.comp (fibreResidue y hyW₀).hom) =
        RingHom.ker (fibreResidue y hyW₀).hom := by
      ext a
      simp only [RingHom.mem_ker, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, map_eq_zero_iff _ e₃.injective]
    have := RingHom.ker_isMaximal_of_surjective _ hsurj
    rwa [hker, ker_fibreResidue hyW₀] at this
  -- points of `β⁻¹ W₀` over `𝔭` are the points over `y`
  have hπ₀y : ∀ x₀, π₀ x₀ = 𝔭 ↔ β (ι₀ x₀) = y := by
    intro x₀
    have e1 : β (ι₀ x₀) = W₀.ι ((β ∣_ W₀) x₀) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, morphismRestrict_ι]
    rw [e1]
    constructor
    · intro h
      have := hW₀.isoSpec.hom.homeomorph.injective (show W₀.toSpecΓ ((β ∣_ W₀) x₀) =
        W₀.toSpecΓ ⟨y, hyW₀⟩ from h)
      rw [this]
      rfl
    · intro h
      change W₀.toSpecΓ ((β ∣_ W₀) x₀) = _
      congr 1
      exact Subtype.ext h
  -- the two linear forms
  have hdim' : ∀ x x' x'' : (β ⁻¹ᵁ W₀).toScheme,
      (j ≫ projectiveSpaceStructure A n) x = 𝔭 → x ⤳ x' → x' ⤳ x'' →
        x = x' ∨ x' = x'' := by
    intro x x' x'' hx hxx' hx'x''
    rw [hjs] at hx
    rcases eq_or_eq_of_topologicalKrullDim_fiber_le_one' β hy hdim (ι₀ x) (ι₀ x') (ι₀ x'')
        ((hπ₀y x).mp hx) (hxx'.map ι₀.continuous) (hx'x''.map ι₀.continuous) with h | h
    · exact Or.inl (ι₀.isOpenEmbedding.injective h)
    · exact Or.inr (ι₀.isOpenEmbedding.injective h)
  obtain ⟨ℓ₀, hℓ₀, ℓ₁, hℓ₁, hcovℓ⟩ := exists_linearForms_fibre j 𝔭 h𝔭cl hdim'
  set D₀ := j ⁻¹ᵁ Proj.basicOpen (projectiveSpaceGrading A n) ℓ₀
  set D₁ := j ⁻¹ᵁ Proj.basicOpen (projectiveSpaceGrading A n) ℓ₁
  -- the common zero locus has closed image avoiding `𝔭`
  have : IsProper (j ≫ projectiveSpaceStructure A n) := inferInstance
  have hπ₀prop : IsProper π₀ := by rw [← hjs]; infer_instance
  have hZ : IsClosed (π₀ '' ((D₀ ⊔ D₁ : (β ⁻¹ᵁ W₀).toScheme.Opens) : Set _)ᶜ) :=
    π₀.isClosedMap _ (D₀ ⊔ D₁).isOpen.isClosed_compl
  have h𝔭Z : 𝔭 ∉ π₀ '' ((D₀ ⊔ D₁ : (β ⁻¹ᵁ W₀).toScheme.Opens) : Set _)ᶜ := by
    rintro ⟨x₀, hx₀, hx₀𝔭⟩
    apply hx₀
    have := hcovℓ x₀ (by rw [hjs]; exact hx₀𝔭)
    exact this
  obtain ⟨_, ⟨g, rfl⟩, h𝔭g, hgZ⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open h𝔭Z hZ.isOpen_compl
  -- the basic open `W = D(g)`
  have hyW : y ∈ Y.basicOpen g := by
    have := (mem_toSpecΓ_asIdeal_iff hyW₀ g).not.mp
    simp only [not_not] at this
    exact this ((PrimeSpectrum.mem_basicOpen _ _).mp h𝔭g)
  refine ⟨Y.basicOpen g, hW₀.basicOpen g, hyW, (Y.basicOpen_le g).trans hW₀W', ?_⟩
  -- `D(g)` pulled back to `β⁻¹ W₀`
  set G := (ι₀ ≫ β).app W₀ g with hGdef
  have hG : (β ⁻¹ᵁ W₀).toScheme.basicOpen G = ι₀ ⁻¹ᵁ β ⁻¹ᵁ Y.basicOpen g := by
    rw [hGdef, ← Scheme.preimage_basicOpen, Scheme.Hom.comp_preimage]
  have hGπ : ∀ x₀, x₀ ∈ (β ⁻¹ᵁ W₀).toScheme.basicOpen G ↔ π₀ x₀ ∈ PrimeSpectrum.basicOpen g := by
    intro x₀
    rw [hG]
    have e1 : β (ι₀ x₀) = W₀.ι ((β ∣_ W₀) x₀) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, morphismRestrict_ι]
    have h := congrArg (fun U : W₀.toScheme.Opens => (β ∣_ W₀) x₀ ∈ U)
      (Scheme.Opens.toSpecΓ_preimage_basicOpen W₀ g)
    simp only [eq_iff_iff] at h
    change β (ι₀ x₀) ∈ Y.basicOpen g ↔ _
    rw [e1]
    exact h.symm
  have hle : ∀ V : (β ⁻¹ᵁ W₀).toScheme.Opens, V ≤ (ι₀ ≫ β) ⁻¹ᵁ W₀ := fun V x₀ _ => x₀.2
  have hD : ∀ (ℓ : MvPolynomial (Fin (n + 1)) A) (m : ℕ), ℓ ∈ projectiveSpaceGrading A n m →
      0 < m → IsAffineOpen (j ⁻¹ᵁ Proj.basicOpen (projectiveSpaceGrading A n) ℓ) := by
    intro ℓ m hℓ hm
    exact Cohomology.isAffineOpen_preimage_basicOpen j ℓ hℓ hm
  -- the opens of `β⁻¹ W₀`
  have hU' : ∀ V : (β ⁻¹ᵁ W₀).toScheme.Opens, IsAffineOpen V →
      IsAffineOpen (V ⊓ (β ⁻¹ᵁ W₀).toScheme.basicOpen G) := by
    intro V hV
    have := hV.basicOpen ((β ⁻¹ᵁ W₀).toScheme.presheaf.map (homOfLE (hle V)).op G)
    rwa [Scheme.basicOpen_res] at this
  have hD₀₁ : D₀ ⊓ D₁ = j ⁻¹ᵁ Proj.basicOpen (projectiveSpaceGrading A n) (ℓ₀ * ℓ₁) := by
    rw [Proj.basicOpen_mul]
    rfl
  have hsup : (D₀ ⊓ (β ⁻¹ᵁ W₀).toScheme.basicOpen G) ⊔ (D₁ ⊓ (β ⁻¹ᵁ W₀).toScheme.basicOpen G) =
      (β ⁻¹ᵁ W₀).toScheme.basicOpen G := by
    rw [← inf_sup_right]
    refine inf_eq_right.mpr fun x₀ hx₀ => ?_
    by_contra hx
    exact hgZ ((hGπ x₀).mp hx₀) ⟨x₀, hx, rfl⟩
  refine ⟨ι₀ ''ᵁ (D₀ ⊓ (β ⁻¹ᵁ W₀).toScheme.basicOpen G),
    ι₀ ''ᵁ (D₁ ⊓ (β ⁻¹ᵁ W₀).toScheme.basicOpen G),
    (hU' _ (hD ℓ₀ 1 hℓ₀ one_pos)).image_of_isOpenImmersion ι₀,
    (hU' _ (hD ℓ₁ 1 hℓ₁ one_pos)).image_of_isOpenImmersion ι₀, ?_, ?_⟩
  · have himg : ι₀ ''ᵁ (D₀ ⊓ (β ⁻¹ᵁ W₀).toScheme.basicOpen G) ⊓
        ι₀ ''ᵁ (D₁ ⊓ (β ⁻¹ᵁ W₀).toScheme.basicOpen G) =
        ι₀ ''ᵁ ((D₀ ⊓ D₁) ⊓ (β ⁻¹ᵁ W₀).toScheme.basicOpen G) := by
      ext : 1
      simp only [Scheme.Hom.coe_image, Opens.coe_inf, ← Set.image_inter ι₀.isOpenEmbedding.injective]
      congr 1
      ext x
      simp only [Set.mem_inter_iff, SetLike.mem_coe]
      tauto
    rw [himg, hD₀₁]
    exact (hU' _ (hD (ℓ₀ * ℓ₁) 2 (SetLike.mul_mem_graded hℓ₀ hℓ₁) two_pos)).image_of_isOpenImmersion ι₀
  · have himg : ι₀ ''ᵁ (D₀ ⊓ (β ⁻¹ᵁ W₀).toScheme.basicOpen G) ⊔
        ι₀ ''ᵁ (D₁ ⊓ (β ⁻¹ᵁ W₀).toScheme.basicOpen G) =
        ι₀ ''ᵁ ((D₀ ⊓ (β ⁻¹ᵁ W₀).toScheme.basicOpen G) ⊔ (D₁ ⊓ (β ⁻¹ᵁ W₀).toScheme.basicOpen G)) := by
      ext : 1
      simp only [Scheme.Hom.coe_image, Opens.coe_sup, Set.image_union]
    have hrange : ι₀.opensRange = β ⁻¹ᵁ W₀ := Scheme.Opens.opensRange_ι _
    rw [himg, hsup, hG, Scheme.Hom.image_preimage_eq_opensRange_inf, hrange]
    exact inf_eq_right.mpr (β.preimage_mono (Y.basicOpen_le g))

end

end DeJongAlterations.StableModification.Projectivity
