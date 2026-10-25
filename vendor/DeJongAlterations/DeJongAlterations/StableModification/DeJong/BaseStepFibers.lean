import DeJongAlterations.StableModification.DeJong.NodalBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Fibres in the base step

Bookkeeping of scheme-theoretic fibres used in the base step 4.22 of de Jong
(`dejong96-alterations:page-0025`, `page-0026`) with Temkin's stable modification plugged in.

* `fiberIsoOfIso`: isomorphic `S`-schemes have isomorphic fibres over `Spec κ(s)`.
* `fiberMarksIso`: the restriction `D_s = D ×_C C_s` of a closed subscheme to a fibre is the
  fibre of `D → S` (Temkin §1.2 computes semi-stability of a multipointed curve on fibres).
* `fiberIsoOfIsIsoOver`: an `S`-morphism which is an isomorphism over an open `U ⊆ S` induces
  isomorphisms of the fibres over the points of `U`. This transports the generic fibre
  through Temkin's `η`-modification `β : C' → C ×_S S'` (Temkin Thm 1.5, `semi-stable.tex`
  l.1771–1775).
* `isIntegral_of_isSchemeTheoreticallyDominant`, `isIntegral_of_flat_of_isIntegral_genericFiber`
  (`lem:sm-dj-strict-transform-integral`): a scheme flat over an integral base with integral
  generic fibre is integral. Flatness makes the inclusion of the generic fibre schematically
  dominant (flat base change of the schematically dominant `Spec κ(η) → S`), so the scheme is
  the scheme-theoretic closure of its generic fibre (de Jong 2.18, `page-0011`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.StableModification.DeJong

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section FiberIso

variable {A B C S : Scheme.{u}}

/-- Isomorphic `S`-schemes have isomorphic fibres. -/
def fiberIsoOfIso (e : A ≅ B) (hA : A ⟶ S) (hB : B ⟶ S) (h : e.hom ≫ hB = hA) (s : S) :
    hA.fiber s ≅ hB.fiber s :=
  asIso (pullback.map hA (S.fromSpecResidueField s) hB (S.fromSpecResidueField s) e.hom (𝟙 _)
    (𝟙 _) (by simp [h]) (by simp))

@[reassoc (attr := simp)]
theorem fiberIsoOfIso_hom_fiberToSpecResidueField (e : A ≅ B) (hA : A ⟶ S) (hB : B ⟶ S)
    (h : e.hom ≫ hB = hA) (s : S) :
    (fiberIsoOfIso e hA hB h s).hom ≫ hB.fiberToSpecResidueField s =
      hA.fiberToSpecResidueField s := by
  simp [fiberIsoOfIso, Scheme.Hom.fiberToSpecResidueField]

/-- The square exhibiting the restriction of a closed subscheme to a fibre as the fibre of
the closed subscheme. -/
theorem isPullback_fiberMarks (g : C ⟶ S) (D : C.IdealSheafData) (s : S) :
    IsPullback (pullback.snd (g.fiberι s) D.subschemeι)
      (pullback.fst (g.fiberι s) D.subschemeι ≫ g.fiberToSpecResidueField s)
      (D.subschemeι ≫ g) (S.fromSpecResidueField s) :=
  (IsPullback.of_hasPullback (g.fiberι s) D.subschemeι).flip.paste_vert
    (IsPullback.of_hasPullback g (S.fromSpecResidueField s))

/-- The restriction `D_s` of a closed subscheme `D ⊆ C` to the fibre `C_s` is the fibre of
`D → S` at `s`. -/
def fiberMarksIso (g : C ⟶ S) (D : C.IdealSheafData) (s : S) :
    (fiberMarks g D s).subscheme ≅ (D.subschemeι ≫ g).fiber s :=
  D.comapIso (g.fiberι s) ≪≫ (isPullback_fiberMarks g D s).isoPullback

@[reassoc (attr := simp)]
theorem fiberMarksIso_hom_fiberToSpecResidueField (g : C ⟶ S) (D : C.IdealSheafData) (s : S) :
    (fiberMarksIso g D s).hom ≫ (D.subschemeι ≫ g).fiberToSpecResidueField s =
      (fiberMarks g D s).subschemeι ≫ g.fiberToSpecResidueField s := by
  simp only [fiberMarksIso, Iso.trans_hom, Category.assoc, Scheme.Hom.fiberToSpecResidueField]
  rw [IsPullback.isoPullback_hom_snd, Scheme.IdealSheafData.comapIso_hom_fst_assoc]

/-- An `S`-morphism `β : A → B` which is an isomorphism over an open `U ⊆ S` induces an
isomorphism of the fibres over every point of `U`. -/
theorem exists_fiberIso_of_isIso_morphismRestrict (β : A ⟶ B) (q : B ⟶ S) (U : S.Opens)
    (hβ : IsIso (β ∣_ (q ⁻¹ᵁ U))) (s : S) (hs : s ∈ U) :
    ∃ E : (β ≫ q).fiber s ≅ q.fiber s,
      E.hom ≫ q.fiberToSpecResidueField s = (β ≫ q).fiberToSpecResidueField s := by
  have hrange : Set.range (S.fromSpecResidueField s) ⊆ Set.range U.ι := by
    rw [Scheme.range_fromSpecResidueField, Scheme.Opens.range_ι]
    simpa using hs
  let t : Spec (S.residueField s) ⟶ U := IsOpenImmersion.lift U.ι _ hrange
  have ht : t ≫ U.ι = S.fromSpecResidueField s := IsOpenImmersion.lift_fac _ _ _
  -- the fibre of `h` over `s` is the pullback of `h ∣_ U` along `t`
  have key : ∀ {X : Scheme.{u}} (h : X ⟶ S), ∃ l : h.fiber s ⟶ h ⁻¹ᵁ U,
      IsPullback l (h.fiberToSpecResidueField s) (h ∣_ U) t := by
    intro X h
    have hr : Set.range (h.fiberι s) ⊆ Set.range (h ⁻¹ᵁ U).ι := by
      rw [Scheme.Hom.range_fiberι, Scheme.Opens.range_ι]
      intro x hx
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
      change h x ∈ U
      rw [hx]
      exact hs
    let l : h.fiber s ⟶ h ⁻¹ᵁ U := IsOpenImmersion.lift _ _ hr
    have hl : l ≫ (h ⁻¹ᵁ U).ι = h.fiberι s := IsOpenImmersion.lift_fac _ _ _
    refine ⟨l, IsPullback.of_right (h₁₂ := (h ⁻¹ᵁ U).ι) (h₂₂ := U.ι) (v₁₃ := h) ?_ ?_
      (isPullback_morphismRestrict h U).flip⟩
    · rw [hl, ht]
      exact IsPullback.of_hasPullback h (S.fromSpecResidueField s)
    · rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, reassoc_of% hl,
        Category.assoc, ht]
      exact pullback.condition
  obtain ⟨l₁, H₁⟩ := key (β ≫ q)
  obtain ⟨l₂, H₂⟩ := key q
  rw [morphismRestrict_comp] at H₁
  have H₃ : IsPullback (β ∣_ (q ⁻¹ᵁ U)) (β ∣_ (q ⁻¹ᵁ U) ≫ q ∣_ U) (q ∣_ U) (𝟙 U.toScheme) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have H₄ := H₁.paste_horiz H₃
  rw [Category.comp_id] at H₄
  exact ⟨H₄.isoIsPullback _ _ H₂, IsPullback.isoIsPullback_hom_snd _ _ _ _⟩

end FiberIso

section Integral

variable {P A C S : Scheme.{u}}

/-- The target of a quasi-compact schematically dominant morphism from an integral scheme is
integral. -/
theorem isIntegral_of_isSchemeTheoreticallyDominant (j : P ⟶ A)
    [IsSchemeTheoreticallyDominant j] [QuasiCompact j] [IsIntegral P] : IsIntegral A := by
  have : IsReduced A := IsSchemeTheoreticallyDominant.isReduced j
  have : IrreducibleSpace A := by
    have hirr : IsIrreducible (Set.range j) := by
      rw [← Set.image_univ]
      exact ((irreducibleSpace_def P).mp inferInstance).image j j.continuous.continuousOn
    have := hirr.closure
    rw [j.denseRange.closure_range] at this
    exact (irreducibleSpace_def A).mpr this
  exact isIntegral_of_irreducibleSpace_of_isReduced A

/-- The inclusion of a point of an integral scheme is schematically dominant when the point is
generic. -/
instance isSchemeTheoreticallyDominant_fromSpecResidueField_genericPoint (S : Scheme.{u})
    [IsIntegral S] : IsSchemeTheoreticallyDominant (S.fromSpecResidueField (genericPoint S)) := by
  have : IsDominant (S.fromSpecResidueField (genericPoint S)) := by
    refine ⟨?_⟩
    rw [DenseRange, Scheme.range_fromSpecResidueField]
    exact dense_iff_closure_eq.mpr (genericPoint_spec S)
  exact IsSchemeTheoreticallyDominant.of_isDominant _

/-- **Flatness and integral generic fibre give integrality**
(`lem:sm-dj-strict-transform-integral`). Let `g : C → S` be flat with `S` integral and
quasi-separated. Then the inclusion of the generic fibre is schematically dominant; hence if
the generic fibre is integral, so is `C`. -/
theorem isIntegral_of_flat_of_isIntegral_genericFiber [IsIntegral S] [QuasiSeparatedSpace S]
    (g : C ⟶ S) [Flat g] (h : IsIntegral (g.fiber (genericPoint S))) : IsIntegral C := by
  have : IsSchemeTheoreticallyDominant (g.fiberι (genericPoint S)) :=
    IsSchemeTheoreticallyDominant.pullbackFst g (S.fromSpecResidueField (genericPoint S))
  have : QuasiCompact (g.fiberι (genericPoint S)) := by
    change QuasiCompact (pullback.fst g (S.fromSpecResidueField (genericPoint S)))
    infer_instance
  exact isIntegral_of_isSchemeTheoreticallyDominant (g.fiberι (genericPoint S))

end Integral

end DeJongAlterations.StableModification.DeJong
