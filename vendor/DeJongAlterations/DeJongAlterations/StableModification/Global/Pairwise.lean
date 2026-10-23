import DeJongAlterations.StableModification.Global.Cover

/-!
# Comparison pieces from the uniqueness over valuation rings

Node G6 of `PLAN-T5.md` (§2.1 step 4; Temkin, *Stable modification of relative curves*,
`semi-stable.tex`, proof of Theorem 1.5, T:3394–3397), by the new gluing argument of the plan: no
Theorem 1.2 over normal bases, no Proposition 5.2.

Let `T₁, T₂` be local stable pieces of `(C, D)` over `S` and `W` a valuation ring of `L` in
`RZ_L(T₁) ∩ RZ_L(T₂)`. The base changes of the two stable models to `Spec W` are stable models of
`(C, D) ×_S Spec W`; by uniqueness over the valuation ring (`StableModelUniqueOver`, provided by
lane T45B's `ValuationStableUniqueness` through node G1) they are isomorphic over
`C ×_S Spec W`. Writing `Spec W` as the cofiltered limit of the spectra `Spec B` of the finitely
generated subalgebras `B ⊆ W` of `Γ(T₁ ×_S T₂, ⊤)`-algebras (lane LIM1, `Limits.isLimitFGSpecCone`),
the isomorphism descends to some `Spec B` (`Limits.exists_iso_of_iso`, EGA IV 8.8.2.5), where it is
still compatible with the projections to `C` by rigidity (the base change along the
scheme-theoretically dominant `Spec W ⟶ Spec B` of the flat `X₁ ×_{T₁} Spec B` is
scheme-theoretically dominant, `ext_of_isSchemeTheoreticallyDominant`). This is a comparison
piece containing `W` in its Riemann–Zariski space (`exists_comparisonPiece`).

* `LocalStablePiece.bc`, `LocalStablePiece.isStableModel_bc`: the base change of a local stable
  piece along `a : T' ⟶ T` mapping the generic point to the generic point.
* `StableModelUniqueOver pS g D L`: uniqueness of stable models over the valuation rings of
  `RZ_L(S)` (a hypothesis here).
* `exists_comparisonPiece`: the comparison pieces.

Blueprint: `sm-global.tex`, `def:sm-global-unique-over`, `thm:sm-global-comparison-piece`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace DeJongAlterations.StableModification.Global

universe u

open DeJong (IsSemistablePair IsRelativelyProjective)
open Curves (pullbackCompMap)
open RiemannZariskiSpace

variable {k : Type u} [CommRing k] {S C : Scheme.{u}} [IsIntegral S] {pS : S ⟶ Spec (.of k)}
  {g : C ⟶ S} {D : C.IdealSheafData} {L : Type u} [Field L] [Algebra S.functionField L]

section BaseChange

variable (P : LocalStablePiece pS g D L) {T' : Scheme.{u}} (a : T' ⟶ P.T)

/-- The base change `X ×_T T' ⟶ C ×_S T'` of the stable model of a piece along `a : T' ⟶ T`. -/
def LocalStablePiece.bc :
    pullback (C := Scheme.{u}) (P.β ≫ pullback.snd g P.t) a ⟶
      pullback (C := Scheme.{u}) g (a ≫ P.t) :=
  pullbackCompMap P.β (pullback.snd g P.t) a ≫ (pullbackLeftPullbackSndIso g P.t a).hom

@[reassoc (attr := simp)]
lemma LocalStablePiece.bc_fst :
    P.bc a ≫ pullback.fst g (a ≫ P.t) =
      pullback.fst (P.β ≫ pullback.snd g P.t) a ≫ P.β ≫ pullback.fst g P.t := by
  simp only [LocalStablePiece.bc, Category.assoc, pullbackLeftPullbackSndIso_hom_fst]
  rw [Curves.pullbackCompMap_fst_assoc]

@[reassoc (attr := simp)]
lemma LocalStablePiece.bc_snd :
    P.bc a ≫ pullback.snd g (a ≫ P.t) = pullback.snd (P.β ≫ pullback.snd g P.t) a := by
  simp only [LocalStablePiece.bc, Category.assoc, pullbackLeftPullbackSndIso_hom_snd]
  rw [Curves.pullbackCompMap_snd]

/-- **Base change of a local stable piece** along a quasi-compact `a : T' ⟶ T` from an integral
scheme, mapping the generic point to the generic point: a stable model of `(C, D) ×_S T'`. -/
theorem LocalStablePiece.isStableModel_bc [IsIntegral T'] [QuasiCompact a]
    (ha : a (genericPoint T') = genericPoint P.T) :
    IsStableModel ((a ≫ P.t) ≫ pS) (pullback.snd g (a ≫ P.t))
      (D.comap (pullback.fst g (a ≫ P.t))) (P.bc a)
      (P.D'.comap (pullback.fst (P.β ≫ pullback.snd g P.t) a)) := by
  have hm1 := P.isStableModel.pullback a ha
  have hD : (D.comap (pullback.fst g (a ≫ P.t))).comap (pullbackLeftPullbackSndIso g P.t a).hom =
      (D.comap (pullback.fst g P.t)).comap (pullback.fst (pullback.snd g P.t) a) := by
    simp only [← Scheme.IdealSheafData.comap_comp, pullbackLeftPullbackSndIso_hom_fst]
  have hm2 := hm1.comp_iso (pullbackLeftPullbackSndIso g P.t a).hom
    (pullbackLeftPullbackSndIso_hom_snd g P.t a) hD
  rw [← Category.assoc] at hm2
  exact hm2

end BaseChange

omit [IsIntegral S] in
/-- Stable models of base changes transport along equalities of the base change morphism. -/
theorem IsStableModel.congr_base {T X : Scheme.{u}} [IsIntegral T] {ψ ψ' : T ⟶ S}
    (h : ψ = ψ') {β : X ⟶ Limits.pullback g ψ} {D' : X.IdealSheafData}
    (hm : IsStableModel (ψ ≫ pS) (pullback.snd g ψ) (D.comap (pullback.fst g ψ)) β D') :
    IsStableModel (ψ' ≫ pS) (pullback.snd g ψ') (D.comap (pullback.fst g ψ'))
      (β ≫ (pullback.congrHom rfl h).hom) D' := by
  subst h
  have : (pullback.congrHom (rfl : g = g) (rfl : ψ = ψ)).hom = 𝟙 _ := by
    apply pullback.hom_ext <;> simp
  rw [this, Category.comp_id]
  exact hm

variable (pS g D L) in
/-- **Uniqueness of stable models over the valuation rings of `RZ_L(S)`** (the form of lane
T45B's `ValuationStableUniqueness` consumed by the comparison of pieces; derived from it in node
G1): over every valuation ring `W` of `L` extending `η = functionFieldPoint S L` along
`ψ : Spec W ⟶ S`, two stable models of `(C, D) ×_S Spec W` are isomorphic over `C ×_S Spec W`. -/
def StableModelUniqueOver : Prop :=
  ∀ (W : RiemannZariskiSpace L) (ψ : Spec (.of W.valuationSubring) ⟶ S),
    toSpecValuationSubring W ≫ ψ = functionFieldPoint S L →
    ∀ (X₁ X₂ : Scheme.{u}) (β₁ : X₁ ⟶ pullback (C := Scheme.{u}) g ψ)
      (β₂ : X₂ ⟶ pullback (C := Scheme.{u}) g ψ) (D₁ : X₁.IdealSheafData)
      (D₂ : X₂.IdealSheafData),
      IsStableModel (ψ ≫ pS) (pullback.snd g ψ) (D.comap (pullback.fst g ψ)) β₁ D₁ →
      IsStableModel (ψ ≫ pS) (pullback.snd g ψ) (D.comap (pullback.fst g ψ)) β₂ D₂ →
      ∃ e : X₁ ≅ X₂, e.hom ≫ β₂ = β₁

omit [IsIntegral S] in
/-- An affine scheme is affine over a separated scheme. -/
theorem isAffineHom_of_isAffine_of_isSeparated {T : Scheme.{u}} [IsAffine T] [S.IsSeparated]
    (t : T ⟶ S) : IsAffineHom t := by
  have : IsAffineHom (t ≫ terminal.from S) := by
    rw [terminal.comp_from]
    infer_instance
  exact IsAffineHom.of_comp t (terminal.from S)

set_option backward.isDefEq.respectTransparency false in
/-- **Comparison pieces** (`PLAN-T5.md` §2.1 step 4, node G6). Over a separated `S`, with
uniqueness of stable models over the valuation rings of `RZ_L(S)`, every valuation ring `W` of
`RZ_L(T₁) ∩ RZ_L(T₂)` for two local stable pieces lies in `RZ_L(T')` for a comparison piece `T'`
of them. -/
theorem exists_comparisonPiece [S.IsSeparated] [IsProper g] (hU : StableModelUniqueOver pS g D L)
    (P₁ P₂ : LocalStablePiece pS g D L) (W : RiemannZariskiSpace L) (hW₁ : W ∈ ofScheme P₁.ηT)
    (hW₂ : W ∈ ofScheme P₂.ηT) : ∃ Q : ComparisonPiece P₁ P₂, W ∈ ofScheme Q.η := by
  classical
  obtain ⟨ψ₁, hψ₁⟩ := hW₁
  obtain ⟨ψ₂, hψ₂⟩ := hW₂
  have hψ : ψ₁ ≫ P₁.t = ψ₂ ≫ P₂.t :=
    extension_unique (by rw [← Category.assoc, hψ₁, P₁.comp_ηT])
      (by rw [← Category.assoc, hψ₂, P₂.comp_ηT])
  -- the product of the two pieces, an affine scheme
  have : IsAffineHom P₂.t := isAffineHom_of_isAffine_of_isSeparated P₂.t
  have : IsAffine (pullback P₁.t P₂.t) := isAffine_of_isAffineHom (pullback.fst P₁.t P₂.t)
  let η₁₂ : Spec (.of L) ⟶ pullback P₁.t P₂.t :=
    pullback.lift P₁.ηT P₂.ηT (by rw [P₁.comp_ηT, P₂.comp_ηT])
  let ψ₁₂ : Spec (.of W.valuationSubring) ⟶ pullback P₁.t P₂.t := pullback.lift ψ₁ ψ₂ hψ
  have hψ₁₂ : toSpecValuationSubring W ≫ ψ₁₂ = η₁₂ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, hψ₁]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, hψ₂]
  -- `W` as a valuation ring of `L` over `A = Γ(T₁ ×_S T₂, ⊤)`
  have hηtop : η₁₂ ⁻¹ᵁ ⊤ = ⊤ := Scheme.Hom.preimage_top _
  let A := Γ(pullback P₁.t P₂.t, ⊤)
  let : Algebra A L := (sectionsToField η₁₂ ⊤ hηtop).toAlgebra
  have hWA : W ∈ ofAlgebra A L := by
    obtain ⟨hU', hW⟩ := mem_ofOpen_of_extension ψ₁₂ hψ₁₂ (U := ⊤) trivial
    exact hW
  let V : ofAlgebra A L := ⟨W, hWA⟩
  -- the approximating system of `W` by finitely generated `A`-subalgebras
  let R := Limits.valuationSubalgebra V
  let Dg := (Limits.fgDiagram R).op ⋙ Scheme.Spec
  let c := Limits.fgSpecCone R
  have hc : IsLimit c := Limits.isLimitFGSpecCone R
  let i₀ : (Limits.FGSubalgebra A R)ᵒᵖ := op ⊥
  let a₀ : Dg.obj i₀ ⟶ pullback P₁.t P₂.t :=
    Spec.map (CommRingCat.ofHom (algebraMap A (⊥ : Limits.FGSubalgebra A R).1)) ≫
      (isAffineOpen_top (pullback P₁.t P₂.t)).fromSpec
  let a₁ : Dg.obj i₀ ⟶ P₁.T := a₀ ≫ pullback.fst P₁.t P₂.t
  let a₂ : Dg.obj i₀ ⟶ P₂.T := a₀ ≫ pullback.snd P₁.t P₂.t
  let ψ₁' : c.pt ⟶ P₁.T := c.π.app i₀ ≫ a₁
  let ψ₂' : c.pt ⟶ P₂.T := c.π.app i₀ ≫ a₂
  let toR : Spec (.of L) ⟶ c.pt := Spec.map (CommRingCat.ofHom (algebraMap R L))
  have htoSpec : toSpecValuationSubring W = toR := rfl
  have hkey : (toR ≫ c.π.app i₀) ≫ a₀ = η₁₂ := by
    rw [show toR ≫ c.π.app i₀ = _ from
      Limits.specMap_comp_fgSpecCone_π_app V (⊥ : Limits.QASystem V)]
    simp only [a₀]
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    convert SpecMap_sectionsToField_fromSpec η₁₂ (isAffineOpen_top _) hηtop using 3
    ext x
    rfl
  have hη₁ : toR ≫ ψ₁' = P₁.ηT := by
    have := hkey =≫ pullback.fst P₁.t P₂.t
    simp only [η₁₂, pullback.lift_fst] at this
    rw [← this]
    simp only [ψ₁', a₁, Category.assoc]
  have hη₂ : toR ≫ ψ₂' = P₂.ηT := by
    have := hkey =≫ pullback.snd P₁.t P₂.t
    simp only [η₁₂, pullback.lift_snd] at this
    rw [← this]
    simp only [ψ₂', a₂, Category.assoc]
  -- the base changes of the two stable models to `Spec W`
  have hdomR : IsDominant toR := isDominant_SpecMap_of_injective _ Subtype.val_injective
  have hgenR : toR (genericPoint (Spec (.of L))) = genericPoint c.pt :=
    genericPoint_map_of_isDominant _
  have hg₁ : ψ₁' (genericPoint c.pt) = genericPoint P₁.T := by
    rw [← hgenR, ← Scheme.Hom.comp_apply, hη₁, genericPoint_map_of_isDominant]
  have hg₂ : ψ₂' (genericPoint c.pt) = genericPoint P₂.T := by
    rw [← hgenR, ← Scheme.Hom.comp_apply, hη₂, genericPoint_map_of_isDominant]
  have : IsAffine c.pt := inferInstanceAs (IsAffine (Spec (.of R)))
  have : QuasiCompact ψ₁' :=
    (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact) (f := ψ₁')).mpr inferInstance
  have : QuasiCompact ψ₂' :=
    (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact) (f := ψ₂')).mpr inferInstance
  have hm₁ := P₁.isStableModel_bc ψ₁' hg₁
  have hm₂ := P₂.isStableModel_bc ψ₂' hg₂
  have hψ' : ψ₂' ≫ P₂.t = ψ₁' ≫ P₁.t := by
    simp only [ψ₁', ψ₂', a₁, a₂, Category.assoc, pullback.condition]
  have hm₂' := hm₂.congr_base hψ'
  have hηψ : toSpecValuationSubring W ≫ (ψ₁' ≫ P₁.t) = functionFieldPoint S L := by
    rw [htoSpec, ← Category.assoc, hη₁, P₁.comp_ηT]
  obtain ⟨θ, hθ⟩ := hU W (ψ₁' ≫ P₁.t) hηψ _ _ (P₁.bc ψ₁')
    (P₂.bc ψ₂' ≫ (pullback.congrHom rfl hψ').hom) _ _ hm₁ hm₂'
  have hθsnd : θ.hom ≫ pullback.snd (P₂.β ≫ pullback.snd g P₂.t) ψ₂' =
      pullback.snd (P₁.β ≫ pullback.snd g P₁.t) ψ₁' := by
    have := hθ =≫ pullback.snd g (ψ₁' ≫ P₁.t)
    rw [Category.assoc, Category.assoc, pullback.congrHom_hom, pullback.lift_snd,
      Category.comp_id, LocalStablePiece.bc_snd, LocalStablePiece.bc_snd] at this
    exact this
  have hθfst : θ.hom ≫ pullback.fst (P₂.β ≫ pullback.snd g P₂.t) ψ₂' ≫ P₂.β ≫
      pullback.fst g P₂.t = pullback.fst (P₁.β ≫ pullback.snd g P₁.t) ψ₁' ≫ P₁.β ≫
        pullback.fst g P₁.t := by
    have := hθ =≫ pullback.fst g (ψ₁' ≫ P₁.t)
    rw [Category.assoc, Category.assoc, pullback.congrHom_hom, pullback.lift_fst,
      Category.comp_id, LocalStablePiece.bc_fst, LocalStablePiece.bc_fst] at this
    exact this
  -- the two base changes as models at the bottom level of the system
  have : IsProper P₁.β := P₁.isStableModel.isProper
  have : IsProper P₂.β := P₂.isStableModel.isProper
  have := P₁.isStableModel.isSemistablePair.nodal
  have := P₂.isStableModel.isSemistablePair.nodal
  let r₁ : Limits.Model Dg c (pullback.snd (P₁.β ≫ pullback.snd g P₁.t) ψ₁') i₀ :=
    { Y := pullback (P₁.β ≫ pullback.snd g P₁.t) a₁
      fY := pullback.snd _ _
      g := pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ c.π.app i₀)
        (by rw [pullback.condition, Category.assoc])
      isPullback := IsPullback.of_right (by
          rw [pullback.lift_fst]
          exact IsPullback.of_hasPullback _ _)
        (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _) }
  let r₂ : Limits.Model Dg c (pullback.snd (P₂.β ≫ pullback.snd g P₂.t) ψ₂') i₀ :=
    { Y := pullback (P₂.β ≫ pullback.snd g P₂.t) a₂
      fY := pullback.snd _ _
      g := pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ c.π.app i₀)
        (by rw [pullback.condition, Category.assoc])
      isPullback := IsPullback.of_right (by
          rw [pullback.lift_fst]
          exact IsPullback.of_hasPullback _ _)
        (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _) }
  have : QuasiCompact r₁.fY := by dsimp [r₁]; infer_instance
  have : QuasiSeparated r₁.fY := by dsimp [r₁]; infer_instance
  have : LocallyOfFinitePresentation r₁.fY := by dsimp [r₁]; infer_instance
  have : QuasiCompact r₂.fY := by dsimp [r₂]; infer_instance
  have : QuasiSeparated r₂.fY := by dsimp [r₂]; infer_instance
  have : LocallyOfFinitePresentation r₂.fY := by dsimp [r₂]; infer_instance
  -- descent of the isomorphism
  obtain ⟨l, Θ, hΘsnd, hΘπ⟩ := Limits.exists_iso_of_iso Dg c hc r₁ r₂ θ hθsnd
  -- rigidity: the descended isomorphism is compatible with the projections to `C`
  have hιd :
      IsSchemeTheoreticallyDominant ((Limits.baseChangeCone Dg c r₁.isPullback).π.app l) := by
    have : IsReduced (Dg.obj l.left) :=
      inferInstanceAs (IsReduced (Spec (.of (l.left.unop.1 : Subalgebra A L))))
    have : IsDominant (c.π.app l.left) := by
      refine isDominant_SpecMap_of_injective _ fun x y hxy ↦ ?_
      have := congrArg Subtype.val hxy
      exact Subtype.ext this
    have : IsSchemeTheoreticallyDominant (c.π.app l.left) :=
      IsSchemeTheoreticallyDominant.of_isDominant _
    have : IsAffine (Dg.obj l.left) :=
      inferInstanceAs (IsAffine (Spec (.of (l.left.unop.1 : Subalgebra A L))))
    have : QuasiCompact (c.π.app l.left) :=
      (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact) (f := c.π.app l.left)).mpr
        (inferInstance : CompactSpace c.pt)
    have : Flat (pullback.snd r₁.fY (Dg.map l.hom)) := by dsimp [r₁]; infer_instance
    exact IsSchemeTheoreticallyDominant.of_isPullback
      (Limits.isPullback_baseChangeCone_π Dg c r₁.isPullback l).flip
  have huv : pullback.fst r₁.fY (Dg.map l.hom) ≫ pullback.fst _ a₁ ≫ P₁.β ≫
      pullback.fst g P₁.t = Θ.hom ≫ pullback.fst r₂.fY (Dg.map l.hom) ≫ pullback.fst _ a₂ ≫
        P₂.β ≫ pullback.fst g P₂.t := by
    refine ext_of_isSchemeTheoreticallyDominant g ?_
      ((Limits.baseChangeCone Dg c r₁.isPullback).π.app l) ?_
    · have h₁ : pullback.fst r₁.fY (Dg.map l.hom) ≫ pullback.fst _ a₁ ≫ P₁.β ≫
          pullback.fst g P₁.t ≫ g =
            pullback.snd r₁.fY (Dg.map l.hom) ≫ Dg.map l.hom ≫ a₁ ≫ P₁.t := by
        rw [pullback.condition (f := g) (g := P₁.t)]
        have e1 := pullback.condition (f := P₁.β ≫ pullback.snd g P₁.t) (g := a₁)
        have e2 := pullback.condition (f := r₁.fY) (g := Dg.map l.hom)
        rw [reassoc_of% e1, ← Category.assoc, ← Category.assoc]
        change (pullback.fst r₁.fY (Dg.map l.hom) ≫ r₁.fY) ≫ a₁ ≫ P₁.t = _
        rw [e2, Category.assoc]
      have h₂ : pullback.fst r₂.fY (Dg.map l.hom) ≫ pullback.fst _ a₂ ≫ P₂.β ≫
          pullback.fst g P₂.t ≫ g =
            pullback.snd r₂.fY (Dg.map l.hom) ≫ Dg.map l.hom ≫ a₂ ≫ P₂.t := by
        rw [pullback.condition (f := g) (g := P₂.t)]
        have e1 := pullback.condition (f := P₂.β ≫ pullback.snd g P₂.t) (g := a₂)
        have e2 := pullback.condition (f := r₂.fY) (g := Dg.map l.hom)
        rw [reassoc_of% e1, ← Category.assoc, ← Category.assoc]
        change (pullback.fst r₂.fY (Dg.map l.hom) ≫ r₂.fY) ≫ a₂ ≫ P₂.t = _
        rw [e2, Category.assoc]
      have ha : a₂ ≫ P₂.t = a₁ ≫ P₁.t := by
        simp only [a₁, a₂, Category.assoc, pullback.condition]
      simp only [Category.assoc]
      rw [h₁, h₂, reassoc_of% hΘsnd, ha]
    · have hπ₁ : (Limits.baseChangeCone Dg c r₁.isPullback).π.app l ≫
          pullback.fst r₁.fY (Dg.map l.hom) = r₁.g := pullback.lift_fst _ _ _
      have hπ₂ : (Limits.baseChangeCone Dg c r₂.isPullback).π.app l ≫
          pullback.fst r₂.fY (Dg.map l.hom) = r₂.g := pullback.lift_fst _ _ _
      have hg₁' : r₁.g ≫ pullback.fst _ a₁ = pullback.fst _ ψ₁' := pullback.lift_fst _ _ _
      have hg₂' : r₂.g ≫ pullback.fst _ a₂ = pullback.fst _ ψ₂' := pullback.lift_fst _ _ _
      rw [reassoc_of% hπ₁, reassoc_of% hg₁', reassoc_of% hΘπ, reassoc_of% hπ₂, reassoc_of% hg₂',
        hθfst]
  -- the comparison piece `Spec B`
  have hlft : LocallyOfFiniteType ((Dg.map l.hom ≫ a₁) ≫ P₁.t) := by
    have e1 : Dg.map l.hom ≫ Spec.map (CommRingCat.ofHom
        (algebraMap A (⊥ : Limits.FGSubalgebra A R).1)) =
          Spec.map (CommRingCat.ofHom (algebraMap A (l.left.unop.1 : Subalgebra A L))) := by
      change Spec.map _ ≫ _ = _
      rw [← Spec.map_comp]
      congr 1
    have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
        (algebraMap A (l.left.unop.1 : Subalgebra A L)))) :=
      Limits.locallyOfFiniteType_specMap l.left.unop
    have : LocallyOfFiniteType (Dg.map l.hom ≫ a₀) := by
      simp only [a₀]
      rw [← Category.assoc, e1]
      infer_instance
    simp only [a₁, Category.assoc]
    rw [← Category.assoc (Dg.map l.hom)]
    infer_instance
  have : IsAffine (Dg.obj l.left) :=
    inferInstanceAs (IsAffine (Spec (.of (l.left.unop.1 : Subalgebra A L))))
  let E₁ := pullbackLeftPullbackSndIso (P₁.β ≫ pullback.snd g P₁.t) a₁ (Dg.map l.hom)
  let E₂ := pullbackLeftPullbackSndIso (P₂.β ≫ pullback.snd g P₂.t) a₂ (Dg.map l.hom)
  have hcw : c.π.app l.left ≫ Dg.map l.hom = c.π.app i₀ := c.w l.hom
  refine ⟨{
      T := Dg.obj l.left
      c₁ := Dg.map l.hom ≫ a₁
      c₂ := Dg.map l.hom ≫ a₂
      comm := by simp only [a₁, a₂, Category.assoc, pullback.condition]
      locallyOfFiniteType := hlft
      η := toR ≫ c.π.app l.left
      comp_η₁ := by rw [Category.assoc, reassoc_of% hcw, hη₁]
      comp_η₂ := by rw [Category.assoc, reassoc_of% hcw, hη₂]
      e := E₁.symm ≪≫ Θ ≪≫ E₂
      e_snd := by
        simp only [E₁, E₂, Iso.trans_hom, Iso.symm_hom, Category.assoc,
          pullbackLeftPullbackSndIso_hom_snd]
        rw [hΘsnd, pullbackLeftPullbackSndIso_inv_snd_snd]
      e_fst := by
        simp only [E₁, E₂, Iso.trans_hom, Iso.symm_hom, Category.assoc,
          pullbackLeftPullbackSndIso_hom_fst_assoc]
        rw [← huv, pullbackLeftPullbackSndIso_inv_fst_assoc] }, ?_⟩
  exact ⟨c.π.app l.left, rfl⟩

end DeJongAlterations.StableModification.Global
