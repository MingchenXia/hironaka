import DeJongAlterations.StableModification.Global.SetupModelTransport
import DeJongAlterations.StableModification.Global.Alteration
import DeJongAlterations.Composition

/-!
# Local stable pieces, comparison pieces and the refinement

Nodes G5–G6 of `PLAN-T5.md` (§2.1 steps 3–4; Temkin, *Stable modification of relative curves*,
`semi-stable.tex`, proof of Theorem 1.5, T:3384–3397), reorganized so that a *single* refinement
of the base is needed.

Let `S` be integral, `L ⊇ K(S)` algebraic (in the application `L = K(S)ᵃ`, decision D-DJ9), and
`η = functionFieldPoint S L`.

* `LocalStablePiece pS g D L`: an affine integral `T`, of finite type over an affine open of `S`,
  with a dominant `L`-point over `η`, and a stable model (`IsStableModel`) of `(C, D) ×_S T` over
  `T`. These are produced around every valuation ring of `RZ_L(S)` by spreading out the stable
  modification over the valuation ring (nodes G1, G3′, G4).
* `ComparisonPiece P₁ P₂`: an affine `T` with morphisms `cᵢ : T ⟶ Pᵢ.T` over `S`, an `L`-point
  over the points of the `Pᵢ`, and an isomorphism `X₁ ×_{T₁} T ≅ X₂ ×_{T₂} T` over `C` and `T`.
  These are produced around every valuation ring of `RZ_L(T₁) ∩ RZ_L(T₂)` by the uniqueness of
  the stable modification over the valuation ring and descent of the isomorphism (node G6).
* `LocalStablePiece.isStableModelOn`: the base change of a piece along a proper `h : W ⟶ T` from
  an open `W` of a refinement `p : S'' ⟶ S` is a stable model over `W` in the sense of
  `IsStableModelOn`, the form consumed by the gluing theorem.

Blueprint: `sm-global.tex`, `def:sm-global-local-piece`, `def:sm-global-comparison-piece`,
`lem:sm-global-piece-base-change`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.StableModification.Global

universe u

open DeJong (IsSemistablePair IsRelativelyProjective)
open Curves (pullbackCompMap)
open RiemannZariskiSpace

variable {k : Type u} [CommRing k] {S C : Scheme.{u}} [IsIntegral S] (pS : S ⟶ Spec (.of k))
  (g : C ⟶ S) (D : C.IdealSheafData) (L : Type u) [Field L] [Algebra S.functionField L]

/-- **A local stable piece** of the multipointed `S`-curve `(C, D)` (`PLAN-T5.md` §2.1 step 2):
an affine integral scheme `T` with a morphism `t : T ⟶ S` locally of finite type into an affine
open `V` of `S`, a dominant `L`-point `ηT` over `η = functionFieldPoint S L`, and a stable model
`β : X ⟶ C ×_S T` of `(C, D) ×_S T` over `T`. -/
structure LocalStablePiece where
  /-- The base of the piece. -/
  T : Scheme.{u}
  [isAffine : IsAffine T]
  [isIntegral : IsIntegral T]
  /-- Its morphism to `S`. -/
  t : T ⟶ S
  [locallyOfFiniteType : LocallyOfFiniteType t]
  /-- An affine open of `S` containing the image. -/
  V : S.Opens
  isAffineOpen : IsAffineOpen V
  preimage_eq_top : t ⁻¹ᵁ V = ⊤
  /-- The `L`-point of `T` over `η`. -/
  ηT : Spec (.of L) ⟶ T
  comp_ηT : ηT ≫ t = functionFieldPoint S L
  [isDominant : IsDominant ηT]
  /-- The stable model. -/
  X : Scheme.{u}
  /-- Its morphism to `C ×_S T`. -/
  β : X ⟶ pullback (C := Scheme.{u}) g t
  /-- Its marks. -/
  D' : X.IdealSheafData
  isStableModel : IsStableModel (t ≫ pS) (pullback.snd g t) (D.comap (pullback.fst g t)) β D'

attribute [instance] LocalStablePiece.isAffine LocalStablePiece.isIntegral
  LocalStablePiece.locallyOfFiniteType LocalStablePiece.isDominant

variable {pS g D L}

/-- **A comparison piece** for two local stable pieces (`PLAN-T5.md` §2.1 step 4): an affine `T`
with morphisms `cᵢ : T ⟶ Pᵢ.T` over `S` (the composite to `S` locally of finite type), an
`L`-point over the points of the `Pᵢ`, and an isomorphism `X₁ ×_{T₁} T ≅ X₂ ×_{T₂} T` compatible
with the projections to `T` and to `C`. -/
structure ComparisonPiece (P₁ P₂ : LocalStablePiece pS g D L) where
  /-- The base of the comparison piece. -/
  T : Scheme.{u}
  [isAffine : IsAffine T]
  /-- The morphism to the first piece. -/
  c₁ : T ⟶ P₁.T
  /-- The morphism to the second piece. -/
  c₂ : T ⟶ P₂.T
  comm : c₁ ≫ P₁.t = c₂ ≫ P₂.t
  [locallyOfFiniteType : LocallyOfFiniteType (c₁ ≫ P₁.t)]
  /-- The `L`-point. -/
  η : Spec (.of L) ⟶ T
  comp_η₁ : η ≫ c₁ = P₁.ηT
  comp_η₂ : η ≫ c₂ = P₂.ηT
  /-- The comparison isomorphism. -/
  e : pullback (C := Scheme.{u}) (P₁.β ≫ pullback.snd g P₁.t) c₁ ≅
    pullback (C := Scheme.{u}) (P₂.β ≫ pullback.snd g P₂.t) c₂
  e_snd : e.hom ≫ pullback.snd _ _ = pullback.snd _ _
  e_fst : e.hom ≫ pullback.fst _ _ ≫ P₂.β ≫ pullback.fst g P₂.t =
    pullback.fst _ _ ≫ P₁.β ≫ pullback.fst g P₁.t

attribute [instance] ComparisonPiece.isAffine ComparisonPiece.locallyOfFiniteType

section BaseChange

variable {S'' : Scheme.{u}} (p : S'' ⟶ S) (P : LocalStablePiece pS g D L) (W : S''.Opens)
  (h : W.toScheme ⟶ P.T) (hh : h ≫ P.t = W.ι ≫ p)

/-- The identification `(C ×_S T) ×_T W ≅ (C ×_S S'') ×_{S''} W` for `h : W ⟶ T` over `S`. -/
def LocalStablePiece.bcIso :
    pullback (C := Scheme.{u}) (pullback.snd g P.t) h ≅
      pullback (C := Scheme.{u}) (pullback.snd g p) W.ι :=
  pullbackLeftPullbackSndIso g P.t h ≪≫ pullback.congrHom rfl hh ≪≫
    (pullbackLeftPullbackSndIso g p W.ι).symm

@[reassoc (attr := simp)]
lemma LocalStablePiece.bcIso_hom_snd :
    (P.bcIso p W h hh).hom ≫ pullback.snd (pullback.snd g p) W.ι = pullback.snd _ h := by
  simp only [LocalStablePiece.bcIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    pullbackLeftPullbackSndIso_inv_snd_snd]
  rw [pullback.congrHom_hom, pullback.lift_snd, Category.comp_id,
    pullbackLeftPullbackSndIso_hom_snd]

@[reassoc (attr := simp)]
lemma LocalStablePiece.bcIso_hom_fst_fst :
    (P.bcIso p W h hh).hom ≫ pullback.fst (pullback.snd g p) W.ι ≫ pullback.fst g p =
      pullback.fst _ h ≫ pullback.fst g P.t := by
  simp only [LocalStablePiece.bcIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    pullbackLeftPullbackSndIso_inv_fst]
  rw [pullback.congrHom_hom, pullback.lift_fst, Category.comp_id,
    pullbackLeftPullbackSndIso_hom_fst]

/-- The base change `X ×_T W ⟶ C ×_S S''` of the stable model of a piece along `h : W ⟶ T`. -/
def LocalStablePiece.bcMap :
    pullback (C := Scheme.{u}) (P.β ≫ pullback.snd g P.t) h ⟶ pullback (C := Scheme.{u}) g p :=
  (pullbackCompMap P.β (pullback.snd g P.t) h ≫ (P.bcIso p W h hh).hom) ≫
    pullback.fst (pullback.snd g p) W.ι

/-- The base change of the marks of a piece along `h : W ⟶ T`. -/
abbrev LocalStablePiece.bcMarks :
    (pullback (C := Scheme.{u}) (P.β ≫ pullback.snd g P.t) h).IdealSheafData :=
  P.D'.comap (pullback.fst (P.β ≫ pullback.snd g P.t) h)

@[reassoc]
lemma LocalStablePiece.bcMap_fst :
    P.bcMap p W h hh ≫ pullback.fst g p =
      pullback.fst (P.β ≫ pullback.snd g P.t) h ≫ P.β ≫ pullback.fst g P.t := by
  simp only [LocalStablePiece.bcMap, Category.assoc, LocalStablePiece.bcIso_hom_fst_fst]
  rw [Curves.pullbackCompMap_fst_assoc]

@[reassoc]
lemma LocalStablePiece.bcMap_snd :
    P.bcMap p W h hh ≫ pullback.snd g p = pullback.snd (P.β ≫ pullback.snd g P.t) h ≫ W.ι := by
  rw [LocalStablePiece.bcMap, Category.assoc, Category.assoc, pullback.condition,
    LocalStablePiece.bcIso_hom_snd_assoc, Curves.pullbackCompMap_snd_assoc]

/-- **Base change of a local stable piece to an open of a refinement** (`PLAN-T5.md` §2.1
step 3, node G5). For `p : S'' ⟶ S` with `S''` integral, an open `W ⊆ S''` with quasi-compact
inclusion and a quasi-compact `h : W ⟶ T` over `S` mapping a dominant `L`-point of `W` to the
point of the piece, the base change `X ×_T W ⟶ C ×_S S''` is a stable model over `W` of
`(C, D) ×_S S''` in the sense of `IsStableModelOn`. -/
theorem LocalStablePiece.isStableModelOn [IsIntegral S''] [Nonempty W] [QuasiCompact W.ι]
    [QuasiCompact h] (e : Spec (.of L) ⟶ W.toScheme) [IsDominant e] (he : e ≫ h = P.ηT) :
    IsStableModelOn (p ≫ pS) (pullback.snd g p) (D.comap (pullback.fst g p)) W
      (P.bcMap p W h hh) (P.bcMarks W h) := by
  have hη : h (genericPoint W) = genericPoint P.T := by
    rw [← genericPoint_map_of_isDominant e, ← Scheme.Hom.comp_apply, he,
      genericPoint_map_of_isDominant]
  have hm1 := P.isStableModel.pullback h hη
  have hD : ((D.comap (pullback.fst g p)).comap (pullback.fst (pullback.snd g p) W.ι)).comap
      (P.bcIso p W h hh).hom =
        (D.comap (pullback.fst g P.t)).comap (pullback.fst (pullback.snd g P.t) h) := by
    simp only [← Scheme.IdealSheafData.comap_comp, LocalStablePiece.bcIso_hom_fst_fst]
  have hm2 := hm1.comp_iso (P.bcIso p W h hh).hom (LocalStablePiece.bcIso_hom_snd p P W h hh) hD
  have hpT : h ≫ P.t ≫ pS = W.ι ≫ p ≫ pS := by rw [reassoc_of% hh]
  rw [hpT] at hm2
  exact hm2.toOn W

end BaseChange

section RZ

open Set.Notation

omit [IsIntegral S] [Algebra S.functionField L] in
/-- **Finite subcovers in `RZ_L(S)`**: a compact subset of `RZ_L(S)` covered by the
Riemann–Zariski spaces of finitely many morphisms locally of finite type is covered by finitely
many of them (they are open in `RZ_L(S)` by Temkin's Corollary 3.2.7,
`RiemannZariskiSpace.isOpen_ofScheme_of_locallyOfFiniteType`). -/
theorem exists_finset_cover_ofScheme [S.IsSeparated] [CompactSpace S] {η : Spec (.of L) ⟶ S}
    {K : Set (RiemannZariskiSpace L)} (hK : IsCompact K) (hKη : K ⊆ ofScheme η)
    {ι : Type*} {T : ι → Scheme.{u}} (f : ∀ i, T i ⟶ S) [∀ i, LocallyOfFiniteType (f i)]
    (ηT : ∀ i, Spec (.of L) ⟶ T i) (hηT : ∀ i, ηT i ≫ f i = η)
    (hcov : K ⊆ ⋃ i, ofScheme (ηT i)) : ∃ s : Finset ι, K ⊆ ⋃ i ∈ s, ofScheme (ηT i) := by
  have hK' : IsCompact (Subtype.val ⁻¹' K : Set (ofScheme η)) := by
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, Set.inter_eq_right.mpr hKη]
    exact hK
  obtain ⟨s, hs⟩ := hK'.elim_finite_subcover (fun i ↦ ofScheme η ↓∩ ofScheme (ηT i))
    (fun i ↦ isOpen_ofScheme_of_locallyOfFiniteType (f i) (hηT i)) (by
      intro W hW
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hW)
      exact Set.mem_iUnion.mpr ⟨i, hi⟩)
  refine ⟨s, fun W hW ↦ ?_⟩
  have := hs (show (⟨W, hKη hW⟩ : ofScheme η) ∈ Subtype.val ⁻¹' K from hW)
  simp only [Set.mem_iUnion] at this ⊢
  obtain ⟨i, hi, hW'⟩ := this
  exact ⟨i, hi, hW'⟩

omit [IsIntegral S] [Algebra S.functionField L] in
/-- A morphism from the spectrum of a valuation ring whose closed point lies in an open `U`
lands in `U` (every point specializes to the closed point). -/
theorem range_subset_of_specClosedPoint_mem {V : RiemannZariskiSpace L}
    (ψ : Spec (.of V.valuationSubring) ⟶ S) {U : S.Opens} (hψ : ψ (specClosedPoint V) ∈ U) :
    Set.range ψ ⊆ U := by
  rintro _ ⟨y, rfl⟩
  exact ((IsLocalRing.specializes_closedPoint y).map ψ.continuous).mem_open U.isOpen hψ

omit [IsIntegral S] [Algebra S.functionField L] in
/-- A valuation ring whose extension to a refinement is centred in the open `W` of a realised
piece `h : W ⟶ T` lies in `RZ_L(T)`. -/
theorem mem_ofScheme_of_mem_open {S'' T : Scheme.{u}} {η'' : Spec (.of L) ⟶ S''}
    {V : RiemannZariskiSpace L} (ψ : Spec (.of V.valuationSubring) ⟶ S'')
    (hψ : toSpecValuationSubring V ≫ ψ = η'') {W : S''.Opens} (hψW : ψ (specClosedPoint V) ∈ W)
    (h : W.toScheme ⟶ T) (e : Spec (.of L) ⟶ W.toScheme) (he : e ≫ W.ι = η'')
    {ηT : Spec (.of L) ⟶ T} (heh : e ≫ h = ηT) : V ∈ ofScheme ηT := by
  have hr := range_subset_of_specClosedPoint_mem ψ hψW
  rw [← Scheme.Opens.range_ι W] at hr
  refine ⟨IsOpenImmersion.lift W.ι ψ hr ≫ h, ?_⟩
  rw [← heh, ← Category.assoc]
  congr 1
  rw [← cancel_mono W.ι, Category.assoc, IsOpenImmersion.lift_fac, hψ, he]

end RZ

end DeJongAlterations.StableModification.Global
