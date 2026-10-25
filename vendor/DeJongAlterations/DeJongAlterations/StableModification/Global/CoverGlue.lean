import DeJongAlterations.StableModification.Global.Cover

/-!
# Gluing the base changes of the local stable pieces

Nodes G5–G7 of `PLAN-T5.md` (§2.1 steps 3–5; Temkin, *Stable modification of relative curves*,
`semi-stable.tex`, proof of Theorem 1.5, T:3384–3397), with a single refinement of the base.

Let `S` be integral, separated, quasi-compact and locally Noetherian, `L ⊇ K(S)` algebraic and
`η = functionFieldPoint S L`. Assume

* every valuation ring of `RZ_L(S)` lies in `RZ_L(T)` for some local stable piece `T`
  (`LocalStablePiece`), and
* for any two local stable pieces `T₁, T₂`, every valuation ring of `RZ_L(T₁) ∩ RZ_L(T₂)` lies in
  `RZ_L(T')` for some comparison piece `T'` (`ComparisonPiece`).

By compactness of `RZ_L(S)` and of `RZ_L(T₁) ∩ RZ_L(T₂)` (Temkin, Proposition 3.2.1) finitely
many pieces suffice; a single refinement `p : S'' ⟶ S` (Proposition 3.2.6 by an alteration,
`exists_refinement_isAlteration`) realises all of them. The base changes of the local stable
pieces to the opens `W_a ⊆ S''` realising them are stable models over `W_a`
(`LocalStablePiece.isStableModelOn`), the `W_a` cover `S''` (every point of `S''` is the centre of
a valuation ring, which lies in some `RZ_L(T_a)`), and near every point of `W_a ∩ W_b` an open
`O ⊆ S''` realising a comparison piece carries a morphism of the two base changes over
`C ×_S S''` (`LocalStablePiece.exists_local_hom`: the two morphisms `O ∩ W_a ⟶ T_a` agree by
rigidity, `ext_of_isDominant_of_isSeparated`). The gluing theorem
`exists_glue_isStableModelOn` then produces the global model (`exists_glued_model`).

Blueprint: `sm-global.tex`, `lem:sm-global-local-hom`, `thm:sm-global-glued-model`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.StableModification.Global

universe u

open DeJong (IsSemistablePair IsRelativelyProjective)
open Curves (pullbackCompMap)
open RiemannZariskiSpace

variable {k : Type u} [CommRing k] {S C : Scheme.{u}} [IsIntegral S] {pS : S ⟶ Spec (.of k)}
  {g : C ⟶ S} {D : C.IdealSheafData} {L : Type u} [Field L] [Algebra S.functionField L]

omit [IsIntegral S] in
/-- An affine scheme is separated over any separated scheme. -/
theorem isSeparated_of_isAffine_of_isSeparated {T : Scheme.{u}} [IsAffine T] [S.IsSeparated]
    (t : T ⟶ S) : IsSeparated t := by
  have : IsSeparated (t ≫ terminal.from S) := by
    rw [terminal.comp_from]
    infer_instance
  exact IsSeparated.of_comp t (terminal.from S)

/-- **The local morphisms on the overlaps** (`PLAN-T5.md` §2.1 step 4, node G6). Let
`p : S'' ⟶ S` be a morphism from an integral scheme with a dominant `L`-point `η''`, let opens
`W₁, W₂, O ⊆ S''` realise two local stable pieces `P₁, P₂` and a comparison piece `Q` of them
(morphisms `h₁, h₂, h_O` over `S`, compatible with `L`-points over `η''`). Then every point `x` of
the base change `X₁ ×_{T₁} W₁` lying over `W₂ ∩ O` has an open neighbourhood `V` lying over `W₂`
with a morphism `V ⟶ X₂ ×_{T₂} W₂` over `C ×_S S''`. -/
theorem LocalStablePiece.exists_local_hom [S.IsSeparated] {S'' : Scheme.{u}} [IsIntegral S'']
    (p : S'' ⟶ S) (η'' : Spec (.of L) ⟶ S'') [IsDominant η'']
    (P₁ P₂ : LocalStablePiece pS g D L) (Q : ComparisonPiece P₁ P₂) (W₁ W₂ O : S''.Opens)
    (h₁ : W₁.toScheme ⟶ P₁.T) (h₂ : W₂.toScheme ⟶ P₂.T) (hO : O.toScheme ⟶ Q.T)
    (hh₁ : h₁ ≫ P₁.t = W₁.ι ≫ p) (hh₂ : h₂ ≫ P₂.t = W₂.ι ≫ p)
    (hhO : hO ≫ Q.c₁ ≫ P₁.t = O.ι ≫ p)
    (e₁ : Spec (.of L) ⟶ W₁.toScheme) (he₁ : e₁ ≫ W₁.ι = η'') (he₁' : e₁ ≫ h₁ = P₁.ηT)
    (e₂ : Spec (.of L) ⟶ W₂.toScheme) (he₂ : e₂ ≫ W₂.ι = η'') (he₂' : e₂ ≫ h₂ = P₂.ηT)
    (eO : Spec (.of L) ⟶ O.toScheme) (heO : eO ≫ O.ι = η'') (heO' : eO ≫ hO = Q.η)
    (x : pullback (C := Scheme.{u}) (P₁.β ≫ pullback.snd g P₁.t) h₁)
    (hx : (P₁.bcMap p W₁ h₁ hh₁ ≫ pullback.snd g p) x ∈ W₂ ⊓ O) :
    ∃ V : (pullback (C := Scheme.{u}) (P₁.β ≫ pullback.snd g P₁.t) h₁).Opens, x ∈ V ∧
      V ≤ (P₁.bcMap p W₁ h₁ hh₁ ≫ pullback.snd g p) ⁻¹ᵁ W₂ ∧
      ∃ m : V.toScheme ⟶ pullback (C := Scheme.{u}) (P₂.β ≫ pullback.snd g P₂.t) h₂,
        m ≫ P₂.bcMap p W₂ h₂ hh₂ = V.ι ≫ P₁.bcMap p W₁ h₁ hh₁ := by
  set f := P₁.bcMap p W₁ h₁ hh₁ ≫ pullback.snd g p with hf
  have hf' : f = pullback.snd _ h₁ ≫ W₁.ι := P₁.bcMap_snd p W₁ h₁ hh₁
  let N : S''.Opens := W₁ ⊓ W₂ ⊓ O
  have hxW₁ : f x ∈ W₁ := by
    rw [hf', Scheme.Hom.comp_apply]
    exact (pullback.snd _ h₁ x).2
  have hxN : f x ∈ N := ⟨⟨hxW₁, hx.1⟩, hx.2⟩
  refine ⟨f ⁻¹ᵁ N, hxN, fun y hy ↦ hy.1.2, ?_⟩
  -- the inclusions and the restriction of `f` to `N`
  have hN₁ : N ≤ W₁ := fun y hy ↦ hy.1.1
  have hN₂ : N ≤ W₂ := fun y hy ↦ hy.1.2
  have hNO : N ≤ O := fun y hy ↦ hy.2
  let i₁ : N.toScheme ⟶ W₁.toScheme := S''.homOfLE hN₁
  let i₂ : N.toScheme ⟶ W₂.toScheme := S''.homOfLE hN₂
  let iO : N.toScheme ⟶ O.toScheme := S''.homOfLE hNO
  let σ : (f ⁻¹ᵁ N).toScheme ⟶ N.toScheme := f ∣_ N
  have hσ : σ ≫ N.ι = (f ⁻¹ᵁ N).ι ≫ f := morphismRestrict_ι f N
  -- the dominant `L`-point of `N`
  have hgen : genericPoint S'' ∈ N :=
    ((genericPoint_spec S'').mem_open_set_iff N.isOpen).mpr ⟨f x, Set.mem_univ _, hxN⟩
  have hrη : Set.range η'' ⊆ Set.range N.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    have : η'' z = genericPoint S'' := by
      rw [← genericPoint_map_of_isDominant η'']
      congr 1
      exact Subsingleton.elim _ _
    rw [this]
    exact hgen
  let eN := IsOpenImmersion.lift N.ι η'' hrη
  have heN : eN ≫ N.ι = η'' := IsOpenImmersion.lift_fac _ _ _
  have : IsDominant eN := by
    have : IsDominant (eN ≫ N.ι) := by rw [heN]; infer_instance
    exact isDominant_of_comp_isOpenImmersion eN N.ι
  have heN₁ : eN ≫ i₁ = e₁ := by
    rw [← cancel_mono W₁.ι, Category.assoc, Scheme.homOfLE_ι, heN, he₁]
  have heN₂ : eN ≫ i₂ = e₂ := by
    rw [← cancel_mono W₂.ι, Category.assoc, Scheme.homOfLE_ι, heN, he₂]
  have heNO : eN ≫ iO = eO := by
    rw [← cancel_mono O.ι, Category.assoc, Scheme.homOfLE_ι, heN, heO]
  -- rigidity: the two morphisms `N ⟶ Tᵢ` agree
  have : IsSeparated P₁.t := isSeparated_of_isAffine_of_isSeparated P₁.t
  have : IsSeparated P₂.t := isSeparated_of_isAffine_of_isSeparated P₂.t
  have rig₁ : i₁ ≫ h₁ = iO ≫ hO ≫ Q.c₁ := by
    refine ext_of_isDominant_of_isSeparated P₁.t ?_ eN ?_
    · rw [Category.assoc, hh₁, Category.assoc, Category.assoc, hhO, Scheme.homOfLE_ι_assoc,
        Scheme.homOfLE_ι_assoc]
    · rw [reassoc_of% heN₁, he₁', reassoc_of% heNO, reassoc_of% heO', Q.comp_η₁]
  have rig₂ : i₂ ≫ h₂ = iO ≫ hO ≫ Q.c₂ := by
    refine ext_of_isDominant_of_isSeparated P₂.t ?_ eN ?_
    · rw [Category.assoc, hh₂, Category.assoc, Category.assoc, ← Q.comm, hhO,
        Scheme.homOfLE_ι_assoc, Scheme.homOfLE_ι_assoc]
    · rw [reassoc_of% heN₂, he₂', reassoc_of% heNO, reassoc_of% heO', Q.comp_η₂]
  have hsnd₁ : (f ⁻¹ᵁ N).ι ≫ pullback.snd _ h₁ = σ ≫ i₁ := by
    rw [← cancel_mono W₁.ι, Category.assoc, ← hf', Category.assoc, Scheme.homOfLE_ι, hσ]
  -- the morphism to `X₁ ×_{T₁} T'` and then to `X₂ ×_{T₂} W₂`
  let A : (f ⁻¹ᵁ N).toScheme ⟶ pullback (C := Scheme.{u}) (P₁.β ≫ pullback.snd g P₁.t) Q.c₁ :=
    pullback.lift ((f ⁻¹ᵁ N).ι ≫ pullback.fst _ h₁) (σ ≫ iO ≫ hO) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hsnd₁, Category.assoc, rig₁,
        Category.assoc, Category.assoc])
  let m : (f ⁻¹ᵁ N).toScheme ⟶ pullback (C := Scheme.{u}) (P₂.β ≫ pullback.snd g P₂.t) h₂ :=
    pullback.lift (A ≫ Q.e.hom ≫ pullback.fst _ _) (σ ≫ i₂) (by
      rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc Q.e.hom, Q.e_snd,
        pullback.lift_snd_assoc]
      simp only [Category.assoc, rig₂])
  refine ⟨m, pullback.hom_ext ?_ ?_⟩
  · rw [Category.assoc, P₂.bcMap_fst, pullback.lift_fst_assoc]
    simp only [Category.assoc]
    rw [Q.e_fst, pullback.lift_fst_assoc, P₁.bcMap_fst, Category.assoc]
  · rw [Category.assoc, P₂.bcMap_snd, pullback.lift_snd_assoc, Category.assoc,
      Scheme.homOfLE_ι, hσ, Category.assoc]

/-- **The glued model over a refinement** (`PLAN-T5.md` §2.1 steps 3–5, nodes G5–G7; Temkin,
proof of Theorem 1.5, T:3384–3397). Let `S` be integral, separated, quasi-compact and locally
Noetherian and `L ⊇ K(S)` algebraic. If every valuation ring of `RZ_L(S)` lies in `RZ_L(T)` for a
local stable piece `T`, and for any two local stable pieces `T₁, T₂` every valuation ring of
`RZ_L(T₁) ∩ RZ_L(T₂)` lies in `RZ_L(T')` for a comparison piece `T'`, then there are an alteration
`p : S'' ⟶ S` which is a refinement of `(S, η)` and `β : X ⟶ C ×_S S''`, proper, with marks `D'`
such that `(X, D')` is a semi-stable pair over `S''` satisfying the generic marks condition,
numerically stable, projective (relative to `Spec k`) over the members of a finite open cover of
`S''`, and an isomorphism over a nonempty open of `S''`. -/
theorem exists_glued_model [IsLocallyNoetherian S] [S.IsSeparated] [CompactSpace S]
    [Algebra.IsAlgebraic S.functionField L]
    (hpiece : ∀ W ∈ ofScheme (functionFieldPoint S L),
      ∃ P : LocalStablePiece pS g D L, W ∈ ofScheme P.ηT)
    (hcomp : ∀ (P₁ P₂ : LocalStablePiece pS g D L) (W : RiemannZariskiSpace L),
      W ∈ ofScheme P₁.ηT → W ∈ ofScheme P₂.ηT → ∃ Q : ComparisonPiece P₁ P₂, W ∈ ofScheme Q.η) :
    ∃ (S'' : Scheme.{u}) (_ : IsIntegral S'') (p : S'' ⟶ S) (η'' : Spec (.of L) ⟶ S'')
      (X : Scheme.{u}) (β : X ⟶ pullback (C := Scheme.{u}) g p) (D' : X.IdealSheafData)
      (ι : Type u) (_ : Finite ι)
      (U : ι → S''.Opens),
      IsAlteration p ∧ IsRefinement (functionFieldPoint S L) p η'' ∧
      IsProper β ∧ IsSemistablePair (β ≫ pullback.snd g p) D' ∧
      GenericMarksCondition (pullback.snd g p) (D.comap (pullback.fst g p)) β D' ∧
      IsNumericallyStable β (pullback.snd g p) D' ∧ ⨆ i, U i = ⊤ ∧
      (∀ i, IsRelativelyProjective (((pullback.snd g p) ⁻¹ᵁ U i).ι ≫ pullback.snd g p ≫ p ≫ pS)
        (β ∣_ ((pullback.snd g p) ⁻¹ᵁ U i))) ∧
      ∃ U₀ : S''.Opens, (U₀ : Set S'').Nonempty ∧ QuasiCompact U₀.ι ∧
        IsIso (β ∣_ ((pullback.snd g p) ⁻¹ᵁ U₀)) := by
  classical
  set η := functionFieldPoint S L with hηdef
  -- finitely many local stable pieces
  let Pf : ofScheme η → LocalStablePiece pS g D L := fun W ↦ (hpiece W.1 W.2).choose
  have hPf : ∀ W : ofScheme η, W.1 ∈ ofScheme (Pf W).ηT := fun W ↦ (hpiece W.1 W.2).choose_spec
  obtain ⟨s, hs⟩ := exists_finset_cover_ofScheme (isCompact_ofScheme (η := η)) le_rfl
    (fun W ↦ (Pf W).t) (fun W ↦ (Pf W).ηT) (fun W ↦ (Pf W).comp_ηT)
    (fun W hW ↦ Set.mem_iUnion.mpr ⟨⟨W, hW⟩, hPf ⟨W, hW⟩⟩)
  let J : Type u := ↥s
  let P : J → LocalStablePiece pS g D L := fun a ↦ Pf a.1
  have hPcov : ∀ W ∈ ofScheme η, ∃ a : J, W ∈ ofScheme (P a).ηT := by
    intro W hW
    have := hs hW
    simp only [Set.mem_iUnion] at this
    obtain ⟨i, hi, hW'⟩ := this
    exact ⟨⟨i, hi⟩, hW'⟩
  -- finitely many comparison pieces for each pair
  have hK : ∀ a b : J, IsCompact (ofScheme (P a).ηT ∩ ofScheme (P b).ηT) := fun a b ↦
    ((isPatchClosed_ofScheme (η := (P a).ηT)).inter
      (isPatchClosed_ofScheme (η := (P b).ηT))).isCompact
  have hKη : ∀ a b : J, ofScheme (P a).ηT ∩ ofScheme (P b).ηT ⊆ ofScheme η := fun a b ↦
    Set.inter_subset_left.trans (ofScheme_subset_of_comp (P a).t (P a).comp_ηT)
  let Qf : ∀ a b : J, ↥(ofScheme (P a).ηT ∩ ofScheme (P b).ηT) → ComparisonPiece (P a) (P b) :=
    fun a b W ↦ (hcomp (P a) (P b) W.1 W.2.1 W.2.2).choose
  have hQf : ∀ a b W, W.1 ∈ ofScheme (Qf a b W).η := fun a b W ↦
    (hcomp (P a) (P b) W.1 W.2.1 W.2.2).choose_spec
  have hQη : ∀ a b W, (Qf a b W).η ≫ (Qf a b W).c₁ ≫ (P a).t = η := fun a b W ↦ by
    rw [← Category.assoc, (Qf a b W).comp_η₁, (P a).comp_ηT]
  choose sQ hsQ using fun a b : J ↦ exists_finset_cover_ofScheme (hK a b) (hKη a b)
    (fun W ↦ (Qf a b W).c₁ ≫ (P a).t) (fun W ↦ (Qf a b W).η) (hQη a b)
    (fun W hW ↦ Set.mem_iUnion.mpr ⟨⟨W, hW⟩, hQf a b ⟨W, hW⟩⟩)
  let M : J → J → Type u := fun a b ↦ ↥(sQ a b)
  let Q : ∀ a b : J, M a b → ComparisonPiece (P a) (P b) := fun a b m ↦ Qf a b m.1
  have hQcov : ∀ a b (W : RiemannZariskiSpace L), W ∈ ofScheme (P a).ηT →
      W ∈ ofScheme (P b).ηT → ∃ m : M a b, W ∈ ofScheme (Q a b m).η := by
    intro a b W ha hb
    have := hsQ a b ⟨ha, hb⟩
    simp only [Set.mem_iUnion] at this
    obtain ⟨i, hi, hW'⟩ := this
    exact ⟨⟨i, hi⟩, hW'⟩
  -- one refinement realising all the pieces
  let κ := J ⊕ (Σ ab : J × J, M ab.1 ab.2)
  let Tκ : κ → Scheme.{u} := Sum.elim (fun a ↦ (P a).T) (fun x ↦ (Q x.1.1 x.1.2 x.2).T)
  let gκ : ∀ i, Tκ i ⟶ S := fun i ↦ match i with
    | .inl a => (P a).t
    | .inr x => (Q x.1.1 x.1.2 x.2).c₁ ≫ (P x.1.1).t
  let ηκ : ∀ i, Spec (.of L) ⟶ Tκ i := fun i ↦ match i with
    | .inl a => (P a).ηT
    | .inr x => (Q x.1.1 x.1.2 x.2).η
  have hηκ : ∀ i, ηκ i ≫ gκ i = η := fun i ↦ match i with
    | .inl a => (P a).comp_ηT
    | .inr x => hQη x.1.1 x.1.2 x.2.1
  let Vκ : κ → S.Opens := Sum.elim (fun a ↦ (P a).V) (fun x ↦ (P x.1.1).V)
  have hVκ : ∀ i, IsAffineOpen (Vκ i) := fun i ↦ match i with
    | .inl a => (P a).isAffineOpen
    | .inr x => (P x.1.1).isAffineOpen
  have hgVκ : ∀ i, gκ i ⁻¹ᵁ Vκ i = ⊤ := fun i ↦ match i with
    | .inl a => (P a).preimage_eq_top
    | .inr x => by
      change ((Q x.1.1 x.1.2 x.2).c₁ ≫ (P x.1.1).t) ⁻¹ᵁ (P x.1.1).V = ⊤
      rw [Scheme.Hom.comp_preimage, (P x.1.1).preimage_eq_top, Scheme.Hom.preimage_top]
  have : ∀ i, IsAffine (Tκ i) := fun i ↦ match i with
    | .inl a => (P a).isAffine
    | .inr x => (Q x.1.1 x.1.2 x.2).isAffine
  have : ∀ i, LocallyOfFiniteType (gκ i) := fun i ↦ match i with
    | .inl a => (P a).locallyOfFiniteType
    | .inr x => (Q x.1.1 x.1.2 x.2).locallyOfFiniteType
  obtain ⟨S'', p, η'', Wr, hr, hAlt, hRef, hprop, hRZ, -⟩ :=
    exists_refinement_isAlteration Tκ gκ ηκ hηκ Vκ hVκ hgVκ
  -- the realising morphisms, with their types made explicit
  have hrA : ∀ a : J, ∃ hA : (Wr (.inl a)).toScheme ⟶ (P a).T, IsProper hA ∧
      hA ≫ (P a).t = (Wr (.inl a)).ι ≫ p ∧ ∃ e : Spec (.of L) ⟶ (Wr (.inl a)).toScheme,
        e ≫ (Wr (.inl a)).ι = η'' ∧ e ≫ hA = (P a).ηT ∧ IsDominant e :=
    fun a ↦ ⟨hr (.inl a), hprop (.inl a)⟩
  choose hA hAp hAc eA heA heA' heAd using hrA
  have hrQ : ∀ (a b : J) (m : M a b), ∃ hB : (Wr (.inr ⟨(a, b), m⟩)).toScheme ⟶ (Q a b m).T,
      hB ≫ (Q a b m).c₁ ≫ (P a).t = (Wr (.inr ⟨(a, b), m⟩)).ι ≫ p ∧
      ∃ e : Spec (.of L) ⟶ (Wr (.inr ⟨(a, b), m⟩)).toScheme,
        e ≫ (Wr (.inr ⟨(a, b), m⟩)).ι = η'' ∧ e ≫ hB = (Q a b m).η :=
    fun a b m ↦ ⟨hr (.inr ⟨(a, b), m⟩), (hprop _).2.1, (hprop _).2.2.choose,
      (hprop _).2.2.choose_spec.1, (hprop _).2.2.choose_spec.2.1⟩
  choose hB hBc eB heB heB' using hrQ
  have : IsIntegral S'' := hRef.isIntegral
  have : IsProper p := hRef.isProper
  have : IsDominant η'' := hRef.isDominant
  have : IsLocallyNoetherian S'' := LocallyOfFiniteType.isLocallyNoetherian p
  have : S''.IsSeparated := isSeparated_of_isProper p
  -- the opens realising the local stable pieces cover `S''`
  have hcovW : ⨆ a : J, Wr (.inl a) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨V, ψ, hψ, rfl⟩ := hRef.exists_extension x
    have hV : V ∈ ofScheme η := ⟨ψ ≫ p, by rw [← Category.assoc, hψ, hRef.comp_eq]⟩
    obtain ⟨a, ha⟩ := hPcov V hV
    obtain ⟨ψ', hψ', hψ'W⟩ := hRZ (.inl a) V ha
    rw [extension_unique hψ hψ']
    exact Opens.mem_iSup.2 ⟨a, hψ'W⟩
  -- the base changes of the local stable pieces
  have hX : ∀ a : J, IsStableModelOn (p ≫ pS) (pullback.snd g p) (D.comap (pullback.fst g p))
      (Wr (.inl a)) ((P a).bcMap p (Wr (.inl a)) (hA a) (hAc a))
      ((P a).bcMarks (Wr (.inl a)) (hA a)) := fun a ↦ by
    have : Nonempty (Wr (.inl a)) := ⟨eA a (Classical.arbitrary _)⟩
    have := hAp a
    have := heAd a
    exact (P a).isStableModelOn p (Wr (.inl a)) (hA a) (hAc a) (eA a) (heA' a)
  -- the local morphisms on the overlaps
  have hloc : ∀ (a b : J) (x : pullback (C := Scheme.{u})
      ((P a).β ≫ pullback.snd g (P a).t) (hA a)),
      ((P a).bcMap p (Wr (.inl a)) (hA a) (hAc a) ≫ pullback.snd g p) x ∈ Wr (.inl b) →
      ∃ V : (pullback (C := Scheme.{u}) ((P a).β ≫ pullback.snd g (P a).t) (hA a)).Opens,
        x ∈ V ∧ V ≤ ((P a).bcMap p (Wr (.inl a)) (hA a) (hAc a) ≫
          pullback.snd g p) ⁻¹ᵁ Wr (.inl b) ∧
        ∃ m : V.toScheme ⟶ pullback (C := Scheme.{u}) ((P b).β ≫ pullback.snd g (P b).t)
          (hA b),
          m ≫ (P b).bcMap p (Wr (.inl b)) (hA b) (hAc b) =
            V.ι ≫ (P a).bcMap p (Wr (.inl a)) (hA a) (hAc a) := by
    intro a b x hx
    have hya : ((P a).bcMap p (Wr (.inl a)) (hA a) (hAc a) ≫ pullback.snd g p) x ∈
        Wr (.inl a) := by
      rw [(P a).bcMap_snd, Scheme.Hom.comp_apply]
      exact (pullback.snd _ (hA a) x).2
    obtain ⟨V, ψ, hψ, hψy⟩ := hRef.exists_extension
      (((P a).bcMap p (Wr (.inl a)) (hA a) (hAc a) ≫ pullback.snd g p) x)
    have hVa : V ∈ ofScheme (P a).ηT :=
      mem_ofScheme_of_mem_open ψ hψ (by rw [hψy]; exact hya) (hA a) (eA a) (heA a) (heA' a)
    have hVb : V ∈ ofScheme (P b).ηT :=
      mem_ofScheme_of_mem_open ψ hψ (by rw [hψy]; exact hx) (hA b) (eA b) (heA b) (heA' b)
    obtain ⟨m, hm⟩ := hQcov a b V hVa hVb
    obtain ⟨ψ', hψ', hψ'O⟩ := hRZ (.inr ⟨(a, b), m⟩) V hm
    have hyO : ((P a).bcMap p (Wr (.inl a)) (hA a) (hAc a) ≫ pullback.snd g p) x ∈
        Wr (.inr ⟨(a, b), m⟩) := by
      rw [← hψy, extension_unique hψ hψ']
      exact hψ'O
    exact LocalStablePiece.exists_local_hom p η'' (P a) (P b) (Q a b m) (Wr (.inl a))
      (Wr (.inl b)) (Wr (.inr ⟨(a, b), m⟩)) (hA a) (hA b) (hB a b m) (hAc a) (hAc b)
      (hBc a b m) (eA a) (heA a) (heA' a) (eA b) (heA b) (heA' b) (eB a b m) (heB a b m)
      (heB' a b m) x ⟨hx, hyO⟩
  obtain ⟨Xg, βg, Dg, hprop', hss, hgm, hns, hproj, hiso⟩ :=
    exists_glue_isStableModelOn (ι := J) (U := fun a ↦ Wr (.inl a)) hcovW hX hloc
  exact ⟨S'', inferInstance, p, η'', Xg, βg, Dg, J, inferInstance, fun a ↦ Wr (.inl a), hAlt,
    hRef, hprop', hss, hgm, hns, hcovW, hproj, hiso⟩

end DeJongAlterations.StableModification.Global
