import DeJongAlterations.StableModification.Limits.Descent

/-!
# Descent of properties local on the source

Let `D : I ⥤ Scheme` be a cofiltered system of affine schemes with affine transition morphisms,
indexed by a thin category, with limit cone `c`, and let `m` be a model of finite presentation at
level `i₀` of a scheme `f : X ⟶ lim D` (lane LIM1, `Limits.Descent`). Let `P` be a property of
morphisms of schemes which is local on the source and stable under base change. If every affine
open `W ⊆ X` has *some* model of finite presentation `M` (at any level) with `P M.fY`, then
`P` holds for the base change of the given model `m` to some level
(`exists_baseChange_of_forall_isAffineOpen`).

This is the scheme-level form of "approximation" of EGA IV 8.10.5 / 17.7.8 used by Temkin,
*Stable modification of relative curves*, §3.1 (T:2262–2298), for properties of morphisms whose
algebras have noetherian models: smooth and étale algebras (Mathlib's
`Algebra.Smooth.exists_subalgebra_fg`, `Algebra.Etale.exists_subalgebra_fg`, used in
`Limits.SpreadMarks`). The proof:

* cover `X` by finitely many affine opens `W`; each `W` is the preimage of a quasi-compact open
  `O ⊆ Y_j` at some level (EGA IV 8.2.11, Mathlib's `exists_preimage_eq`), so `O` is a model of
  `W`, and LIM1's descent of isomorphisms (`exists_iso_of_iso`) identifies its base change with
  that of the `P`-model of `W` at some lower level (`exists_opens_of_isCompact`);
* `P` is stable under base change, so it persists for the preimages of `O` at lower levels
  (`baseChange_restrict`);
* at a common level the union of these opens contains the image of `X`, hence the image of some
  `Y_{j'}` (EGA IV 8.3.3, Mathlib's `exists_map_eq_top`), and `P` is local on the source.

Blueprint: `sm-spread.tex`, `lem:sm-spread-local-property`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace DeJongAlterations.StableModification.Limits.Spread

universe u

set_option backward.isDefEq.respectTransparency false

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} {c : Cone D}
  (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
  {X : Scheme.{u}} {f : X ⟶ c.pt} {i₀ : I} (m : Model D c f i₀)

/-- **Restriction to a preimage persists.** If `P` holds for an open `V ⊆ Y_j` of the base change
system, it holds for the preimage of `V` in `Y_{j'}` for every `j' → j`. -/
theorem baseChange_restrict {j j' : Over i₀} (a : j' ⟶ j)
    (V : ((baseChangeDiagram D m.fY).obj j).Opens)
    (hV : P (V.ι ≫ pullback.snd m.fY (D.map j.hom))) :
    P (((baseChangeDiagram D m.fY).map a ⁻¹ᵁ V).ι ≫ pullback.snd m.fY (D.map j'.hom)) :=
  P.of_isPullback ((isPullback_morphismRestrict _ V).paste_vert
    (isPullback_baseChangeDiagram_map D m.fY a)) hV

omit [P.IsStableUnderBaseChange] in
/-- The restriction of a model of finite presentation to a quasi-compact open is of finite
presentation. -/
theorem isFP_restrict [∀ j, IsAffine (D.obj j)] {j : I} {r : Model D c f j} (hr : r.IsFP)
    (O : r.Y.Opens) (hO : IsCompact (O : Set r.Y)) : (r.restrict O).IsFP := by
  obtain ⟨_, _, _⟩ := hr
  have : CompactSpace O := isCompact_iff_compactSpace.mp hO
  refine ⟨inferInstanceAs (LocallyOfFinitePresentation (O.ι ≫ r.fY)), ?_,
    inferInstanceAs (QuasiSeparated (O.ι ≫ r.fY))⟩
  exact HasAffineProperty.iff_of_isAffine (P := @QuasiCompact) (f := O.ι ≫ r.fY) |>.mpr
    inferInstance

variable (hc : IsLimit c) [IsCofiltered I] [Quiver.IsThin I]
  [∀ {j k : I} (g : j ⟶ k), IsAffineHom (D.map g)] [∀ j, IsAffine (D.obj j)]
  [IsZariskiLocalAtSource P]

include hc in
/-- **Quasi-compact pieces.** Let `W ⊆ X` be a quasi-compact open with a model of finite
presentation `M` such that `P M.fY`. Then for some level `J` there is an open `V ⊆ Y_J` whose
preimage in `X` is `W` and such that `P` holds for `V ⟶ D_J`. -/
theorem exists_opens_of_isCompact (hm : m.IsFP) (W : X.Opens) (hW : IsCompact (W : Set X))
    (HP : ∀ W' : X.Opens, W' = W →
      ∃ (k : I) (M : Model D c (W'.ι ≫ f) k), M.IsFP ∧ P M.fY) :
    ∃ (J : Over i₀) (V : ((baseChangeDiagram D m.fY).obj J).Opens),
      (baseChangeCone D c m.isPullback).π.app J ⁻¹ᵁ V = W ∧
        P (V.ι ≫ pullback.snd m.fY (D.map J.hom)) := by
  obtain ⟨_, _, _⟩ := hm
  have hc' := isLimitBaseChangeCone D c hc m.isPullback
  obtain ⟨j, O, hOc, hO⟩ := exists_preimage_eq (baseChangeDiagram D m.fY)
    (baseChangeCone D c m.isPullback) hc' W hW
  -- the restricted model of `W`, and the `P`-model of `W`
  let mj := m.baseChange j.hom
  have hmj : mj.IsFP := Model.IsFP.baseChange ⟨‹_›, ‹_›, ‹_›⟩ j.hom
  let r := mj.restrict O
  have hr : r.IsFP := isFP_restrict hmj O hOc
  obtain ⟨k, M, hM, hPM⟩ := HP (mj.g ⁻¹ᵁ O) hO
  -- bring both models to a common level and compare them
  let k₁ := IsCofiltered.min j.left k
  let g₁ : k₁ ⟶ j.left := IsCofiltered.minToLeft j.left k
  let g₂ : k₁ ⟶ k := IsCofiltered.minToRight j.left k
  have hr' : (r.baseChange g₁).IsFP := hr.baseChange g₁
  have hM' : (M.baseChange g₂).IsFP := hM.baseChange g₂
  obtain ⟨_, _, _⟩ := hr'
  obtain ⟨_, _, _⟩ := hM'
  obtain ⟨l, Θ, hΘ, -⟩ := exists_iso_of_iso D c hc (r.baseChange g₁) (M.baseChange g₂)
    (Iso.refl _) (by simp)
  have hPM' : P (M.baseChange g₂).fY :=
    P.of_isPullback (IsPullback.of_hasPullback M.fY (D.map g₂)) hPM
  have hPM'' : P (pullback.snd (M.baseChange g₂).fY (D.map l.hom)) :=
    P.of_isPullback (IsPullback.of_hasPullback _ (D.map l.hom)) hPM'
  have hPr : P (pullback.snd (r.baseChange g₁).fY (D.map l.hom)) := by
    rw [← hΘ]
    exact (MorphismProperty.cancel_left_of_respectsIso P Θ.hom _).mpr hPM''
  -- the open `V` at level `J`
  let J : Over i₀ := Over.mk (l.hom ≫ g₁ ≫ j.hom)
  let a : J ⟶ j := Over.homMk (l.hom ≫ g₁) (by simp [J])
  let V := (baseChangeDiagram D m.fY).map a ⁻¹ᵁ O
  have hA : IsPullback ((baseChangeDiagram D m.fY).map a ∣_ O)
      (V.ι ≫ pullback.snd m.fY (D.map J.hom)) (O.ι ≫ pullback.snd m.fY (D.map j.hom))
      (D.map l.hom ≫ D.map g₁) := by
    have := (isPullback_morphismRestrict _ O).paste_vert
      (isPullback_baseChangeDiagram_map D m.fY a)
    rwa [show a.left = l.hom ≫ g₁ from rfl, D.map_comp] at this
  have hB : IsPullback
      (pullback.fst (r.baseChange g₁).fY (D.map l.hom) ≫ pullback.fst r.fY (D.map g₁))
      (pullback.snd (r.baseChange g₁).fY (D.map l.hom)) r.fY (D.map l.hom ≫ D.map g₁) :=
    (IsPullback.of_hasPullback (r.baseChange g₁).fY (D.map l.hom)).paste_horiz
      (IsPullback.of_hasPullback r.fY (D.map g₁))
  have hPV : P (V.ι ≫ pullback.snd m.fY (D.map J.hom)) := by
    rw [← hA.isoIsPullback_hom_snd _ _ hB]
    exact (MorphismProperty.cancel_left_of_respectsIso P _ _).mpr hPr
  refine ⟨J, V, ?_, hPV⟩
  rw [← Scheme.Hom.comp_preimage, (baseChangeCone D c m.isPullback).w a]
  exact hO

include hc in
/-- **Descent of properties local on the source** (EGA IV 8.10.5, 17.7.8, in the form of
Temkin §3.1). Let `P` be local on the source and stable under base change, and let `m` be a
model of finite presentation of `f : X ⟶ lim D`. If every affine open of `X` has a model of
finite presentation satisfying `P`, then `P` holds for the base change of `m` to some level. -/
theorem exists_baseChange_of_forall_isAffineOpen (hm : m.IsFP)
    (HP : ∀ W : X.Opens, IsAffineOpen W →
      ∃ (k : I) (M : Model D c (W.ι ≫ f) k), M.IsFP ∧ P M.fY) :
    ∃ (j : I) (h : j ⟶ i₀), P (m.baseChange h).fY := by
  classical
  obtain ⟨_, _, _⟩ := hm
  have hc' := isLimitBaseChangeCone D c hc m.isPullback
  have : CompactSpace X := Scheme.compactSpace_of_isLimit _ _ hc'
  obtain ⟨s, hs, hsf, hsup⟩ :=
    X.isBasis_affineOpens.exists_finite_of_isCompact (U := ⊤) isCompact_univ
  have key : ∀ W : s, ∃ (J : Over i₀) (V : ((baseChangeDiagram D m.fY).obj J).Opens),
      (baseChangeCone D c m.isPullback).π.app J ⁻¹ᵁ V = W.1 ∧
        P (V.ι ≫ pullback.snd m.fY (D.map J.hom)) := fun W ↦
    exists_opens_of_isCompact P m hc ⟨‹_›, ‹_›, ‹_›⟩ W (hs W.2).isCompact
      (fun W' hW' ↦ by subst hW'; exact HP _ (hs W.2))
  choose J V hV hPV using key
  have : Finite s := hsf
  have : Fintype s := Fintype.ofFinite _
  obtain ⟨L, hL⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image J)
  let a : ∀ W : s, L ⟶ J W := fun W ↦
    (hL (Finset.mem_image_of_mem _ (Finset.mem_univ W))).some
  let U : ((baseChangeDiagram D m.fY).obj L).Opens :=
    ⨆ W : s, (baseChangeDiagram D m.fY).map (a W) ⁻¹ᵁ V W
  have hU : (baseChangeCone D c m.isPullback).π.app L ⁻¹ᵁ U = ⊤ := by
    simp only [U, Scheme.Hom.preimage_iSup, ← Scheme.Hom.comp_preimage,
      (baseChangeCone D c m.isPullback).w, hV]
    rw [hsup, sSup_eq_iSup']
  obtain ⟨L', b, hb⟩ := exists_map_eq_top _ _ hc' U hU
  refine ⟨L'.left, L'.hom, ?_⟩
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := P)
    (fun W : s ↦ (baseChangeDiagram D m.fY).map (b ≫ a W) ⁻¹ᵁ V W) ?_
    fun W ↦ baseChange_restrict P m (b ≫ a W) (V W) (hPV W)
  simp only [Functor.map_comp, Scheme.Hom.comp_preimage]
  rw [← Scheme.Hom.preimage_iSup]
  exact hb

end DeJongAlterations.StableModification.Limits.Spread
