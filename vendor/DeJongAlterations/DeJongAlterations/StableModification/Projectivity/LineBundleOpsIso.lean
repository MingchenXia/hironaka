/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane OM3A)
-/
import DeJongAlterations.StableModification.Projectivity.LineBundleTwistFunctor

/-!
# Isomorphisms of line-bundle data

Blueprint `sm-projectivity-core.tex`, `lem:sm-lbd-iso` (PLAN-OM3 M1, "iso of LBDs (cohomologous
cocycles)"). Line-bundle data `L` (charts `U i`, generators `e i`) and `L'` (charts `V a`,
generators `f a`) on the same scheme, possibly with different covers, are isomorphic through
units `w i a ∈ Γ(U i ∩ V a, 𝒪_X)ˣ` with `f a = w i a · e i`; the compatibility with the cocycles is
`u'_{ab} · w i a = u_{ij} · w j b` on `U i ∩ V a ∩ U j ∩ V b` (`LineBundleData.IsoData`). Such data
give isomorphisms `F ⊗ 𝓛^m ≅ F ⊗ 𝓛'^m` for all modules `F` and all `m`
(`IsoData.twistIso`): the `a`-th coefficient of the image of `t` is glued from
`(w i a)^{-m} t_i` over the charts `U i`.

The data are produced from an isomorphism of the line bundles themselves, `𝒪 ⊗ 𝓛 ≅ 𝒪 ⊗ 𝓛'`
(`IsoData.ofIso`): `w i a` is the `i`-th coefficient of the preimage of the generator `f a`.
Hence an isomorphism of line bundles (e.g. `ν^* ω ≅ Ω¹(E)`, lane OM3D) transports twists of all
modules by all powers (`twistIsoOfIso`), as needed for fibre-ampleness: `SerreAmple L` is the
condition of `FiberAmple` for line-bundle data on any scheme (`fiberAmple_iff_serreAmple`), and it
is invariant under isomorphisms (`SerreAmple.of_isoData`, `SerreAmple.of_iso`).
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Limits

namespace DeJongAlterations.StableModification.Projectivity

noncomputable section

variable {X : Scheme.{u}}

namespace LineBundleData

/-! ### Gluing along the charts -/

section Glue

variable (L : LineBundleData X) (F : X.Modules)

/-- Local sections of `F` over `W ∩ U i` which agree on overlaps glue to a section over `W`. -/
lemma exists_glue_cover (W : X.Opens) (A : ∀ i, Γ(F, W ⊓ L.U i))
    (hA : ∀ i j, F.presheaf.map (homOfLE (L.le_left W i j)).op (A i) =
      F.presheaf.map (homOfLE (L.le_right W i j)).op (A j)) :
    ∃ s : Γ(F, W), ∀ i, F.presheaf.map (homOfLE (inf_le_left : W ⊓ L.U i ≤ W)).op s = A i := by
  obtain ⟨s, hs⟩ := L.toTwistZero_surjective F W
    ⟨A, fun i j => by
      rw [L.transPow_zero, one_smul]
      exact hA i j⟩
  exact ⟨s, fun i => congrFun (congrArg Subtype.val hs) i⟩

/-- Sections of `F` over `W` which agree on every `W ∩ U i` are equal. -/
lemma eq_of_forall_chart {W : X.Opens} {s s' : Γ(F, W)}
    (h : ∀ i, F.presheaf.map (homOfLE (inf_le_left : W ⊓ L.U i ≤ W)).op s =
      F.presheaf.map (homOfLE (inf_le_left : W ⊓ L.U i ≤ W)).op s') : s = s' :=
  L.toTwistZero_injective F W (Subtype.ext (funext h))

end Glue

/-! ### Isomorphism data -/

lemma map_res_trans {V₁ V₂ V₃ : X.Opens} (h₁ : V₂ ≤ V₁) (h₂ : V₃ ≤ V₂) (r : Γ(X, V₁)) :
    X.presheaf.map (homOfLE h₂).op (res h₁ r) = res (h₂.trans h₁) r :=
  res_res h₁ h₂ _ r

/-- Restriction of units along `V ≤ W`. -/
abbrev resUnit {V W : X.Opens} (h : V ≤ W) : Γ(X, W)ˣ →* Γ(X, V)ˣ :=
  Units.map (res h).toMonoidHom

lemma coe_resUnit {V W : X.Opens} (h : V ≤ W) (v : Γ(X, W)ˣ) :
    ((resUnit h v : Γ(X, V)ˣ) : Γ(X, V)) = X.presheaf.map (homOfLE h).op (v : Γ(X, W)) :=
  rfl

lemma resUnit_resUnit {V₁ V₂ V₃ : X.Opens} (h₁ : V₂ ≤ V₁) (h₂ : V₃ ≤ V₂) (v : Γ(X, V₁)ˣ) :
    resUnit h₂ (resUnit h₁ v) = resUnit (h₂.trans h₁) v :=
  Units.ext (res_res h₁ h₂ _ _)

lemma resUnit_trans (L : LineBundleData X) {i j : L.ι} {V V' : X.Opens}
    (h : V ≤ L.U i ⊓ L.U j) (h' : V' ≤ V) :
    resUnit h' (L.trans h) = L.trans (h'.trans h) :=
  Units.ext (L.res_trans h h')

/-- **Isomorphism data** between line-bundle data `L` (charts `U i`, generators `e i`) and `L'`
(charts `V a`, generators `f a`): units `w i a` on `U i ∩ V a` with `f a = w i a · e i`, so that
`u'_{ab} · w i a = u_{ij} · w j b` on `U i ∩ V a ∩ U j ∩ V b`. -/
structure IsoData (L L' : LineBundleData X) where
  /-- The comparison units `f a = w i a · e i`. -/
  w : ∀ (i : L.ι) (a : L'.ι), Γ(X, L.U i ⊓ L'.U a)ˣ
  compat : ∀ (i j : L.ι) (a b : L'.ι) {V : X.Opens}
    (hV : V ≤ (L.U i ⊓ L'.U a) ⊓ (L.U j ⊓ L'.U b)),
    L'.trans (i := a) (j := b)
        (le_inf ((hV.trans inf_le_left).trans inf_le_right)
          ((hV.trans inf_le_right).trans inf_le_right)) *
        resUnit (hV.trans inf_le_left) (w i a) =
      L.trans (i := i) (j := j)
        (le_inf ((hV.trans inf_le_left).trans inf_le_left)
          ((hV.trans inf_le_right).trans inf_le_left)) *
        resUnit (hV.trans inf_le_right) (w j b)

namespace IsoData

variable {L L' : LineBundleData X} (E : IsoData L L')

/-- The comparison unit `w i a` restricted to `V ⊆ U i ∩ V a`. -/
abbrev wRes (i : L.ι) (a : L'.ι) {V : X.Opens} (h : V ≤ L.U i ⊓ L'.U a) : Γ(X, V)ˣ :=
  resUnit h (E.w i a)

/-- Same chart of `L'`: `w i a = u i j · w j a`. -/
lemma compat_left (i j : L.ι) (a : L'.ι) {V : X.Opens} (h₁ : V ≤ L.U i ⊓ L'.U a)
    (h₂ : V ≤ L.U i ⊓ L.U j) (h₃ : V ≤ L.U j ⊓ L'.U a) :
    E.wRes i a h₁ = L.trans h₂ * E.wRes j a h₃ := by
  have e := E.compat i j a a (V := V) (le_inf h₁ h₃)
  rwa [L'.trans_self, one_mul] at e

/-- Same chart of `L`: `u'_{ab} · w i a = w i b`. -/
lemma compat_right (i : L.ι) (a b : L'.ι) {V : X.Opens} (h₁ : V ≤ L.U i ⊓ L'.U a)
    (h₂ : V ≤ L'.U a ⊓ L'.U b) (h₃ : V ≤ L.U i ⊓ L'.U b) :
    L'.trans h₂ * E.wRes i a h₁ = E.wRes i b h₃ := by
  have e := E.compat i i a b (V := V) (le_inf h₁ h₃)
  rwa [L.trans_self, one_mul] at e

/-! #### The map on sections -/

variable (F : X.Modules) (m : ℤ)

lemma le_piece (W : X.Opens) (i : L.ι) (a : L'.ι) :
    (W ⊓ L'.U a) ⊓ L.U i ≤ L.U i ⊓ L'.U a :=
  fun _ hx => ⟨hx.2, hx.1.2⟩

lemma le_piece' (W : X.Opens) (i : L.ι) (a : L'.ι) :
    (W ⊓ L'.U a) ⊓ L.U i ≤ W ⊓ L.U i :=
  fun _ hx => ⟨hx.1.1, hx.2⟩

/-- The local pieces `(w i a)^{-m} · t_i` on `W ∩ V a ∩ U i`. -/
def piece {W : X.Opens} (t : L.twistSubgroup F m W) (a : L'.ι) (i : L.ι) :
    Γ(F, (W ⊓ L'.U a) ⊓ L.U i) :=
  (((E.wRes i a (le_piece W i a))⁻¹ ^ m : Γ(X, (W ⊓ L'.U a) ⊓ L.U i)ˣ) :
      Γ(X, (W ⊓ L'.U a) ⊓ L.U i)) •
    F.presheaf.map (homOfLE (le_piece' W i a)).op (t.1 i)

/-- Restriction of a piece to a smaller open `V`. -/
lemma map_piece {W V : X.Opens} (t : L.twistSubgroup F m W) (a : L'.ι) (i : L.ι)
    (h : V ≤ (W ⊓ L'.U a) ⊓ L.U i) :
    F.presheaf.map (homOfLE h).op (E.piece F m t a i) =
      (((E.wRes i a (h.trans (le_piece W i a)))⁻¹ ^ m : Γ(X, V)ˣ) : Γ(X, V)) •
        F.presheaf.map (homOfLE (h.trans (le_piece' W i a))).op (t.1 i) := by
  rw [piece, Scheme.Modules.map_smul, Cohomology.presheaf_map_map F _ _ (h.trans (le_piece' W i a))]
  congr 1
  rw [← coe_resUnit, map_zpow, map_inv, resUnit_resUnit]

lemma piece_compatible {W : X.Opens} (t : L.twistSubgroup F m W) (a : L'.ι) (i j : L.ι) :
    F.presheaf.map (homOfLE (L.le_left (W ⊓ L'.U a) i j)).op (E.piece F m t a i) =
      F.presheaf.map (homOfLE (L.le_right (W ⊓ L'.U a) i j)).op (E.piece F m t a j) := by
  set V := (W ⊓ L'.U a) ⊓ (L.U i ⊓ L.U j)
  have hVW : V ≤ W ⊓ (L.U i ⊓ L.U j) := fun _ hx => ⟨hx.1.1, hx.2⟩
  rw [map_piece, map_piece]
  have ht := congrArg (F.presheaf.map (homOfLE hVW).op) (t.2 i j)
  rw [Cohomology.presheaf_map_map F _ _ (hVW.trans (L.le_left W i j)), Scheme.Modules.map_smul,
    Cohomology.presheaf_map_map F _ _ (hVW.trans (L.le_right W i j)),
    L.map_res_trans_zpow] at ht
  rw [ht, smul_smul]
  congr 1
  rw [← Units.val_mul, ← mul_zpow]
  congr 2
  rw [E.compat_left i j a _ (hVW.trans inf_le_right) _, mul_inv_rev, mul_assoc, inv_mul_cancel,
    mul_one]

/-- The `a`-th coefficient of the image: the glued pieces. -/
def glued {W : X.Opens} (t : L.twistSubgroup F m W) (a : L'.ι) : Γ(F, W ⊓ L'.U a) :=
  (L.exists_glue_cover F (W ⊓ L'.U a) (E.piece F m t a) (E.piece_compatible F m t a)).choose

lemma glued_spec {W : X.Opens} (t : L.twistSubgroup F m W) (a : L'.ι) (i : L.ι) :
    F.presheaf.map (homOfLE (inf_le_left : (W ⊓ L'.U a) ⊓ L.U i ≤ W ⊓ L'.U a)).op
      (E.glued F m t a) = E.piece F m t a i :=
  (L.exists_glue_cover F (W ⊓ L'.U a) (E.piece F m t a) (E.piece_compatible F m t a)).choose_spec i

/-- Restriction of the glued section to any open inside `W ∩ V a ∩ U i`. -/
lemma map_glued {W V : X.Opens} (t : L.twistSubgroup F m W) (a : L'.ι) (i : L.ι)
    (h : V ≤ (W ⊓ L'.U a) ⊓ L.U i) :
    F.presheaf.map (homOfLE (h.trans inf_le_left)).op (E.glued F m t a) =
      (((E.wRes i a (h.trans (le_piece W i a)))⁻¹ ^ m : Γ(X, V)ˣ) : Γ(X, V)) •
        F.presheaf.map (homOfLE (h.trans (le_piece' W i a))).op (t.1 i) := by
  rw [← E.map_piece F m t a i h, ← E.glued_spec F m t a i,
    Cohomology.presheaf_map_map F _ _ (h.trans inf_le_left)]

lemma glued_compatible {W : X.Opens} (t : L.twistSubgroup F m W) :
    L'.IsCompatible F m W (E.glued F m t) := by
  intro a b
  apply L.eq_of_forall_chart F
  intro i
  set V := (W ⊓ (L'.U a ⊓ L'.U b)) ⊓ L.U i
  have hVa : V ≤ (W ⊓ L'.U a) ⊓ L.U i := fun _ hx => ⟨⟨hx.1.1, hx.1.2.1⟩, hx.2⟩
  have hVb : V ≤ (W ⊓ L'.U b) ⊓ L.U i := fun _ hx => ⟨⟨hx.1.1, hx.1.2.2⟩, hx.2⟩
  rw [Cohomology.presheaf_map_map F _ _ (hVa.trans inf_le_left), E.map_glued F m t a i hVa,
    Scheme.Modules.map_smul, Cohomology.presheaf_map_map F _ _ (hVb.trans inf_le_left),
    E.map_glued F m t b i hVb, smul_smul, L'.map_res_trans_zpow]
  congr 1
  rw [← Units.val_mul, ← mul_zpow]
  congr 2
  rw [← E.compat_right i a b (hVa.trans (le_piece W i a))
      (le_inf (hVa.trans (inf_le_left.trans inf_le_right))
        (hVb.trans (inf_le_left.trans inf_le_right))) (hVb.trans (le_piece W i b)),
    mul_inv_rev, mul_comm (E.wRes i a _)⁻¹, ← mul_assoc, mul_inv_cancel, one_mul]

/-- The image of a section of `F ⊗ 𝓛^m` in `F ⊗ 𝓛'^m`. -/
def mapSections (W : X.Opens) (t : L.twistSubgroup F m W) : L'.twistSubgroup F m W :=
  ⟨E.glued F m t, E.glued_compatible F m t⟩

lemma mapSections_apply (W : X.Opens) (t : L.twistSubgroup F m W) (a : L'.ι) :
    (E.mapSections F m W t).1 a = E.glued F m t a :=
  rfl

lemma map_mapSections {W V : X.Opens} (t : L.twistSubgroup F m W) (a : L'.ι) (i : L.ι)
    (h : V ≤ (W ⊓ L'.U a) ⊓ L.U i) :
    F.presheaf.map (homOfLE (h.trans inf_le_left)).op ((E.mapSections F m W t).1 a) =
      (((E.wRes i a (h.trans (le_piece W i a)))⁻¹ ^ m : Γ(X, V)ˣ) : Γ(X, V)) •
        F.presheaf.map (homOfLE (h.trans (le_piece' W i a))).op (t.1 i) :=
  E.map_glued F m t a i h

/-- Characterization of `mapSections` by its local pieces. -/
lemma mapSections_eq_iff {W : X.Opens} (t : L.twistSubgroup F m W)
    (t' : L'.twistSubgroup F m W)
    (h : ∀ a i, F.presheaf.map (homOfLE (inf_le_left : (W ⊓ L'.U a) ⊓ L.U i ≤ W ⊓ L'.U a)).op
      (t'.1 a) = E.piece F m t a i) : E.mapSections F m W t = t' := by
  apply Subtype.ext
  funext a
  apply L.eq_of_forall_chart F
  intro i
  rw [h a i]
  exact E.glued_spec F m t a i

lemma mapSections_add {W : X.Opens} (t s : L.twistSubgroup F m W) :
    E.mapSections F m W (t + s) = E.mapSections F m W t + E.mapSections F m W s := by
  apply mapSections_eq_iff
  intro a i
  change F.presheaf.map _ ((E.mapSections F m W t).1 a + (E.mapSections F m W s).1 a) = _
  rw [map_add, mapSections_apply, mapSections_apply, E.glued_spec, E.glued_spec, piece, piece,
    piece]
  change _ = _ • F.presheaf.map _ (t.1 i + s.1 i)
  rw [map_add, smul_add]

lemma mapSections_smul {W : X.Opens} (r : Γ(X, W)) (t : L.twistSubgroup F m W) :
    E.mapSections F m W (r • t) = r • E.mapSections F m W t := by
  apply mapSections_eq_iff
  intro a i
  change F.presheaf.map _ (res _ r • (E.mapSections F m W t).1 a) = _
  rw [Scheme.Modules.map_smul, mapSections_apply, E.glued_spec, piece, piece]
  change _ = _ • F.presheaf.map _ (res _ r • t.1 i)
  rw [Scheme.Modules.map_smul, map_res_trans, map_res_trans]
  exact smul_comm _ _ _

lemma mapSections_restrict {W W' : X.Opens} (h : W' ≤ W) (t : L.twistSubgroup F m W) :
    E.mapSections F m W' (L.twistRestrict F m h t) =
      L'.twistRestrict F m h (E.mapSections F m W t) := by
  apply mapSections_eq_iff
  intro a i
  have hV : (W' ⊓ L'.U a) ⊓ L.U i ≤ (W ⊓ L'.U a) ⊓ L.U i :=
    inf_le_inf_right _ (inf_le_inf_right _ h)
  change F.presheaf.map _ (F.presheaf.map _ ((E.mapSections F m W t).1 a)) = _
  rw [Cohomology.presheaf_map_map F _ _ (hV.trans inf_le_left), E.map_mapSections F m t a i hV,
    piece]
  change _ = _ • F.presheaf.map _ (F.presheaf.map _ (t.1 i))
  rw [Cohomology.presheaf_map_map F _ _ (hV.trans (le_piece' W i a))]

/-- **The morphism of twists given by isomorphism data**, `F ⊗ 𝓛^m ⟶ F ⊗ 𝓛'^m`. -/
def twistHom : L.twist F m ⟶ L'.twist F m where
  val := PresheafOfModules.homMk
    { app := fun W => AddCommGrpCat.ofHom
        { toFun := E.mapSections F m W.unop
          map_zero' := by
            have := E.mapSections_add F m (0 : L.twistSubgroup F m W.unop) 0
            rw [add_zero] at this
            exact (add_eq_left.mp this.symm)
          map_add' := E.mapSections_add F m }
      naturality := fun {W W'} k => by
        ext t
        exact E.mapSections_restrict F m (leOfHom k.unop) t }
    (fun W r t => E.mapSections_smul F m r t)

lemma twistHom_app (W : X.Opens) (t : L.twistSubgroup F m W) :
    (E.twistHom F m).app W t = E.mapSections F m W t :=
  rfl

/-! #### The inverse -/

/-- The inverse isomorphism data, `e i = (w i a)^{-1} · f a`. -/
def symm : IsoData L' L where
  w a i := resUnit (inf_comm (L'.U a) (L.U i)).le (E.w i a)⁻¹
  compat a b i j {V} hV := by
    have hV' : V ≤ (L.U i ⊓ L'.U a) ⊓ (L.U j ⊓ L'.U b) :=
      fun _ hx => ⟨⟨(hV hx).1.2, (hV hx).1.1⟩, (hV hx).2.2, (hV hx).2.1⟩
    have e := E.compat i j a b hV'
    simp only [map_inv, resUnit_resUnit]
    rw [mul_inv_eq_iff_eq_mul, mul_assoc, mul_comm _ (resUnit _ (E.w i a)), ← mul_assoc, e,
      mul_assoc, mul_inv_cancel, mul_one]

lemma symm_wRes (i : L.ι) (a : L'.ι) {V : X.Opens} (h : V ≤ L'.U a ⊓ L.U i) :
    E.symm.wRes a i h = (E.wRes i a (h.trans (inf_comm (L'.U a) (L.U i)).le))⁻¹ := by
  rw [wRes, symm]
  dsimp only
  rw [map_inv, map_inv, resUnit_resUnit]

lemma mapSections_symm_mapSections (W : X.Opens) (t : L.twistSubgroup F m W) :
    E.symm.mapSections F m W (E.mapSections F m W t) = t := by
  apply mapSections_eq_iff
  intro i a
  rw [piece]
  have hV : (W ⊓ L.U i) ⊓ L'.U a ≤ (W ⊓ L'.U a) ⊓ L.U i :=
    fun _ hx => ⟨⟨hx.1.1, hx.2⟩, hx.1.2⟩
  have e := E.map_mapSections F m t a i hV
  have hle : (W ⊓ L.U i) ⊓ L'.U a ≤ W ⊓ L'.U a := hV.trans inf_le_left
  change _ = _ • F.presheaf.map (homOfLE hle).op ((E.mapSections F m W t).1 a)
  rw [e, smul_smul, symm_wRes, inv_inv, ← Units.val_mul, ← mul_zpow]
  rw [show E.wRes i a _ * (E.wRes i a _)⁻¹ = 1 from mul_inv_cancel _, one_zpow, Units.val_one,
    one_smul]

lemma symm_symm_w (i : L.ι) (a : L'.ι) : E.symm.symm.w i a = E.w i a := by
  change resUnit _ (resUnit _ (E.w i a)⁻¹)⁻¹ = E.w i a
  simp only [map_inv, inv_inv, resUnit_resUnit]
  exact Units.ext (res_self _ _)

lemma symm_symm : E.symm.symm = E := by
  obtain ⟨w, hw⟩ := E
  show IsoData.mk _ _ = IsoData.mk w hw
  congr 1
  funext i a
  exact symm_symm_w ⟨w, hw⟩ i a

/-- **Isomorphism data give isomorphic twists**: `F ⊗ 𝓛^m ≅ F ⊗ 𝓛'^m`. -/
def twistIso : L.twist F m ≅ L'.twist F m where
  hom := E.twistHom F m
  inv := E.symm.twistHom F m
  hom_inv_id := by
    ext W t
    exact E.mapSections_symm_mapSections F m W t
  inv_hom_id := by
    ext W t
    have := E.symm.mapSections_symm_mapSections F m W t
    rw [E.symm_symm] at this
    exact this

/-! #### Isomorphism data from an isomorphism of line bundles -/

section OfIso

/-- The section of `𝓛 = 𝒪 ⊗ 𝓛` over `V ⊆ U i` with `i`-th coefficient `1` (the generator
`e i`). -/
abbrev gen (L : LineBundleData X) {V : X.Opens} {i : L.ι} (h : V ≤ L.U i) :
    L.twistSubgroup (unitModule X) 1 V :=
  ofLocal (unitModule X) 1 h (1 : Γ(X, V))

/-- The `i`-th coefficient of a section of `𝓛` over `V ⊆ U i`, as a function. -/
abbrev coeffOne (L : LineBundleData X) {V : X.Opens} {i : L.ι} (h : V ≤ L.U i)
    (y : L.twistSubgroup (unitModule X) 1 V) : Γ(X, V) :=
  toLocal (unitModule X) 1 h y

lemma coeffOne_gen (L : LineBundleData X) {V : X.Opens} {i : L.ι} (h : V ≤ L.U i) :
    coeffOne L h (gen L h) = 1 :=
  toLocal_ofLocal _ _ _ _

lemma coeffOne_smul (L : LineBundleData X) {V : X.Opens} {i : L.ι} (h : V ≤ L.U i)
    (r : Γ(X, V)) (y : L.twistSubgroup (unitModule X) 1 V) :
    coeffOne L h (r • y) = r * coeffOne L h y :=
  toLocal_smul _ _ _ _ _

lemma coeffOne_restrict (L : LineBundleData X) {V V' : X.Opens} {i : L.ι} (h : V ≤ L.U i)
    (h' : V' ≤ V) (y : L.twistSubgroup (unitModule X) 1 V) :
    coeffOne L (h'.trans h) (L.twistRestrict (unitModule X) 1 h' y) =
      X.presheaf.map (homOfLE h').op (coeffOne L h y) :=
  toLocal_restrict _ _ h h' y

lemma coeffOne_change (L : LineBundleData X) {V : X.Opens} {i j : L.ι} (hi : V ≤ L.U i)
    (hj : V ≤ L.U j) (y : L.twistSubgroup (unitModule X) 1 V) :
    coeffOne L hi y = (L.trans (le_inf hi hj) : Γ(X, V)) * coeffOne L hj y := by
  have := L.toLocal_change (unitModule X) hi hj y
  rw [zpow_one] at this
  exact this

/-- Every section of `𝓛` over `V ⊆ U i` is its `i`-th coefficient times the generator. -/
lemma eq_smul_gen (L : LineBundleData X) {V : X.Opens} {i : L.ι} (h : V ≤ L.U i)
    (y : L.twistSubgroup (unitModule X) 1 V) : y = coeffOne L h y • gen L h := by
  apply (localEquiv (unitModule X) 1 h).injective
  rw [LinearEquiv.map_smul, localEquiv_apply, localEquiv_apply]
  exact (congrArg (fun r : Γ(X, V) => coeffOne L h y * r) (coeffOne_gen L h)).trans
    (mul_one _) |>.symm

/-- On `V ⊆ U i ∩ U j`, `e j = u i j · e i`. -/
lemma gen_change (L : LineBundleData X) {V : X.Opens} {i j : L.ι} (hi : V ≤ L.U i)
    (hj : V ≤ L.U j) :
    gen L hj = (L.trans (le_inf hi hj) : Γ(X, V)) • gen L hi := by
  rw [eq_smul_gen L hi (gen L hj)]
  refine congrArg (fun r : Γ(X, V) => r • gen L hi) ?_
  rw [coeffOne_change L hi hj, coeffOne_gen, mul_one]

lemma restrict_gen (L : LineBundleData X) {V V' : X.Opens} {i : L.ι} (h : V ≤ L.U i)
    (h' : V' ≤ V) :
    L.twistRestrict (unitModule X) 1 h' (gen L h) = gen L (h'.trans h) := by
  apply (localEquiv (unitModule X) 1 (h'.trans h)).injective
  rw [localEquiv_apply, localEquiv_apply]
  change coeffOne L (h'.trans h) _ = coeffOne L (h'.trans h) _
  rw [coeffOne_restrict L h h', coeffOne_gen, coeffOne_gen]
  exact map_one (X.presheaf.map (homOfLE h').op).hom

variable {L L' : LineBundleData X}

/-- A morphism of line bundles applied to sections over `V`. -/
abbrev appT (φ : L.twist (unitModule X) 1 ⟶ L'.twist (unitModule X) 1) (V : X.Opens)
    (y : L.twistSubgroup (unitModule X) 1 V) : L'.twistSubgroup (unitModule X) 1 V :=
  φ.app V y

lemma appT_smul (φ : L.twist (unitModule X) 1 ⟶ L'.twist (unitModule X) 1) (V : X.Opens)
    (r : Γ(X, V)) (y : L.twistSubgroup (unitModule X) 1 V) :
    appT φ V (r • y) = r • appT φ V y :=
  Scheme.Modules.Hom.app_smul φ r y

lemma appT_restrict (φ : L.twist (unitModule X) 1 ⟶ L'.twist (unitModule X) 1)
    {V V' : X.Opens} (h : V' ≤ V) (y : L.twistSubgroup (unitModule X) 1 V) :
    appT φ V' (L.twistRestrict (unitModule X) 1 h y) =
      L'.twistRestrict (unitModule X) 1 h (appT φ V y) :=
  ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE h).op) y

variable (e : L.twist (unitModule X) 1 ≅ L'.twist (unitModule X) 1)

lemma appT_hom_inv {V : X.Opens} (y : L'.twistSubgroup (unitModule X) 1 V) :
    appT e.hom V (appT e.inv V y) = y := by
  change (e.inv.app V ≫ e.hom.app V) y = y
  rw [← Scheme.Modules.Hom.comp_app, e.inv_hom_id]
  rfl

/-- The coefficient `d i a` of `e⁻¹ (f a)` with respect to `e i` on `U i ∩ V a`. -/
def isoCoeff (i : L.ι) (a : L'.ι) : Γ(X, L.U i ⊓ L'.U a) :=
  coeffOne L (inf_le_left : L.U i ⊓ L'.U a ≤ L.U i)
    (appT e.inv (L.U i ⊓ L'.U a) (gen L' (inf_le_right : L.U i ⊓ L'.U a ≤ L'.U a)))

/-- The coefficient of `e (e i)` with respect to `f a` on `U i ∩ V a`. -/
def isoCoeffInv (i : L.ι) (a : L'.ι) : Γ(X, L.U i ⊓ L'.U a) :=
  coeffOne L' (inf_le_right : L.U i ⊓ L'.U a ≤ L'.U a)
    (appT e.hom (L.U i ⊓ L'.U a) (gen L (inf_le_left : L.U i ⊓ L'.U a ≤ L.U i)))

lemma isoCoeff_mul (i : L.ι) (a : L'.ι) : isoCoeff e i a * isoCoeffInv e i a = 1 := by
  have hy := eq_smul_gen L (inf_le_left : L.U i ⊓ L'.U a ≤ L.U i)
    (appT e.inv (L.U i ⊓ L'.U a) (gen L' (inf_le_right : L.U i ⊓ L'.U a ≤ L'.U a)))
  have h1 := appT_hom_inv e (gen L' (inf_le_right : L.U i ⊓ L'.U a ≤ L'.U a))
  rw [hy, appT_smul] at h1
  have h2 := congrArg (coeffOne L' (inf_le_right : L.U i ⊓ L'.U a ≤ L'.U a)) h1
  rw [coeffOne_smul, coeffOne_gen] at h2
  exact h2

/-- The comparison units of an isomorphism of line bundles. -/
def isoUnit (i : L.ι) (a : L'.ι) : Γ(X, L.U i ⊓ L'.U a)ˣ :=
  Units.mkOfMulEqOne _ _ (isoCoeff_mul e i a)

/-- The coefficient of `e⁻¹ (f a)` on a smaller open. -/
lemma coeffOne_inv_gen (i : L.ι) (a : L'.ι) {V : X.Opens} (h : V ≤ L.U i ⊓ L'.U a) :
    coeffOne L (h.trans inf_le_left) (appT e.inv V (gen L' (h.trans inf_le_right))) =
      X.presheaf.map (homOfLE h).op (isoCoeff e i a) := by
  rw [← restrict_gen L' (inf_le_right : L.U i ⊓ L'.U a ≤ L'.U a) h, appT_restrict,
    coeffOne_restrict L (inf_le_left : L.U i ⊓ L'.U a ≤ L.U i) h]
  rfl

/-- **Isomorphism data from an isomorphism of line bundles** `𝒪 ⊗ 𝓛 ≅ 𝒪 ⊗ 𝓛'`. -/
def ofIso : IsoData L L' where
  w := isoUnit e
  compat i j a b {V} hV := by
    have hVi : V ≤ L.U i := (hV.trans inf_le_left).trans inf_le_left
    have hVj : V ≤ L.U j := (hV.trans inf_le_right).trans inf_le_left
    have hVa : V ≤ L'.U a := (hV.trans inf_le_left).trans inf_le_right
    have hVb : V ≤ L'.U b := (hV.trans inf_le_right).trans inf_le_right
    apply Units.ext
    change (L'.trans (le_inf hVa hVb) : Γ(X, V)) *
        X.presheaf.map (homOfLE (hV.trans inf_le_left)).op (isoCoeff e i a) =
      (L.trans (le_inf hVi hVj) : Γ(X, V)) *
        X.presheaf.map (homOfLE (hV.trans inf_le_right)).op (isoCoeff e j b)
    rw [← coeffOne_inv_gen e i a (hV.trans inf_le_left),
      ← coeffOne_inv_gen e j b (hV.trans inf_le_right), ← coeffOne_change L hVi hVj,
      gen_change L' hVa hVb, appT_smul, coeffOne_smul]

end OfIso

end IsoData

/-- **Isomorphic line bundles have isomorphic twists**: an isomorphism `𝒪 ⊗ 𝓛 ≅ 𝒪 ⊗ 𝓛'` gives
`F ⊗ 𝓛^m ≅ F ⊗ 𝓛'^m` for every module `F` and every `m`. -/
def twistIsoOfIso {L L' : LineBundleData X}
    (e : L.twist (unitModule X) 1 ≅ L'.twist (unitModule X) 1) (F : X.Modules) (m : ℤ) :
    L.twist F m ≅ L'.twist F m :=
  (IsoData.ofIso e).twistIso F m

/-! ### Serre ampleness of line-bundle data -/

/-- **Serre ampleness** of the line bundle of `L` on `Z` (the condition of `FiberAmple` on the
fibre): for every quasi-coherent `F` of finite type and all `m ≫ 0`, `F ⊗ 𝓛^m` is globally
generated and has vanishing first Čech cohomology for every finite affine cover. -/
def SerreAmple {Z : Scheme.{u}} (L : LineBundleData Z) : Prop :=
  ∀ (F : Z.Modules) [F.IsQuasicoherent] [F.IsFiniteType], ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
    (∀ 𝒰 : Cohomology.FiniteAffineCover Z,
      IsZero (Cohomology.cechCohomology (L.twist F m) 𝒰.U (RingHom.id Γ(Z, ⊤)) 1)) ∧
    IsGloballyGenerated (L.twist F m)

/-- Fibre-ampleness is Serre ampleness of the pulled-back line-bundle data on the fibre. -/
theorem fiberAmple_iff_serreAmple {Y : Scheme.{u}} (L : LineBundleData X) (β : X ⟶ Y) (y : Y) :
    FiberAmple L β y ↔ SerreAmple (L.pullback (β.fiberι y)) :=
  Iff.rfl

/-- Serre ampleness is invariant under isomorphism data. -/
theorem SerreAmple.of_isoData {Z : Scheme.{u}} {L L' : LineBundleData Z} (E : L.IsoData L')
    (h : SerreAmple L) : SerreAmple L' := by
  intro F _ _
  obtain ⟨m₀, hm₀⟩ := h F
  refine ⟨m₀, fun m hm => ⟨fun 𝒰 => ?_, ?_⟩⟩
  · exact (isZero_cechCohomology_iff_of_iso (E.twistIso F m) 𝒰.U _ 1).mp ((hm₀ m hm).1 𝒰)
  · exact (hm₀ m hm).2.of_iso (E.twistIso F m)

/-- Serre ampleness is invariant under isomorphisms of the line bundles. -/
theorem SerreAmple.of_iso {Z : Scheme.{u}} {L L' : LineBundleData Z}
    (e : L.twist (unitModule Z) 1 ≅ L'.twist (unitModule Z) 1) (h : SerreAmple L) :
    SerreAmple L' :=
  h.of_isoData (IsoData.ofIso e)

end LineBundleData

end

end DeJongAlterations.StableModification.Projectivity
