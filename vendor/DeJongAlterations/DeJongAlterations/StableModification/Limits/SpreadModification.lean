import DeJongAlterations.StableModification.Limits.SpreadModificationIso
import DeJongAlterations.StableModification.Limits.SpreadModificationProjective
import DeJongAlterations.StableModification.Limits.SpreadMarks

/-!
# Spreading out projective modifications

Let `D : I ⥤ Scheme` be a cofiltered system of affine schemes with affine transition maps,
indexed by a thin category, with limit cone `c` (lane LIM1, `Limits.Descent`), let `C₀ ⟶ D i₀`
be of finite presentation, given as a model `m` of `f : C ⟶ lim D` (so `C = C₀ ×_{D i₀} lim D`),
with a structure morphism `p₀ : C₀ ⟶ Spec R` to a noetherian ring, and let `β : C' ⟶ C` be
*projective*: a closed immersion `C' ↪ ℙⁿ_C = C ×_R ℙⁿ_R` followed by the projection, with
`C' ⟶ lim D` of finite presentation (given by a model `r`). If `β` is an isomorphism over the
preimage of a quasi-compact open `U ⊆ lim D`, then for some level `j` there is a projective
morphism `β_j : C'_j ⟶ C₀ ×_{D i₀} D j` whose base change to `lim D` is `β`, which is an
isomorphism over the preimage of an open `U_j ⊆ D j` with preimage `U` in `lim D`
(`exists_projective_model`).

Over the approximating system of a valuation ring (`Limits.QASystem`, lane LIM1), combining this
with lane LIM2's spreading of semi-stable pairs (`Spread.exists_isSemistablePair_model`), a
projective modification `(C', D') ⟶ C ×_{S} Spec V` with `(C', D')` semi-stable and `β` an
isomorphism over a quasi-compact open of `Spec V` descends to a projective morphism
`β_B : (C'_B, D'_B) ⟶ C₀ ×_{B₀} Spec B` with `(C'_B, D'_B)` semi-stable over `Spec B`, an
isomorphism over an open of `Spec B` (`exists_semistable_projective_model`), and, when `C₀` is flat
over `Spec B₀` and `U` is nonempty, an η-modification in Temkin's sense
(`exists_semistable_projective_etaModification`). When the generic point of `Spec V` is open
(`V` of finite height, `isOpen_singleton_genericPoint_of_finite`), an isomorphism on the generic
fibres suffices (`isIso_morphismRestrict_of_isIso_fiberMap`,
`exists_semistable_projective_etaModification_of_isIso_fiberMap`).

This is the rest of `prop:sm-spread-semistable`: the spreading of a stable modification
`(C'_𝔵, D'_𝔵) ⟶ (C, D) ×_S Spec 𝒪_{𝔖,𝔵}` to a quasi-alteration of the base in the proofs of
Theorems 1.2 and 1.5 of Temkin, *Stable modification of relative curves* (`semi-stable.tex`,
T:3347–3352, T:3384–3394), via Remark 3.1.1 (ii) (T:2297–2298), except for the absence of
exceptional components (Temkin's Lemma 5.1 (ii), `openloclem`) and the identification of the
descended marks with the transported marks, which are not treated here.
Properness is obtained from projectivity (Temkin Thm. 1.1, T:1713–1716), avoiding EGA IV 8.10.5
(xii).

Blueprint: `sm-spread-modification.tex`, `lem:sm-spread-mod-iterated`,
`thm:sm-spread-mod-projective-model`, `lem:sm-spread-mod-eta`,
`lem:sm-spread-mod-open-generic-point`, `thm:sm-spread-mod-semistable`, `cor:sm-spread-mod-eta`,
`cor:sm-spread-mod-eta-fibre`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace DeJongAlterations.StableModification.Limits.SpreadModification

universe u

set_option backward.isDefEq.respectTransparency false

open DeJong (IsRelativelyProjective IsSemistablePair)

section General

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} {c : Cone D}

@[reassoc (attr := simp)]
lemma _root_.DeJongAlterations.StableModification.Limits.Model.baseChange_g_fst
    {X : Scheme.{u}} {f : X ⟶ c.pt} {i : I} (m : Model D c f i)
    {k : I} (h : k ⟶ i) : (m.baseChange h).g ≫ pullback.fst m.fY (D.map h) = m.g := by
  simp [Model.baseChange]

/-- Iterated base changes of a model are pullbacks along the composite. -/
lemma _root_.DeJongAlterations.StableModification.Limits.Model.isPullback_baseChange₃
    {X : Scheme.{u}} {f : X ⟶ c.pt} {i : I} (m : Model D c f i)
    {k₁ k₂ k₃ : I} (h₁ : k₁ ⟶ i) (h₂ : k₂ ⟶ k₁) (h₃ : k₃ ⟶ k₂) :
    IsPullback (pullback.fst ((m.baseChange h₁).baseChange h₂).fY (D.map h₃) ≫
        pullback.fst (m.baseChange h₁).fY (D.map h₂) ≫ pullback.fst m.fY (D.map h₁))
      (((m.baseChange h₁).baseChange h₂).baseChange h₃).fY m.fY (D.map (h₃ ≫ h₂ ≫ h₁)) := by
  rw [D.map_comp, D.map_comp]
  exact (IsPullback.of_hasPullback _ _).paste_horiz
    ((IsPullback.of_hasPullback _ _).paste_horiz (IsPullback.of_hasPullback _ _))

lemma _root_.DeJongAlterations.StableModification.Limits.Model.baseChange₃_g
    {X : Scheme.{u}} {f : X ⟶ c.pt} {i : I} (m : Model D c f i)
    {k₁ k₂ k₃ : I} (h₁ : k₁ ⟶ i) (h₂ : k₂ ⟶ k₁) (h₃ : k₃ ⟶ k₂) :
    (((m.baseChange h₁).baseChange h₂).baseChange h₃).g ≫
        (pullback.fst ((m.baseChange h₁).baseChange h₂).fY (D.map h₃) ≫
          pullback.fst (m.baseChange h₁).fY (D.map h₂) ≫ pullback.fst m.fY (D.map h₁)) = m.g := by
  simp only [Model.baseChange_g_fst_assoc, Model.baseChange_g_fst]

variable [IsCofiltered I] [Quiver.IsThin I] (hc : IsLimit c)
  [∀ {j k : I} (g : j ⟶ k), IsAffineHom (D.map g)] [∀ j, IsAffine (D.obj j)]

include hc in
/-- **Projective morphisms spread out** (Temkin, Rem. 3.1.1 (ii), for projective modifications).
Let `m` be a model of finite presentation at level `i₀` of `f : C ⟶ lim D`, with a structure
morphism `p₀ : m.Y ⟶ Spec R` to a noetherian ring, let `β : C' ⟶ C` be projective relative to
`m.g ≫ p₀` (a closed immersion into `ℙⁿ_C` followed by the projection), let `r` be a model of
finite presentation of `C' ⟶ lim D`, and assume `β` is an isomorphism over the preimage of a
quasi-compact open `U ⊆ lim D`. Then there are a level `j` below `i₀` and the level of `r`,
models `M` of `C` and `M'` of `C'` at level `j` which are the base changes of `m` and `r`
(`t, t'`), and a morphism `β_j : M'.Y ⟶ M.Y` over `D j` with base change `β`, projective relative
to `M.Y ⟶ m.Y ⟶ Spec R`, and an isomorphism over the preimage of a quasi-compact open
`U_j ⊆ D j` whose preimage in `lim D` is `U`. -/
theorem exists_projective_model {C C' : Scheme.{u}} {f : C ⟶ c.pt} {i₀ j₀ : I}
    (m : Model D c f i₀) (hm : m.IsFP) {R : Type u} [CommRing R] [IsNoetherianRing R]
    (p₀ : m.Y ⟶ Spec (.of R)) (β : C' ⟶ C) (r : Model D c (β ≫ f) j₀) (hr : r.IsFP)
    (hβ : IsRelativelyProjective (m.g ≫ p₀) β)
    (U : c.pt.Opens) (hU : IsCompact (U : Set c.pt)) (hiso : IsIso (β ∣_ (f ⁻¹ᵁ U))) :
    ∃ (j : I) (a : j ⟶ i₀) (b : j ⟶ j₀) (M : Model D c f j) (M' : Model D c (β ≫ f) j)
      (t : M.Y ⟶ m.Y) (t' : M'.Y ⟶ r.Y) (βj : M'.Y ⟶ M.Y) (Uj : (D.obj j).Opens),
      M.IsFP ∧ M'.IsFP ∧
      IsPullback t M.fY m.fY (D.map a) ∧ M.g ≫ t = m.g ∧
      IsPullback t' M'.fY r.fY (D.map b) ∧ M'.g ≫ t' = r.g ∧
      βj ≫ M.fY = M'.fY ∧ IsPullback M'.g β βj M.g ∧
      IsRelativelyProjective (t ≫ p₀) βj ∧
      IsCompact (Uj : Set (D.obj j)) ∧ c.π.app j ⁻¹ᵁ Uj = U ∧
      IsIso (βj ∣_ (M.fY ⁻¹ᵁ Uj)) := by
  obtain ⟨n, i, hi, hiβ⟩ := hβ
  obtain ⟨jU, VU, hVUc, hVU⟩ := exists_preimage_eq D c hc U hU
  -- a common level for `m`, `r` and `U`
  let k₁ := IsCofiltered.min i₀ j₀
  let k := IsCofiltered.min k₁ jU
  let a₁ : k ⟶ i₀ := IsCofiltered.minToLeft k₁ jU ≫ IsCofiltered.minToLeft i₀ j₀
  let b₁ : k ⟶ j₀ := IsCofiltered.minToLeft k₁ jU ≫ IsCofiltered.minToRight i₀ j₀
  let u₁ : k ⟶ jU := IsCofiltered.minToRight k₁ jU
  let m₁ := m.baseChange a₁
  have hm₁ : m₁.IsFP := hm.baseChange a₁
  let r₁ := r.baseChange b₁
  have hr₁ : r₁.IsFP := hr.baseChange b₁
  let p₁ : m₁.Y ⟶ Spec (.of R) := pullback.fst m.fY (D.map a₁) ≫ p₀
  have hp₁ : m₁.g ≫ p₁ = m.g ≫ p₀ := Model.baseChange_g_fst_assoc m a₁ p₀
  -- the projective space model at level `k`
  let Pn := projectiveSpaceStructure R n
  let P₁ := m₁.projectiveSpace p₁ (m.g ≫ p₀) hp₁ n
  have hP₁ : P₁.IsFP := hm₁.projectiveSpace p₁ _ hp₁ n
  obtain ⟨_, _, _⟩ := hr₁
  obtain ⟨_, _, _⟩ := hP₁
  -- descend the projective embedding as a morphism
  have hw : (i ≫ P₁.g) ≫ P₁.fY = r₁.g ≫ r₁.fY := by
    rw [Category.assoc, P₁.isPullback.w, r₁.isPullback.w, ← hiβ]
    simp only [Category.assoc]
  obtain ⟨l₀, b, hb, hb'⟩ := exists_hom_of_isPullback D c hc r₁.fY P₁.fY r₁.isPullback
    (i ≫ P₁.g) hw
  -- re-base at level `l₀`
  let r₂ := r₁.baseChange l₀.hom
  let m₂ := m₁.baseChange l₀.hom
  let P₂ := P₁.baseChange l₀.hom
  have hr₂ : r₂.IsFP := (hr.baseChange b₁).baseChange l₀.hom
  have hm₂ : m₂.IsFP := hm₁.baseChange l₀.hom
  have hP₂ : P₂.IsFP := (hm₁.projectiveSpace p₁ _ hp₁ n).baseChange l₀.hom
  let ι₂ : r₂.Y ⟶ P₂.Y := pullback.lift b (pullback.snd _ _) (by rw [hb, pullback.condition])
  have hι₂ : ι₂ ≫ P₂.fY = r₂.fY := pullback.lift_snd _ _ _
  have hι₂g : r₂.g ≫ ι₂ = i ≫ P₂.g := by
    apply pullback.hom_ext
    · simp only [Category.assoc, ι₂, pullback.lift_fst]
      exact hb'.trans (by simp [P₂, Model.baseChange])
    · simp [ι₂, r₂, P₂, Model.baseChange, reassoc_of% hiβ]
  -- the projection `ℙⁿ ⟶ C` at level `l₀`
  let π₁ : P₁.Y ⟶ m₁.Y := pullback.fst p₁ Pn
  have hπ₁ : π₁ ≫ m₁.fY = P₁.fY := rfl
  have Hπ₁ : IsPullback (pullback.snd p₁ Pn) π₁ Pn p₁ := (IsPullback.of_hasPullback p₁ Pn).flip
  let π₂ := topBaseChange P₁ m₁ π₁ hπ₁ l₀
  have hπ₂ : π₂ ≫ m₂.fY = P₂.fY := topBaseChange_snd _ _ _ _ _
  let p₂ : m₂.Y ⟶ Spec (.of R) := pullback.fst m₁.fY (D.map l₀.hom) ≫ p₁
  have Hπ₂ : IsPullback (pullback.fst P₁.fY (D.map l₀.hom) ≫ pullback.snd p₁ Pn) π₂ Pn p₂ :=
    isPullback_projectiveSpace_topBaseChange P₁ m₁ π₁ hπ₁ _ p₁ Hπ₁ l₀
  have hP₁g : P₁.g ≫ π₁ = pullback.fst (m.g ≫ p₀) Pn ≫ m₁.g := by
    simp [P₁, π₁, Pn]
  have hπ₂g : P₂.g ≫ π₂ = pullback.fst (m.g ≫ p₀) Pn ≫ m₂.g :=
    π_topBaseChange P₁ m₁ π₁ hπ₁ (pullback.fst _ _) hP₁g rfl l₀
  -- the descended morphism at level `l₀`
  let β₂ := ι₂ ≫ π₂
  have hβ₂ : β₂ ≫ m₂.fY = r₂.fY := by rw [Category.assoc, hπ₂, hι₂]
  have hβ₂g : r₂.g ≫ β₂ = β ≫ m₂.g := by
    rw [← Category.assoc, hι₂g, Category.assoc, hπ₂g, ← Category.assoc, hiβ]
  -- projectivity at all levels below `l₁`
  obtain ⟨l₁, hl₁⟩ := exists_isRelativelyProjective_topBaseChange hc r₂ P₂ m₂ hr₂ hP₂ ι₂ hι₂
    π₂ hπ₂ _ p₂ Hπ₂ i hι₂g (by rw [← Category.assoc, hiβ])
  -- the isomorphism over `U`
  let O : m₂.Y.Opens := m₂.fY ⁻¹ᵁ (D.map (l₀.hom ≫ u₁) ⁻¹ᵁ VU)
  have hm₂' := hm₂
  obtain ⟨_, _, _⟩ := hm₂'
  have hO : IsCompact (O : Set m₂.Y) := by
    have h1 : IsCompact ((D.map (l₀.hom ≫ u₁) ⁻¹ᵁ VU : (D.obj l₀.left).Opens) :
        Set (D.obj l₀.left)) :=
      QuasiCompact.isCompact_preimage (f := D.map (l₀.hom ≫ u₁)) _ VU.isOpen hVUc
    exact QuasiCompact.isCompact_preimage (f := m₂.fY) _ (TopologicalSpace.Opens.isOpen _) h1
  have hgO : m₂.g ⁻¹ᵁ O = f ⁻¹ᵁ U := by
    rw [← Scheme.Hom.comp_preimage, m₂.isPullback.w, Scheme.Hom.comp_preimage,
      ← Scheme.Hom.comp_preimage (c.π.app _), c.w, hVU]
  have hiso₂ : IsIso (β ∣_ (m₂.g ⁻¹ᵁ O)) := by rw [hgO]; exact hiso
  obtain ⟨l₂, hl₂⟩ := exists_isIso_morphismRestrict_topBaseChange r₂ m₂ β₂ hβ₂ hc hr₂
    (hm₁.baseChange l₀.hom) β hβ₂g rfl O hO hiso₂
  -- a common level
  let l := IsCofiltered.min l₁ l₂
  let g₁ : l ⟶ l₁ := IsCofiltered.minToLeft l₁ l₂
  let g₂ : l ⟶ l₂ := IsCofiltered.minToRight l₁ l₂
  have hproj := hl₁ l g₁
  have hisol : IsIso (topBaseChange r₂ m₂ β₂ hβ₂ l ∣_
      (pullback.fst m₂.fY (D.map l.hom) ⁻¹ᵁ O)) := by
    have := hl₂
    have := isIso_morphismRestrict_of_isPullback'
      (isPullback_topBaseChange_map r₂ m₂ β₂ hβ₂ g₂) (pullback.fst m₂.fY (D.map l₂.hom) ⁻¹ᵁ O)
    have heq : (baseChangeDiagram D m₂.fY).map g₂ ⁻¹ᵁ
        (pullback.fst m₂.fY (D.map l₂.hom) ⁻¹ᵁ O) = pullback.fst m₂.fY (D.map l.hom) ⁻¹ᵁ O := by
      rw [← Scheme.Hom.comp_preimage, baseChangeDiagram_map_fst]
    rw [heq] at this
    exact this
  -- the final data
  let M := m₂.baseChange l.hom
  let M' := r₂.baseChange l.hom
  let βj : M'.Y ⟶ M.Y := topBaseChange r₂ m₂ β₂ hβ₂ l
  have hβj : βj ≫ M.fY = M'.fY := topBaseChange_snd _ _ _ _ _
  let Uj : (D.obj l.left).Opens := D.map (l.hom ≫ l₀.hom ≫ u₁) ⁻¹ᵁ VU
  have hOpen : pullback.fst m₂.fY (D.map l.hom) ⁻¹ᵁ O = M.fY ⁻¹ᵁ Uj := by
    simp only [O, Uj, M, Model.baseChange_fY, ← Scheme.Hom.comp_preimage, pullback.condition_assoc,
      Functor.map_comp]
  refine ⟨l.left, l.hom ≫ l₀.hom ≫ a₁, l.hom ≫ l₀.hom ≫ b₁, M, M',
    pullback.fst m₂.fY (D.map l.hom) ≫ pullback.fst m₁.fY (D.map l₀.hom) ≫
      pullback.fst m.fY (D.map a₁),
    pullback.fst r₂.fY (D.map l.hom) ≫ pullback.fst r₁.fY (D.map l₀.hom) ≫
      pullback.fst r.fY (D.map b₁),
    βj, Uj, hm₂.baseChange l.hom, hr₂.baseChange l.hom, m.isPullback_baseChange₃ a₁ l₀.hom l.hom,
    m.baseChange₃_g a₁ l₀.hom l.hom, r.isPullback_baseChange₃ b₁ l₀.hom l.hom,
    r.baseChange₃_g b₁ l₀.hom l.hom, hβj, ?_, ?_,
    QuasiCompact.isCompact_preimage (f := D.map (l.hom ≫ l₀.hom ≫ u₁)) _ VU.isOpen hVUc, ?_, ?_⟩
  · refine IsPullback.of_bot ?_ (π_topBaseChange r₂ m₂ β₂ hβ₂ β hβ₂g rfl l) M.isPullback
    rw [hβj]
    exact M'.isPullback
  · have e : (pullback.fst m₂.fY (D.map l.hom) ≫ pullback.fst m₁.fY (D.map l₀.hom) ≫
        pullback.fst m.fY (D.map a₁)) ≫ p₀ = pullback.fst m₂.fY (D.map l.hom) ≫ p₂ := by
      simp only [p₂, p₁, Category.assoc]
    rw [e]
    exact hproj
  · rw [← Scheme.Hom.comp_preimage, c.w, hVU]
  · rw [← hOpen]
    exact hisol

end General

/-! ### η-modifications -/

section EtaModification

variable {C C' S T : Scheme.{u}}

/-- `pullbackCompMap β g a : C' ×_S T ⟶ C ×_S T` is the base change of `β` along
`C ×_S T ⟶ C`. -/
lemma isPullback_pullbackCompMap (β : C' ⟶ C) (g : C ⟶ S) (a : T ⟶ S) :
    IsPullback (pullback.fst (β ≫ g) a) (Curves.pullbackCompMap β g a) β (pullback.fst g a) := by
  refine IsPullback.of_bot ?_ (Curves.pullbackCompMap_fst β g a).symm
    (IsPullback.of_hasPullback g a)
  rw [Curves.pullbackCompMap_snd]
  exact IsPullback.of_hasPullback (β ≫ g) a

/-- If `β` is an isomorphism over the preimage of an open `U ⊆ S` and `a : T ⟶ S` maps into `U`,
then the base change `C' ×_S T ⟶ C ×_S T` is an isomorphism. -/
theorem isIso_pullbackCompMap_of_isIso_morphismRestrict (β : C' ⟶ C) (g : C ⟶ S)
    (U : S.Opens) [IsIso (β ∣_ (g ⁻¹ᵁ U))] (a : T ⟶ S) (ha : a ⁻¹ᵁ U = ⊤) :
    IsIso (Curves.pullbackCompMap β g a) := by
  have H := isIso_morphismRestrict_of_isPullback' (isPullback_pullbackCompMap β g a) (g ⁻¹ᵁ U)
  have htop : pullback.fst g a ⁻¹ᵁ (g ⁻¹ᵁ U) = ⊤ := by
    rw [← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage, ha,
      Scheme.Hom.preimage_top]
  rw [htop] at H
  exact IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    (fun _ : Unit ↦ ⊤) (by simp) fun _ ↦ H

/-- **Isomorphisms over a nonempty open of an integral base are η-modifications.** Let `S` be
integral, `g : C ⟶ S` and `β ≫ g` flat, `β` proper, and `β` an isomorphism over the preimage of
a nonempty open `U ⊆ S` with quasi-compact inclusion. Then `β` is an η-modification in Temkin's
sense (T:2241–2243): the preimages of `U` are schematically dense (flat base change of the
schematically dense `U ⊆ S`), and the generic point of `S` lies in `U`. -/
theorem isEtaModification_of_isIso_morphismRestrict [IsIntegral S] (β : C' ⟶ C) (g : C ⟶ S)
    [IsProper β] [Flat g] [Flat (β ≫ g)] (U : S.Opens) (hU : (U : Set S).Nonempty)
    [QuasiCompact U.ι] [IsIso (β ∣_ (g ⁻¹ᵁ U))] : Curves.IsEtaModification β g where
  toIsProper := inferInstance
  exists_isIso := by
    have : IsSchemeTheoreticallyDominant U.ι :=
      Curves.isSchemeTheoreticallyDominant_ι_of_nonempty U hU
    refine ⟨g ⁻¹ᵁ U, ?_, ?_, inferInstance⟩
    · exact IsSchemeTheoreticallyDominant.of_isPullback (isPullback_morphismRestrict g U)
    · rw [← Scheme.Hom.comp_preimage]
      exact IsSchemeTheoreticallyDominant.of_isPullback (isPullback_morphismRestrict (β ≫ g) U)
  isIso_fiberMap := by
    have hη : genericPoint S ∈ U :=
      ((genericPoint_spec S).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
    refine isIso_pullbackCompMap_of_isIso_morphismRestrict β g U _ ?_
    refine eq_top_iff.mpr fun x _ ↦ ?_
    change S.fromSpecResidueField (genericPoint S) x ∈ U
    rw [Scheme.fromSpecResidueField_apply]
    exact hη

/-- **Open points.** If `{x}` is open in `X` and the stalk at `x` is a field (e.g. `x` the generic
point of an integral scheme), then `Spec κ(x) ⟶ X` is an open immersion. -/
theorem isOpenImmersion_fromSpecResidueField {X : Scheme.{u}} (x : X)
    (hx : IsOpen ({x} : Set X)) (hfield : IsField (X.presheaf.stalk x)) :
    IsOpenImmersion (X.fromSpecResidueField x) := by
  have hemb : Topology.IsOpenEmbedding (X.fromSpecResidueField x) :=
    ⟨(X.fromSpecResidueField x).isEmbedding, by rw [Scheme.range_fromSpecResidueField]; exact hx⟩
  have hiso : ∀ p, IsIso ((X.fromSpecResidueField x).stalkMap p) := by
    intro p
    have hfield' : IsField (X.presheaf.stalk ((X.fromSpecResidueField x) p)) := by
      rw [Scheme.fromSpecResidueField_apply]
      exact hfield
    have hsurj := (X.fromSpecResidueField x).stalkMap_surjective p
    have hinj : Function.Injective ((X.fromSpecResidueField x).stalkMap p) := by
      refine (injective_iff_map_eq_zero ((X.fromSpecResidueField x).stalkMap p).hom).mpr ?_
      intro a ha
      have hmem : a ∈ IsLocalRing.maximalIdeal _ := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        have := hu.map ((X.fromSpecResidueField x).stalkMap p).hom
        rw [ha] at this
        exact not_isUnit_zero this
      rwa [IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield'] at hmem
    exact (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hinj, hsurj⟩
  exact IsOpenImmersion.of_isIso_stalkMap _ hemb

/-- **Isomorphism on the generic fibre over an open generic point.** If `S` is integral with
open generic point `η`, `U = {η}`, and the fibre map `β_η` of `β : C' ⟶ C` over `g : C ⟶ S` is
an isomorphism, then `β` is an isomorphism over `g⁻¹(U)`. -/
theorem isIso_morphismRestrict_of_isIso_fiberMap [IsIntegral S] (β : C' ⟶ C) (g : C ⟶ S)
    (U : S.Opens) (hU : (U : Set S) = {genericPoint S})
    [IsIso (Curves.fiberMap β g (genericPoint S))] : IsIso (β ∣_ (g ⁻¹ᵁ U)) := by
  have hfield : IsField (S.presheaf.stalk (genericPoint S)) := by
    refine isField_stalk_of_closure_mem_irreducibleComponents S _ ?_
    rw [(genericPoint_spec S).def, irreducibleComponents_eq_singleton]
    exact Set.mem_singleton _
  have hopen : IsOpen ({genericPoint S} : Set S) := hU ▸ U.isOpen
  have := isOpenImmersion_fromSpecResidueField _ hopen hfield
  have H := isPullback_pullbackCompMap β g (S.fromSpecResidueField (genericPoint S))
  have : IsIso (Curves.pullbackCompMap β g (S.fromSpecResidueField (genericPoint S))) :=
    inferInstanceAs (IsIso (Curves.fiberMap β g (genericPoint S)))
  have h := isIso_morphismRestrict_of_isPullback H
  have hrange : (pullback.fst g (S.fromSpecResidueField (genericPoint S))).opensRange =
      g ⁻¹ᵁ U := by
    apply TopologicalSpace.Opens.ext
    rw [Scheme.Hom.coe_opensRange, Scheme.Pullback.range_fst, Scheme.range_fromSpecResidueField,
      ← hU]
    rfl
  rw [hrange] at h
  exact h

/-- **The generic point of a domain with finitely many primes is open** (e.g. a valuation ring of
finite height): its complement is the finite union of the closed sets `V(𝔭)`, `𝔭 ≠ 0`. -/
theorem isOpen_singleton_genericPoint_of_finite (R : CommRingCat.{u}) [IsDomain R]
    [Finite (PrimeSpectrum R)] : IsOpen ({genericPoint (Spec R)} : Set (Spec R)) := by
  rw [genericPoint_eq_bot_of_affine]
  have hcl : IsClosed (⋃ p ∈ {p : PrimeSpectrum R | p ≠ ⊥},
      PrimeSpectrum.zeroLocus (p.asIdeal : Set R)) :=
    (Set.toFinite _).isClosed_biUnion fun p _ ↦ PrimeSpectrum.isClosed_zeroLocus _
  have heq : (⋃ p ∈ {p : PrimeSpectrum R | p ≠ ⊥},
      PrimeSpectrum.zeroLocus (p.asIdeal : Set R)) = ({⊥} : Set (PrimeSpectrum R))ᶜ := by
    ext q
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, PrimeSpectrum.mem_zeroLocus, exists_prop,
      Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨p, hp, hpq⟩ rfl
      apply hp
      ext x
      constructor
      · intro hx
        exact hpq hx
      · intro hx
        rw [PrimeSpectrum.asIdeal_bot] at hx
        rw [hx]
        exact p.asIdeal.zero_mem
    · intro hq
      exact ⟨q, hq, le_rfl⟩
  rw [heq] at hcl
  exact isClosed_compl_iff.mp hcl

end EtaModification

/-! ### The approximating system of a valuation ring -/

section QASystem

variable (k : Type u) [Field k] {A L : Type u} [CommRing A] [Algebra k A]
  [Algebra.FiniteType k A] [Field L] [Algebra A L] {R : Subalgebra A L}

/-- The members `Spec B` of the approximating system are integral (`B ⊆ L` is a domain). -/
instance isIntegral_qaSystem_obj (B : (FGSubalgebra A R)ᵒᵖ) :
    IsIntegral (((fgDiagram R).op ⋙ Scheme.Spec).obj B) :=
  inferInstanceAs (IsIntegral (Spec (.of B.unop.1)))

/-- The limit `Spec R` of the approximating system is integral (`R ⊆ L` is a domain). -/
instance isIntegral_fgSpecCone_pt : IsIntegral (fgSpecCone R).pt :=
  inferInstanceAs (IsIntegral (Spec (.of R)))

include k in
/-- **Semi-stable projective modifications spread out** (Temkin, Rem. 3.1.1 and the proofs of
Thms. 1.2 and 1.5, T:3347–3352, T:3384–3394, without the absence of exceptional components). Let
`m` be a model of finite presentation over `Spec B₀` of `f : C ⟶ Spec R`, with a `k`-structure
`p₀`, let `β : C' ⟶ C` be projective relative to `m.g ≫ p₀`, let `(C', D')` be a semi-stable
pair over `Spec R` (for `β ≫ f`), and let `β` be an isomorphism over the preimage of a
quasi-compact open `U ⊆ Spec R`. Then for some member `B ⊇ B₀` of the approximating system there
are a model `M = C₀ ×_{B₀} Spec B` of `C`, a model `M'` of `C'` with a closed subscheme `D'_B`
such that `(M', D'_B)` is a semi-stable pair over `Spec B` pulling back to `(C', D')`, and a
projective morphism `β_B : M'.Y ⟶ M.Y` over `Spec B` with base change `β`, which is an
isomorphism over the preimage of a quasi-compact open `U_B ⊆ Spec B` with preimage `U`. -/
theorem exists_semistable_projective_model {C C' : Scheme.{u}} {f : C ⟶ (fgSpecCone R).pt}
    {B₀ : (FGSubalgebra A R)ᵒᵖ}
    (m : Model ((fgDiagram R).op ⋙ Scheme.Spec) (fgSpecCone R) f B₀) (hm : m.IsFP)
    (p₀ : m.Y ⟶ Spec (.of k)) (β : C' ⟶ C) (hβ : IsRelativelyProjective (m.g ≫ p₀) β)
    {DX : C'.IdealSheafData} (hD : IsSemistablePair (β ≫ f) DX)
    (U : (fgSpecCone R).pt.Opens) (hU : IsCompact (U : Set (fgSpecCone R).pt))
    (hiso : IsIso (β ∣_ (f ⁻¹ᵁ U))) :
    ∃ (B : (FGSubalgebra A R)ᵒᵖ) (a : B ⟶ B₀)
      (M : Model ((fgDiagram R).op ⋙ Scheme.Spec) (fgSpecCone R) f B)
      (M' : Model ((fgDiagram R).op ⋙ Scheme.Spec) (fgSpecCone R) (β ≫ f) B)
      (t : M.Y ⟶ m.Y) (βB : M'.Y ⟶ M.Y) (DB : M'.Y.IdealSheafData)
      (UB : (((fgDiagram R).op ⋙ Scheme.Spec).obj B).Opens),
      M.IsFP ∧ M'.IsFP ∧ IsPullback t M.fY m.fY (((fgDiagram R).op ⋙ Scheme.Spec).map a) ∧
      M.g ≫ t = m.g ∧ βB ≫ M.fY = M'.fY ∧ IsPullback M'.g β βB M.g ∧
      IsRelativelyProjective (t ≫ p₀) βB ∧
      IsSemistablePair M'.fY DB ∧ DB.comap M'.g = DX ∧
      IsCompact (UB : Set (((fgDiagram R).op ⋙ Scheme.Spec).obj B)) ∧
      (fgSpecCone R).π.app B ⁻¹ᵁ UB = U ∧ IsIso (βB ∣_ (M.fY ⁻¹ᵁ UB)) := by
  have hc := isLimitFGSpecCone R
  have : IsProper β := hβ.isProper
  have hm' := hm
  obtain ⟨_, _, _⟩ := hm'
  have : QuasiCompact f := MorphismProperty.of_isPullback (P := @QuasiCompact) m.isPullback
    inferInstance
  have : QuasiSeparated f := MorphismProperty.of_isPullback (P := @QuasiSeparated) m.isPullback
    inferInstance
  obtain ⟨B₁, M₁, DM₁, hM₁, hss, hDM⟩ := Spread.exists_isSemistablePair_model k (β ≫ f) hD
  obtain ⟨j, a, b, M, M', t, t', βj, Uj, hM, hM', ht, htg, ht', ht'g, hβj, hpb, hproj, hUjc,
    hUj, hisoj⟩ := exists_projective_model hc m hm p₀ β M₁ hM₁ hβ U hU hiso
  have hss' : IsSemistablePair M'.fY (DM₁.comap t') := by
    have h1 := Curves.IsSemistablePair.pullback hss (((fgDiagram R).op ⋙ Scheme.Spec).map b)
    have h2 := Curves.IsSemistablePair.etale_comp h1 ht'.isoPullback.hom
    rw [ht'.isoPullback_hom_snd, ← Scheme.IdealSheafData.comap_comp,
      ht'.isoPullback_hom_fst] at h2
    exact h2
  refine ⟨j, a, M, M', t, βj, DM₁.comap t', Uj, hM, hM', ht, htg, hβj, hpb, hproj, hss', ?_,
    hUjc, hUj, hisoj⟩
  rw [← Scheme.IdealSheafData.comap_comp, ht'g, hDM]

include k in
/-- **Semi-stable projective η-modifications spread out.** In the situation of
`exists_semistable_projective_model`, if moreover `C₀ = m.Y` is flat over `Spec B₀` and `U` is
nonempty, then the descended `β_B` is an η-modification of `M.Y ⟶ Spec B` in Temkin's sense
(proper, an isomorphism between schematically dense opens, and an isomorphism on generic
fibres). -/
theorem exists_semistable_projective_etaModification {C C' : Scheme.{u}}
    {f : C ⟶ (fgSpecCone R).pt} {B₀ : (FGSubalgebra A R)ᵒᵖ}
    (m : Model ((fgDiagram R).op ⋙ Scheme.Spec) (fgSpecCone R) f B₀) (hm : m.IsFP)
    [Flat m.fY] (p₀ : m.Y ⟶ Spec (.of k)) (β : C' ⟶ C)
    (hβ : IsRelativelyProjective (m.g ≫ p₀) β)
    {DX : C'.IdealSheafData} (hD : IsSemistablePair (β ≫ f) DX)
    (U : (fgSpecCone R).pt.Opens) (hU : IsCompact (U : Set (fgSpecCone R).pt))
    (hUne : (U : Set (fgSpecCone R).pt).Nonempty) (hiso : IsIso (β ∣_ (f ⁻¹ᵁ U))) :
    ∃ (B : (FGSubalgebra A R)ᵒᵖ) (a : B ⟶ B₀)
      (M : Model ((fgDiagram R).op ⋙ Scheme.Spec) (fgSpecCone R) f B)
      (M' : Model ((fgDiagram R).op ⋙ Scheme.Spec) (fgSpecCone R) (β ≫ f) B)
      (t : M.Y ⟶ m.Y) (βB : M'.Y ⟶ M.Y) (DB : M'.Y.IdealSheafData)
      (UB : (((fgDiagram R).op ⋙ Scheme.Spec).obj B).Opens),
      M.IsFP ∧ M'.IsFP ∧ IsPullback t M.fY m.fY (((fgDiagram R).op ⋙ Scheme.Spec).map a) ∧
      M.g ≫ t = m.g ∧ βB ≫ M.fY = M'.fY ∧ IsPullback M'.g β βB M.g ∧
      IsRelativelyProjective (t ≫ p₀) βB ∧
      IsSemistablePair M'.fY DB ∧ DB.comap M'.g = DX ∧
      IsCompact (UB : Set (((fgDiagram R).op ⋙ Scheme.Spec).obj B)) ∧
      (fgSpecCone R).π.app B ⁻¹ᵁ UB = U ∧ IsIso (βB ∣_ (M.fY ⁻¹ᵁ UB)) ∧
      (UB : Set (((fgDiagram R).op ⋙ Scheme.Spec).obj B)).Nonempty ∧
      Curves.IsEtaModification βB M.fY := by
  obtain ⟨B, a, M, M', t, βB, DB, UB, hM, hM', ht, htg, hβB, hpb, hproj, hss, hDB, hUBc, hUB,
    hisoB⟩ := exists_semistable_projective_model k m hm p₀ β hβ hD U hU hiso
  have hUBne : (UB : Set (((fgDiagram R).op ⋙ Scheme.Spec).obj B)).Nonempty := by
    obtain ⟨x, hx⟩ := hUne
    rw [← hUB] at hx
    exact ⟨_, hx⟩
  refine ⟨B, a, M, M', t, βB, DB, UB, hM, hM', ht, htg, hβB, hpb, hproj, hss, hDB, hUBc, hUB,
    hisoB, hUBne, ?_⟩
  have : IsProper βB := hproj.isProper
  have : Flat M.fY := MorphismProperty.of_isPullback (P := @Flat) ht inferInstance
  have : Flat (βB ≫ M.fY) := by
    rw [hβB]
    have := hss.nodal
    infer_instance
  have : CompactSpace UB := isCompact_iff_compactSpace.mp hUBc
  have : QuasiCompact UB.ι :=
    (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact) (f := UB.ι)).mpr inferInstance
  exact isEtaModification_of_isIso_morphismRestrict βB M.fY UB hUBne

include k in
/-- **Spreading out from the generic fibre.** In the situation of
`exists_semistable_projective_etaModification`, assume instead of an isomorphism over a
quasi-compact open that the generic point `η` of `Spec R` is open (e.g. `R` a valuation ring of
finite height) and that `β` is an isomorphism on the generic fibres (Temkin's η-modifications,
T:2243). Then the same conclusion holds, with `U = {η}`. -/
theorem exists_semistable_projective_etaModification_of_isIso_fiberMap {C C' : Scheme.{u}}
    {f : C ⟶ (fgSpecCone R).pt} {B₀ : (FGSubalgebra A R)ᵒᵖ}
    (m : Model ((fgDiagram R).op ⋙ Scheme.Spec) (fgSpecCone R) f B₀) (hm : m.IsFP)
    [Flat m.fY] (p₀ : m.Y ⟶ Spec (.of k)) (β : C' ⟶ C)
    (hβ : IsRelativelyProjective (m.g ≫ p₀) β)
    {DX : C'.IdealSheafData} (hD : IsSemistablePair (β ≫ f) DX)
    (hη : IsOpen ({genericPoint (fgSpecCone R).pt} : Set (fgSpecCone R).pt))
    [IsIso (Curves.fiberMap β f (genericPoint (fgSpecCone R).pt))] :
    ∃ (B : (FGSubalgebra A R)ᵒᵖ) (a : B ⟶ B₀)
      (M : Model ((fgDiagram R).op ⋙ Scheme.Spec) (fgSpecCone R) f B)
      (M' : Model ((fgDiagram R).op ⋙ Scheme.Spec) (fgSpecCone R) (β ≫ f) B)
      (t : M.Y ⟶ m.Y) (βB : M'.Y ⟶ M.Y) (DB : M'.Y.IdealSheafData)
      (UB : (((fgDiagram R).op ⋙ Scheme.Spec).obj B).Opens),
      M.IsFP ∧ M'.IsFP ∧ IsPullback t M.fY m.fY (((fgDiagram R).op ⋙ Scheme.Spec).map a) ∧
      M.g ≫ t = m.g ∧ βB ≫ M.fY = M'.fY ∧ IsPullback M'.g β βB M.g ∧
      IsRelativelyProjective (t ≫ p₀) βB ∧
      IsSemistablePair M'.fY DB ∧ DB.comap M'.g = DX ∧
      IsCompact (UB : Set (((fgDiagram R).op ⋙ Scheme.Spec).obj B)) ∧
      (fgSpecCone R).π.app B ⁻¹ᵁ UB = ⟨{genericPoint (fgSpecCone R).pt}, hη⟩ ∧
      IsIso (βB ∣_ (M.fY ⁻¹ᵁ UB)) ∧
      (UB : Set (((fgDiagram R).op ⋙ Scheme.Spec).obj B)).Nonempty ∧
      Curves.IsEtaModification βB M.fY := by
  let U : (fgSpecCone R).pt.Opens := ⟨{genericPoint _}, hη⟩
  have hiso : IsIso (β ∣_ (f ⁻¹ᵁ U)) := isIso_morphismRestrict_of_isIso_fiberMap β f U rfl
  obtain ⟨B, a, M, M', t, βB, DB, UB, hM, hM', ht, htg, hβB, hpb, hproj, hss, hDB, hUBc, hUB,
    hisoB, hUBne, heta⟩ := exists_semistable_projective_etaModification k m hm p₀ β hβ hD U
      isCompact_singleton (Set.singleton_nonempty _) hiso
  exact ⟨B, a, M, M', t, βB, DB, UB, hM, hM', ht, htg, hβB, hpb, hproj, hss, hDB, hUBc, hUB,
    hisoB, hUBne, heta⟩

end QASystem

end DeJongAlterations.StableModification.Limits.SpreadModification
