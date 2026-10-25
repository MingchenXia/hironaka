import DeJongAlterations.StableModification.Limits.SpreadNodal
import DeJongAlterations.StableModification.Limits.SpreadProperty
import DeJongAlterations.StableModification.Limits.SpreadAffine

/-!
# Spreading out semi-stable pairs along the system of quasi-alterations

Let `k` be a field, `A` a finitely generated `k`-algebra, `L` a field over `A` and `R ⊆ L` an
`A`-subalgebra, with lane LIM1's approximating system `Spec B`, `B ⊆ R` finitely generated over
`A`, whose limit is `Spec R`. This file proves that **semi-stable pairs spread out**
(`exists_isSemistablePair_model`): if `f : X ⟶ Spec R` is quasi-compact and quasi-separated and
`(X, D)` is a semi-stable pair over `Spec R` (`DeJong.IsSemistablePair`: `f` nodal, `D ⟶ Spec R`
étale, `D` in the smooth locus of `f`), then for some `B` there are a model `Y ⟶ Spec B` of
finite presentation of `X` and a closed subscheme `D_B ⊆ Y` such that `(Y, D_B)` is a
semi-stable pair over `Spec B` and the pullback of `D_B` to `X` is `D`.

This is Temkin's Remark 3.1.1 (`prem`, M. Temkin, *Stable modification of relative curves*,
`semi-stable.tex` T:2283–2300), semi-stable part, as used for spreading semi-stable
modifications in the proofs of Theorems 1.2 and 1.5 (T:3347–3352, T:3384–3389). Since basic
opens `D(f) ∋` (centre) of `Spec B` are again members `Spec B[1/f]` of the system, "over some
`Spec B`" also means "over a neighbourhood of the centre in some `Spec B`".

## Proof

* `Y` nodal: `Spread.exists_isNodalCurve_baseChange`.
* Smoothness along the marks: `D` has a quasi-compact open neighbourhood `U` in the smooth locus
  of `f`; `U` has smooth models (`Spread.exists_smooth_model_of_isAffine` and the descent of
  properties local on the source, `Spread.exists_baseChange_of_forall_isAffineOpen`), so at
  some level an open `V ⊆ Y` with preimage `U` is smooth over the base
  (`Spread.exists_opens_of_isCompact`).
* The marks: lane LIM1's descent of closed subschemes (`Limits.exists_closedImmersion_model`)
  gives a closed subscheme model `Z ⊆ Y`; it is étale at some level (étale models,
  `Spread.exists_etale_model_of_isAffine`, and the same descent); `Z ⊆ V` at some level, since
  the closed sets `Z_j ∖ V_j` have empty limit (Mathlib's
  `exists_mem_of_isClosed_of_nonempty`, EGA IV 8.3.3).
* The pullback of `D_B = ker(Z ⟶ Y)` to `X` is `D` because `D = Z ×_Y X`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace DeJongAlterations.StableModification.Limits.Spread

universe u

set_option backward.isDefEq.respectTransparency false

open DeJong (IsNodalCurve IsSemistablePair IsSmoothAt)

section Marks

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} {c : Cone D}
  {X Z : Scheme.{u}} {f : X ⟶ c.pt} {fZ : Z ⟶ c.pt} {l : I}
  (m : Model D c f l) (mZ : Model D c fZ l) (a : Z ⟶ X) (ι : mZ.Y ⟶ m.Y)
  (hιf : ι ≫ m.fY = mZ.fY)

/-- The base change of the closed subscheme model `ι : Z_l ⟶ Y_l` to a level `j → l`. -/
def baseChangeι (j : Over l) :
    (baseChangeDiagram D mZ.fY).obj j ⟶ (baseChangeDiagram D m.fY).obj j :=
  pullback.map mZ.fY (D.map j.hom) m.fY (D.map j.hom) ι (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, hιf]) (by simp)

include hιf in
@[reassoc (attr := simp)]
lemma baseChangeι_fst (j : Over l) :
    baseChangeι m mZ ι hιf j ≫ pullback.fst _ _ = pullback.fst _ _ ≫ ι :=
  pullback.lift_fst _ _ _

include hιf in
@[reassoc (attr := simp)]
lemma baseChangeι_snd (j : Over l) :
    baseChangeι m mZ ι hιf j ≫ pullback.snd _ _ = pullback.snd _ _ := by
  simp [baseChangeι]

include hιf in
/-- The base change of `ι` is natural in the level. -/
lemma baseChangeι_naturality {j j' : Over l} (b : j' ⟶ j) :
    (baseChangeDiagram D mZ.fY).map b ≫ baseChangeι m mZ ι hιf j =
      baseChangeι m mZ ι hιf j' ≫ (baseChangeDiagram D m.fY).map b := by
  apply pullback.hom_ext <;> simp

include hιf in
/-- The base change of `ι` is compatible with the projections from the limit. -/
lemma π_baseChangeι (hιg : mZ.g ≫ ι = a ≫ m.g) (ha : a ≫ f = fZ) (j : Over l) :
    (baseChangeCone D c mZ.isPullback).π.app j ≫ baseChangeι m mZ ι hιf j =
      a ≫ (baseChangeCone D c m.isPullback).π.app j := by
  apply pullback.hom_ext
  · simp [hιg]
  · simp [reassoc_of% ha]

include hιf in
/-- The base change of a closed immersion is a closed immersion. -/
lemma isClosedImmersion_baseChangeι [IsClosedImmersion ι] (j : Over l) :
    IsClosedImmersion (baseChangeι m mZ ι hιf j) := by
  have h : IsPullback (pullback.fst _ _) (baseChangeι m mZ ι hιf j) ι (pullback.fst _ _) := by
    refine IsPullback.of_bot ?_ (baseChangeι_fst m mZ ι hιf j).symm
      (IsPullback.of_hasPullback m.fY (D.map j.hom))
    rw [baseChangeι_snd, hιf]
    exact IsPullback.of_hasPullback mZ.fY (D.map j.hom)
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) h inferInstance

end Marks

variable (k : Type u) [Field k] {A L : Type u} [CommRing A] [Algebra k A]
  [Algebra.FiniteType k A] [Field L] [Algebra A L] {R : Subalgebra A L}

/-- A quasi-compact open neighbourhood of a compact set inside a given open set. -/
theorem exists_isCompact_open_between {X : Scheme.{u}} {K : Set X} (hK : IsCompact K)
    (W : X.Opens) (hKW : K ⊆ W) :
    ∃ U : X.Opens, IsCompact (U : Set X) ∧ K ⊆ U ∧ U ≤ W := by
  classical
  let ι := {V : X.Opens // IsAffineOpen V ∧ V ≤ W}
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun V : ι ↦ (V.1 : Set X)) (fun V ↦ V.1.2) (by
    intro x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (hKW hx) W.2
    exact Set.mem_iUnion.mpr ⟨⟨V, hV, hVW⟩, hxV⟩)
  refine ⟨⨆ V ∈ t, V.1, ?_, ?_, iSup₂_le fun V _ ↦ V.2.2⟩
  · simp only [Opens.iSup_mk, Opens.carrier_eq_coe, Opens.coe_mk]
    exact t.isCompact_biUnion fun V _ ↦ V.2.1.isCompact
  · intro x hx
    obtain ⟨V, hVt, hxV⟩ := Set.mem_iUnion₂.mp (ht hx)
    exact (le_iSup₂ (f := fun V (_ : V ∈ t) ↦ V.1) V hVt :) hxV

include k in
/-- **Semi-stable pairs spread out along the approximating system** (Temkin, Rem. 3.1.1,
semi-stable part). Let `f : X ⟶ Spec R` be quasi-compact and quasi-separated, and `(X, D)` a
semi-stable pair over `Spec R`. Then there are a member `B` of the approximating system, a model
`M : Y ⟶ Spec B` of finite presentation of `X`, and a closed subscheme `D_B ⊆ Y` such that
`(Y, D_B)` is a semi-stable pair over `Spec B` and `D_B` pulls back to `D` on `X`. -/
theorem exists_isSemistablePair_model {X : Scheme.{u}} (f : X ⟶ (fgSpecCone R).pt)
    [QuasiCompact f] [QuasiSeparated f] {DX : X.IdealSheafData} (hD : IsSemistablePair f DX) :
    ∃ (B : (FGSubalgebra A R)ᵒᵖ)
      (M : Model ((fgDiagram R).op ⋙ Scheme.Spec) (fgSpecCone R) f B)
      (DM : M.Y.IdealSheafData),
      M.IsFP ∧ IsSemistablePair M.fY DM ∧ DM.comap M.g = DX := by
  have hc := isLimitFGSpecCone R
  have : IsNodalCurve f := hD.nodal
  -- Step 0 and 1: a nodal model
  obtain ⟨B₀, m₀, hm₀⟩ := exists_model_fgSubalgebra R f
  obtain ⟨B₁, h₁, hnod₁⟩ := exists_isNodalCurve_baseChange k m₀ hm₀
  set m₁ := m₀.baseChange h₁
  have hm₁ : m₁.IsFP := hm₀.baseChange h₁
  obtain ⟨_, _, _⟩ := hm₁
  -- Step 2: a smooth open around the marks
  have : CompactSpace (fgSpecCone R).pt := inferInstanceAs (CompactSpace (Spec (.of R)))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨U, hUc, hDU, hUs⟩ := exists_isCompact_open_between DX.support.isClosed.isCompact
    f.smoothLocus (hD.support_subset_smoothLocus)
  have hUsm : Smooth (U.ι ≫ f) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq, eq_top_iff]
    intro x _
    exact hUs x.2
  have hc₁ := isLimitBaseChangeCone _ _ hc m₁.isPullback
  obtain ⟨jO, O, hOc, hO⟩ := exists_preimage_eq _ _ hc₁ U hUc
  let mO := m₁.baseChange jO.hom
  have hmO : mO.IsFP := Model.IsFP.baseChange ⟨‹_›, ‹_›, ‹_›⟩ jO.hom
  let rU := mO.restrict O
  have hrU : rU.IsFP := isFP_restrict hmO O hOc
  have hU' : mO.g ⁻¹ᵁ O = U := hO
  have hsmU' : Smooth ((mO.g ⁻¹ᵁ O).ι ≫ f) := by rw [hU']; exact hUsm
  obtain ⟨j₂, h₂, hsm₂⟩ := exists_baseChange_of_forall_isAffineOpen @Smooth rU hc hrU
    fun W hW ↦ by
      have : IsAffine W := hW
      obtain ⟨B, M, hM, hs⟩ := exists_smooth_model_of_isAffine (W.ι ≫ (mO.g ⁻¹ᵁ O).ι ≫ f)
      exact ⟨op B, M, hM, hs⟩
  obtain ⟨J, V, hV, hVsm⟩ := exists_opens_of_isCompact @Smooth m₁ hc ⟨‹_›, ‹_›, ‹_›⟩ U hUc
    fun W' hW' ↦ by
      subst hW'
      rw [← hU']
      exact ⟨j₂, rU.baseChange h₂, hrU.baseChange h₂, hsm₂⟩
  set m₂ := m₁.baseChange J.hom
  have hm₂ : m₂.IsFP := Model.IsFP.baseChange ⟨‹_›, ‹_›, ‹_›⟩ J.hom
  have hnod₂ : IsNodalCurve m₂.fY := inferInstanceAs (IsNodalCurve (pullback.snd _ _))
  have hV₂ : m₂.g ⁻¹ᵁ V = U := hV
  have hVsm₂ : Smooth (V.ι ≫ m₂.fY) := hVsm
  -- Step 3: a closed subscheme model of the marks
  have : Etale (DX.subschemeι ≫ f) := hD.etale
  obtain ⟨l, g, mZ, ι, hmZ, hι, hιf, hιg⟩ :=
    exists_closedImmersion_model hc m₂ hm₂ (DX.subschemeι ≫ f) DX.subschemeι rfl
  let m₃ := m₂.baseChange g
  have hm₃ : m₃.IsFP := hm₂.baseChange g
  have hnod₃ : IsNodalCurve m₃.fY := inferInstanceAs (IsNodalCurve (pullback.snd _ _))
  let V₃ : m₃.Y.Opens := pullback.fst m₂.fY (((fgDiagram R).op ⋙ Scheme.Spec).map g) ⁻¹ᵁ V
  have hVsm₃ : Smooth (V₃.ι ≫ m₃.fY) :=
    MorphismProperty.of_isPullback (P := @Smooth) ((isPullback_morphismRestrict _ V).paste_vert
      (IsPullback.of_hasPullback m₂.fY (((fgDiagram R).op ⋙ Scheme.Spec).map g))) hVsm₂
  have hgfst : m₃.g ≫ pullback.fst m₂.fY (((fgDiagram R).op ⋙ Scheme.Spec).map g) = m₂.g := by
    change (baseChangeCone _ _ m₂.isPullback).π.app (Over.mk g) ≫ pullback.fst _ _ = m₂.g
    simp
  have hV₃ : m₃.g ⁻¹ᵁ V₃ = U := by
    rw [← hV₂, ← Scheme.Hom.comp_preimage, hgfst]
  -- Step 4: the marks model is étale at some level
  obtain ⟨_, _, _⟩ := hmZ
  obtain ⟨l₁, h₁', het⟩ := exists_baseChange_of_forall_isAffineOpen @Etale mZ hc
    ⟨‹_›, ‹_›, ‹_›⟩ fun W hW ↦ by
      have : IsAffine W := hW
      obtain ⟨B, M, hM, he⟩ := exists_etale_model_of_isAffine (W.ι ≫ DX.subschemeι ≫ f)
      exact ⟨op B, M, hM, he⟩
  let J₁ : Over l := Over.mk h₁'
  -- Step 5: at some level the marks lie in the smooth open
  have hcZ := isLimitBaseChangeCone _ _ hc mZ.isPullback
  let ιj := baseChangeι m₃ mZ ι hιf
  let Vj : ∀ j : Over l, ((baseChangeDiagram _ m₃.fY).obj j).Opens := fun j ↦
    pullback.fst m₃.fY (((fgDiagram R).op ⋙ Scheme.Spec).map j.hom) ⁻¹ᵁ V₃
  let K : ∀ j : Over l, Set ((baseChangeDiagram _ mZ.fY).obj j) := fun j ↦
    ιj j ⁻¹' (Vj j : Set _)ᶜ
  have hKc : ∀ j, IsClosed (K j) := fun j ↦
    (Vj j).isOpen.isClosed_compl.preimage (ιj j).continuous
  have hmaps : ∀ {i i' : Over l} (b : i ⟶ i'),
      Set.MapsTo ((baseChangeDiagram _ mZ.fY).map b) (K i) (K i') := by
    intro i i' b z hz hz'
    apply hz
    have h2 : ιj i' ((baseChangeDiagram _ mZ.fY).map b z) =
        (baseChangeDiagram _ m₃.fY).map b (ιj i z) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, baseChangeι_naturality]
    have h1 : ((baseChangeDiagram _ m₃.fY).map b ≫
        pullback.fst m₃.fY (((fgDiagram R).op ⋙ Scheme.Spec).map i'.hom)) (ιj i z) ∈ V₃ := by
      change pullback.fst m₃.fY (((fgDiagram R).op ⋙ Scheme.Spec).map i'.hom)
        ((baseChangeDiagram _ m₃.fY).map b (ιj i z)) ∈ V₃
      rw [← h2]
      exact hz'
    rw [baseChangeDiagram_map_fst] at h1
    exact h1
  have hK : ∃ j : Over l, K j = ∅ := by
    by_contra hne
    push Not at hne
    obtain ⟨z, hz⟩ := exists_mem_of_isClosed_of_nonempty _ _ hcZ K hKc
      hne (fun j ↦ (hKc j).isCompact) (fun b ↦ hmaps b)
    let j₀ : Over l := Over.mk (𝟙 l)
    let z' : DX.subscheme := z
    have hz₀ : ιj j₀ ((mZ.baseChange j₀.hom).g z') ∉ Vj j₀ := hz j₀
    apply hz₀
    have hπ := π_baseChangeι m₃ mZ DX.subschemeι ι hιf hιg rfl j₀
    have hπz : ιj j₀ ((mZ.baseChange j₀.hom).g z') =
        (m₃.baseChange j₀.hom).g (DX.subschemeι z') :=
      congrArg (fun h ↦ h z') hπ
    have hfst : (m₃.baseChange j₀.hom).g ≫
        pullback.fst m₃.fY (((fgDiagram R).op ⋙ Scheme.Spec).map j₀.hom) = m₃.g := by
      change (baseChangeCone _ _ m₃.isPullback).π.app (Over.mk j₀.hom) ≫ pullback.fst _ _ = _
      simp
    have hmem : DX.subschemeι z' ∈ m₃.g ⁻¹ᵁ V₃ := by
      rw [hV₃]
      apply hDU
      rw [← DX.range_subschemeι]
      exact ⟨z', rfl⟩
    change pullback.fst m₃.fY (((fgDiagram R).op ⋙ Scheme.Spec).map j₀.hom)
      (ιj j₀ ((mZ.baseChange j₀.hom).g z')) ∈ V₃
    rw [hπz]
    have h3 : pullback.fst m₃.fY (((fgDiagram R).op ⋙ Scheme.Spec).map j₀.hom)
        ((m₃.baseChange j₀.hom).g (DX.subschemeι z')) = m₃.g (DX.subschemeι z') :=
      congrArg (fun h ↦ h (DX.subschemeι z')) hfst
    rw [h3]
    exact hmem
  obtain ⟨J₂, hJ₂⟩ := hK
  -- Step 6: a common level
  let Jst := IsCofiltered.min J₁ J₂
  let b₁ : Jst ⟶ J₁ := IsCofiltered.minToLeft J₁ J₂
  let b₂ : Jst ⟶ J₂ := IsCofiltered.minToRight J₁ J₂
  have hetst : Etale (pullback.snd mZ.fY (((fgDiagram R).op ⋙ Scheme.Spec).map Jst.hom)) :=
    MorphismProperty.of_isPullback (P := @Etale)
      (isPullback_baseChangeDiagram_map _ mZ.fY b₁) het
  have hKst : K Jst = ∅ := Set.eq_empty_of_forall_notMem fun z hz ↦ by
    have := hmaps b₂ hz
    rw [hJ₂] at this
    exact this
  -- the final model and marks
  let M := m₃.baseChange Jst.hom
  have hM : M.IsFP := hm₃.baseChange Jst.hom
  let ιst := ιj Jst
  have : IsClosedImmersion ιst := isClosedImmersion_baseChangeι m₃ mZ ι hιf Jst
  refine ⟨op (unop Jst.left), M, ιst.ker, hM, ⟨inferInstanceAs (IsNodalCurve (pullback.snd _ _)),
    ?_, ?_⟩, ?_⟩
  · -- the marks are étale
    have h : ιst.ker.subschemeι ≫ M.fY =
        inv ιst.toImage ≫ pullback.snd mZ.fY (((fgDiagram R).op ⋙ Scheme.Spec).map Jst.hom) := by
      rw [IsIso.eq_inv_comp, ← Category.assoc]
      change (ιst.toImage ≫ ιst.imageι) ≫ pullback.snd _ _ = _
      rw [Scheme.Hom.toImage_imageι]
      exact baseChangeι_snd m₃ mZ ι hιf Jst
    rw [h]
    infer_instance
  · -- the marks lie in the smooth locus
    intro x hx
    rw [Scheme.Hom.support_ker] at hx
    obtain ⟨z, rfl⟩ : x ∈ Set.range ιst := ιst.isClosedEmbedding.isClosed_range.closure_subset hx
    have hzV : ιst z ∈ Vj Jst := by
      by_contra h
      have : z ∈ K Jst := h
      rw [hKst] at this
      exact this
    have hsmst : Smooth ((Vj Jst).ι ≫ M.fY) :=
      MorphismProperty.of_isPullback (P := @Smooth) ((isPullback_morphismRestrict _ V₃).paste_vert
        (IsPullback.of_hasPullback m₃.fY (((fgDiagram R).op ⋙ Scheme.Spec).map Jst.hom))) hVsm₃
    have := Curves.isSmoothAt_of_isOpenImmersion_comp (Vj Jst).ι
      (Curves.isSmoothAt_of_smooth ((Vj Jst).ι ≫ M.fY) ⟨ιst z, hzV⟩)
    exact this
  · -- the marks pull back to `D`
    have e : ιst ≫ M.fY = (mZ.baseChange Jst.hom).fY := baseChangeι_snd m₃ mZ ι hιf Jst
    have hsq : IsPullback DX.subschemeι (mZ.baseChange Jst.hom).g M.g ιst := by
      refine (IsPullback.of_bot ?_ ?_ M.isPullback).flip
      · rw [e]
        exact (mZ.baseChange Jst.hom).isPullback
      · exact (π_baseChangeι m₃ mZ DX.subschemeι ι hιf hιg rfl _)
    have h1 := Scheme.Hom.ker_comp_of_isIso hsq.isoPullback.hom (pullback.fst M.g ιst)
    rw [hsq.isoPullback_hom_fst, Scheme.IdealSheafData.ker_subschemeι] at h1
    rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, ← h1]

end DeJongAlterations.StableModification.Limits.Spread
