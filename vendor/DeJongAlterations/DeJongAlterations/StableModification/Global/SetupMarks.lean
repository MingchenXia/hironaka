import DeJongAlterations.StableModification.Global.Statements
import DeJongAlterations.StableModification.Global.Glue
import DeJongAlterations.Geometry.ProjectiveCompactification
import Mathlib.RingTheory.Unramified.Field

/-!
# Transported marks are determined by their points over the generic point

Temkin's stable modification `β : C' ⟶ C` of `(C, D)` carries the *transported marks*
`D' = genericMarksClosure β g D η`, the schematic closure of `β_η⁻¹(D_η)` (Temkin, Remark 4.1,
T:2810; `Curves.IsStableModification.marks_eq`). In the global assembly (`PLAN-T5.md` §2.1, nodes
G3′, G5, G7, gap "G-marks" of §8: LIM3 does not identify the descended marks with the transported
marks) the marks are produced by descent, base change and gluing, and their identification with
the transported marks is reduced here to a statement about **points over the generic point**:

* `ker_eq_vanishingIdeal_closure_range`: the kernel (schematic image) of a quasi-compact morphism
  from a reduced scheme is the reduced induced structure on the closure of its image.
* `eq_vanishingIdeal_of_etale`: marks `D'` étale over an integral base are the reduced induced
  structure on the closure of their points over the generic point (their generic fibre is
  schematically dense by flatness and reduced by étaleness over a field).
* `genericMarksClosure_eq_vanishingIdeal`: if the generic transported marks are reduced, the
  transported marks are the reduced induced structure on the closure of
  `{x | x over η, β x ∈ D}`.
* `eq_genericMarksClosure_of_forall` (**G-marks**): étale marks `D'` are the transported marks as
  soon as a point `x` over `η` lies on `D'` iff `β x` lies on `D`;
  `mem_genericMarksClosure_iff`: conversely the transported marks have this property.
* `isReduced_genericMarks`: the generic transported marks are reduced when `β` is an isomorphism
  on generic fibres and `D` is étale over a neighbourhood of `η`.

Blueprint: `sm-global.tex`, `lem:sm-global-marks`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.StableModification.Global

universe u

open Curves (fiberMap genericMarksClosure)

/-- **Étale schemes over a field are reduced** (an étale algebra over a field is reduced,
`Algebra.FormallyUnramified.isReduced_of_field`). -/
theorem isReduced_of_etale_field {K : Type u} [Field K] {X : Scheme.{u}}
    (q : X ⟶ Spec (.of K)) [Etale q] : IsReduced X := by
  have : ∀ j : X.affineOpenCover.openCover.I₀, IsReduced (X.affineOpenCover.openCover.X j) :=
    fun j ↦ by
    change IsReduced (Spec (X.affineOpenCover.X j))
    have h0 : IsOpenImmersion (X.affineOpenCover.f j) := X.affineOpenCover.map_prop j
    have h1 : Etale (X.affineOpenCover.f j ≫ q) := inferInstance
    have h : Etale (Spec.map (Spec.preimage (X.affineOpenCover.f j ≫ q))) := by
      rw [Spec.map_preimage]
      exact h1
    have h' := (HasRingHomProperty.Spec_iff (P := @Etale)).mp h
    algebraize [(Spec.preimage (X.affineOpenCover.f j ≫ q)).hom]
    have : Algebra.Etale K (X.affineOpenCover.X j) := h'
    have := Algebra.FormallyUnramified.isReduced_of_field K (X.affineOpenCover.X j)
    infer_instance
  exact IsReduced.of_openCover X X.affineOpenCover.openCover

/-- Morphisms from the spectrum of a residue field are quasi-compact. -/
instance quasiCompact_fromSpecResidueField (T : Scheme.{u}) (t : T) :
    QuasiCompact (T.fromSpecResidueField t) := by
  have : Subsingleton (Spec (T.residueField t)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum _))
  exact ⟨fun _ _ _ ↦ Set.subsingleton_of_subsingleton.isCompact⟩

/-- **The schematic image of a reduced scheme** is the reduced induced structure on the closure
of the image. -/
theorem ker_eq_vanishingIdeal_closure_range {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f]
    [IsReduced Y] :
    f.ker = Scheme.IdealSheafData.vanishingIdeal ⟨closure (Set.range f), isClosed_closure⟩ := by
  have := Geometry.ProjectiveCompactification.image_isReduced f
  have h := ker_eq_vanishingIdeal_of_isClosedImmersion f.imageι (closure (Set.range f))
    isClosed_closure (by
      rw [Scheme.Hom.imageι, Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.support_ker])
  rwa [Scheme.Hom.imageι, Scheme.IdealSheafData.ker_subschemeι] at h

/-- **Étale marks are the closure of their generic points.** If `T` is integral and `D' ⊆ X` is
étale over `T`, then `D'` is the reduced induced structure on the closure of its points over
the generic point: the generic fibre of `D'` is schematically dense in `D'` (flat base change of
the schematically dense `Spec κ(η) ⟶ T`) and reduced (étale over `κ(η)`). -/
theorem eq_vanishingIdeal_of_etale {T X : Scheme.{u}} [IsIntegral T] (q : X ⟶ T)
    (D' : X.IdealSheafData) [Etale (D'.subschemeι ≫ q)] :
    D' = Scheme.IdealSheafData.vanishingIdeal
      ⟨closure ((D'.support : Set X) ∩ q ⁻¹' {genericPoint T}), isClosed_closure⟩ := by
  obtain ⟨_, _⟩ := isSchemeTheoreticallyDominant_fromSpecResidueField_genericPoint T
  have : IsSchemeTheoreticallyDominant
      (pullback.fst (D'.subschemeι ≫ q) (T.fromSpecResidueField (genericPoint T))) :=
    IsSchemeTheoreticallyDominant.pullbackFst _ _
  have he : Etale (pullback.snd (D'.subschemeι ≫ q) (T.fromSpecResidueField (genericPoint T))) :=
    inferInstance
  have : IsReduced (pullback (D'.subschemeι ≫ q) (T.fromSpecResidueField (genericPoint T))) :=
    @isReduced_of_etale_field _ _ _
      (pullback.snd (D'.subschemeι ≫ q) (T.fromSpecResidueField (genericPoint T))) he
  set F := T.fromSpecResidueField (genericPoint T)
  have hker : (pullback.fst (D'.subschemeι ≫ q) F ≫ D'.subschemeι).ker = D' := by
    rw [Scheme.Hom.ker_comp, (pullback.fst (D'.subschemeι ≫ q) F).ker_eq_bot,
      Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.ker_subschemeι]
  have hrange : Set.range (pullback.fst (D'.subschemeι ≫ q) F ≫ D'.subschemeι) =
      (D'.support : Set X) ∩ q ⁻¹' {genericPoint T} := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Pullback.range_fst,
      Scheme.range_fromSpecResidueField]
    ext x
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact ⟨by rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨d, rfl⟩, hd⟩
    · rintro ⟨hx, hxη⟩
      rw [← Scheme.IdealSheafData.range_subschemeι] at hx
      obtain ⟨d, rfl⟩ := hx
      exact ⟨d, hxη, rfl⟩
  have h2 := ker_eq_vanishingIdeal_closure_range
    (pullback.fst (D'.subschemeι ≫ q) F ≫ D'.subschemeι)
  rw [hker] at h2
  refine h2.trans ?_
  rw [hrange]

variable {T P X : Scheme.{u}} {g : P ⟶ T} {β : X ⟶ P}

/-- The points of the generic transported marks, viewed in `X`. -/
theorem range_genericMarks (β : X ⟶ P) (g : P ⟶ T) (D : P.IdealSheafData) (s : T) :
    Set.range (((DeJong.fiberMarks g D s).comap (fiberMap β g s)).subschemeι ≫
        (β ≫ g).fiberι s) =
      {x | (β ≫ g) x = s ∧ β x ∈ (D.support : Set P)} := by
  ext x
  constructor
  · rintro ⟨e, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← Set.mem_singleton_iff, ← Set.mem_preimage, ← Scheme.Hom.range_fiberι,
        Scheme.Hom.comp_apply]
      exact ⟨_, rfl⟩
    · have he : (((DeJong.fiberMarks g D s).comap (fiberMap β g s)).subschemeι e) ∈
          (((DeJong.fiberMarks g D s).comap (fiberMap β g s)).support : Set _) := by
        rw [← Scheme.IdealSheafData.range_subschemeι]
        exact ⟨e, rfl⟩
      rw [Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.support_comap] at he
      change g.fiberι s (fiberMap β g s _) ∈ (D.support : Set P) at he
      rw [← Scheme.Hom.comp_apply, Curves.fiberMap_fiberι, Scheme.Hom.comp_apply] at he
      rwa [Scheme.Hom.comp_apply]
  · rintro ⟨hxs, hxD⟩
    have : x ∈ Set.range ((β ≫ g).fiberι s) := by
      rw [Scheme.Hom.range_fiberι]
      exact hxs
    obtain ⟨y, rfl⟩ := this
    have hy : y ∈ (((DeJong.fiberMarks g D s).comap (fiberMap β g s)).support : Set _) := by
      rw [Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.support_comap]
      change g.fiberι s (fiberMap β g s y) ∈ (D.support : Set P)
      rw [← Scheme.Hom.comp_apply, Curves.fiberMap_fiberι, Scheme.Hom.comp_apply]
      exact hxD
    rw [← Scheme.IdealSheafData.range_subschemeι] at hy
    obtain ⟨e, rfl⟩ := hy
    exact ⟨e, rfl⟩

theorem quasiCompact_genericMarks (β : X ⟶ P) (g : P ⟶ T) (D : P.IdealSheafData) (s : T) :
    QuasiCompact (((DeJong.fiberMarks g D s).comap (fiberMap β g s)).subschemeι ≫
      (β ≫ g).fiberι s) := by
  have : QuasiCompact ((β ≫ g).fiberι s) :=
    inferInstanceAs (QuasiCompact (pullback.fst (β ≫ g) (T.fromSpecResidueField s)))
  exact MorphismProperty.comp_mem @QuasiCompact _ _
    (inferInstance : QuasiCompact ((DeJong.fiberMarks g D s).comap (fiberMap β g s)).subschemeι)
    this

/-- **The transported marks as a reduced closure.** If the generic transported marks
`β_η⁻¹(D_η)` are reduced, the transported marks are the reduced induced structure on the closure
of `{x | x over η, β x ∈ D}`. -/
theorem genericMarksClosure_eq_vanishingIdeal (β : X ⟶ P) (g : P ⟶ T) (D : P.IdealSheafData)
    (s : T) [IsReduced ((DeJong.fiberMarks g D s).comap (fiberMap β g s)).subscheme] :
    genericMarksClosure β g D s = Scheme.IdealSheafData.vanishingIdeal
      ⟨closure {x | (β ≫ g) x = s ∧ β x ∈ (D.support : Set P)}, isClosed_closure⟩ := by
  have := quasiCompact_genericMarks β g D s
  unfold genericMarksClosure
  rw [ker_eq_vanishingIdeal_closure_range, range_genericMarks]

/-- **Points of the transported marks over the generic point**: a point `x` of `C'` over `s`
lies on the transported marks iff `β x` lies on `D`. -/
theorem mem_genericMarksClosure_iff (β : X ⟶ P) (g : P ⟶ T) (D : P.IdealSheafData) (s : T)
    (x : X) (hx : (β ≫ g) x = s) :
    x ∈ ((genericMarksClosure β g D s).support : Set X) ↔ β x ∈ (D.support : Set P) := by
  have := quasiCompact_genericMarks β g D s
  unfold genericMarksClosure
  rw [Scheme.Hom.support_ker, range_genericMarks]
  constructor
  · intro h
    have hcl : IsClosed (β ⁻¹' (D.support : Set P)) := D.support.isClosed.preimage β.continuous
    exact closure_minimal (fun y hy ↦ hy.2) hcl h
  · intro h
    exact subset_closure ⟨hx, h⟩

/-- **G-marks: étale marks with the right points over the generic point are the transported
marks** (`PLAN-T5.md` §8, "LIM3 … does not identify the descended marks with the transported
marks"). Let `T` be integral, `β : X ⟶ P` over `g : P ⟶ T`, `D ⊆ P` with reduced generic
transported marks, and `D' ⊆ X` étale over `T`. If a point `x` of `X` over the generic point lies
on `D'` iff `β x` lies on `D`, then `D'` is the transported marks `genericMarksClosure β g D η`. -/
theorem eq_genericMarksClosure_of_forall [IsIntegral T] (β : X ⟶ P) (g : P ⟶ T)
    (D : P.IdealSheafData) (D' : X.IdealSheafData) [Etale (D'.subschemeι ≫ β ≫ g)]
    [IsReduced ((DeJong.fiberMarks g D (genericPoint T)).comap
      (fiberMap β g (genericPoint T))).subscheme]
    (h : ∀ x : X, (β ≫ g) x = genericPoint T →
      (x ∈ (D'.support : Set X) ↔ β x ∈ (D.support : Set P))) :
    D' = genericMarksClosure β g D (genericPoint T) := by
  have hset : (D'.support : Set X) ∩ (β ≫ g) ⁻¹' {genericPoint T} =
      {x | (β ≫ g) x = genericPoint T ∧ β x ∈ (D.support : Set P)} := by
    ext x
    constructor
    · rintro ⟨hxD, hxη⟩
      exact ⟨hxη, (h x hxη).mp hxD⟩
    · rintro ⟨hxη, hxD⟩
      exact ⟨(h x hxη).mpr hxD, hxη⟩
  rw [genericMarksClosure_eq_vanishingIdeal]
  refine (eq_vanishingIdeal_of_etale (β ≫ g) D').trans ?_
  rw [hset]

/-- The generic transported marks are the pull-back of `β⁻¹(D)` to the generic fibre. -/
theorem genericMarks_eq_comap (β : X ⟶ P) (g : P ⟶ T) (D : P.IdealSheafData) (s : T) :
    (DeJong.fiberMarks g D s).comap (fiberMap β g s) = (D.comap β).comap ((β ≫ g).fiberι s) := by
  rw [DeJong.fiberMarks, ← Scheme.IdealSheafData.comap_comp, Curves.fiberMap_fiberι,
    Scheme.IdealSheafData.comap_comp]

/-- The generic fibre of `D' ⊆ X` over an integral `T` is schematically dense in `D'` when `D'`
is flat over `T`: the projection `X_η ×_X D' ⟶ D'` is scheme-theoretically dominant. -/
theorem isSchemeTheoreticallyDominant_pullback_snd_fiberι [IsIntegral T] (q : X ⟶ T)
    (D' : X.IdealSheafData) [Flat (D'.subschemeι ≫ q)] :
    IsSchemeTheoreticallyDominant (pullback.snd (q.fiberι (genericPoint T)) D'.subschemeι) := by
  obtain ⟨_, _⟩ := isSchemeTheoreticallyDominant_fromSpecResidueField_genericPoint T
  have H : IsPullback (pullback.fst (q.fiberι (genericPoint T)) D'.subschemeι ≫
      pullback.snd q (T.fromSpecResidueField (genericPoint T)))
      (pullback.snd (q.fiberι (genericPoint T)) D'.subschemeι)
      (T.fromSpecResidueField (genericPoint T)) (D'.subschemeι ≫ q) :=
    (IsPullback.of_hasPullback (q.fiberι (genericPoint T)) D'.subschemeι).paste_horiz
      (IsPullback.of_hasPullback q (T.fromSpecResidueField (genericPoint T))).flip
  exact IsSchemeTheoreticallyDominant.of_isPullback H

/-- **Flat marks are the closure of their generic fibre**: for `D' ⊆ X` flat over the integral
`T`, `D'` is the kernel (schematic image) of `D'_η ⟶ X`. -/
theorem ker_comap_fiberι_subschemeι [IsIntegral T] (q : X ⟶ T) (D' : X.IdealSheafData)
    [Flat (D'.subschemeι ≫ q)] :
    ((D'.comap (q.fiberι (genericPoint T))).subschemeι ≫ q.fiberι (genericPoint T)).ker = D' := by
  have := isSchemeTheoreticallyDominant_pullback_snd_fiberι q D'
  rw [← Scheme.IdealSheafData.comapIso_hom_fst, Category.assoc, Scheme.Hom.ker_comp_of_isIso,
    pullback.condition, Scheme.Hom.ker_comp,
    (pullback.snd (q.fiberι (genericPoint T)) D'.subschemeι).ker_eq_bot,
    Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.ker_subschemeι]

/-- **G-marks, scheme-theoretic form.** Let `T` be integral and `D' ⊆ X` flat over `T`. If on the
generic fibre `X_η` the marks `D'` agree with `β⁻¹(D)` (as closed subschemes), then `D'` is the
transported marks `genericMarksClosure β g D η`. -/
theorem eq_genericMarksClosure_of_comap_eq [IsIntegral T] (β : X ⟶ P) (g : P ⟶ T)
    (D : P.IdealSheafData) (D' : X.IdealSheafData) [Flat (D'.subschemeι ≫ β ≫ g)]
    (h : D'.comap ((β ≫ g).fiberι (genericPoint T)) =
      (D.comap β).comap ((β ≫ g).fiberι (genericPoint T))) :
    D' = genericMarksClosure β g D (genericPoint T) := by
  unfold genericMarksClosure
  rw [genericMarks_eq_comap, ← h, ker_comap_fiberι_subschemeι]

/-- **The generic condition from points** (for reduced generic marks): two closed subschemes of
the generic fibre with reduced subscheme structure agree as soon as they have the same points. -/
theorem comap_eq_of_forall_of_isReduced (q : X ⟶ T) (s : T) (D₁ D₂ : X.IdealSheafData)
    [IsReduced (D₁.comap (q.fiberι s)).subscheme] [IsReduced (D₂.comap (q.fiberι s)).subscheme]
    (h : ∀ x : X, q x = s → (x ∈ (D₁.support : Set X) ↔ x ∈ (D₂.support : Set X))) :
    D₁.comap (q.fiberι s) = D₂.comap (q.fiberι s) := by
  have hr : ∀ D : X.IdealSheafData, Set.range (D.comap (q.fiberι s)).subschemeι =
      (q.fiberι s) ⁻¹' (D.support : Set X) := fun D ↦ by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_comap]
    rfl
  have hc : ∀ D : X.IdealSheafData, IsClosed ((q.fiberι s) ⁻¹' (D.support : Set X)) :=
    fun D ↦ D.support.isClosed.preimage (q.fiberι s).continuous
  have e₁ := ker_eq_vanishingIdeal_of_isClosedImmersion (D₁.comap (q.fiberι s)).subschemeι _
    (hc D₁) (hr D₁)
  have e₂ := ker_eq_vanishingIdeal_of_isClosedImmersion (D₂.comap (q.fiberι s)).subschemeι _
    (hc D₂) (hr D₂)
  rw [Scheme.IdealSheafData.ker_subschemeι] at e₁ e₂
  rw [e₁, e₂]
  congr 2
  ext y
  have hy : q (q.fiberι s y) = s := by
    have : q.fiberι s y ∈ Set.range (q.fiberι s) := ⟨y, rfl⟩
    rw [Scheme.Hom.range_fiberι] at this
    exact this
  exact h _ hy

/-- **Generic fibres of étale marks are reduced**: if `D' ⊆ X` is étale over `T`, its restriction
to the fibre over any point is étale over the residue field, hence reduced. -/
theorem isReduced_comap_fiberι_of_etale (q : X ⟶ T) (D' : X.IdealSheafData)
    [Etale (D'.subschemeι ≫ q)] (s : T) : IsReduced (D'.comap (q.fiberι s)).subscheme := by
  have H : IsPullback (pullback.fst (q.fiberι s) D'.subschemeι ≫
      pullback.snd q (T.fromSpecResidueField s))
      (pullback.snd (q.fiberι s) D'.subschemeι)
      (T.fromSpecResidueField s) (D'.subschemeι ≫ q) :=
    (IsPullback.of_hasPullback (q.fiberι s) D'.subschemeι).paste_horiz
      (IsPullback.of_hasPullback q (T.fromSpecResidueField s)).flip
  have he : Etale (pullback.fst (q.fiberι s) D'.subschemeι ≫
      pullback.snd q (T.fromSpecResidueField s)) :=
    MorphismProperty.of_isPullback (P := @Etale) H.flip inferInstance
  have : IsReduced (pullback (q.fiberι s) D'.subschemeι) :=
    @isReduced_of_etale_field _ _ _ _ he
  exact isReduced_of_isOpenImmersion (D'.comapIso (q.fiberι s)).hom

end DeJongAlterations.StableModification.Global
