import DeJongAlterations.StableModification.Limits.Descent
import DeJongAlterations.StableModification.DeJong.BaseStepProjective

/-!
# Descent of projective morphisms along the approximating system

Let `D : I ⥤ Scheme` be a cofiltered system of affine schemes with affine transition maps,
indexed by a thin category, with limit cone `c` (lane LIM1, `Limits.Descent`). Let `m` be a
model of finite presentation at level `k` of `f : C ⟶ lim D` and `p : m.Y ⟶ Spec R` a structure
morphism to the spectrum of a noetherian ring `R`. Projective space `ℙⁿ_C = C ×_R ℙⁿ_R` has the
model `ℙⁿ_{m.Y} = m.Y ×_R ℙⁿ_R` of finite presentation (`Model.projectiveSpace`), and a closed
subscheme `C' ⊆ ℙⁿ_C` of finite presentation over `lim D`, with a model `r` of finite
presentation, descends to a closed subscheme of `ℙⁿ_{m_l.Y}` at some level `l`
(`exists_isRelativelyProjective_topBaseChange`): the morphism `C' ⟶ C` is the base change of a
morphism `r_l.Y ⟶ m_l.Y` which is projective in the sense of `DeJong.IsRelativelyProjective`.

This is the route of the plan `PLAN-SM-GEOM`, chapter C, avoiding EGA IV 8.10.5 (xii)
(descent of properness, proved there with Chow's lemma): the stable modification of Temkin,
*Stable modification of relative curves* (`semi-stable.tex`), is projective by Theorem 1.1
(T:1713–1716), so it is a closed subscheme of `ℙⁿ_{C ×_S S'}`, and closed immersions descend
(EGA IV 8.10.5 (iv), lane LIM1's `Limits.exists_isClosedImmersion`). Projectivity then gives
properness at the finite level.

## Main results

* `locallyOfFinitePresentation_of_locallyOfFiniteType`: over a locally noetherian base, locally
  of finite type implies locally of finite presentation; in particular
  `projectiveSpaceStructure R n` is of finite presentation for `R` noetherian.
* `isRelativelyProjective_of_isPullback`, `isRelativelyProjective_comp_of_isPullback`:
  base change, and closed subschemes of a scheme presented as a projective space.
* `Model.projectiveSpace`, `Model.IsFP.projectiveSpace`: the model `ℙⁿ_{m.Y}` of `ℙⁿ_C`.
* `isPullback_projectiveSpace_topBaseChange`: projective spaces over models are compatible with
  base change along the system.
* `exists_isRelativelyProjective_topBaseChange`: the descent statement.

Blueprint: `sm-spread-modification.tex`, `lem:sm-spread-mod-fp-projective`,
`def:sm-spread-mod-projective-model`, `prop:sm-spread-mod-projective`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace DeJongAlterations.StableModification.Limits.SpreadModification

universe u

set_option backward.isDefEq.respectTransparency false

open DeJong (IsRelativelyProjective)

/-! ### Finite presentation of projective space -/

/-- **Finite type over a locally noetherian base is finite presentation.** -/
theorem locallyOfFinitePresentation_of_locallyOfFiniteType {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsLocallyNoetherian Y] [LocallyOfFiniteType f] : LocallyOfFinitePresentation f := by
  rw [HasRingHomProperty.iff_appLE (P := @LocallyOfFinitePresentation)]
  intro U V e
  have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian U
  exact RingHom.FinitePresentation.of_finiteType.mp
    (HasRingHomProperty.appLE (P := @LocallyOfFiniteType) f ‹_› U V e)

/-- Projective space over a noetherian ring is of finite presentation. -/
instance locallyOfFinitePresentation_projectiveSpaceStructure (R : Type u) [CommRing R]
    [IsNoetherianRing R] (n : ℕ) : LocallyOfFinitePresentation (projectiveSpaceStructure R n) :=
  locallyOfFinitePresentation_of_locallyOfFiniteType _

/-! ### Relative projectivity -/

section RelativelyProjective

variable {R : Type u} [CommRing R] {X X' T T' : Scheme.{u}}

/-- Relative projectivity is invariant under precomposition with isomorphisms. -/
theorem isRelativelyProjective_iso_comp {pT : T ⟶ Spec (.of R)} {β : X ⟶ T}
    (h : IsRelativelyProjective pT β) (e : X' ≅ X) :
    IsRelativelyProjective pT (e.hom ≫ β) := by
  obtain ⟨n, i, hi, hiβ⟩ := h
  exact ⟨n, e.hom ≫ i, inferInstance, by rw [Category.assoc, hiβ]⟩

/-- **Base change of relative projectivity along a pullback square.** -/
theorem isRelativelyProjective_of_isPullback {pT : T ⟶ Spec (.of R)} {β : X ⟶ T}
    (h : IsRelativelyProjective pT β) {t₁ : X' ⟶ X} {β' : X' ⟶ T'} {t : T' ⟶ T}
    (H : IsPullback t₁ β' β t) :
    IsRelativelyProjective (t ≫ pT) β' := by
  rw [← H.isoPullback_hom_snd]
  exact isRelativelyProjective_iso_comp (h.pullback_snd t) _

/-- **Closed subschemes of a projective space.** If `P` is presented as `T ×_R ℙⁿ_R` by a
pullback square with projection `π : P ⟶ T`, and `ι : Z ⟶ P` is a closed immersion, then
`ι ≫ π` is projective relative to `p : T ⟶ Spec R`. -/
theorem isRelativelyProjective_comp_of_isPullback {P Z : Scheme.{u}} {n : ℕ}
    {q : P ⟶ projectiveSpace R n} {π : P ⟶ T} {p : T ⟶ Spec (.of R)}
    (H : IsPullback q π (projectiveSpaceStructure R n) p) (ι : Z ⟶ P) [IsClosedImmersion ι] :
    IsRelativelyProjective p (ι ≫ π) :=
  ⟨n, ι ≫ H.flip.isoPullback.hom, inferInstance, by
    rw [Category.assoc, IsPullback.isoPullback_hom_fst]⟩

end RelativelyProjective

/-! ### The projective space model -/

section Model

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} {c : Cone D}
  {C : Scheme.{u}} {f : C ⟶ c.pt} {k : I} {R : Type u} [CommRing R]

/-- The square `ℙⁿ_X = X ×_R ℙⁿ_R ⟶ ℙⁿ_T = T ×_R ℙⁿ_R` over `X ⟶ T` is cartesian. -/
lemma isPullback_pullback_map_projectiveSpace {X T : Scheme.{u}} (t : X ⟶ T)
    (pT : T ⟶ Spec (.of R)) (pX : X ⟶ Spec (.of R)) (hpX : t ≫ pT = pX) (n : ℕ) :
    IsPullback (pullback.map pX (projectiveSpaceStructure R n) pT (projectiveSpaceStructure R n)
        t (𝟙 _) (𝟙 _) (by simp [hpX]) (by simp))
      (pullback.fst pX (projectiveSpaceStructure R n))
      (pullback.fst pT (projectiveSpaceStructure R n)) t := by
  subst hpX
  refine IsPullback.of_right (h₁₂ := pullback.snd pT (projectiveSpaceStructure R n))
    (h₂₂ := pT) (v₁₃ := projectiveSpaceStructure R n) ?_ (by simp)
    (IsPullback.of_hasPullback pT (projectiveSpaceStructure R n)).flip
  rw [pullback.lift_snd, Category.comp_id]
  exact (IsPullback.of_hasPullback (t ≫ pT) (projectiveSpaceStructure R n)).flip

/-- The model `ℙⁿ_{m.Y} = m.Y ×_R ℙⁿ_R` at level `k` of `ℙⁿ_C = C ×_R ℙⁿ_R`, for a model `m` of
`C` with a structure morphism `p : m.Y ⟶ Spec R` and `pC = m.g ≫ p`. -/
@[simps]
def _root_.DeJongAlterations.StableModification.Limits.Model.projectiveSpace
    (m : Model D c f k) (p : m.Y ⟶ Spec (.of R))
    (pC : C ⟶ Spec (.of R)) (hpC : m.g ≫ p = pC) (n : ℕ) :
    Model D c (pullback.fst pC (projectiveSpaceStructure R n) ≫ f) k where
  Y := pullback p (projectiveSpaceStructure R n)
  fY := pullback.fst p _ ≫ m.fY
  g := pullback.map pC (projectiveSpaceStructure R n) p (projectiveSpaceStructure R n)
    m.g (𝟙 _) (𝟙 _) (by simp [hpC]) (by simp)
  isPullback :=
    (isPullback_pullback_map_projectiveSpace m.g p pC hpC n).paste_vert m.isPullback

/-- The projective space model of a model of finite presentation is of finite presentation. -/
lemma _root_.DeJongAlterations.StableModification.Limits.Model.IsFP.projectiveSpace
    [IsNoetherianRing R] {m : Model D c f k} (hm : m.IsFP)
    (p : m.Y ⟶ Spec (.of R)) (pC : C ⟶ Spec (.of R)) (hpC : m.g ≫ p = pC) (n : ℕ) :
    (m.projectiveSpace p pC hpC n).IsFP := by
  obtain ⟨_, _, _⟩ := hm
  exact ⟨inferInstanceAs (LocallyOfFinitePresentation (pullback.fst p _ ≫ m.fY)),
    inferInstanceAs (QuasiCompact (pullback.fst p _ ≫ m.fY)),
    inferInstanceAs (QuasiSeparated (pullback.fst p _ ≫ m.fY))⟩

/-- **Projective spaces over models commute with base change.** If `P.Y = m.Y ×_R ℙⁿ_R` via
`q, π`, then `P_l.Y = m_l.Y ×_R ℙⁿ_R` via the base changes. -/
lemma isPullback_projectiveSpace_topBaseChange {X₂ : Scheme.{u}} {f₂ : X₂ ⟶ c.pt}
    (P : Model D c f₂ k) (m : Model D c f k) (π : P.Y ⟶ m.Y) (hπ : π ≫ m.fY = P.fY) {n : ℕ}
    (q : P.Y ⟶ projectiveSpace R n) (p : m.Y ⟶ Spec (.of R))
    (H : IsPullback q π (projectiveSpaceStructure R n) p) (l : Over k) :
    IsPullback (pullback.fst P.fY (D.map l.hom) ≫ q) (topBaseChange P m π hπ l)
      (projectiveSpaceStructure R n) (pullback.fst m.fY (D.map l.hom) ≫ p) :=
  (isPullback_topBaseChange P m π hπ l).paste_horiz H

end Model

/-! ### Descent of closed subschemes of projective spaces -/

section Descent

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} {c : Cone D}
  {k : I} {X₁ X₂ C : Scheme.{u}} {f₁ : X₁ ⟶ c.pt} {f₂ : X₂ ⟶ c.pt} {f : C ⟶ c.pt}
  {R : Type u} [CommRing R]

/-- Base change along the system is functorial: the base change of a composite is the composite
of the base changes. -/
lemma topBaseChange_comp (r : Model D c f₁ k) (P : Model D c f₂ k) (m : Model D c f k)
    (ι : r.Y ⟶ P.Y) (hι : ι ≫ P.fY = r.fY) (π : P.Y ⟶ m.Y) (hπ : π ≫ m.fY = P.fY) (l : Over k) :
    topBaseChange r m (ι ≫ π) (by rw [Category.assoc, hπ, hι]) l =
      topBaseChange r P ι hι l ≫ topBaseChange P m π hπ l := by
  apply pullback.hom_ext
  · simp
  · simp

variable [IsCofiltered I] [Quiver.IsThin I] (hc : IsLimit c)
  [∀ {j k : I} (g : j ⟶ k), IsAffineHom (D.map g)] [∀ j, IsAffine (D.obj j)]

include hc in
/-- **Descent of closed subschemes of projective spaces** (EGA IV 8.10.5 (iv) applied to a
projective embedding). Let `r, P, m` be models at level `k`, `r` and `P` of finite presentation,
with `P.Y = m.Y ×_R ℙⁿ_R` via `q, π`, and let `ι : r.Y ⟶ P.Y` be a morphism over `D k` whose base
change to `lim D` is a closed immersion `a`. Then for some level `l₁`, at every level `l → l₁`
the base change of `ι ≫ π` is projective relative to `m_l.Y ⟶ m.Y ⟶ Spec R`. -/
theorem exists_isRelativelyProjective_topBaseChange (r : Model D c f₁ k) (P : Model D c f₂ k)
    (m : Model D c f k) (hr : r.IsFP) (hP : P.IsFP) (ι : r.Y ⟶ P.Y) (hι : ι ≫ P.fY = r.fY)
    (π : P.Y ⟶ m.Y) (hπ : π ≫ m.fY = P.fY) {n : ℕ} (q : P.Y ⟶ projectiveSpace R n)
    (p : m.Y ⟶ Spec (.of R)) (H : IsPullback q π (projectiveSpaceStructure R n) p)
    (a : X₁ ⟶ X₂) [IsClosedImmersion a] (ha : r.g ≫ ι = a ≫ P.g) (ha' : a ≫ f₂ = f₁) :
    ∃ l₁ : Over k, ∀ (l : Over k), (l ⟶ l₁) →
      IsRelativelyProjective (pullback.fst m.fY (D.map l.hom) ≫ p)
        (topBaseChange r m (ι ≫ π) (by rw [Category.assoc, hπ, hι]) l) := by
  obtain ⟨_, _, _⟩ := hr
  obtain ⟨_, _, _⟩ := hP
  obtain ⟨l₁, hl₁⟩ := exists_isClosedImmersion r P ι hι hc a ha ha'
  refine ⟨l₁, fun l g ↦ ?_⟩
  have : IsClosedImmersion (topBaseChange r P ι hι l) :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (isPullback_topBaseChange_map r P ι hι g) hl₁
  rw [topBaseChange_comp r P m ι hι π hπ l]
  exact isRelativelyProjective_comp_of_isPullback
    (isPullback_projectiveSpace_topBaseChange P m π hπ q p H l) _

end Descent

end DeJongAlterations.StableModification.Limits.SpreadModification
