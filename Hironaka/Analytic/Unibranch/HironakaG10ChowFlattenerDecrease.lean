import Hironaka.Analytic.Unibranch.HironakaG10ChowCentreMachine
import Hironaka.Analytic.Unibranch.HironakaG10ChowProductCentre
import Hironaka.Resolution.HironakaG10ChowAnalyticSquare

/-!
# Native Lemma 1.18: the fibre decreases where the pulled flattener is the pulled centre (M6)

Module M6 of lane G10H's plan (`work/hironaka-resume-20261111/G10H/HIRONAKA75-GLOBAL-STEP.md` §4),
proved natively, without named input.  Source: Hironaka, *Flattening theorem in complex-analytic
geometry* (1975), (2.4.3), Th. 2.5, Lemma 3.1 (printed pp. 526, 529–530), Lemma 4.6.1 (p. 544);
Rydh, Lemma 1.18.

* `stalkConst`, `nonempty_germPresentation` — every stalk of a reduced complex space is an analytic
  algebra (a quotient of the germs of some `ℂⁿ`, compatibly with the constants), and stalk maps of
  morphisms respect the constants (`stalkMap_stalkConst`);
* `IsPointFlattenerAt`, `exists_isPointFlattenerAt` — pointed flatteners of `f` at every point of a
  fibre (Hironaka (1.14.2) at a point; from `HironakaG10ChowAnalyticSquare.exists_pointFlattener`);
* `IsGermFlattenerAt` (G10H's whole-fibre flattener, tested on closed-subspace germs) and
  `eq_iSup_of_isGermFlattenerAt` — it is the sum of the pointed flatteners;
* `exists_fibre_decrease_of_pointFlattener` — Lemma 1.18 at one point of a commutative square;
* `exists_fibre_decrease_of_flattener` — **Lemma 1.18 for one admissible blowup step**: if the
  whole-fibre flattener of `f` at `σ x'` pulls back to the pulled centre at `x'`, the fibre strictly
  decreases over `x'` (point selection, `exists_map_eq_span_of_iSup`);
* `stepFibreDecreasesAt_of_flattener` (stateless driver), `machine_stepFibreDecreasesAt_of_flattener`
  (centre machines, the form consumed by `exists_flattening_of_machine'` through `hfreq`).
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry IsLocalRing
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10ChowFlattenerDecrease

open Hironaka Hironaka
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaActualAnalyticSubspace
  HironakaReducedComplexAnalyticSpaces HironakaActualAnalyticSubspaceResidue
  HironakaSingularModuleSheafStalk HironakaNativePulledIdealSheaf
  HironakaG10ChowFibreAlgebra HironakaG10ChowAnalyticSquare HironakaG10ChowFibreTorsionWitness
  SourceReducedComplexSpace HironakaG10ChowOneStepStrictTransform HironakaG10ChowStrictTorsionFree
  HironakaG10ChowProductCentre HironakaG10ChowFlatteningDriver HironakaG10ChowFibreChain

noncomputable section

/-! ### Constants and analytic presentations of native stalks -/

/-- The constants at a point of the complex point. -/
def pointConst (p : complexPoint) : ℂ →+* complexPoint.presheaf.stalk p :=
  (eqToHom (congrArg complexPoint.presheaf.stalk (Subsingleton.elim (0 : ComplexModel 0) p))).hom.comp
    actualComplexPointStalkEquiv.symm.toRingHom

/-- The constants of a stalk of a space over the complex point. -/
def stalkConst {T : LocallyRingedSpace.{0}} (Ψ : T ⟶ complexPoint) (t : T) :
    ℂ →+* T.presheaf.stalk t :=
  (Ψ.stalkMap t).hom.comp (pointConst (Ψ.base t))

theorem stalkMap_stalkConst {T T' : LocallyRingedSpace.{0}} (g : T ⟶ T') (Ψ : T' ⟶ complexPoint)
    (t : T) (c : ℂ) : (g.stalkMap t).hom (stalkConst Ψ (g.base t) c) = stalkConst (g ≫ Ψ) t c := by
  unfold stalkConst
  rw [LocallyRingedSpace.stalkMap_comp]
  rfl

theorem stalkConst_congr {T : LocallyRingedSpace.{0}} (Ψ Ψ' : T ⟶ complexPoint) (h : Ψ = Ψ')
    (t : T) : stalkConst Ψ t = stalkConst Ψ' t := by
  subst h
  rfl

theorem eqToHom_stalkConst {T : LocallyRingedSpace.{0}} (Ψ : T ⟶ complexPoint) {a b : T}
    (h : a = b) (c : ℂ) :
    (eqToHom (congrArg T.presheaf.stalk h)).hom (stalkConst Ψ a c) = stalkConst Ψ b c := by
  subst h
  rfl

/-- On an embedded model the constants are the constant germs. -/
theorem model_stalkConst {n : ℕ} (U : Opens (ComplexModel n)) (C : Set U) (c : C) (κ : ℂ) :
    stalkConst (modelOver U C).hom c κ = actualSubspaceStalkConst (n := n) C c κ :=
  actualSubspacePointMap_stalk_const (n := n) C c κ

/-- **Every stalk of a reduced complex space is an analytic algebra.** -/
theorem nonempty_germPresentation (X : SourceReducedComplexSpace) (x : X.obj.left) :
    Nonempty (GermPresentation (X.obj.left.presheaf.stalk x) (stalkConst X.obj.hom x)) := by
  obtain ⟨n, U, C, -, i, hi, hpoint, c, rfl⟩ := X.property.2.2 x
  let _ : LocallyRingedSpace.IsOpenImmersion i := hi
  let πC : HolGerm (ComplexModel n) →+* (modelOver U C).left.presheaf.stalk c :=
    (actualSubspaceStalkChartEquiv (n := n) C c).symm.toRingHom.comp (Ideal.Quotient.mk _)
  have hπC : Function.Surjective πC :=
    (actualSubspaceStalkChartEquiv (n := n) C c).symm.surjective.comp Ideal.Quotient.mk_surjective
  have hiso : IsIso (i.stalkMap c) := LocallyRingedSpace.IsOpenImmersion.stalk_iso i c
  let e := asIso (i.stalkMap c)
  refine ⟨⟨n, e.inv.hom.comp πC, ?_, fun κ => ?_⟩⟩
  · exact (ConcreteCategory.bijective_of_isIso e.inv).2.comp hπC
  · apply (ConcreteCategory.bijective_of_isIso e.hom).1
    change e.hom.hom (e.inv.hom (πC (algebraMap ℂ _ κ))) = (i.stalkMap c).hom (stalkConst X.obj.hom _ κ)
    rw [← CommRingCat.comp_apply, e.inv_hom_id, CommRingCat.id_apply, stalkMap_stalkConst,
      stalkConst_congr _ _ hpoint]
    exact (model_stalkConst U C c κ).symm

/-- Stalk maps of morphisms of reduced complex spaces respect the constants. -/
theorem stalkMap_stalkConst' {X Y : SourceReducedComplexSpace} (f : Y ⟶ X) (y : Y.obj.left)
    (c : ℂ) :
    (f.hom.left.stalkMap y).hom (stalkConst X.obj.hom (f.hom.left.base y) c) =
      stalkConst Y.obj.hom y c := by
  rw [stalkMap_stalkConst, stalkConst_congr _ _ (Over.w f.hom)]

/-! ### Pointed and whole-fibre flatteners -/

variable {X Y : SourceReducedComplexSpace}

/-- The stalk map of `f` at `y`, read from the stalk at a point `x = f y`. -/
abbrev fibreStalkMap (f : Y ⟶ X) (x : X.obj.left) (y : Y.obj.left) (h : f.hom.left.base y = x) :
    X.obj.left.presheaf.stalk x →+* Y.obj.left.presheaf.stalk y :=
  (f.hom.left.stalkMap y).hom.comp (eqToHom (congrArg X.obj.left.presheaf.stalk h.symm)).hom

/-- **Pointed flattener** of `f` at `y` (over `x = f y`): base change to the germ `V(J)` makes `f`
flat at `y` iff `I ≤ J` (Hironaka (1.14.2), at one point). -/
def IsPointFlattenerAt (f : Y ⟶ X) (x : X.obj.left) (y : Y.obj.left) (h : f.hom.left.base y = x)
    (I : Ideal (X.obj.left.presheaf.stalk x)) : Prop :=
  ∀ J : Ideal (X.obj.left.presheaf.stalk x),
    (Ideal.quotientMap (J.map (fibreStalkMap f x y h)) (fibreStalkMap f x y h)
      Ideal.le_comap_map).Flat ↔ I ≤ J

/-- **Native whole-fibre flattener** at `x` (lane G10H's statement): `f` becomes flat at every
point of the fibre over `x` after base change to the germ `V(J)` iff `I ≤ J` (Hironaka (1.14.2);
HLT 1973 Th. 1′, Frisch 1968 Lemme 5). -/
def IsGermFlattenerAt (f : Y ⟶ X) (x : X.obj.left) (I : Ideal (X.obj.left.presheaf.stalk x)) :
    Prop :=
  ∀ J : Ideal (X.obj.left.presheaf.stalk x),
    (∀ (y : Y.obj.left) (h : f.hom.left.base y = x),
      (Ideal.quotientMap (J.map (fibreStalkMap f x y h)) (fibreStalkMap f x y h)
        Ideal.le_comap_map).Flat) ↔ I ≤ J

theorem isLocalHom_fibreStalkMap (f : Y ⟶ X) (x : X.obj.left) (y : Y.obj.left)
    (h : f.hom.left.base y = x) : IsLocalHom (fibreStalkMap f x y h) := by
  subst h
  change IsLocalHom ((f.hom.left.stalkMap y).hom.comp (RingHom.id _))
  rw [RingHom.comp_id]
  infer_instance

theorem fibreStalkMap_stalkConst (f : Y ⟶ X) (x : X.obj.left) (y : Y.obj.left)
    (h : f.hom.left.base y = x) (c : ℂ) :
    fibreStalkMap f x y h (stalkConst X.obj.hom x c) = stalkConst Y.obj.hom y c := by
  subst h
  exact stalkMap_stalkConst' f y c

theorem map_fibreStalkMap_maximalIdeal (f : Y ⟶ X) (x : X.obj.left) (y : Y.obj.left)
    (h : f.hom.left.base y = x) :
    Ideal.map (fibreStalkMap f x y h) (maximalIdeal (X.obj.left.presheaf.stalk x)) =
      fibreIdealAt f y := by
  subst h
  change Ideal.map ((f.hom.left.stalkMap y).hom.comp (RingHom.id _)) _ = _
  rw [RingHom.comp_id]
  rfl

/-- **Pointed flatteners exist** at every point of every fibre. -/
theorem exists_isPointFlattenerAt (f : Y ⟶ X) (x : X.obj.left) (y : Y.obj.left)
    (h : f.hom.left.base y = x) : ∃ I, IsPointFlattenerAt f x y h I := by
  obtain ⟨PX⟩ := nonempty_germPresentation X x
  obtain ⟨PY⟩ := nonempty_germPresentation Y y
  have := isLocalHom_fibreStalkMap f x y h
  exact exists_pointFlattener PX PY (fibreStalkMap f x y h) (fibreStalkMap_stalkConst f x y h)

/-- The whole-fibre flattener is the sum of the pointed flatteners. -/
theorem eq_iSup_of_isGermFlattenerAt (f : Y ⟶ X) (x : X.obj.left)
    (I : Ideal (X.obj.left.presheaf.stalk x)) (hI : IsGermFlattenerAt f x I)
    (Iy : {y : Y.obj.left // f.hom.left.base y = x} → Ideal (X.obj.left.presheaf.stalk x))
    (hIy : ∀ k, IsPointFlattenerAt f x k.1 k.2 (Iy k)) : I = ⨆ k, Iy k := by
  refine pointFlattener_unique (fun J => ∀ (y : Y.obj.left) (h : f.hom.left.base y = x),
    (Ideal.quotientMap (J.map (fibreStalkMap f x y h)) (fibreStalkMap f x y h)
      Ideal.le_comap_map).Flat) I _ hI (fun J => ?_)
  rw [iSup_le_iff]
  exact ⟨fun H k => (hIy k J).mp (H k.1 k.2), fun H y h => (hIy ⟨y, h⟩ J).mpr (H ⟨y, h⟩)⟩

/-! ### Lemma 1.18 at one point of a commutative square -/

theorem stalkMap_eq_of_eq {T S : LocallyRingedSpace.{0}} (Θ₁ Θ₂ : T ⟶ S) (H : Θ₁ = Θ₂) (t : T)
    (hb : Θ₂.base t = Θ₁.base t) (r : S.presheaf.stalk (Θ₁.base t)) :
    (Θ₁.stalkMap t).hom r =
      (Θ₂.stalkMap t).hom ((eqToHom (congrArg S.presheaf.stalk hb.symm)).hom r) := by
  subst H
  rfl

theorem nativePulledIdealStalkIdeal_eqToHom {A D : LocallyRingedSpace.{0}} (F : A ⟶ D)
    (M : SheafOfModules.{0} (forgetRing D.toSheafedSpace.sheaf))
    (m : M ⟶ SheafOfModules.unit (forgetRing D.toSheafedSpace.sheaf)) {a c : A} (h : a = c) :
    nativePulledIdealStalkIdeal F M m c =
      Ideal.map (eqToHom (congrArg A.presheaf.stalk h)).hom (nativePulledIdealStalkIdeal F M m a) := by
  subst h
  rw [eqToHom_refl, CommRingCat.hom_id, Ideal.map_id]

variable {X' Y' : SourceReducedComplexSpace}

/-- **Native Lemma 1.18 at one point** (Hironaka (2.4.3), Th. 2.5; Rydh, Lemma 1.18): in a
commutative square `p ≫ σ = q ≫ f`, if the pointed flattener of `f` at `q y'` pulls back to `p y'`
as `(a)` with `a` regular and `p^♯ a` regular at `y'`, then some germ at `q y'` outside the fibre
ideal of `f` is sent by `q^♯` into the fibre ideal of `p` at `y'`. -/
theorem exists_fibre_decrease_of_pointFlattener (f : Y ⟶ X) (σ : X' ⟶ X) (p : Y' ⟶ X')
    (q : Y' ⟶ Y) (hsq : p ≫ σ = q ≫ f) (y' : Y'.obj.left) (x' : X'.obj.left)
    (hp : p.hom.left.base y' = x') (y : Y.obj.left) (hq : q.hom.left.base y' = y)
    (h : f.hom.left.base y = σ.hom.left.base x')
    (I : Ideal (X.obj.left.presheaf.stalk (σ.hom.left.base x')))
    (hI : IsPointFlattenerAt f _ y h I)
    (a : X'.obj.left.presheaf.stalk x') (ha : IsRegular a)
    (hRR : Ideal.map (σ.hom.left.stalkMap x').hom I = Ideal.span {a})
    (hpa : IsRegular (fibreStalkMap p x' y' hp a)) :
    ∃ g : Y.obj.left.presheaf.stalk (q.hom.left.base y'),
      g ∉ fibreIdealAt f (q.hom.left.base y') ∧
        (q.hom.left.stalkMap y').hom g ∈ fibreIdealAt p y' := by
  subst hp
  subst hq
  obtain ⟨PX⟩ := nonempty_germPresentation X (σ.hom.left.base (p.hom.left.base y'))
  obtain ⟨PY⟩ := nonempty_germPresentation Y (q.hom.left.base y')
  obtain ⟨PX'⟩ := nonempty_germPresentation X' (p.hom.left.base y')
  obtain ⟨PB⟩ := nonempty_germPresentation Y' y'
  have := isLocalHom_fibreStalkMap f _ _ h
  have H : p.hom.left ≫ σ.hom.left = q.hom.left ≫ f.hom.left :=
    congrArg (fun H => H.hom.left) hsq
  have hsq' : ∀ r, (p.hom.left.stalkMap y').hom
      ((σ.hom.left.stalkMap (p.hom.left.base y')).hom r) =
        (q.hom.left.stalkMap y').hom (fibreStalkMap f _ _ h r) := by
    intro r
    have e1 : (p.hom.left.stalkMap y').hom ((σ.hom.left.stalkMap (p.hom.left.base y')).hom r) =
        ((p.hom.left ≫ σ.hom.left).stalkMap y').hom r := by
      rw [LocallyRingedSpace.stalkMap_comp]
      rfl
    rw [e1, stalkMap_eq_of_eq _ _ H y' h r, LocallyRingedSpace.stalkMap_comp]
    rfl
  obtain ⟨g, hg, hqg⟩ := exists_fibre_decrease_of_square PX PY PX' PB (fibreStalkMap f _ _ h)
    (σ.hom.left.stalkMap (p.hom.left.base y')).hom (p.hom.left.stalkMap y').hom
    (q.hom.left.stalkMap y').hom (fibreStalkMap_stalkConst f _ _ h)
    (stalkMap_stalkConst' σ _) (stalkMap_stalkConst' p y') (stalkMap_stalkConst' q y')
    hsq' I hI a ha hRR hpa
  rw [map_fibreStalkMap_maximalIdeal] at hg
  exact ⟨g, hg, hqg⟩

/-! ### Lemma 1.18 for one admissible blowup step -/

section Step

variable (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf)) [B.IsFiniteType]
  (hDense : Dense {x : X.obj.left |
    LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b x) = ⊤})
  (f : Y ⟶ X)

/-- **Lemma 1.18 for one blowup step** (Hironaka Lemma 3.1 via (4.4.4), (2.4.3), (2.5); the
situation at every point where a branch leaves a tracked flattener, Lemma 4.6.1): if the
whole-fibre flattener of `f` at `σ x'` pulls back to the pulled centre at `x'`, then over `x'`
the fibre of the strict transform is a strict quotient of the fibre of `f` at some point. -/
theorem exists_fibre_decrease_of_flattener
    (x' : (OriginalFiniteIdealBlowup.sourceObject B b hDense).obj.left)
    (I : Ideal (X.obj.left.presheaf.stalk ((stepProj B b hDense).hom.left.base x')))
    (hI : IsGermFlattenerAt f _ I)
    (hpull : Ideal.map ((stepProj B b hDense).hom.left.stalkMap x').hom I =
      Ideal.map ((stepProj B b hDense).hom.left.stalkMap x').hom
        (LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b
          ((stepProj B b hDense).hom.left.base x')))) :
    ∃ y : Y.obj.left, f.hom.left.base y = (stepProj B b hDense).hom.left.base x' ∧
      ∀ y' : (strictSource B b f).obj.left, (strictQ B b f).hom.left.base y' = y →
        (strictP B b hDense f).hom.left.base y' = x' →
          ∃ g : Y.obj.left.presheaf.stalk ((strictQ B b f).hom.left.base y'),
            g ∉ fibreIdealAt f ((strictQ B b f).hom.left.base y') ∧
              ((strictQ B b f).hom.left.stalkMap y').hom g ∈
                fibreIdealAt (strictP B b hDense f) y' := by
  obtain ⟨e, he, hreg⟩ := stepProj_pulledIdeal_regular B b hDense x'
  have hIe : Ideal.map ((stepProj B b hDense).hom.left.stalkMap x').hom I = Ideal.span {e} :=
    hpull.trans he
  choose Iy hIy using fun k : {y : Y.obj.left //
      f.hom.left.base y = (stepProj B b hDense).hom.left.base x'} =>
    exists_isPointFlattenerAt f _ k.1 k.2
  rw [eq_iSup_of_isGermFlattenerAt f _ I hI Iy hIy] at hIe
  obtain ⟨⟨y, hy⟩, hk⟩ := exists_map_eq_span_of_iSup _ Iy e hreg hIe
  refine ⟨y, hy, fun y' hq hp => ?_⟩
  have ha' : nativePulledIdealStalkIdeal (stepProj B b hDense).hom.left B b
      ((strictP B b hDense f).hom.left.base y') =
        Ideal.span {(eqToHom (congrArg (OriginalFiniteIdealBlowup.sourceObject B b
          hDense).obj.left.presheaf.stalk hp.symm)).hom e} := by
    rw [nativePulledIdealStalkIdeal_eqToHom _ B b hp.symm, he, Ideal.map_span, Set.image_singleton]
  exact exists_fibre_decrease_of_pointFlattener f (stepProj B b hDense) (strictP B b hDense f)
    (strictQ B b f) (strictP_comp B b hDense f) y' x' hp y hq hy _ (hIy ⟨y, hy⟩) e hreg hk
    (strictP_generator_regular B b f hDense y' _ ha').2

end Step

/-! ### The driver forms -/

/-- **M6 for the stateless driver** (lane G10H's statement, without its `I ≠ ⊥` hypothesis, which
follows from `hpull`). -/
theorem stepFibreDecreasesAt_of_flattener (rule : ∀ s : Stage, AdmissibleCentre s.f) (s : Stage)
    (x' : (Stage.next rule s).X.obj.left)
    (I : Ideal (s.X.obj.left.presheaf.stalk ((Stage.σ rule s).hom.left.base x')))
    (hI : IsGermFlattenerAt s.f _ I)
    (hpull : Ideal.map ((Stage.σ rule s).hom.left.stalkMap x').hom I =
      Ideal.map ((Stage.σ rule s).hom.left.stalkMap x').hom
        (LinearMap.range (stalkInclusionLinearMap s.X.obj.left.toSheafedSpace.sheaf (rule s).B
          (rule s).b ((Stage.σ rule s).hom.left.base x')))) :
    StepFibreDecreasesAt rule s x' := by
  let c := rule s
  let _ := c.finiteType
  exact exists_fibre_decrease_of_flattener c.B c.b c.dense s.f x' I hI hpull

open HironakaG10ChowCentreMachine in
/-- **M6 for centre machines** (the form feeding `hfreq` of `exists_flattening_of_machine'`): at
step `n` of the run of a machine, if the whole-fibre flattener at `σ_n x'` pulls back to the pulled
centre at `x'`, the fibre strictly decreases over `x'`. -/
theorem machine_stepFibreDecreasesAt_of_flattener (M : CentreMachine) (s₀ : Stage) (d₀ : M.St s₀)
    (hf : IsProperMap s₀.f.hom.left.base) (n : ℕ)
    (x' : ((toFlatteningSequence M s₀ d₀ hf).X (n + 1)).obj.left)
    (I : Ideal (((toFlatteningSequence M s₀ d₀ hf).X n).obj.left.presheaf.stalk
      (((toFlatteningSequence M s₀ d₀ hf).σ n).hom.left.base x')))
    (hI : IsGermFlattenerAt ((toFlatteningSequence M s₀ d₀ hf).f n) _ I)
    (hpull : Ideal.map (((toFlatteningSequence M s₀ d₀ hf).σ n).hom.left.stalkMap x').hom I =
      nativePulledIdealStalkIdeal ((toFlatteningSequence M s₀ d₀ hf).σ n).hom.left
        (centreAt M s₀ d₀ n).B (centreAt M s₀ d₀ n).b x') :
    HironakaG10ChowSequenceFibreChain.StepFibreDecreasesAt (toFlatteningSequence M s₀ d₀ hf) n x' := by
  let c := centreAt M s₀ d₀ n
  let _ := c.finiteType
  exact exists_fibre_decrease_of_flattener c.B c.b c.dense (run M s₀ d₀ n).1.f x' I hI hpull

end

end Hironaka.Analytic.Unibranch.HironakaG10ChowFlattenerDecrease
