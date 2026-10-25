import DeJongAlterations.Theorem
import DeJongAlterations.Modification
import DeJongAlterations.Geometry.SemistableCurve
import DeJongAlterations.Geometry.RegularCurve
import DeJongAlterations.Geometry.ProjectiveIdentity
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# The interface of the de Jong main chain with Temkin's stable modification

This file fixes the predicates and the producer propositions through which the proof of
de Jong's Theorem 4.1 (de Jong, *Smoothness, semi-stability and alterations*, 1996,
`dejong96-alterations:page-0017`) over an algebraically closed field is assembled from
Temkin's stable modification theorem (M. Temkin, *Stable modification of relative curves*,
J. Algebraic Geom. 19 (2010), `references/temkin10-stable-modification`, §1.2) instead of
the moduli of stable pointed curves (de Jong 2.24, 4.17–4.21).

## Curves

* `IsNodalCurve g`: `g` is flat, locally of finite presentation, every geometric fibre has
  pure dimension one, and every closed point of every geometric fibre is smooth or an
  ordinary double point in the completed-local sense of
  `DeJongAlterations.Geometry.IsGeometricOrdinaryDoublePoint` (de Jong 2.21, Temkin §1.2:
  "flat and its geometric fibers have at most ordinary double points"). Unlike Codex's
  `Geometry.IsSemistableCurve` it asks neither for properness nor for geometrically
  connected or reduced fibres; `isNodalCurve_of_isSemistableCurve` is the comparison.
* `IsSemistablePair g D` (Temkin §1.2): `g` nodal, `D → S` étale and `D` inside the smooth
  locus of `g`.
* `IsMultipointedCurve g D` (Temkin §1.2): `C → S` and `D → S` flat, locally of finite
  presentation, of pure relative dimension one and zero.
* `IsRelativelyProjective pT f`: `f : X ⟶ T` factors through a closed immersion into
  `ℙⁿ_T = T ×_k ℙⁿ_k` over `T`.
* `strictTransform w ψ`: the scheme-theoretic closure of the generic fibre of `W ×_S S' → S'`
  in `W ×_S S'` (de Jong 2.18, 2.20).

## Producer propositions

These are plain propositions; nothing here asserts them. Each one is the exact statement
proved by its producer, over an algebraically closed field.

* `TemkinStableModification k` (Temkin Thm 1.5 with Thm 1.1, consumed form).
* `FlatteningAfterGEAlteration k` (a weak form of de Jong 2.19 / Raynaud–Gruson, proved
  by Temkin's method of §3.4).
* `TemkinReadyFibration k` (the generic part of de Jong 4.11–4.12, with a purely
  inseparable base change replacing Bertini).
* `SemistableResolution k` (de Jong 4.23–4.28 with 3.1–3.5 and 2.4).
* `CartierCaseUpTo k d`, `TheoremUpTo k d`: dimension-indexed forms of 4.1.
* `BaseStep k`: the inductive step 4.22 with Temkin plugged in.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.StableModification.DeJong

universe u

open Geometry (IsGeometricOrdinaryDoublePoint IsSemistableCurve)

section Curves

variable {C S : Scheme.{u}}

/-- `g` is smooth at `x`: the stalk map `𝒪_{S,g(x)} → 𝒪_{C,x}` is formally smooth. For `g`
locally of finite presentation this is membership in `g.smoothLocus`
(`isSmoothAt_iff_mem_smoothLocus`). -/
def IsSmoothAt (g : C ⟶ S) (x : C) : Prop :=
  (g.stalkMap x).hom.FormallySmooth

theorem isSmoothAt_iff_mem_smoothLocus (g : C ⟶ S) [LocallyOfFinitePresentation g] (x : C) :
    IsSmoothAt g x ↔ x ∈ g.smoothLocus :=
  Iff.rfl

/-- A *nodal curve* (de Jong 2.21 without properness and connectedness; Temkin §1.2,
`semi-stable.tex` l.1683–1685): `g` is flat and locally of finite presentation, every
irreducible component of every geometric fibre `C ×_S Spec K` (`K` algebraically closed) has
dimension one, and every closed point of every such fibre is a smooth point or a geometric
ordinary double point (its completed local `K`-algebra is `K[[u,v]]/(uv)`). -/
class IsNodalCurve (g : C ⟶ S) : Prop extends Flat g, LocallyOfFinitePresentation g where
  pureGeometricFibers : ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (a : Spec (.of K) ⟶ S) (Z : Set (pullback (C := Scheme.{u}) g a)),
    Z ∈ irreducibleComponents (pullback (C := Scheme.{u}) g a) → topologicalKrullDim Z = 1
  geometricNodes : ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (a : Spec (.of K) ⟶ S) (y : pullback (C := Scheme.{u}) g a),
    IsClosed ({y} : Set (pullback (C := Scheme.{u}) g a)) →
      y ∈ (pullback.snd g a).smoothLocus ∨ IsGeometricOrdinaryDoublePoint (pullback.snd g a) y

/-- Codex's semi-stable curves (de Jong 2.21, with properness and geometrically connected,
reduced fibres) are nodal curves. -/
instance (priority := 100) isNodalCurve_of_isSemistableCurve
    (g : C ⟶ S) [h : IsSemistableCurve g] : IsNodalCurve g where
  pureGeometricFibers := h.pureGeometricFibers
  geometricNodes := h.geometricNodes

/-- A *semi-stable pair* (Temkin §1.2, `semi-stable.tex` l.1683–1687): `g : C ⟶ S` is a nodal
curve, the closed subscheme `D` is étale over `S`, and `D` lies in the smooth locus of `g`
(i.e. it is disjoint from the non-smoothness locus). -/
structure IsSemistablePair (g : C ⟶ S) (D : C.IdealSheafData) : Prop where
  nodal : IsNodalCurve g
  etale : Etale (D.subschemeι ≫ g)
  smoothAlong : ∀ x ∈ (D.support : Set C), IsSmoothAt g x

theorem IsSemistablePair.support_subset_smoothLocus {g : C ⟶ S} {D : C.IdealSheafData}
    (h : IsSemistablePair g D) [LocallyOfFinitePresentation g] :
    (D.support : Set C) ⊆ g.smoothLocus :=
  fun x hx ↦ (isSmoothAt_iff_mem_smoothLocus g x).mp (h.smoothAlong x hx)

/-- Every irreducible component of every fibre `f⁻¹(s)` has dimension `n` (pure relative
dimension `n`, EGA IV 4.2; empty fibres are allowed). -/
def HasPureFiberDimension {X : Scheme.{u}} (f : X ⟶ S) (n : ℕ) : Prop :=
  ∀ (s : S) (Z : Set (f.fiber s)), Z ∈ irreducibleComponents (f.fiber s) →
    topologicalKrullDim Z = n

/-- A *multipointed `S`-curve* (Temkin §1.2, `semi-stable.tex` l.1671–1675): `C → S` and
`D → S` are flat, locally of finite presentation, of pure relative dimension one and zero,
and `D ⊆ C` is a closed subscheme (here given by its ideal sheaf; `D` may be empty). -/
structure IsMultipointedCurve (g : C ⟶ S) (D : C.IdealSheafData) : Prop where
  flat : Flat g
  locallyOfFinitePresentation : LocallyOfFinitePresentation g
  pureFibers : HasPureFiberDimension g 1
  marksFlat : Flat (D.subschemeι ≫ g)
  marksLocallyOfFinitePresentation : LocallyOfFinitePresentation (D.subschemeι ≫ g)
  marksPureFibers : HasPureFiberDimension (D.subschemeι ≫ g) 0

/-- The restriction `D_s = D ×_C C_s` of a closed subscheme to the fibre of `g` over `s`. -/
abbrev fiberMarks (g : C ⟶ S) (D : C.IdealSheafData) (s : S) :
    (g.fiber s).IdealSheafData :=
  D.comap (g.fiberι s)

end Curves

section Projective

/-- `f : X ⟶ T` is *projective relative to* `pT : T ⟶ Spec k`: it factors through a closed
immersion into `ℙⁿ_T = T ×_{Spec k} ℙⁿ_k` over `T` (Hartshorne II.4; `ℙⁿ_T` does not depend
on `k`, being `T ×_ℤ ℙⁿ_ℤ`). For `pT = 𝟙` this is `IsProjectiveOver`
(`isRelativelyProjective_id_iff`). -/
def IsRelativelyProjective {k : Type u} [CommRing k] {X T : Scheme.{u}}
    (pT : T ⟶ Spec (.of k)) (f : X ⟶ T) : Prop :=
  ∃ (n : ℕ) (i : X ⟶ pullback pT (projectiveSpaceStructure k n)),
    IsClosedImmersion i ∧ i ≫ pullback.fst pT (projectiveSpaceStructure k n) = f

variable {k : Type u} [CommRing k] {X T : Scheme.{u}}

/-- A relatively projective morphism is proper. -/
theorem IsRelativelyProjective.isProper {pT : T ⟶ Spec (.of k)} {f : X ⟶ T}
    (h : IsRelativelyProjective pT f) : IsProper f := by
  obtain ⟨n, i, hi, rfl⟩ := h
  have := hi
  infer_instance

/-- Closed immersions are relatively projective (via `ℙ⁰_T = T`). -/
theorem isRelativelyProjective_of_isClosedImmersion (pT : T ⟶ Spec (.of k)) (f : X ⟶ T)
    [IsClosedImmersion f] : IsRelativelyProjective pT f := by
  refine ⟨0, f ≫ inv (pullback.fst pT (projectiveSpaceStructure k 0)), inferInstance, ?_⟩
  simp

/-- Over `T = Spec k` itself, relative projectivity is Codex's `IsProjectiveOver`. -/
theorem isRelativelyProjective_id_iff (p : X ⟶ Spec (.of k)) :
    IsRelativelyProjective (𝟙 (Spec (.of k))) p ↔ IsProjectiveOver p := by
  constructor
  · rintro ⟨n, i, hi, hp⟩
    have := hi
    refine ⟨n, i ≫ pullback.snd _ _, inferInstance, ?_⟩
    rw [Category.assoc, ← pullback.condition, Category.comp_id, hp]
  · rintro ⟨n, i, hi, hp⟩
    have := hi
    refine ⟨n, i ≫ inv (pullback.snd (𝟙 (Spec (.of k))) (projectiveSpaceStructure k n)),
      inferInstance, ?_⟩
    have hc := pullback.condition (f := 𝟙 (Spec (.of k))) (g := projectiveSpaceStructure k n)
    rw [Category.comp_id] at hc
    rw [Category.assoc, hc, IsIso.inv_hom_id_assoc, hp]

end Projective

section StrictTransform

variable {W S S' : Scheme.{u}}

/-- The *strict transform* of `w : W ⟶ S` along `ψ : S' ⟶ S` with `S'` irreducible: the
scheme-theoretic closure (kernel ideal sheaf of the inclusion) of the generic fibre of the
projection `W ×_S S' ⟶ S'` in `W ×_S S'` (de Jong 2.18 and 2.20, `page-0011`, `page-0012`;
Temkin §3.4). -/
def strictTransform (w : W ⟶ S) (ψ : S' ⟶ S) [IrreducibleSpace S'] :
    (pullback w ψ).IdealSheafData :=
  ((pullback.snd w ψ).fiberι (genericPoint S')).ker

end StrictTransform

section Producers

variable (k : Type u) [Field k]

/-- The output of Temkin's stable modification theorem for the multipointed curve `(C, D)`
over `S` (Temkin Thm 1.5 and Thm 1.1, `semi-stable.tex` l.1713–1716, l.1771–1775): an
alteration `ψ : S' ⟶ S` (Temkin's is generically étale; that is not required here, since the base
step does not use it, decision D-DJ9), a semi-stable pair `(C', D')` over `S'` with `D'`
finite étale over `S'`, and an `S'`-morphism `β : C' ⟶ C ×_S S'` which is projective
(closed immersion into `ℙⁿ_{C ×_S S'}`), an isomorphism over a nonempty open `U ⊆ S'`, and
over `U` carries `D'` onto the preimage of `D`. Stability is not recorded. -/
def HasStableModification {S C : Scheme.{u}} (pS : S ⟶ Spec (.of k)) (g : C ⟶ S)
    (D : C.IdealSheafData) : Prop :=
  ∃ (S' : Scheme.{u}) (ψ : S' ⟶ S) (C' : Scheme.{u}) (D' : C'.IdealSheafData)
    (β : C' ⟶ pullback g ψ),
    IsAlteration ψ ∧
    IsSemistablePair (β ≫ pullback.snd g ψ) D' ∧
    IsFinite (D'.subschemeι ≫ β ≫ pullback.snd g ψ) ∧
    IsRelativelyProjective (pullback.snd g ψ ≫ ψ ≫ pS) β ∧
    ∃ U : S'.Opens, Nonempty U ∧ IsIso (β ∣_ ((pullback.snd g ψ) ⁻¹ᵁ U)) ∧
      ∀ x : C', (β ≫ pullback.snd g ψ) x ∈ U →
        (x ∈ (D'.support : Set C') ↔ (β ≫ pullback.fst g ψ) x ∈ (D.support : Set C))

/-- **TSM** (Temkin Thm 1.5 + Thm 1.1, consumed form, PLAN-DJ-MAIN §3.2). For `S` a normal
projective variety over the algebraically closed field `k` and `(C, D)` a multipointed
`S`-curve with `C` projective over `k`, whose generic fibre is smooth, geometrically integral
(decision D-DJ6) and, with the marks, semi-stable, a stable modification `HasStableModification`
exists. -/
def TemkinStableModification [IsAlgClosed k] : Prop :=
  ∀ (S : Scheme.{u}) (pS : S ⟶ Spec (.of k)) (_ : IsVariety pS), IsNormalScheme S →
    IsProjectiveOver pS →
    ∀ (C : Scheme.{u}) (g : C ⟶ S) (D : C.IdealSheafData),
      IsProjectiveOver (g ≫ pS) → IsMultipointedCurve g D →
      Smooth (g.fiberToSpecResidueField (genericPoint S)) →
      IsSemistablePair (g.fiberToSpecResidueField (genericPoint S))
        (fiberMarks g D (genericPoint S)) →
      GeometricallyIntegral (g.fiberToSpecResidueField (genericPoint S)) →
      HasStableModification k pS g D

/-- **FLAT** (weak de Jong 2.19, PLAN-DJ-MAIN §3.2). For finitely many morphisms of finite
type `w i : W i ⟶ S` to a normal projective variety, there is a generically étale alteration
`ψ : S₁ ⟶ S` with `S₁` normal and projective over `k` such that every strict transform
`strictTransform (w i) ψ` is flat over `S₁`. -/
def FlatteningAfterGEAlteration [IsAlgClosed k] : Prop :=
  ∀ (S : Scheme.{u}) (pS : S ⟶ Spec (.of k)) (_ : IsVariety pS), IsNormalScheme S →
    IsProjectiveOver pS →
    ∀ (n : ℕ) (W : Fin n → Scheme.{u}) (w : (i : Fin n) → W i ⟶ S),
      (∀ i, LocallyOfFiniteType (w i)) → (∀ i, QuasiCompact (w i)) →
      ∃ (S₁ : Scheme.{u}) (_ : IsIntegral S₁) (ψ : S₁ ⟶ S),
        IsAlteration ψ ∧ IsGenericallyEtale ψ ∧ IsNormalScheme S₁ ∧
          IsProjectiveOver (ψ ≫ pS) ∧
          ∀ i, Flat ((strictTransform (w i) ψ).subschemeι ≫ pullback.snd (w i) ψ)

/-- **FIB** (generic part of de Jong 4.11–4.12, PLAN-DJ-MAIN §4). For a normal projective
variety `X` of dimension `d ≥ 2` and an effective Cartier divisor `D` with `Supp D ≠ X` there
are a projective alteration `φ : X' ⟶ X`, a normal projective variety `Y` of dimension `d - 1`
and a dominant `f : X' ⟶ Y` over `k` whose generic fibre is smooth and geometrically integral,
and a closed subscheme `Dh ⊆ φ⁻¹(Supp D)` whose generic fibre is étale (so that the generic
fibre pair is semi-stable), with `φ⁻¹(Supp D) ⊆ Supp Dh ∪ f⁻¹(T)` for a proper closed
`T ⊊ Y`. -/
def TemkinReadyFibration [IsAlgClosed k] : Prop :=
  ∀ (d : ℕ), 2 ≤ d →
    ∀ (X : Scheme.{u}) (p : X ⟶ Spec (.of k)), IsVariety p → IsProjectiveOver p →
      IsNormalScheme X → topologicalKrullDim X = d →
      ∀ D : X.IdealSheafData, IsEffectiveCartierDivisor D → D.support ≠ ⊤ →
      ∃ (X' : Scheme.{u}) (φ : X' ⟶ X) (Y : Scheme.{u}) (pY : Y ⟶ Spec (.of k))
        (_ : IsVariety pY) (f : X' ⟶ Y) (Dh : X'.IdealSheafData) (T : Closeds Y),
        IsAlteration φ ∧ IsProjectiveOver (φ ≫ p) ∧
        IsNormalScheme Y ∧ IsProjectiveOver pY ∧
        topologicalKrullDim Y = ((d - 1 : ℕ) : WithBot ℕ∞) ∧
        f ≫ pY = φ ≫ p ∧ IsDominant f ∧
        Smooth (f.fiberToSpecResidueField (genericPoint Y)) ∧
        GeometricallyIntegral (f.fiberToSpecResidueField (genericPoint Y)) ∧
        IsSemistablePair (f.fiberToSpecResidueField (genericPoint Y))
          (fiberMarks f Dh (genericPoint Y)) ∧
        (Dh.support : Set X') ⊆ φ ⁻¹' (D.support : Set X) ∧ T ≠ ⊤ ∧
        φ ⁻¹' (D.support : Set X) ⊆ (Dh.support : Set X') ∪ f ⁻¹' (T : Set Y)

/-- **END** (de Jong 4.23–4.28 with 3.1–3.5 and 2.4, `page-0026`, `page-0027`). In the
semi-stable situation 4.23 — `Y` a regular projective variety, `B` a strict normal crossings
divisor on `Y`, `g : C ⟶ Y` a nodal curve with `C` a projective variety, smooth over `Y ∖ B`,
and disjoint sections `τ i` into the smooth locus of `g` — the pair
`(C, ⋃ τ i (Y) ∪ g⁻¹(B))` has a full de Jong output whose alteration is a modification. -/
def SemistableResolution [IsAlgClosed k] : Prop :=
  ∀ (Y : Scheme.{u}) (pY : Y ⟶ Spec (.of k)), IsVariety pY → IsProjectiveOver pY →
    IsRegularScheme Y →
    ∀ B : Y.IdealSheafData, IsStrictNormalCrossings B →
    ∀ (C : Scheme.{u}) (g : C ⟶ Y), IsVariety (g ≫ pY) → IsProjectiveOver (g ≫ pY) →
      IsNodalCurve g → (∀ x : C, g x ∉ (B.support : Set Y) → IsSmoothAt g x) →
      ∀ (n : ℕ) (τ : Fin n → (Y ⟶ C)), (∀ i, τ i ≫ g = 𝟙 Y) →
        (∀ i j, i ≠ j → Disjoint (Set.range (τ i)) (Set.range (τ j))) →
        (∀ i (y : Y), IsSmoothAt g (τ i y)) →
        ∃ d : AlterationWithBoundary (g ≫ pY)
            ((⋃ i, Set.range (τ i)) ∪ g ⁻¹' (B.support : Set Y)),
          IsModification d.alteration

/-- de Jong 4.1 for normal projective varieties of dimension at most `d` with boundary the
support of an effective Cartier divisor (the situation (i)–(v) of 4.5–4.10). -/
def CartierCaseUpTo (d : ℕ) : Prop :=
  ∀ (X : Scheme.{u}) (p : X ⟶ Spec (.of k)), IsVariety p → IsProjectiveOver p →
    IsNormalScheme X → topologicalKrullDim X ≤ d →
    ∀ D : X.IdealSheafData, IsEffectiveCartierDivisor D → D.support ≠ ⊤ →
      Nonempty (AlterationWithBoundary p (D.support : Set X))

/-- de Jong 4.1 for varieties of dimension at most `d` (`page-0017`). -/
def TheoremUpTo (d : ℕ) : Prop :=
  ∀ (X : Scheme.{u}) (p : X ⟶ Spec (.of k)), IsVariety p → topologicalKrullDim X ≤ d →
    ∀ Z : Closeds X, Z ≠ ⊤ → Nonempty (AlterationWithBoundary p (Z : Set X))

/-- **STEP** (de Jong 4.22 with Temkin plugged in): given the four producers, 4.1 in dimension
at most `d - 1` implies the Cartier case in dimension at most `d`, for `d ≥ 2`. -/
def BaseStep [IsAlgClosed k] : Prop :=
  TemkinReadyFibration k → FlatteningAfterGEAlteration k → TemkinStableModification k →
    SemistableResolution k →
    ∀ d : ℕ, 2 ≤ d → TheoremUpTo k (d - 1) → CartierCaseUpTo k d

end Producers

section Sanity

variable {k : Type u} [Field k]

/-- Non-vacuity of the output of **TSM**: an already semi-stable pair, with marks finite over
the base, is its own stable modification (`S' = S`, `ψ = 𝟙`, `β` the canonical isomorphism
`C ≅ C ×_S S`). -/
theorem hasStableModification_of_isSemistablePair {S C : Scheme.{u}} [IsIntegral S]
    (pS : S ⟶ Spec (.of k)) (g : C ⟶ S) (D : C.IdealSheafData)
    (h : IsSemistablePair g D) [IsFinite (D.subschemeι ≫ g)] :
    HasStableModification k pS g D := by
  let β : C ⟶ pullback g (𝟙 S) := pullback.lift (𝟙 C) g (by simp)
  have hβs : β ≫ pullback.snd g (𝟙 S) = g := pullback.lift_snd _ _ _
  have hβf : β ≫ pullback.fst g (𝟙 S) = 𝟙 C := pullback.lift_fst _ _ _
  have : IsIso β := by
    have : β = inv (pullback.fst g (𝟙 S)) := by
      rw [← cancel_mono (pullback.fst g (𝟙 S)), hβf, IsIso.inv_hom_id]
    rw [this]
    infer_instance
  refine ⟨S, 𝟙 S, C, D, β, inferInstance, ?_, ?_,
    isRelativelyProjective_of_isClosedImmersion _ _, ⊤, ?_, inferInstance, ?_⟩
  · rw [hβs]
    exact h
  · rw [hβs]
    infer_instance
  · exact ⟨⟨Classical.choice inferInstance, trivial⟩⟩
  · intro x _
    rw [hβf]
    rfl

/-- Non-vacuity of the output of **END**: a regular projective variety `C` over `Y`, with
empty boundary and no sections, is solved by the identity. -/
theorem exists_modification_alterationWithBoundary_of_isRegularScheme {Y C : Scheme.{u}}
    (pY : Y ⟶ Spec (.of k)) (g : C ⟶ Y) [IsVariety (g ≫ pY)]
    (hproj : IsProjectiveOver (g ≫ pY)) (hreg : IsRegularScheme C) (τ : Fin 0 → (Y ⟶ C)) :
    ∃ d : AlterationWithBoundary (g ≫ pY)
        ((⋃ i, Set.range (τ i)) ∪ g ⁻¹' ((⊤ : Y.IdealSheafData).support : Set Y)),
      IsModification d.alteration := by
  have hZ : (⋃ i, Set.range (τ i)) ∪ g ⁻¹' ((⊤ : Y.IdealSheafData).support : Set Y) = ∅ := by
    simp
  rw [hZ]
  exact ⟨identityAlterationWithBoundary (g ≫ pY) hproj hreg, isModification_id C⟩

end Sanity

end DeJongAlterations.StableModification.DeJong
