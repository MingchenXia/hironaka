import Hironaka.Resolution.HironakaG1RSmoothLocusPushout
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# The smooth locus under flat base change of schemes (ALG14 input D3, scheme form)

**Main result** (`preimage_smoothLocus_of_isPullback`): for a cartesian square of schemes

```
P --fst--> X
|snd       | f
Y ---g---> Z
```

with `f` locally of finite presentation, `g` flat and `Y`, `Z` affine (e.g. `Z = Spec k`,
`Y = Spec L` for a field extension `L / k`, `X` any `k`-scheme locally of finite type), the smooth
locus of `snd` is the preimage of the smooth locus of `f`:  `fst ⁻¹ᵁ f.smoothLocus = snd.smoothLocus`.
This is the scheme form of `p ⁻¹ (X ↘ Spec k).smoothLocus = (X_L ↘ Spec L).smoothLocus` (input D3
of lane G1's ALG14 note, `work/hironaka-resume-20261111/G1/ALG14-R02-FINITE-GENERATION-DESCENT.md`
§3); `preimage_smoothLocus_pullback_field` states it for `pullback f (Spec.map (algebraMap k L))`.

Proof: the affine case (`mem_smoothLocus_iff_of_isPullback_of_isAffine`) is the ring statement
`HironakaG1RSmoothLocusPushout.mem_smoothLocus_of_isPushout` for the pushout of global sections
(`isPushout_appTop_of_isPullback`) through Mathlib's `formallySmooth_stalkMap_iff`; in general one
restricts to an affine open `V ∋ fst z` of `X` (`isPullback_morphismRestrict`, pasted with the
square) and uses that smooth loci are compatible with open immersions
(`Scheme.Hom.preimage_smoothLocus_eq`).

Only Mathlib and lane G1's ring-level modules are imported; no named input.
Blueprint: `hironaka-g1-r-smooth-locus-base-change.tex` (node `g1r:smooth-locus-pullback`).
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace Hironaka.HironakaG1RSmoothLocusPullback

open AlgebraicGeometry HironakaG1RSmoothLocusPushout

universe u

/-- `f.appLE ⊤ ⊤ _` is the map on global sections. -/
theorem appLE_top_top {X Y : Scheme.{u}} (f : X ⟶ Y) (h : (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤) :
    f.appLE ⊤ ⊤ h = f.appTop :=
  f.appLE_eq_app

/-- **The affine case.** -/
theorem mem_smoothLocus_iff_of_isPullback_of_isAffine {P X Y Z : Scheme.{u}} {fst : P ⟶ X}
    {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} [IsAffine X] [IsAffine Y] [IsAffine Z]
    (h : IsPullback fst snd f g) [LocallyOfFinitePresentation f]
    [LocallyOfFinitePresentation snd] [Flat g] (z : P) :
    z ∈ snd.smoothLocus ↔ fst z ∈ f.smoothLocus := by
  have : IsAffine P := .of_isPullback h
  have hX := isAffineOpen_top X
  have hY := isAffineOpen_top Y
  have hZ := isAffineOpen_top Z
  have hP := isAffineOpen_top P
  have hf : (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤ := le_top
  have hg : (⊤ : Y.Opens) ≤ g ⁻¹ᵁ ⊤ := le_top
  have hfst : (⊤ : P.Opens) ≤ fst ⁻¹ᵁ ⊤ := le_top
  have hsnd : (⊤ : P.Opens) ≤ snd ⁻¹ᵁ ⊤ := le_top
  have hcomp : (⊤ : P.Opens) ≤ (fst ≫ f) ⁻¹ᵁ ⊤ := le_top
  rw [Scheme.Hom.mem_smoothLocus, Scheme.Hom.mem_smoothLocus,
    formallySmooth_stalkMap_iff ⊤ hY ⊤ hP hsnd trivial,
    formallySmooth_stalkMap_iff ⊤ hZ ⊤ hX hf trivial]
  let _ : Algebra Γ(Z, ⊤) Γ(X, ⊤) := (f.appLE ⊤ ⊤ hf).hom.toAlgebra
  let _ : Algebra Γ(Z, ⊤) Γ(Y, ⊤) := (g.appLE ⊤ ⊤ hg).hom.toAlgebra
  let _ : Algebra Γ(X, ⊤) Γ(P, ⊤) := (fst.appLE ⊤ ⊤ hfst).hom.toAlgebra
  let _ : Algebra Γ(Y, ⊤) Γ(P, ⊤) := (snd.appLE ⊤ ⊤ hsnd).hom.toAlgebra
  let _ : Algebra Γ(Z, ⊤) Γ(P, ⊤) := ((fst ≫ f).appLE ⊤ ⊤ hcomp).hom.toAlgebra
  have : IsScalarTower Γ(Z, ⊤) Γ(X, ⊤) Γ(P, ⊤) := .of_algebraMap_eq' <| by
    change ((fst ≫ f).appLE ⊤ ⊤ hcomp).hom = (fst.appLE ⊤ ⊤ hfst).hom.comp (f.appLE ⊤ ⊤ hf).hom
    rw [appLE_top_top, appLE_top_top, appLE_top_top, Scheme.Hom.comp_appTop]
    rfl
  have : IsScalarTower Γ(Z, ⊤) Γ(Y, ⊤) Γ(P, ⊤) := .of_algebraMap_eq' <| by
    change ((fst ≫ f).appLE ⊤ ⊤ hcomp).hom = (snd.appLE ⊤ ⊤ hsnd).hom.comp (g.appLE ⊤ ⊤ hg).hom
    rw [appLE_top_top, appLE_top_top, appLE_top_top, h.w, Scheme.Hom.comp_appTop]
    rfl
  have hpush : Algebra.IsPushout Γ(Z, ⊤) Γ(X, ⊤) Γ(Y, ⊤) Γ(P, ⊤) := by
    have h' := isPushout_appTop_of_isPullback h
    rw [← appLE_top_top f hf, ← appLE_top_top g hg, ← appLE_top_top fst hfst,
      ← appLE_top_top snd hsnd] at h'
    exact CommRingCat.isPushout_iff_isPushout.mp h'
  have : Algebra.IsPushout Γ(Z, ⊤) Γ(Y, ⊤) Γ(X, ⊤) Γ(P, ⊤) := hpush.symm
  have : Module.Flat Γ(Z, ⊤) Γ(Y, ⊤) := g.flat_appLE hZ hY hg
  have : Algebra.FinitePresentation Γ(Z, ⊤) Γ(X, ⊤) := f.finitePresentation_appLE hZ hX hf
  rw [mem_smoothLocus_of_isPushout (R := Γ(Z, ⊤)) (T := Γ(Y, ⊤)) (A := Γ(X, ⊤)) (B := Γ(P, ⊤))]
  change (hP.primeIdealOf ⟨z, trivial⟩).comap (fst.appLE ⊤ ⊤ hfst).hom ∈ _ ↔ _
  rw [IsAffineOpen.comap_primeIdealOf_appLE ⊤ hX ⊤ hP hfst trivial]

/-- **The smooth locus under flat base change of schemes.**  For a cartesian square with `f`
locally of finite presentation, `g` flat and `Y`, `Z` affine, the smooth locus of `snd` is the
preimage of the smooth locus of `f`. -/
theorem preimage_smoothLocus_of_isPullback {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} [IsAffine Y] [IsAffine Z] (h : IsPullback fst snd f g)
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation snd] [Flat g] :
    fst ⁻¹ᵁ f.smoothLocus = snd.smoothLocus := by
  ext z
  obtain ⟨_, ⟨V, hV, rfl⟩, hzV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (fst z)) isOpen_univ
  change X.Opens at V
  have : IsAffine V := hV
  have h₁ : IsPullback (fst ∣_ V) ((fst ⁻¹ᵁ V).ι ≫ snd) (V.ι ≫ f) g :=
    (isPullback_morphismRestrict fst V).paste_vert h
  let z₀ : (fst ⁻¹ᵁ V).toScheme := ⟨z, hzV⟩
  have key := mem_smoothLocus_iff_of_isPullback_of_isAffine h₁ z₀
  rw [← Scheme.Hom.preimage_smoothLocus_eq, ← Scheme.Hom.preimage_smoothLocus_eq,
    Scheme.Hom.mem_preimage, Scheme.Hom.mem_preimage] at key
  have hz : (fst ⁻¹ᵁ V).ι z₀ = z := rfl
  have hx : V.ι ((fst ∣_ V) z₀) = fst z := by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply, hz]
  rw [hz, hx] at key
  exact key.symm

/-- **Field extensions.**  For a scheme `X` locally of finite presentation over a field `k` and any
field extension `L / k`, the smooth locus of `X_L = X ×_k L` over `L` is the preimage of the smooth
locus of `X` over `k`. -/
theorem preimage_smoothLocus_pullback_field {k L : Type u} [Field k] [Field L] [Algebra k L]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFinitePresentation f] :
    pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k L))) ⁻¹ᵁ f.smoothLocus =
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k L)))).smoothLocus := by
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap k L))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  exact preimage_smoothLocus_of_isPullback (IsPullback.of_hasPullback _ _)

end Hironaka.HironakaG1RSmoothLocusPullback
