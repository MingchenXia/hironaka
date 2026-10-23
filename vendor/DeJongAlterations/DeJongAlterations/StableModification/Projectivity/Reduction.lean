/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane OM3A)
-/
import DeJongAlterations.StableModification.Projectivity.LineBundle
import DeJongAlterations.StableModification.DeJong.BaseStepProjective
import DeJongAlterations.Geometry.FiniteProjectivePreservation
import DeJongAlterations.Geometry.ProjectiveSpaceBaseChange
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Reduction of relative projectivity to a finite map into `ℙᴺ`

Blueprint `sm-projectivity-core.tex`, node M0 of PLAN-OM3 (Temkin, *Stable modification of
relative curves*, Thm 1.1, T:1713–1749). The consumed conjunct of `DeJong.HasStableModification`
is `IsRelativelyProjective pT β` for `β : C' ⟶ T = C ×_S S'`. This file shows that it suffices to
find a `k`-morphism `h : C' ⟶ ℙᴺ_k` which is quasi-finite on the fibres of `β`:

* `isRelativelyProjective_of_isProjectiveOver` (`lem:sm-proj-cancel`): a projective `k`-scheme
  over a separated `k`-scheme `T` is projective relative to `T` (cancellation of the closed
  immersion along the separated projection `T ×_k ℙⁿ_k ⟶ ℙⁿ_k`);
* `isRelativelyProjective_of_isFinite` (`lem:sm-proj-finite`): a finite `T`-morphism into
  `T ×_k ℙᴺ_k`, `T` projective over `k`, gives relative projectivity (Codex's "finite over
  projective is projective" and the Segre embedding);
* `isFinite_of_finite_preimage_singleton`, `isRelativelyProjective_of_finite_fibres`
  (`lem:sm-proj-quasifinite`): for proper `β` and `h` with `β⁻¹(t) ∩ h⁻¹(p)` finite for all
  `t, p`, the map `Φ = (β, h)` is finite (Zariski's main theorem in Mathlib), hence `β` is
  relatively projective;
* bookkeeping (`lem:sm-proj-bookkeeping`): isomorphism invariance, closed subschemes,
  restriction to opens, `LocallyRelativelyProjective` of a relatively projective morphism,
  composition over a projective base, change of the coefficient ring along `Spec V ⟶ Spec k`, and
  the equivalence with absolute projectivity over a projective base (PLAN-OM3 §8 O1).

The first two statements were checked in the planning probe
`.archon-horizon/scratch/offlib/dja-PO3/ProbeReduction.lean` (lane PO3).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace DeJongAlterations.StableModification.Projectivity

universe u

open DeJong

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [CommRing k] {X X' T : Scheme.{u}}

/-- **Cancellation** (blueprint `lem:sm-proj-cancel`): a `k`-morphism `f : X ⟶ T` from a
projective `k`-scheme to a separated `k`-scheme is projective relative to `pT`. -/
theorem isRelativelyProjective_of_isProjectiveOver (pT : T ⟶ Spec (.of k)) [IsSeparated pT]
    (f : X ⟶ T) (hX : IsProjectiveOver (f ≫ pT)) : IsRelativelyProjective pT f := by
  obtain ⟨n, j, hj, hjp⟩ := hX
  have := hj
  let i : X ⟶ pullback pT (projectiveSpaceStructure k n) :=
    pullback.lift f j (by rw [hjp])
  have hi2 : i ≫ pullback.snd pT (projectiveSpaceStructure k n) = j := pullback.lift_snd _ _ _
  have : IsClosedImmersion (i ≫ pullback.snd pT (projectiveSpaceStructure k n)) := by
    rw [hi2]; infer_instance
  have : IsSeparated (pullback.snd pT (projectiveSpaceStructure k n)) := inferInstance
  exact ⟨n, i, IsClosedImmersion.of_comp i (pullback.snd _ _), pullback.lift_fst _ _ _⟩

/-- Over a projective `k`-scheme, relative projectivity is absolute projectivity (PLAN-OM3 §8
O1). -/
theorem isRelativelyProjective_iff_isProjectiveOver (pT : T ⟶ Spec (.of k))
    (hT : IsProjectiveOver pT) (f : X ⟶ T) :
    IsRelativelyProjective pT f ↔ IsProjectiveOver (f ≫ pT) := by
  have : IsProper pT := hT.isProper
  exact ⟨fun h => h.isProjectiveOver hT, isRelativelyProjective_of_isProjectiveOver pT f⟩

/-- **The finite-map criterion** (blueprint `lem:sm-proj-finite`): a finite `T`-morphism
`Φ : X ⟶ T ×_k ℙᴺ_k`, with `T` projective over `k`, makes `Φ ≫ pr₁` projective relative to
`pT`. -/
theorem isRelativelyProjective_of_isFinite (pT : T ⟶ Spec (.of k)) (hT : IsProjectiveOver pT)
    (N : ℕ) (Φ : X ⟶ pullback pT (projectiveSpaceStructure k N)) [IsFinite Φ] :
    IsRelativelyProjective pT (Φ ≫ pullback.fst pT (projectiveSpaceStructure k N)) := by
  have : IsProper pT := hT.isProper
  have hP : IsProjectiveOver (pullback.fst pT (projectiveSpaceStructure k N) ≫ pT) :=
    Geometry.ChowLemmaProduct.isProjectiveOver_product pT (projectiveSpaceStructure k N) hT
      (isProjectiveOver_projectiveSpaceStructure k N)
  have hX := Geometry.FiniteProjective.isProjectiveOver_comp_of_isFinite _ hP Φ
  refine isRelativelyProjective_of_isProjectiveOver pT _ ?_
  simpa [Category.assoc] using hX

/-- A proper morphism with finite set-theoretic fibres is finite (Mathlib's
`LocallyQuasiFinite.of_finite_preimage_singleton` and Zariski's main theorem
`IsFinite.of_isProper_of_locallyQuasiFinite`). -/
theorem isFinite_of_finite_preimage_singleton {Z : Scheme.{u}} (Φ : X ⟶ Z) [IsProper Φ]
    (hΦ : ∀ z, (Φ ⁻¹' {z}).Finite) : IsFinite Φ := by
  have : LocallyQuasiFinite Φ := LocallyQuasiFinite.of_finite_preimage_singleton Φ hΦ
  exact IsFinite.of_isProper_of_locallyQuasiFinite Φ

/-- **The finite-map trick** (blueprint `lem:sm-proj-quasifinite`): let `β : X ⟶ T` be proper,
`T` projective over `k`, and `h : X ⟶ ℙᴺ_k` a `k`-morphism whose restriction to each fibre of `β`
has finite fibres. Then `Φ = (β, h) : X ⟶ T ×_k ℙᴺ_k` is finite and `β` is projective relative to
`pT`. -/
theorem isRelativelyProjective_of_finite_fibres (pT : T ⟶ Spec (.of k))
    (hT : IsProjectiveOver pT) (β : X ⟶ T) [IsProper β] {N : ℕ}
    (h : X ⟶ projectiveSpace k N) (hh : h ≫ projectiveSpaceStructure k N = β ≫ pT)
    (hfin : ∀ (t : T) (p : projectiveSpace k N), (β ⁻¹' {t} ∩ h ⁻¹' {p}).Finite) :
    IsRelativelyProjective pT β := by
  let Φ : X ⟶ pullback pT (projectiveSpaceStructure k N) := pullback.lift β h hh.symm
  have hΦ₁ : Φ ≫ pullback.fst _ _ = β := pullback.lift_fst _ _ _
  have hΦ₂ : Φ ≫ pullback.snd _ _ = h := pullback.lift_snd _ _ _
  have : IsSeparated (pullback.fst pT (projectiveSpaceStructure k N)) := inferInstance
  have : IsProper (Φ ≫ pullback.fst pT (projectiveSpaceStructure k N)) := by
    rw [hΦ₁]; infer_instance
  have : IsProper Φ := IsProper.of_comp Φ (pullback.fst _ _)
  have : IsFinite Φ := by
    refine isFinite_of_finite_preimage_singleton Φ fun z => ?_
    refine (hfin (pullback.fst pT (projectiveSpaceStructure k N) z)
      (pullback.snd pT (projectiveSpaceStructure k N) z)).subset fun x hx => ?_
    have hx' : Φ x = z := hx
    refine ⟨?_, ?_⟩
    · change β x = _
      rw [← hΦ₁, Scheme.Hom.comp_apply, hx']
    · change h x = _
      rw [← hΦ₂, Scheme.Hom.comp_apply, hx']
  have H := isRelativelyProjective_of_isFinite pT hT N Φ
  rwa [hΦ₁] at H

/-! ### Bookkeeping -/

/-- Relative projectivity is invariant under isomorphisms of the source. -/
theorem isRelativelyProjective_iso_hom_comp {pT : T ⟶ Spec (.of k)} {f : X ⟶ T}
    (h : IsRelativelyProjective pT f) (e : X' ≅ X) : IsRelativelyProjective pT (e.hom ≫ f) := by
  obtain ⟨n, i, hi, rfl⟩ := h
  have := hi
  exact ⟨n, e.hom ≫ i, inferInstance, by rw [Category.assoc]⟩

/-- Closed subschemes of relatively projective schemes are relatively projective. -/
theorem isRelativelyProjective_closedImmersion_comp {pT : T ⟶ Spec (.of k)} {f : X ⟶ T}
    (h : IsRelativelyProjective pT f) (j : X' ⟶ X) [IsClosedImmersion j] :
    IsRelativelyProjective pT (j ≫ f) := by
  obtain ⟨n, i, hi, rfl⟩ := h
  have := hi
  exact ⟨n, j ≫ i, inferInstance, by rw [Category.assoc]⟩

/-- **Restriction to an open of the base**: if `f : X ⟶ T` is projective relative to `pT`, then
`f⁻¹(W) ⟶ W` is projective relative to `W ⟶ T ⟶ Spec k`. -/
theorem isRelativelyProjective_restrict {pT : T ⟶ Spec (.of k)} {f : X ⟶ T}
    (h : IsRelativelyProjective pT f) (W : T.Opens) :
    IsRelativelyProjective (W.ι ≫ pT) (f ∣_ W) := by
  have H := isRelativelyProjective_iso_hom_comp (h.pullback_snd W.ι)
    (pullbackRestrictIsoRestrict f W).symm
  simpa [morphismRestrict] using H

/-- A relatively projective morphism is locally relatively projective (trivial cover). -/
theorem locallyRelativelyProjective_of_isRelativelyProjective {pT : T ⟶ Spec (.of k)}
    {f : X ⟶ T} (h : IsRelativelyProjective pT f) : LocallyRelativelyProjective pT f :=
  ⟨PUnit, inferInstance, fun _ => ⊤, iSup_const, fun _ => isRelativelyProjective_restrict h ⊤⟩

/-- A locally relatively projective morphism is proper (properness is local on the target). -/
theorem LocallyRelativelyProjective.isProper {pT : T ⟶ Spec (.of k)} {f : X ⟶ T}
    (h : LocallyRelativelyProjective pT f) : IsProper f := by
  obtain ⟨J, _, W, hW, hWf⟩ := h
  have : ∀ j, IsProper (f ∣_ W j) := fun j => (hWf j).isProper
  exact (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsProper) W hW).mpr this

/-- **Composition over a projective base**: if `S` is projective over `k`, `g : T ⟶ S` is
projective relative to `pS` and `f : X ⟶ T` is projective relative to `g ≫ pS`, then `f ≫ g` is
projective relative to `pS`. -/
theorem isRelativelyProjective_comp {S : Scheme.{u}} {pS : S ⟶ Spec (.of k)}
    (hS : IsProjectiveOver pS) {g : T ⟶ S} {f : X ⟶ T} (hg : IsRelativelyProjective pS g)
    (hf : IsRelativelyProjective (g ≫ pS) f) : IsRelativelyProjective pS (f ≫ g) := by
  have : IsProper pS := hS.isProper
  have hT : IsProjectiveOver (g ≫ pS) := hg.isProjectiveOver hS
  have hX : IsProjectiveOver (f ≫ g ≫ pS) := hf.isProjectiveOver hT
  exact isRelativelyProjective_of_isProjectiveOver pS (f ≫ g) (by simpa [Category.assoc] using hX)

/-- **Change of coefficient ring**: for `pV : T ⟶ Spec V` and `φ : k →+* V`, projectivity
relative to `pV` is projectivity relative to `pV ≫ Spec φ` (because
`ℙⁿ_V = ℙⁿ_k ×_k Spec V`, Codex's `isPullback_projectiveCoefficientMap`). This converts the
valuation-ring level output into the form `IsRelativelyProjective (m.g ≫ p₀) β` of LIM3. -/
theorem isRelativelyProjective_comp_specMap_iff {V : Type u} [CommRing V] (φ : k →+* V)
    (pV : T ⟶ Spec (.of V)) (f : X ⟶ T) :
    IsRelativelyProjective (pV ≫ Spec.map (CommRingCat.ofHom φ)) f ↔
      IsRelativelyProjective pV f := by
  have key : ∀ n : ℕ, IsPullback (pullback.fst pV (projectiveSpaceStructure V n))
      (pullback.snd pV (projectiveSpaceStructure V n) ≫
        Geometry.BlowupProjectiveEmbedding.projectiveCoefficientMap φ n)
      (pV ≫ Spec.map (CommRingCat.ofHom φ)) (projectiveSpaceStructure k n) := fun n =>
    ((IsPullback.of_hasPullback pV (projectiveSpaceStructure V n)).flip.paste_horiz
      (Geometry.ProjectiveSpaceBaseChange.isPullback_projectiveCoefficientMap φ n)).flip
  constructor
  · rintro ⟨n, i, hi, hif⟩
    have := hi
    refine ⟨n, i ≫ (key n).isoPullback.inv, inferInstance, ?_⟩
    rw [Category.assoc, IsPullback.isoPullback_inv_fst, hif]
  · rintro ⟨n, i, hi, hif⟩
    have := hi
    refine ⟨n, i ≫ (key n).isoPullback.hom, inferInstance, ?_⟩
    rw [Category.assoc, IsPullback.isoPullback_hom_fst, hif]

/-- Change of coefficient ring for `LocallyRelativelyProjective`. -/
theorem locallyRelativelyProjective_comp_specMap_iff {V : Type u} [CommRing V] (φ : k →+* V)
    (pV : T ⟶ Spec (.of V)) (f : X ⟶ T) :
    LocallyRelativelyProjective (pV ≫ Spec.map (CommRingCat.ofHom φ)) f ↔
      LocallyRelativelyProjective pV f := by
  constructor
  · rintro ⟨J, hJ, W, hW, hWf⟩
    refine ⟨J, hJ, W, hW, fun j => ?_⟩
    have := hWf j
    rw [← Category.assoc, isRelativelyProjective_comp_specMap_iff] at this
    exact this
  · rintro ⟨J, hJ, W, hW, hWf⟩
    refine ⟨J, hJ, W, hW, fun j => ?_⟩
    rw [← Category.assoc, isRelativelyProjective_comp_specMap_iff]
    exact hWf j

end DeJongAlterations.StableModification.Projectivity
