import Hironaka.Resolution.Algebraic.ActualGlobalWeakResolutionSmoothSurjective
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-!
# ORIGINAL singular ideal under actual smooth original morphisms

Source-first proof: `actual-global-original-sing-smooth-naturality-20261102.tex`.
Actual weak-history smooth-SURJ functoriality plus genuine fpqc IsIso
reflection proves actual regular-image smoothness, without BP circularity.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Scheme.IdealSheafData
universe u

namespace Hironaka.Resolution.Algebraic.ActualGlobalOriginalSingSmoothNaturality

noncomputable section
open ActualGlobalWeakResolutionSmoothSurjective

private instance open_noetherian {Z : Scheme.{u}} [IsNoetherian Z] (U : Z.Opens) :
    IsNoetherian U.toScheme := by
  have : CompactSpace U.toScheme :=
    isCompact_iff_compactSpace.mp (NoetherianSpace.isCompact (U : Set Z))
  exact AlgebraicGeometry.IsNoetherian.mk

variable {X Y : Scheme.{u}} [IsNoetherian X] [IsReduced X] [IsNoetherian Y] [IsReduced Y]
    {k : Type u} [Field k] [CharZero k]
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [IsSeparated p]

theorem weakHistory_isIso_of_smooth [Smooth p] : IsIso (weakHistory p).composite := by
  have hs : IsIso ((weakHistory p).composite ∣_ (⊤ : X.Opens)) := by
    rw [← p.smoothLocus_eq_top]
    exact weakHistory_isIso_original_regular p
  exact IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    (fun _ : Unit => (⊤ : X.Opens)) (by simp) (fun _ => hs)

variable (f : Y ⟶ X) [Smooth f] [IsSeparated (f ≫ p)]

def regularImage : X.Opens :=
  ⟨Set.range ((f ≫ p).smoothLocus.ι ≫ f), ((f ≫ p).smoothLocus.ι ≫ f).isOpenMap.isOpen_range⟩

def regularImageMap : (f ≫ p).smoothLocus.toScheme ⟶ (regularImage p f).toScheme :=
  IsOpenImmersion.lift (regularImage p f).ι ((f ≫ p).smoothLocus.ι ≫ f) (by
    rw [Scheme.Opens.range_ι]
    intro x hx
    change x ∈ Set.range ((f ≫ p).smoothLocus.ι ≫ f)
    exact hx)

omit [AlgebraicGeometry.IsNoetherian X] [IsReduced X] [AlgebraicGeometry.IsNoetherian Y] [IsReduced Y]
  [CharZero k] [IsSeparated p] [IsSeparated (f ≫ p)] in
theorem regularImageMap_over : regularImageMap p f ≫ (regularImage p f).ι = (f ≫ p).smoothLocus.ι ≫ f :=
  IsOpenImmersion.lift_fac (regularImage p f).ι ((f ≫ p).smoothLocus.ι ≫ f) _

omit [AlgebraicGeometry.IsNoetherian X] [IsReduced X] [AlgebraicGeometry.IsNoetherian Y] [IsReduced Y]
  [CharZero k] [IsSeparated p] [IsSeparated (f ≫ p)] in
theorem regularImageMap_smooth : Smooth (regularImageMap p f) := by
  exact property_of_isPullback _ (IsOpenImmersion.isPullback_lift_id
    ((f ≫ p).smoothLocus.ι ≫ f) (regularImage p f).ι _) (inferInstance : Smooth ((f ≫ p).smoothLocus.ι ≫ f))

omit [AlgebraicGeometry.IsNoetherian X] [IsReduced X] [AlgebraicGeometry.IsNoetherian Y] [IsReduced Y]
  [CharZero k] [IsSeparated p] [IsSeparated (f ≫ p)] in
theorem regularImageMap_surjective : Surjective (regularImageMap p f) := by
  constructor
  intro v
  obtain ⟨u, hu⟩ := v.property
  refine ⟨u, ?_⟩
  apply (regularImage p f).ι.injective
  have h := congrArg (fun g => g u) (regularImageMap_over p f)
  exact h.trans hu

theorem regularImage_structure_smooth : Smooth ((regularImage p f).ι ≫ p) := by
  let U := (f ≫ p).smoothLocus
  let V := regularImage p f
  let g := regularImageMap p f
  have : Smooth g := regularImageMap_smooth p f
  have : Surjective g := regularImageMap_surjective p f
  have hscalar : g ≫ (V.ι ≫ p) = U.ι ≫ (f ≫ p) := by
    rw [← Category.assoc, regularImageMap_over, Category.assoc]
  have : Smooth (U.ι ≫ (f ≫ p)) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    exact U.ι_preimage_self
  have : Smooth (g ≫ (V.ι ≫ p)) := by rw [hscalar]; infer_instance
  have : IsSeparated (g ≫ (V.ι ≫ p)) := by rw [hscalar]; infer_instance
  have : IsIso (weakHistory (g ≫ (V.ι ≫ p))).composite := weakHistory_isIso_of_smooth _
  have H := endpoint_isPullback (V.ι ≫ p) g
  have : IsIso (weakHistory (V.ι ≫ p)).composite :=
    MorphismProperty.of_isPullback_of_descendsAlong
      (P := MorphismProperty.isomorphisms Scheme) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      H.flip ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @Smooth) (weakHistory (V.ι ≫ p)).composite]
  exact weakHistory_smooth (V.ι ≫ p)

theorem preimage_smoothLocus_eq : f ⁻¹ᵁ p.smoothLocus = (f ≫ p).smoothLocus := by
  ext y
  constructor
  · intro hy
    let W := f ⁻¹ᵁ p.smoothLocus
    have : Smooth (f ∣_ p.smoothLocus) := IsZariskiLocalAtTarget.restrict (inferInstance : Smooth f) _
    have : Smooth (p.smoothLocus.ι ≫ p) := by
      rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
      exact p.smoothLocus.ι_preimage_self
    have hscalar : W.ι ≫ (f ≫ p) = (f ∣_ p.smoothLocus) ≫ p.smoothLocus.ι ≫ p := by
      rw [← Category.assoc (f ∣_ p.smoothLocus), morphismRestrict_ι, Category.assoc]
    have : Smooth (W.ι ≫ (f ≫ p)) := by rw [hscalar]; infer_instance
    exact (f ≫ p).mem_smoothLocus_iff_exists_smooth.mpr ⟨W, hy, inferInstance⟩
  · intro hy
    have : Smooth ((regularImage p f).ι ≫ p) := regularImage_structure_smooth p f
    apply p.mem_smoothLocus_iff_exists_smooth.mpr
    refine ⟨regularImage p f, ?_, inferInstance⟩
    exact ⟨⟨y, hy⟩, rfl⟩

include p in
theorem singIdeal_smooth : X.singIdeal.comap f = Y.singIdeal := by
  rw [Scheme.singIdeal_eq_vanishingIdeal_closure_singularLocus,
    Hironaka.Smooth.comap_vanishingIdeal_of_smooth,
    Scheme.singIdeal_eq_vanishingIdeal_closure_singularLocus]
  congr 1
  apply Closeds.ext
  change f ⁻¹' closure X.singularLocus = closure Y.singularLocus
  rw [(Scheme.isClosed_singularLocus p).closure_eq,
    (Scheme.isClosed_singularLocus (f ≫ p)).closure_eq,
    Scheme.singularLocus_eq_compl_smoothLocus p,
    Scheme.singularLocus_eq_compl_smoothLocus (f ≫ p)]
  change ((f ⁻¹ᵁ p.smoothLocus : Y.Opens) : Set Y)ᶜ = ((f ≫ p).smoothLocus : Set Y)ᶜ
  rw [preimage_smoothLocus_eq p f]

end
end Hironaka.Resolution.Algebraic.ActualGlobalOriginalSingSmoothNaturality
