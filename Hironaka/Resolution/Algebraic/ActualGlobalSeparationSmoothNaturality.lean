import Hironaka.Resolution.Algebraic.ActualSmoothComponentDimensionTransport

/-!
# Actual intrinsic global separation ideal is smooth-natural

Source-first proof: `actual-global-separation-smooth-naturality-20261102.tex`.
Actual generic component lifting and intrinsic dimension shift derive the real
coherent centre equality; no smooth/J compatibility certificate is supplied.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.IdealSheafData
universe u

namespace Hironaka.Resolution.Algebraic.ActualGlobalSeparationSmoothNaturality

noncomputable section
open ActualIntrinsicComponentDimensions ActualSmoothComponentDimensionTransport

variable {X Y : Scheme.{u}} [IsNoetherian X] [IsReduced X] [IsNoetherian Y] [IsReduced Y]

theorem exists_component_over_point (f : Y ⟶ X) [Flat f] (C : irreducibleComponents X)
    (y : Y) (hy : f y ∈ C.val) :
    ∃ D : irreducibleComponents Y, y ∈ D.val ∧ imageComponent f D = C := by
  obtain ⟨ξ, hξy, hfξ⟩ := Flat.generalizingMap f ((componentGenericPoint_generic C).specializes hy)
  let D : irreducibleComponents Y := ⟨irreducibleComponent ξ, irreducibleComponent_mem_irreducibleComponents ξ⟩
  have hηξ : componentGenericPoint D ⤳ ξ := (componentGenericPoint_generic D).specializes mem_irreducibleComponent
  have hmap : f (componentGenericPoint D) = componentGenericPoint C := by
    apply eq_of_specializes_of_isGenericPoint_of_mem_irreducibleComponents C.property (componentGenericPoint_generic C)
    rw [← hfξ]
    exact hηξ.map f.continuous
  refine ⟨D, (componentGenericPoint_generic D).specializes_iff_mem.mp (hηξ.trans hξy), ?_⟩
  apply Subtype.ext
  have hpoint : componentGenericPoint (imageComponent f D) = componentGenericPoint C :=
    (imageComponent_genericPoint f D).symm.trans hmap
  have hgen := componentGenericPoint_generic (imageComponent f D)
  rw [hpoint] at hgen
  exact hgen.symm.trans (componentGenericPoint_generic C)

theorem complementaryClosed_preimage {k : Type u} [Field k] [CharZero k]
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] (f : Y ⟶ X) (r n : ℕ)
    [SmoothOfRelativeDimension r f] :
    (ActualGlobalDimensionSeparationIdeal.complementaryClosed X n).preimage f.continuous =
      ActualGlobalDimensionSeparationIdeal.complementaryClosed Y (n + r : ℕ) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth r f
  ext y
  change f y ∈ ActualGlobalDimensionSeparationIdeal.complementaryClosed X n ↔
    y ∈ ActualGlobalDimensionSeparationIdeal.complementaryClosed Y (n + r : ℕ)
  rw [ActualGlobalDimensionSeparationIdeal.mem_complementaryClosed,
    ActualGlobalDimensionSeparationIdeal.mem_complementaryClosed]
  constructor
  · rintro ⟨C, hC, hyC⟩
    obtain ⟨D, hyD, hDC⟩ := exists_component_over_point f C y hyC
    refine ⟨D, ?_, hyD⟩
    intro hD
    have hshift := componentDimension_add p f r D
    rw [hDC] at hshift
    obtain ⟨m, hm⟩ := componentDimension_nat p C
    have he : ((m : WithBot ℕ∞) + r) = (n + r : ℕ) := by
      rw [← hm]
      exact hshift.symm.trans hD
    have hnat : m + r = n + r := by exact_mod_cast he
    exact hC (hm.trans (by exact_mod_cast Nat.add_right_cancel hnat))
  · rintro ⟨D, hD, hyD⟩
    refine ⟨imageComponent f D, ?_, imageComponent_image_subset f D ⟨y, hyD, rfl⟩⟩
    intro hC
    apply hD
    calc
      componentDimension D = componentDimension (imageComponent f D) + r := componentDimension_add p f r D
      _ = (n : WithBot ℕ∞) + r := congrArg (· + (r : WithBot ℕ∞)) hC
      _ = (n + r : ℕ) := by exact_mod_cast rfl

theorem separationIdeal_smooth_relative {k : Type u} [Field k] [CharZero k]
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] (f : Y ⟶ X) (r : ℕ)
    [SmoothOfRelativeDimension r f] :
    (ActualGlobalDimensionSeparationIdeal.separationIdeal X).comap f =
      ActualGlobalDimensionSeparationIdeal.separationIdeal Y := by
  have : Smooth f := SmoothOfRelativeDimension.smooth r f
  apply le_antisymm
  · rw [ActualGlobalDimensionSeparationIdeal.separationIdeal_eq_finite_sum X, comap_iSup]
    refine iSup_le fun d => ?_
    obtain ⟨C, hC⟩ := d.property
    obtain ⟨n, hn⟩ := componentDimension_nat p C
    have hd : d.val = (n : WithBot ℕ∞) := hC.symm.trans hn
    rw [hd, Hironaka.Smooth.comap_vanishingIdeal_of_smooth, complementaryClosed_preimage p f r n]
    exact le_iSup (fun e : WithBot ℕ∞ => vanishingIdeal
      (ActualGlobalDimensionSeparationIdeal.complementaryClosed Y e)) (n + r : ℕ)
  · rw [ActualGlobalDimensionSeparationIdeal.separationIdeal_eq_finite_sum Y]
    refine iSup_le fun e => ?_
    obtain ⟨D, hD⟩ := e.property
    obtain ⟨m, hm⟩ := componentDimension_nat p (imageComponent f D)
    have he : e.val = (m + r : ℕ) := by
      calc
        e.val = componentDimension D := hD.symm
        _ = componentDimension (imageComponent f D) + r := componentDimension_add p f r D
        _ = (m + r : ℕ) := by rw [hm]; exact_mod_cast rfl
    have hterm : vanishingIdeal (ActualGlobalDimensionSeparationIdeal.complementaryClosed Y e.val) =
        (vanishingIdeal (ActualGlobalDimensionSeparationIdeal.complementaryClosed X m)).comap f := by
      rw [he, Hironaka.Smooth.comap_vanishingIdeal_of_smooth, complementaryClosed_preimage p f r m]
    rw [hterm]
    exact comap_mono f (le_iSup (fun d : WithBot ℕ∞ => vanishingIdeal
      (ActualGlobalDimensionSeparationIdeal.complementaryClosed X d)) m)

theorem separationIdeal_smooth {k : Type u} [Field k] [CharZero k]
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] (f : Y ⟶ X) [Smooth f] :
    (ActualGlobalDimensionSeparationIdeal.separationIdeal X).comap f =
      ActualGlobalDimensionSeparationIdeal.separationIdeal Y := by
  apply Scheme.IdealSheafData.ext_stalkIdeal
  intro y
  obtain ⟨U, r, hyU, hr⟩ := Hironaka.Resolution.exists_smoothOfRelativeDimension_ι_comp f y
  have : CompactSpace U.toScheme :=
    isCompact_iff_compactSpace.mp (NoetherianSpace.isCompact (U : Set Y))
  have : IsNoetherian U.toScheme := AlgebraicGeometry.IsNoetherian.mk
  have : SmoothOfRelativeDimension r (U.ι ≫ f) := hr
  have hlocal : ((ActualGlobalDimensionSeparationIdeal.separationIdeal X).comap f).comap U.ι =
      (ActualGlobalDimensionSeparationIdeal.separationIdeal Y).comap U.ι := by
    rw [← comap_comp]
    exact (separationIdeal_smooth_relative p (U.ι ≫ f) r).trans
      (ActualGlobalDimensionSeparationIdeal.separationIdeal_open (f ≫ p) U.ι).symm
  let u : U.toScheme := ⟨y, hyU⟩
  have hs := congrArg (fun I : U.toScheme.IdealSheafData => I.stalkIdeal u) hlocal
  rw [stalkIdeal_comap ((ActualGlobalDimensionSeparationIdeal.separationIdeal X).comap f) U.ι u,
    stalkIdeal_comap (ActualGlobalDimensionSeparationIdeal.separationIdeal Y) U.ι u] at hs
  have hc := congrArg (fun I => I.comap (U.ι.stalkMap u).hom) hs
  simp only [Scheme.Hom.comap_stalkMap_map_eq_self] at hc
  simpa only [Scheme.Opens.ι_apply, u] using hc

end
end Hironaka.Resolution.Algebraic.ActualGlobalSeparationSmoothNaturality
