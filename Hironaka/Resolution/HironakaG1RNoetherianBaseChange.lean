import Hironaka.Resolution.HironakaG1RComponentBaseChange
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Noetherian schemes of finite type under field extension

`noetherianSpace_of_isPullback`: for a cartesian square `IsPullback p fL f (Spec.map (k → L))`
(`X_L = X ×_k L`, `L / k` any field extension) with `f` locally of finite type, if the underlying
space of `X` is noetherian then so is that of `X_L` (`X_L` is quasi-compact, `p` being the base
change of the quasi-compact `Spec L → Spec k`, and locally noetherian, being locally of finite type
over `Spec L`).  This discharges the hypothesis `[NoetherianSpace X_L]` of
`HironakaG1RComponentBaseChange.comap_separationIdeal_of_isPullback` (layer F1) from `[NoetherianSpace X]`.

Only Mathlib and lane G1's modules are imported; no named input.
Blueprint: `hironaka-g1-r-integral-scheme-dimension.tex` (node `g1r:separation-ideal-base-change`).
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hironaka.HironakaG1RNoetherianBaseChange

open AlgebraicGeometry

universe u

variable {k L : Type u} [Field k] [Field L] [Algebra k L] {X XL : Scheme.{u}}
  {f : X ⟶ Spec (.of k)} {fL : XL ⟶ Spec (.of L)} {p : XL ⟶ X}

/-- **Noetherian underlying spaces are preserved by field extension** (finite type schemes). -/
theorem noetherianSpace_of_isPullback
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    [LocallyOfFiniteType f] [NoetherianSpace X] : NoetherianSpace XL := by
  have : LocallyOfFiniteType fL := MorphismProperty.of_isPullback h ‹_›
  have : IsLocallyNoetherian XL := LocallyOfFiniteType.isLocallyNoetherian fL
  have : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap k L))) := inferInstance
  have : QuasiCompact p := MorphismProperty.of_isPullback h.flip this
  have : CompactSpace XL := QuasiCompact.compactSpace_of_compactSpace p
  have : IsNoetherian XL := {}
  infer_instance

/-- **F1 with the noetherian hypothesis on `X` only** (`k` perfect). -/
theorem comap_separationIdeal_of_isPullback' [PerfectField k]
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    [LocallyOfFiniteType f] [NoetherianSpace X] :
    letI := noetherianSpace_of_isPullback h
    (HironakaG1RComponentBaseChange.separationIdeal X).comap p =
      HironakaG1RComponentBaseChange.separationIdeal XL := by
  let _ := noetherianSpace_of_isPullback h
  exact HironakaG1RComponentBaseChange.comap_separationIdeal_of_isPullback h

end Hironaka.HironakaG1RNoetherianBaseChange
