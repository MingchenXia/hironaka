/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.CompletionCoords
public import Hironaka.Algebra.Local.MaximalContact

/-!
# Derivatives commute with completion

Kollár's `D(Î) = \widehat{D(I)}`, where `^` denotes completion [Kol07, Lemma 74(5)].  With the
extended coordinate derivations `∂̂ᵢ` of `Hironaka/Algebra/Local/CompletionCoords.lean` (`∂̂ᵢ ∘ ι =
ι ∘ ∂ᵢ`, so that `R̂` carries the coordinate structure `c.adicCompletion`, given its regularity) and
the identification `I R̂ = Î`, this is the case `e = id` of the base-change formula
`D(φ(I)) = φ(D(I))` of `Hironaka/Algebra/Local/Derivative.lean` (`D_map`): `D(I R̂) = D(I) R̂`.
Iterating, `Dʳ(I R̂) = Dʳ(I) R̂`, in particular `MC(Î) = \widehat{MC(I)}` (Kollár's "since taking
derivatives commutes with completion (74.5), we see that `\widehat{MC(I)} = MC(Î)`" in the
discussion preceding [Kol07, Theorem 92]), and, since `I R̂ ∩ R = I`, `I` is MC-invariant iff `Î` is
— the transfer used in the proof of [Kol07, Theorem 92].
-/

public section

namespace IsLocalRing

open IsLocalRing

section Local

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- Extension of ideals to `R̂` reflects inclusions (from `I R̂ ∩ R = I`). -/
theorem map_adicCompletion_le_iff {I J : Ideal R} :
    I.map (algebraMap R (AdicCompletion (maximalIdeal R) R)) ≤
        J.map (algebraMap R (AdicCompletion (maximalIdeal R) R)) ↔ I ≤ J := by
  refine ⟨fun h => ?_, Ideal.map_mono⟩
  have := Ideal.comap_mono (f := algebraMap R (AdicCompletion (maximalIdeal R) R)) h
  rwa [comap_map_adicCompletion, comap_map_adicCompletion] at this

end Local

namespace RegularCoords

variable {R : Type*} [CommRing R] [IsRegularLocalRing R] [Algebra ℚ R] {n : ℕ}
  (c : RegularCoords R n) [IsRegularLocalRing (AdicCompletion (maximalIdeal R) R)]

/-- The extended coordinate derivations restrict to the originals, read through
`c.adicCompletion`: `∂̂ᵢ (ι f) = ι (∂ᵢ f)`. -/
theorem adicCompletion_pderiv_algebraMap (i : Fin n) (f : R) :
    c.adicCompletion.pderiv i (algebraMap R (AdicCompletion (maximalIdeal R) R) f) =
      algebraMap R (AdicCompletion (maximalIdeal R) R) (c.pderiv i f) :=
  Derivation.adicCompletion_algebraMap _ _ f

/-- **Derivatives commute with completion** [Kol07, Lemma 74(5)]: `D(I R̂) = D(I) R̂`, the case
`e = id` of `D_map` applied to `ι : R → R̂` and the extended derivations. -/
theorem D_adicCompletion (I : Ideal R) :
    c.adicCompletion.D (I.map (algebraMap R (AdicCompletion (maximalIdeal R) R))) =
      (c.D I).map (algebraMap R (AdicCompletion (maximalIdeal R) R)) :=
  c.D_map c.adicCompletion _ id (fun i f => c.adicCompletion_pderiv_algebraMap i f)
    (fun j hj => (hj (Set.mem_range_self j)).elim) I

/-- Iterated: `Dʳ(I R̂) = Dʳ(I) R̂`. -/
theorem Dpow_adicCompletion (r : ℕ) (I : Ideal R) :
    c.adicCompletion.Dpow r (I.map (algebraMap R (AdicCompletion (maximalIdeal R) R))) =
      (c.Dpow r I).map (algebraMap R (AdicCompletion (maximalIdeal R) R)) := by
  induction r with
  | zero => simp
  | succ r ih => rw [Dpow_succ, Dpow_succ, ih, c.D_adicCompletion]

/-- Kollár's notation `D(Î) = \widehat{D(I)}` [Kol07, Lemma 74(5)], with `Î` the image in `R̂` of
the completion of the module `I` (`range_adicCompletion_map_subtype`). -/
theorem D_range_adicCompletion_map_subtype (I : Ideal R) :
    c.adicCompletion.D (LinearMap.range (AdicCompletion.map (maximalIdeal R) I.subtype)) =
      LinearMap.range (AdicCompletion.map (maximalIdeal R) (c.D I).subtype) :=
  (congrArg c.adicCompletion.D (range_adicCompletion_map_subtype I)).trans
    ((c.D_adicCompletion I).trans (range_adicCompletion_map_subtype (c.D I)).symm)

/-- `MC(Î) = \widehat{MC(I)}`, i.e. `D^{m-1}(I R̂) = D^{m-1}(I) R̂` (the discussion preceding
[Kol07, Theorem 92]). -/
theorem MC_adicCompletion (I : Ideal R) (m : ℕ) :
    c.adicCompletion.MC (I.map (algebraMap R (AdicCompletion (maximalIdeal R) R))) m =
      (c.MC I m).map (algebraMap R (AdicCompletion (maximalIdeal R) R)) :=
  c.Dpow_adicCompletion (m - 1) I

/-- `D(I R̂) ∩ R = D(I)`. -/
theorem comap_D_adicCompletion (I : Ideal R) :
    (c.adicCompletion.D (I.map (algebraMap R (AdicCompletion (maximalIdeal R) R)))).comap
        (algebraMap R (AdicCompletion (maximalIdeal R) R)) = c.D I := by
  rw [c.D_adicCompletion, comap_map_adicCompletion]

/-- `MC(Î) ∩ R = MC(I)`. -/
theorem comap_MC_adicCompletion (I : Ideal R) (m : ℕ) :
    (c.adicCompletion.MC (I.map (algebraMap R (AdicCompletion (maximalIdeal R) R))) m).comap
        (algebraMap R (AdicCompletion (maximalIdeal R) R)) = c.MC I m := by
  rw [c.MC_adicCompletion, comap_map_adicCompletion]

/-- `I` is MC-invariant with respect to `m` iff `I R̂` is: the transfer of MC-invariance to the
completion in the discussion preceding [Kol07, Theorem 92], with the definition (53.1) of
[Kol07, 53]. -/
theorem isMCInvariant_adicCompletion_iff (I : Ideal R) (m : ℕ) :
    c.adicCompletion.IsMCInvariant (I.map (algebraMap R (AdicCompletion (maximalIdeal R) R))) m ↔
      c.IsMCInvariant I m := by
  unfold IsMCInvariant
  rw [c.MC_adicCompletion, c.D_adicCompletion, ← Ideal.map_mul, map_adicCompletion_le_iff]

end RegularCoords

end IsLocalRing
