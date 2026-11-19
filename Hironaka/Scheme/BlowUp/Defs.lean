/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Hironaka.Scheme.BlowUp.AffineBlowUp.Defs
import Hironaka.Scheme.BlowUp.AffineBlowUp.Universal.Restrict
import Hironaka.Scheme.BlowUp.Glue.AffineBlowUpFunctor

/-!
# The blow-up of a scheme along an ideal sheaf

**The blow-up** `blowUp I` of a scheme `X` along an ideal sheaf `I` is `Proj_X (⨁ Iⁿ)`
[Sta, Tag 01OF], built by the relative gluing lemma [Sta, Tag 01LH] from the affine blow-ups
`Proj Rees(I(U))` over the affine opens `U` of `X` (`blowUpOf`). The gluing hypothesis — that the
naturality squares of `affineBlowUpNatTrans I` are pullbacks — is the open-restriction square of
the universal property of the affine blow-up (`affineBlowUp.isPullback_mapHom`), pasted with the
isomorphisms `Spec Γ(X, U) ≅ U` (`affineBlowUpNatTrans_equifibered`). It is Hauser's blow-up
[Hau14, Definitions 4.4 and 4.7], Kollár's `B_Z X` [Kol07, Notation 19] and Hironaka's monoidal
transformation of `X` with centre the closed subscheme defined by `I` [Hir64, Ch. 0, §2], with its
blow-up map `IdealSheafData.blowUpπ I : blowUp I ⟶ X` and its exceptional divisor
`IdealSheafData.exceptionalDivisor I`, the inverse image ideal sheaf of the centre `Z = V(I)`, whose
closed subscheme is `π⁻¹(Z)`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

open Scheme.IdealSheafData

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The naturality squares of the affine blow-ups over the affine opens are pullbacks — the
open-restriction square `affineBlowUp.isPullback_mapHom` pasted with the isomorphisms
`Spec Γ(X, U) ≅ U`. -/
theorem affineBlowUpNatTrans_equifibered : (affineBlowUpNatTrans I).Equifibered :=
  equifibered_of_isPullback I affineBlowUp.isPullback_mapHom

/-- **The blow-up of `X` along `I`** [Sta, Tag 01OF]; [Hau14, Definition 4.4];
[Kol07, Notation 19]: glued from the affine blow-ups `Proj Rees(I(U))` over the affine opens `U`
of `X`.

Relation to the source.
* **Translation.** `D.blowUp` is Hironaka's monoidal transformation of $X$ with centre $D$
  [Hir64, Ch. 0, §2], and `D.blowUpπ` its projection $f$; "blow-up" and "monoidal transformation"
  are used interchangeably. The centre is any closed subscheme, not necessarily non-singular or
  nonempty: the main theorems state the conditions on their centres as clauses. -/
noncomputable def Scheme.IdealSheafData.blowUp : Scheme.{u} := blowUpOf I
    (affineBlowUpNatTrans_equifibered I)

/-- **The blow-up map** `π : blowUp I ⟶ X`. -/
noncomputable def Scheme.IdealSheafData.blowUpπ : blowUp I ⟶ X := blowUpOf.π I
    (affineBlowUpNatTrans_equifibered I)

/-- The ideal sheaf of the exceptional divisor `f⁻¹(D)`: the inverse image ideal sheaf of the
centre under the projection [Hir64, Ch. 0, §5, p. 142]; [Kol07, Notation 19]. -/
noncomputable def Scheme.IdealSheafData.exceptionalDivisor (D : X.IdealSheafData) :
    D.blowUp.IdealSheafData :=
  D.comap D.blowUpπ

end AlgebraicGeometry
