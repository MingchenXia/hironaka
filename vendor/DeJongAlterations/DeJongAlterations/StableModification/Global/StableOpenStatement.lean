/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Global.StatementsBaseChange

/-!
# The corrected spreading statement `StableOpenNbhdConn`

Node G4 of `PLAN-T5.md` (Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19
(2010), Lemma 5.1 (ii) `openloclem`, T:3282–3311, in the open form used in the proof of
Theorem 1.5, T:3384–3394), corrected as recorded in ERRATA DJA-O36.

The integrated statement `Global.StableOpenNbhd k` spreads numerical stability from one geometric
fibre to a neighbourhood. Its planned proof (via the positivity of `ω_{X/U}(D')` on the contracted
components, PLAN-T5 §0.5 and G4) needs that `ω(D')` is positive on every component contracted by
`β_a`; on a component of arithmetic genus one without special points (for instance
`X = E ×_k U → C = U` for a smooth genus-one curve `E`, `D' = ∅`) the degree is zero, and such a
component is a connected component of `X_a`. We therefore add the hypothesis that **no nonempty
clopen subset of the geometric fibre `X_a` is contracted by `β_a`** (`NoContractedClopen`). The
consumer (`exists_localStablePiece_conn`, `Global/SpreadPieceConn.lean`) supplies it from
Zariski's connectedness theorem for the closed fibre of the projective stable model.

* `NoContractedClopen β g a`: no nonempty clopen subset of `(X ×_S Spec K)` has subsingleton
  image in `C ×_S Spec K` under `β_a`.
* `NoContractedClopen.of_iso`, `noContractedClopen_iff_of_isPullback`,
  `noContractedClopen_pullback_iff`: the condition is fibrewise (transport along isomorphisms of
  geometric fibres and base change), as `NumericallyStableFibre` is
  (`Global/StatementsBaseChange.lean`).
* `StableOpenNbhdConn k`: `StableOpenNbhd k` with the extra hypothesis `NoContractedClopen β q a`;
  `StableOpenNbhd.conn` (the old statement implies the new one).
* `StableOpenNbhdRational K`: the same statement over an algebraically closed field `K`, for a
  *normal* variety `V` and a `K`-rational point (a section `a` of `V ⟶ Spec K`). This is the
  remaining ω step of node G4 (ERRATA DJA-O36), the hypothesis of the reduction
  `stableOpenNbhdConn_of_rational` (`Global/StableOpenReduce.lean`).

Blueprint: `sm-global-stable-open.tex` (`def:sm-gso-no-contracted-clopen`,
`lem:sm-gso-no-contracted-clopen-base-change`, `def:sm-gso-stable-open-conn`,
`def:sm-gso-stable-open-rational`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.StableModification.Global

universe u

open DeJong (IsSemistablePair IsRelativelyProjective)
open Curves (pullbackCompMap)

section Clopen

variable {C C' S S' : Scheme.{u}}

/-- **No contracted clopen subset** (ERRATA DJA-O36): no nonempty clopen subset of the geometric
fibre `X_a = X ×_S Spec K` of `β ≫ g` over `a : Spec K ⟶ S` is contracted by
`β_a : X_a ⟶ C_a` (has subsingleton image). If `X_a` is connected, this says that `β_a` does not
contract the whole fibre. -/
def NoContractedClopen (β : C' ⟶ C) (g : C ⟶ S) {K : Type u} [Field K]
    (a : Spec (.of K) ⟶ S) : Prop :=
  ∀ Z : Set (pullback (C := Scheme.{u}) (β ≫ g) a), IsClopen Z → Z.Nonempty →
    ¬ (pullbackCompMap β g a '' Z).Subsingleton

/-- **`NoContractedClopen` transports along isomorphisms of geometric fibres** compatible with the
maps of geometric fibres (no condition on the second map `χ` is needed). -/
theorem NoContractedClopen.of_iso {C₁ C₁' S₁ C₂ C₂' S₂ : Scheme.{u}} {β₁ : C₁' ⟶ C₁}
    {g₁ : C₁ ⟶ S₁} {β₂ : C₂' ⟶ C₂} {g₂ : C₂ ⟶ S₂} {K : Type u} [Field K]
    {a₁ : Spec (.of K) ⟶ S₁} {a₂ : Spec (.of K) ⟶ S₂}
    (φ : pullback (β₁ ≫ g₁) a₁ ≅ pullback (β₂ ≫ g₂) a₂) (χ : pullback g₁ a₁ ⟶ pullback g₂ a₂)
    (hmap : φ.hom ≫ pullbackCompMap β₂ g₂ a₂ = pullbackCompMap β₁ g₁ a₁ ≫ χ)
    (h : NoContractedClopen β₂ g₂ a₂) : NoContractedClopen β₁ g₁ a₁ := by
  intro Z hZ hne hsub
  refine h (φ.hom '' Z) ⟨?_, ?_⟩ (hne.image _) ?_
  · exact φ.hom.homeomorph.isClosedMap _ hZ.1
  · exact φ.hom.homeomorph.isOpenMap _ hZ.2
  · rw [Set.image_image]
    have : (fun y ↦ pullbackCompMap β₂ g₂ a₂ (φ.hom y)) =
        fun y ↦ χ (pullbackCompMap β₁ g₁ a₁ y) :=
      funext fun y ↦ by rw [← Scheme.Hom.comp_apply, hmap, Scheme.Hom.comp_apply]
    rw [this, ← Set.image_image]
    exact hsub.image _

/-- **`NoContractedClopen` along pull-back squares**: if `X₁ = X₂ ×_{P₂} P₁` and
`P₁ = P₂ ×_{T₂} T₁`, the geometric fibre of `(β₁, g₁)` over `a` is that of `(β₂, g₂)` over
`a ≫ w`. -/
theorem noContractedClopen_iff_of_isPullback {X₁ X₂ P₁ P₂ T₁ T₂ : Scheme.{u}}
    {β₁ : X₁ ⟶ P₁} {β₂ : X₂ ⟶ P₂} {g₁ : P₁ ⟶ T₁} {g₂ : P₂ ⟶ T₂} {u : X₁ ⟶ X₂}
    {v : P₁ ⟶ P₂} {w : T₁ ⟶ T₂} (H₁ : IsPullback u β₁ β₂ v) (H₂ : IsPullback v g₁ g₂ w)
    {K : Type u} [Field K] (a : Spec (.of K) ⟶ T₁) :
    NoContractedClopen β₁ g₁ a ↔ NoContractedClopen β₂ g₂ (a ≫ w) := by
  have H : IsPullback u (β₁ ≫ g₁) (β₂ ≫ g₂) w := H₁.paste_vert H₂
  have Hx : IsPullback (pullback.fst (β₁ ≫ g₁) a ≫ u) (pullback.snd (β₁ ≫ g₁) a) (β₂ ≫ g₂)
      (a ≫ w) := (IsPullback.of_hasPullback (β₁ ≫ g₁) a).paste_horiz H
  have Hp : IsPullback (pullback.fst g₁ a ≫ v) (pullback.snd g₁ a) g₂ (a ≫ w) :=
    (IsPullback.of_hasPullback g₁ a).paste_horiz H₂
  let φ := Hx.isoPullback
  let χ := Hp.isoPullback
  have hφf : φ.hom ≫ pullback.fst (β₂ ≫ g₂) (a ≫ w) = pullback.fst (β₁ ≫ g₁) a ≫ u :=
    Hx.isoPullback_hom_fst
  have hφs : φ.hom ≫ pullback.snd (β₂ ≫ g₂) (a ≫ w) = pullback.snd (β₁ ≫ g₁) a :=
    Hx.isoPullback_hom_snd
  have hmap : φ.hom ≫ pullbackCompMap β₂ g₂ (a ≫ w) = pullbackCompMap β₁ g₁ a ≫ χ.hom := by
    apply pullback.hom_ext
    · rw [Category.assoc, Curves.pullbackCompMap_fst, reassoc_of% hφf, Category.assoc,
        Hp.isoPullback_hom_fst, Curves.pullbackCompMap_fst_assoc, H₁.w]
    · rw [Category.assoc, Curves.pullbackCompMap_snd, hφs, Category.assoc,
        Hp.isoPullback_hom_snd, Curves.pullbackCompMap_snd]
  constructor
  · intro h
    refine NoContractedClopen.of_iso φ.symm χ.inv ?_ h
    rw [Iso.symm_hom, Iso.inv_comp_eq, ← Category.assoc, hmap, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  · exact NoContractedClopen.of_iso φ χ.hom hmap

/-- **Base change of `NoContractedClopen`**: the geometric fibre of the base change of `(β, g)`
along `ψ : S' ⟶ S` over `a` is the geometric fibre of `(β, g)` over `a ≫ ψ`. -/
theorem noContractedClopen_pullback_iff (β : C' ⟶ C) (g : C ⟶ S) (ψ : S' ⟶ S) {K : Type u}
    [Field K] (a : Spec (.of K) ⟶ S') :
    NoContractedClopen (pullbackCompMap β g ψ) (pullback.snd g ψ) a ↔
      NoContractedClopen β g (a ≫ ψ) := by
  obtain ⟨φ, χ, -, hmap, -⟩ := exists_iso_pullback_fibre β g ψ a
  constructor
  · intro h
    refine NoContractedClopen.of_iso φ.symm χ.inv ?_ h
    rw [Iso.symm_hom, Iso.inv_comp_eq, ← Category.assoc, hmap, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  · exact NoContractedClopen.of_iso φ χ.hom hmap

end Clopen

section Statements

/-- **Spreading of numerical stability, corrected** (Temkin Lemma 5.1 (ii) `openloclem`,
T:3282–3311, in the form used in the proof of Thm 1.5, T:3384–3394; node G4 of `PLAN-T5.md`, with
the correction of ERRATA DJA-O36). This is `StableOpenNbhd k` with the extra hypothesis that no
nonempty clopen subset of the geometric fibre `X_a` is contracted by `β_a`
(`NoContractedClopen β q a`). Let `U` be a variety over `k`, `q : C ⟶ U` projective relative to
`k`, `β : X ⟶ C` projective relative to `k`, and `(X, D')` a semi-stable pair over `U`. If the
geometric fibre over one geometric point `a` over `z ∈ U` is numerically stable and has no
contracted clopen subset, the geometric fibres over all points of an open neighbourhood of `z` are
numerically stable. -/
def StableOpenNbhdConn (k : Type u) [Field k] : Prop :=
  ∀ (U : Scheme.{u}) (pU : U ⟶ Spec (.of k)) (_ : IsVariety pU)
    (C : Scheme.{u}) (q : C ⟶ U), IsRelativelyProjective pU q →
    ∀ (X : Scheme.{u}) (β : X ⟶ C), IsRelativelyProjective (q ≫ pU) β →
    ∀ (D' : X.IdealSheafData), IsSemistablePair (β ≫ q) D' →
    ∀ (z : U) (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ U), (∀ x, a x = z) →
      NumericallyStableFibre β q D' a → NoContractedClopen β q a →
      ∃ O : U.Opens, z ∈ O ∧ ∀ z' ∈ O, IsNumericallyStableAt β q D' z'

/-- The integrated statement `StableOpenNbhd k` implies the corrected one (which has one more
hypothesis). -/
theorem StableOpenNbhd.conn {k : Type u} [Field k] (h : StableOpenNbhd k) :
    StableOpenNbhdConn k :=
  fun U pU hU C q hq X β hβ D' hss z K _ _ a ha hst _ ↦
    h U pU hU C q hq X β hβ D' hss z K a ha hst

/-- **The ω step of node G4** (ERRATA DJA-O36; the hypothesis of the reduction
`stableOpenNbhdConn_of_rational`): `StableOpenNbhdConn` over an algebraically closed field `K`,
for a *normal* variety `V` over `K` and a `K`-rational point, i.e. a section `a` of
`pV : V ⟶ Spec K` (whose image is a closed point). The planned proof (PLAN-T5 G4): `ω(D')` has
positive degree on every component of `X_a` contracted by `β_a` (numerical stability and
`NoContractedClopen`), hence is ample on the fibres of `β` over `C_a`, hence `β`-ample over a
neighbourhood of `C_a`, which gives positive degree, i.e. numerical stability, on the contracted
components of the nearby fibres. Not asserted here. -/
def StableOpenNbhdRational (K : Type u) [Field K] [IsAlgClosed K] : Prop :=
  ∀ (V : Scheme.{u}) (pV : V ⟶ Spec (.of K)) (_ : IsVariety pV), IsNormalScheme V →
    ∀ (C : Scheme.{u}) (q : C ⟶ V), IsRelativelyProjective pV q →
    ∀ (X : Scheme.{u}) (β : X ⟶ C), IsRelativelyProjective (q ≫ pV) β →
    ∀ (D' : X.IdealSheafData), IsSemistablePair (β ≫ q) D' →
    ∀ (a : Spec (.of K) ⟶ V), a ≫ pV = 𝟙 _ →
      NumericallyStableFibre β q D' a → NoContractedClopen β q a →
      ∃ O : V.Opens, a (IsLocalRing.closedPoint K) ∈ O ∧
        ∀ z' ∈ O, IsNumericallyStableAt β q D' z'

end Statements

end DeJongAlterations.StableModification.Global
