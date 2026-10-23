import DeJongAlterations.StableModification.Resolution.StrictifyStep

/-!
# Iterating the blowup step

By induction on the multiplicity bound `m` of the distinguished member `F none`: if `m = 0` the
member is empty; otherwise blow up its `m`-fold locus (`blowup_step`), which lowers the bound to
`m - 1` and adds one exceptional member of multiplicity `1`. The result
(`exists_modification_ncFamily_le_one`) is a projective modification `π : X' → X` with `X'`
regular and a normal crossings family on `X'`, all of whose members have multiplicity at most `1`
and whose union is the preimage of the union of the original family.

This is the strictification of normal crossings divisors by blowups along regular strata
(de Jong 1996, 2.4, `references/dejong96-alterations/tex/page-0006.tex`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

namespace DeJongAlterations.StableModification.Resolution.Strictify

set_option backward.isDefEq.respectTransparency false

open Geometry.BlowupGluing

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A family with all members of multiplicity at most `1` after dropping an empty member. -/
theorem isNCFamily_some_of_zero {X : Scheme.{u}} [IsLocallyNoetherian X] {r : ℕ}
    (F : Option (Fin r) → Closeds X) (hF : IsNCFamily F (fun l ↦ l.elim 0 fun _ ↦ 1)) :
    IsNCFamily (fun i : Fin r ↦ F (some i)) (fun _ ↦ 1) := by
  intro x hx
  obtain ⟨c, hc⟩ := hF x hx
  exact ⟨
    { n := c.n
      t := c.t
      indep := c.indep
      span_eq := c.span_eq
      A := fun i ↦ c.A (some i)
      disjoint := fun i i' h ↦ c.disjoint fun h' ↦ h (Option.some_injective _ h')
      formalIdeal_eq := fun i ↦ c.formalIdeal_eq (some i) }, fun i ↦ hc (some i)⟩

/-- A member of multiplicity `0` at every closed point is empty (Jacobson space). -/
theorem not_mem_of_zero {X : Scheme.{u}} [IsLocallyNoetherian X] [JacobsonSpace X] {r : ℕ}
    (F : Option (Fin r) → Closeds X) (hF : IsNCFamily F (fun l ↦ l.elim 0 fun _ ↦ 1)) (x : X) :
    x ∉ F none := by
  intro hx
  obtain ⟨y, hyF, hy⟩ := nonempty_inter_closedPoints ⟨x, hx⟩ (F none).isClosed.isLocallyClosed
  obtain ⟨c, hc⟩ := hF y hy
  have h0 : c.A none = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp (hc none))
  apply (formalIdeal_ne_top_iff (F none) y).mpr hyF
  rw [c.formalIdeal_eq none, h0, Finset.prod_empty, Ideal.span_singleton_one]

/-- **Strictification by blowups along regular strata.** Let `X` be a smooth projective variety
over an algebraically closed field and `F` a normal crossings family whose member `F none` has
multiplicity at most `m` and whose other members have multiplicity at most `1`. Then there is a
projective modification `π : X' → X` (a composition of blowups along regular strata) with `X'`
regular and a normal crossings family `F'` on `X'` with all multiplicities at most `1` and
`⋃ F' = π⁻¹ (⋃ F)`. -/
theorem exists_modification_ncFamily_le_one (m : ℕ) :
    ∀ {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X]
      [LocallyOfFiniteType p] [Smooth p] {r : ℕ} (F : Option (Fin r) → Closeds X),
      IsNCFamily F (fun l ↦ l.elim m fun _ ↦ 1) → IsProjectiveOver p →
      ∃ (X' : Scheme.{u}) (_ : IsLocallyNoetherian X') (π : X' ⟶ X) (r' : ℕ)
        (F' : Fin r' → Closeds X'), IsModification π ∧ IsProjectiveOver (π ≫ p) ∧
        IsRegularScheme X' ∧ IsNCFamily F' (fun _ ↦ 1) ∧
        ∀ y, (∃ l, y ∈ F' l) ↔ ∃ l, π y ∈ F l := by
  induction m with
  | zero =>
    intro X p _ _ _ _ r F hF hp
    have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
    refine ⟨X, inferInstance, 𝟙 X, r, fun i ↦ F (some i), inferInstance, by simpa using hp,
      Geometry.RegularSmooth.isRegularScheme_of_smooth p, isNCFamily_some_of_zero F hF, ?_⟩
    intro y
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨some i, hi⟩
    · rintro ⟨_ | i, hi⟩
      · exact absurd hi (not_mem_of_zero F hF y)
      · exact ⟨i, hi⟩
  | succ m ih =>
    intro X p _ _ _ _ r F hF hp
    classical
    have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
    have hreg : IsRegularScheme X := Geometry.RegularSmooth.isRegularScheme_of_smooth p
    -- the centre is a proper closed subset
    have hC : mFoldLocus F none (m + 1) ≠ ⊤ := by
      obtain ⟨x, -, hx⟩ := nonempty_inter_closedPoints (Set.univ_nonempty (α := X))
        isClosed_univ.isLocallyClosed
      obtain ⟨c, -⟩ := hF x hx
      have : IsRegularLocalRing (X.presheaf.stalk x) := hreg x
      have : IsRegularLocalRing (X.completedLocalRing x) :=
        Algebra.CompletionRegularityAscent.isRegularLocalRing_completion _
      have : IsDomain (X.completedLocalRing x) :=
        Algebra.RegularLocalDomain.isDomain_of_isRegularLocalRing _
      intro htop
      apply ne_top_of_ncChart F x c none
      exact top_unique (htop ▸ mFoldLocus_le F none (by omega))
    obtain ⟨hreg1, hF1⟩ := blowup_step p (by omega) F hF hC
    let D := Scheme.IdealSheafData.vanishingIdeal (mFoldLocus F none (m + 1))
    let π₁ := blowupStructure D
    have hD : D.support ≠ ⊤ := by
      rwa [Geometry.ReducedClosedSubscheme.support_vanishingIdeal]
    have hmod₁ : IsModification π₁ :=
      Geometry.BlowupModification.blowupStructure_isModification D hD
    have : IsIntegral (blowup D) := hmod₁.sourceIntegral
    have : LocallyOfFiniteType (π₁ ≫ p) := inferInstance
    have : Smooth (π₁ ≫ p) :=
      Geometry.RegularSmoothConverse.smooth_of_isRegularScheme (π₁ ≫ p) hreg1
    have hp₁ : IsProjectiveOver (π₁ ≫ p) :=
      Geometry.BlowupProjective.blowupStructure_comp_isProjective D p hp
    obtain ⟨X', _, π', r', F', hmod', hp', hreg', hF', hunion'⟩ := ih (π₁ ≫ p) _ hF1 hp₁
    refine ⟨X', inferInstance, π' ≫ π₁, r', F', IsModification.comp π' π₁,
      by rwa [Category.assoc], hreg', hF', ?_⟩
    intro y
    rw [hunion' y, exists_mem_transformFamily_iff π₁ F _ (m + 1) (mFoldLocus_le F none (by omega))]
    rfl

end DeJongAlterations.StableModification.Resolution.Strictify
