import DeJongAlterations.StableModification.Projectivity.Relative

/-!
# Original generating sections with a whole prescribed fibre lift

The generating family and the lifted positive power live on the same actual neighborhood and
have the same original line-bundle exponent. Neither desired family nor desired lift is supplied.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.StableModificationBridge.LocalGeneratingSections

open StableModification.Projectivity

universe u

variable {X Y : Scheme.{u}} {β : X ⟶ Y} [IsProper β] {L : LineBundleData X}

/-- Native eventual generation and whole fibre lifting can be realized at the same actual
positive power, on the same original two-affine-cover neighborhood. -/
theorem exists_generating_with_lift (D : TwoAffineCover β L) {y : Y}
    (hyW : y ∈ D.W) (hy : IsClosed ({y} : Set Y)) (hL : FiberAmple L β y)
    {n : ℕ} (hn : 0 < n) (s : (L.pullback (β.fiberι y)).Sections n ⊤) :
    ∃ q : ℕ, 0 < q ∧ ∃ (K : Finset X)
      (τ : X → L.Sections ((n * q : ℕ) : ℤ) (β ⁻¹ᵁ D.W))
      (σ : L.Sections ((n * q : ℕ) : ℤ) (β ⁻¹ᵁ D.W)) (O : Y.Opens),
      y ∈ O ∧ O ≤ D.W ∧
      (∀ x, β x ∈ O → ∃ k ∈ K, x ∈ (τ k).nonvanishingLocus) ∧
      σ.pullback (β.fiberι y) =
        ((s.npow q).cast (by push_cast; rfl)).restrict le_top := by
  obtain ⟨m₀, hlift⟩ := D.exists_lift hyW hy hL
  obtain ⟨m₁, hgenerates⟩ := D.exists_generating hyW hy hL
  let q : ℕ := max m₀ m₁ + 1
  have hq : 0 < q := Nat.succ_pos _
  have hq₀ : m₀ ≤ q := (le_max_left _ _).trans (Nat.le_succ _)
  have hq₁ : m₁ ≤ q := (le_max_right _ _).trans (Nat.le_succ _)
  have hprod : q ≤ n * q := Nat.le_mul_of_pos_left _ hn
  obtain ⟨K, τ, O, hyO, hOW, hτ⟩ := hgenerates (n * q) (hq₁.trans hprod)
  let z : (L.pullback (β.fiberι y)).Sections ((n * q : ℕ) : ℤ) ⊤ :=
    (s.npow q).cast (by push_cast; rfl)
  obtain ⟨σ, hσ⟩ := hlift (n * q) (hq₀.trans hprod) z
  exact ⟨q, hq, K, τ, σ, O, hyO, hOW, hτ, hσ⟩

end DeJongAlterations.StableModificationBridge.LocalGeneratingSections
