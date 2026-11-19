import Hironaka.Analytic.PositiveClasses
import Hironaka.Analytic.PotentialTheory.GlobalPotentialsBasic
import Hironaka.Analytic.BoundedPotentialSmoothingOfAlgebraicApproximation

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Demailly's smooth regularization of a *bounded* potential

**Run 0094: no longer an independent input.**  The theorem below is proved in
`Hironaka.BoundedPotentialSmoothingOfAlgebraicApproximation` from the project's
single named form of Demailly 1992,
`Demailly1992AlgebraicApproximation.demailly1992_exists_algebraicApproximation`
(`bou02-volume:2.6`, human decision `I-0598`): a bounded-below approximant has no
poles, hence is chart-smooth; the curvature clause holds once `δ_k ≤ ε`; and the
two comparison clauses below follow from clause (ii) of that theorem, the upper
one by a one-sided Dini argument on the compact manifold.  Its statement is
unchanged.  The text below is the run-0082 description, kept as written; read
"External classical input" there as "the statement this module records".

**External classical input.**  Demailly, *Regularization of closed positive
currents and intersection theory*, J. Algebraic Geom. 1 (1992), Theorem 1.1,
applied to a potential with **no** singularities.

Let `θ` be a smooth closed real `(1,1)`-form on a compact Kähler manifold
`(M, ω)` and let `u` be a globally bounded `θ`-PSH function.  Demailly's
Bergman-kernel approximants `u_m = (1/m) log K_m`, built from an orthonormal
basis of the weighted space `H(mu)`, satisfy `θ + (c/m) ω + ddᶜ u_m ≥ 0`.
Because `u` is bounded, every multiplier ideal `𝓘(mu)` is the full structure
sheaf, so the basis has no common zero and each `u_m` is **smooth**.  Letting
`m → ∞` gives the curvature clause below, for every `ε > 0` at once.

## Provenance of the two comparison clauses — read this before citing

The curvature clause is `Hironaka.QuantitativeRegularization`'s
`lem:regularization` for a potential with no singularities, plus the smoothness
observation above.  The two comparison clauses `u ≤ h + ε` and `h ≤ b + ε`
are **not** in that source: Copy-4 `lem:regularization` asserts only
`ζ + ddᶜφ_m ≥ -(c/m)ω` and the local ideal bound
`φ_m ≥ m⁻¹ ψ_{𝓘(mφ)} + O(1)`, and with `𝓘(mu) = 𝒪` the latter gives only
`φ_m ≥ O(1)`.  They are the standard two-sided estimates of Demailly's
construction as usually stated (`u ≤ φ_m + C₁/m`,
`φ_m ≤ sup_{B(·,r)} u + (1/m) log(C₂/r^{2n})`), **reconstructed here rather
than quoted**: Demailly, *J. Algebraic Geom.* 1 (1992) is not in
`references/`, so no `\source` anchor is claimed for them.

## Why this is not a restatement of its consumer

It is one, on the part that is used.  The consumer, `Hironaka.ResidualNef`,
uses only the curvature clause, and with `D = 0` the nefness half of
`lem:residual-nef` *is* the curvature clause — `ResidualNef.
coefficientSemipositive_of_residualNef` proves that direction in Lean,
sorry-free.  So on the smoothing side the classical obligation is **renamed and
divisor-stripped, not reduced**; the reduction this round performs is on the
other two parts (the residual potential, and the removable-singularity split).
This interface must never be described as a *smaller* obligation than
`lem:residual-nef`.

The two approximation clauses are what makes the statement formally
non-derivable from its consumer, and they are exactly the part nothing uses
(`ResidualNef.lean`, `obtain ⟨h, hh, hpos, -, -⟩`).  They are recorded because
they are what the construction delivers and later consumers (a Kähler *form* in
the class, monotone approximation, mass convergence) will want them — not
because they carry weight here.

Everything that surrounds this input in `lem:residual-nef` — the passage from
`φ` to the residual potential, and the reduction of the Kähler half to the nef
half — is proved in `Hironaka.ResidualNefReduction` and `Hironaka.ResidualNef`.
Note that the Kähler half itself is *not* sorry-free: it goes through the nef
half, hence through this interface.
-/

open Set Filter
open scoped Topology

namespace Hironaka.BoundedPotentialSmoothing

open Hironaka.PositiveClasses

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **Demailly 1992, Theorem 1.1 for a bounded potential** — since run 0094
proved from `bou02-volume:2.6`
(`BoundedPotentialSmoothingOfAlgebraicApproximation.exists_chartSmooth_of_bounded_thetaPsh`).
A globally bounded `θ`-PSH function on a compact Kähler manifold is, up to `ε` in
value and `ε ω` in curvature, a chart-smooth function. -/
theorem demailly1992_exists_chartSmooth_of_bounded_thetaPsh
    [CompactSpace M] (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {u : M → EReal} (_hu : ThetaPlurisubharmonic theta.val u)
    {a b : ℝ} (_hlow : ∀ x, (a : EReal) ≤ u x) (_hupp : ∀ x, u x ≤ (b : EReal))
    {eps : ℝ} (_heps : 0 < eps) :
    ∃ h : M → ℝ, ChartSmooth (n := n) h ∧
      (∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
        CoefficientSemipositive
          (theta.val.coeff e z + smoothDDC (fun y => h (e.val.symm y)) z
            + eps • omega.form.val.coeff e z)) ∧
      (∀ x, u x ≤ ((h x + eps : ℝ) : EReal)) ∧
      (∀ x, h x ≤ b + eps) :=
  BoundedPotentialSmoothingOfAlgebraicApproximation.exists_chartSmooth_of_bounded_thetaPsh
    omega theta _hu _hlow _hupp _heps

end

end Hironaka.BoundedPotentialSmoothing
