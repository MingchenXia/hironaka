import Hironaka.MarkedIdeal.GermIdealOrder
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.GermIdealOrder
open Hironaka.HolomorphicIdealSheaves
open Hironaka.IdealWeightPowers
noncomputable section
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
variable {N : Set M} {x : M} {g : M → ℂ}
variable {𝔞 : GermIdeal n M}
variable (n) in
/-- **The order `ord_x(𝔞|_N) ∈ ℕ∞`**: the supremum of the `q` with `𝔞_x|_N ⊆ 𝔪_{N,x}^q`
(`⊤` when `𝔞|_N` vanishes near `x`, e.g. for the zero ideal). -/
def order (N : Set M) (𝔞 : GermIdeal n M) (x : M) : ℕ∞ :=
  ⨆ (q : ℕ) (_ : OrderGE n N 𝔞 x q), (q : ℕ∞)
end
end Hironaka.GermIdealOrder
open Lean Elab Command
partial def actualNames (e : Expr) : Array Name :=
  match e with
  | .lam n t b _ | .forallE n t b _ => #[n] ++ actualNames t ++ actualNames b
  | .letE n t v b _ => #[n] ++ actualNames t ++ actualNames v ++ actualNames b
  | .app f a => actualNames f ++ actualNames a
  | .mdata _ b | .proj _ _ b => actualNames b
  | _ => #[]
run_cmd do
  let env ← getEnv
  let some ci := env.find? `Hironaka.GermIdealOrder.order | throwError "absent"
  for n in actualNames ci.type ++ actualNames (ci.value? (allowOpaque := true)).get! do
    logInfo m!"ACTUAL_NAME {n}"

