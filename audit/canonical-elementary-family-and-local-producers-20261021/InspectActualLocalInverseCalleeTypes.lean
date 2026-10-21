import Lean
import TranscendentalNakamaye.Pending.HolomorphicLocalInverse
import Hironaka.Analytic.HolomorphicLocalInverse
open Lean
namespace ActualLocalInverseTypeProbe
def node (tag : String) (xs : List Json := []) : Json :=
  toJson (Json.str tag :: xs)

def nameTree : Name → Json
  | .anonymous => node "anonymous"
  | .str p s => node "str" [nameTree p,toJson s]
  | .num p k => node "num" [nameTree p,toJson k]

def levelTree : Level → Json
  | .zero => node "zero"
  | .succ u => node "succ" [levelTree u]
  | .max u v => node "max" [levelTree u,levelTree v]
  | .imax u v => node "imax" [levelTree u,levelTree v]
  | .param n => node "param" [nameTree n]
  | .mvar v => node "mvar" [nameTree v.name]

def substringTree (s : Substring.Raw) : Json :=
  node "substring" [toJson s.str,toJson s.startPos.byteIdx,toJson s.stopPos.byteIdx]

def sourceInfoTree : SourceInfo → Json
  | .original l p t e => node "original" [substringTree l,toJson p.byteIdx,substringTree t,toJson e.byteIdx]
  | .synthetic p e c => node "synthetic" [toJson p.byteIdx,toJson e.byteIdx,toJson c]
  | .none => node "none"

def preresolvedTree : Syntax.Preresolved → Json
  | .namespace n => node "namespace" [nameTree n]
  | .decl n fs => node "declaration" [nameTree n,toJson fs]

partial def syntaxTree : Syntax → Json
  | .missing => node "missing"
  | .node i k xs => node "syntaxNode" [sourceInfoTree i,nameTree k,toJson (xs.toList.map syntaxTree)]
  | .atom i s => node "atom" [sourceInfoTree i,toJson s]
  | .ident i r n ps => node "identifier" [sourceInfoTree i,substringTree r,nameTree n,toJson (ps.map preresolvedTree)]

-- Entire metadata is encoded structurally, including syntax/source positions.
-- No pretty-print representation, hash, dropping or metadata normalization.
def dataTree : DataValue → Json
  | .ofString s => node "string" [toJson s]
  | .ofBool b => node "bool" [toJson b]
  | .ofName n => node "name" [nameTree n]
  | .ofNat k => node "nat" [toJson k]
  | .ofInt k => node "int" [toJson k]
  | .ofSyntax s => node "syntax" [syntaxTree s]

def binderInfoTree : BinderInfo → Json
  | .default => node "default"
  | .implicit => node "implicit"
  | .strictImplicit => node "strictImplicit"
  | .instImplicit => node "instanceImplicit"

structure DagState where
  cache : ExprStructMap Nat := {}
  nodes : Array Json := #[]

-- ExprStructMap's BEq is Expr.equal; it keeps binder names and annotations.
-- Ordinary ExprMap/Expr.eqv must never be used here.
partial def internExpr (e : Expr) : StateM DagState Nat := do
  if let some id := (← get).cache.get? ⟨e⟩ then return id
  let (tag,data,children) ← match e with
    | .bvar k => pure ("bvar",[toJson k],[])
    | .fvar f => pure ("fvar",[nameTree f.name],[])
    | .mvar m => pure ("mvar",[nameTree m.name],[])
    | .sort u => pure ("sort",[levelTree u],[])
    | .const c us => pure ("constant",[nameTree c,toJson (us.map levelTree)],[])
    | .app f a => do
      let fi ← internExpr f
      let ai ← internExpr a
      pure ("application",[],[fi,ai])
    | .lam n t b i => do
      let ti ← internExpr t
      let bi ← internExpr b
      pure ("lambda",[nameTree n,binderInfoTree i],[ti,bi])
    | .forallE n t b i => do
      let ti ← internExpr t
      let bi ← internExpr b
      pure ("forall",[nameTree n,binderInfoTree i],[ti,bi])
    | .letE n t v b nd => do
      let ti ← internExpr t
      let vi ← internExpr v
      let bi ← internExpr b
      pure ("let",[nameTree n,toJson nd],[ti,vi,bi])
    | .lit (.natVal k) => pure ("naturalLiteral",[toJson k],[])
    | .lit (.strVal s) => pure ("stringLiteral",[toJson s],[])
    | .mdata md b => do
      let bi ← internExpr b
      pure ("metadata",[toJson (md.entries.map fun (n,v) => node "entry" [nameTree n,dataTree v])],[bi])
    | .proj s i b => do
      let bi ← internExpr b
      pure ("projection",[nameTree s,toJson i],[bi])
  let st ← get
  let id := st.nodes.size
  let record := Json.mkObj [("tag",toJson tag),("data",toJson data),("children",toJson children)]
  set ({ cache := st.cache.insert ⟨e⟩ id, nodes := st.nodes.push record } : DagState)
  return id


run_cmd do
  let env ← getEnv
  let mut rows : Array Json := #[]
  for name in #[`TranscendentalNakamaye.Pending.HolomorphicLocalInverse.exists_localInverse,
      `Hironaka.HolomorphicLocalInverse.exists_localInverse] do
    let some ci := env.find? name | throwError "Missing actual callee {name}"
    let some idx := env.getModuleIdxFor? name | throwError "Missing actual owner {name}"
    let (root,st) := (internExpr ci.type).run {}
    let mut owners : Array String := #[]
    for j in [:env.header.moduleNames.size] do
      if (env.header.moduleData[j]!.constants.any fun c => c.name==name) then
        owners := owners.push env.header.moduleNames[j]!.toString
    rows := rows.push (Json.mkObj [
      ("actual_callee",toJson name.toString),
      ("actual_lookup_owner",toJson env.header.moduleNames[idx.toNat]!.toString),
      ("actual_moduleData_owners",toJson owners),
      ("levelParams",toJson (ci.levelParams.map nameTree)),
      ("typeRoot",toJson root),("fullTypeExprNodes",Json.arr st.nodes),
      ("whole_value_exported",toJson false),("name_or_number_normalization",toJson false)])
  IO.FS.writeFile "audit/canonical-elementary-family-and-local-producers-20261021/actual-local-inverse-callee-types.json"
    (Json.arr rows).pretty
  logInfo "ACTUAL_LOCAL_INVERSE_TYPE_OWNER_ROWS 2; raw complete types only"
end ActualLocalInverseTypeProbe
