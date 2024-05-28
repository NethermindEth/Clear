import Clear.ReasoningPrinciple



namespace Peano.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def if_6183625948864629624 := <s
  if eq(k, 0) 
{break}
>

set_option maxRecDepth 5000
set_option maxHeartbeats 400000

def if_6183625948864629624_concrete_of_code : {
    C : State → State → Prop
    // ∀ {s₀ s₉ fuel}
    , exec fuel if_6183625948864629624 s₀ = s₉
    → Spec C s₀ s₉
  } := by
  constructor
  intros s₀ s₉ fuel

  unfold Spec if_6183625948864629624
  rcases s₀ with ⟨evm₀, store₀⟩ | _ | c <;> dsimp only
  rotate_left 1
  · generalize If _ _ = f; aesop
  · generalize If _ _ = f; aesop
  swap
  generalize hok : Ok evm₀ store₀ = s₀
  intros h _
  revert h

  rw [If']

  -- AST-specific tactics

  simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]
  rw [EVMEq']
  rw [cons, Break']
  
  
  -- tacticsOfStmt offsetting
  try rw [nil]
  try simp [Bool.toUInt256, UInt256.size]
  intros h
  exact h


end

end Peano.Common
