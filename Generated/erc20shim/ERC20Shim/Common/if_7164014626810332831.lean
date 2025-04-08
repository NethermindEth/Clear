import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b

import Generated.erc20shim.ERC20Shim.Common.if_7164014626810332831_gen

import Generated.erc20shim.ERC20Shim.Common.if_7164014626810332831_user


namespace ERC20Shim.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.erc20shim ERC20Shim

lemma if_7164014626810332831_abs_of_code {s₀ : State} {fuel : Nat} :
  ∀ s₉, exec fuel if_7164014626810332831 s₀ = s₉ →
        Spec A_if_7164014626810332831 s₀ s₉ :=
  λ _ h ↦ if_7164014626810332831_abs_of_concrete (if_7164014626810332831_concrete_of_code.2 h)

end

end ERC20Shim.Common
