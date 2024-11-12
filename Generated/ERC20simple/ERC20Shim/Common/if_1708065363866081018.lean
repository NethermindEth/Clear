import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.abi_encode_uint256

import Generated.ERC20simple.ERC20Shim.Common.if_1708065363866081018_gen

import Generated.ERC20simple.ERC20Shim.Common.if_1708065363866081018_user


namespace ERC20Shim.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.ERC20simple ERC20Shim

lemma if_1708065363866081018_abs_of_code {s₀ : State} {fuel : Nat} :
  ∀ s₉, exec fuel if_1708065363866081018 s₀ = s₉ →
        Spec A_if_1708065363866081018 s₀ s₉ :=
  λ _ h ↦ if_1708065363866081018_abs_of_concrete (if_1708065363866081018_concrete_of_code.2 h)

end

end ERC20Shim.Common
