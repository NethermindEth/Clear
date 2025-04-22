import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.abi_encode_tuple_address

import Generated.erc20shim.ERC20Shim.Common.if_4692225504622348326_gen

import Generated.erc20shim.ERC20Shim.Common.if_4692225504622348326_user


namespace ERC20Shim.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.erc20shim ERC20Shim

lemma if_4692225504622348326_abs_of_code {s₀ : State} {fuel : Nat} :
  ∀ s₉, exec fuel if_4692225504622348326 s₀ = s₉ →
        Spec A_if_4692225504622348326 s₀ s₉ :=
  λ _ h ↦ if_4692225504622348326_abs_of_concrete (if_4692225504622348326_concrete_of_code.2 h)

end

end ERC20Shim.Common
