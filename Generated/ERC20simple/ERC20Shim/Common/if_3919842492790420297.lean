import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.abi_encode_tuple_address

import Generated.ERC20simple.ERC20Shim.Common.if_3919842492790420297_gen

import Generated.ERC20simple.ERC20Shim.Common.if_3919842492790420297_user


namespace ERC20Shim.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.ERC20simple ERC20Shim

lemma if_3919842492790420297_abs_of_code {s₀ : State} {fuel : Nat} :
  ∀ s₉, exec fuel if_3919842492790420297 s₀ = s₉ →
        Spec A_if_3919842492790420297 s₀ s₉ :=
  λ _ h ↦ if_3919842492790420297_abs_of_concrete (if_3919842492790420297_concrete_of_code.2 h)

end

end ERC20Shim.Common
