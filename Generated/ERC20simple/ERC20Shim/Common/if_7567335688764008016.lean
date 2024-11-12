import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.abi_encode_tuple_address

import Generated.ERC20simple.ERC20Shim.Common.if_7567335688764008016_gen

import Generated.ERC20simple.ERC20Shim.Common.if_7567335688764008016_user


namespace ERC20Shim.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.ERC20simple ERC20Shim

lemma if_7567335688764008016_abs_of_code {s₀ : State} {fuel : Nat} :
  ∀ s₉, exec fuel if_7567335688764008016 s₀ = s₉ →
        Spec A_if_7567335688764008016 s₀ s₉ :=
  λ _ h ↦ if_7567335688764008016_abs_of_concrete (if_7567335688764008016_concrete_of_code.2 h)

end

end ERC20Shim.Common
