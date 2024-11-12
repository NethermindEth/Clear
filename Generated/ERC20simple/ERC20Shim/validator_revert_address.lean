import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.Common.if_8073281237182003506

import Generated.ERC20simple.ERC20Shim.validator_revert_address_gen

import Generated.ERC20simple.ERC20Shim.validator_revert_address_user


namespace Generated.ERC20simple.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common 

lemma validator_revert_address_abs_of_code {s₀ s₉ : State} { value} {fuel : Nat} :
  execCall fuel validator_revert_address [] (s₀, [value]) = s₉ →
  Spec (A_validator_revert_address  value) s₀ s₉
:= λ h ↦ validator_revert_address_abs_of_concrete (validator_revert_address_concrete_of_code.2 h)

end

end Generated.ERC20simple.ERC20Shim
