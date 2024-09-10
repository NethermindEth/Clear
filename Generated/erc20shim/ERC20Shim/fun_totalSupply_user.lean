import Clear.ReasoningPrinciple


import Generated.erc20shim.ERC20Shim.fun_totalSupply_gen
import Generated.erc20shim.ERC20Shim.Variables

namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_fun_totalSupply (var_ : Identifier)  (s₀ s₉ : State) : Prop :=
  s₉ = s₀⟦var_ ↦ s₀.evm.sload ERC20Private.totalSupply ⟧

lemma fun_totalSupply_abs_of_concrete {s₀ s₉ : State} {var_ } :
  Spec (fun_totalSupply_concrete_of_code.1 var_ ) s₀ s₉ →
  Spec (A_fun_totalSupply var_ ) s₀ s₉ := by
  unfold fun_totalSupply_concrete_of_code A_fun_totalSupply
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [simp only; aesop_spec; aesop_spec]
  apply spec_eq  
  clr_funargs
  intro hasFuel

  unfold reviveJump
  simp

  rw [ ← State.insert_of_ok,  ← State.insert_of_ok,  ← State.insert_of_ok ]  
  clr_varstore
  intro h
  unfold ERC20Private; dsimp only
  symm
  assumption

end

end Generated.erc20shim.ERC20Shim
