import Clear.ReasoningPrinciple


import Generated.erc20shim.ERC20Shim.fun_msgSender_gen


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_fun_msgSender (var : Identifier)  (s₀ s₉ : State) : Prop := 
  ((preservesEvm s₀ s₉ ∧
  s₉.isOk ∧
  (s₀.evm.isEVMState → s₉.evm.isEVMState) ∧
  s₉[var]!! = s₀.evm.execution_env.source ∧
  s₉.evm.hash_collision = false)
  ∨ s₉.evm.hash_collision = true)
  ∧ (s₀.evm.hash_collision = true → s₉.evm.hash_collision) 

lemma fun_msgSender_abs_of_concrete {s₀ s₉ : State} {var } :
  Spec (fun_msgSender_concrete_of_code.1 var ) s₀ s₉ →
  Spec (A_fun_msgSender var ) s₀ s₉ := by
  unfold fun_msgSender_concrete_of_code A_fun_msgSender
  rcases s₀ with ⟨evm₀, varstore₀⟩ | _ | _ <;> [simp only; aesop_spec; aesop_spec]
  apply spec_eq
  clr_funargs
  rintro hasFuel code
  simp at code
  rw [←code]
  unfold preservesEvm
  rw [← State.insert_of_ok, lookup_insert, State.insert_of_ok]
  unfold lookup!
  simp

end

end Generated.erc20shim.ERC20Shim
