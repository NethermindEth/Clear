import Clear.ReasoningPrinciple


import Generated.erc20shim.ERC20Shim.fun_msgSender_gen


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities

def A_fun_msgSender (var : Identifier)  (s₀ s₉ : State) : Prop :=
  preservesEvm s₀ s₉ ∧
  s₉.isOk ∧
  (s₀.evm.isEVMState → s₉.evm.isEVMState) ∧
  -- Case: Existing Hash collision in s₀
  (s₀.evm.hash_collision = true → s₉.evm.hash_collision) ∧
  (
  -- Case: No hash collision
    (
      match s₀ with
      | Ok evm _ => let s : State := s₀⟦var ↦ evm.execution_env.source⟧
                    s₉.store = s.store  ∧
                    s₉.evm.hash_collision = false
      | _ => s₉.evm.hash_collision = false -- OutOfFuel or Checkpoint
    )
  -- Case: Hash collision during msgSender
    ∨ s₉.evm.hash_collision = true
  )

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
  simp

  split_ands
  · unfold preservesEvm
    rw [← State.insert_of_ok, lookup_insert, State.insert_of_ok]
    simp
  · by_cases h : evm₀.hash_collision <;> [(right;assumption);skip]
    left
    split_ands <;> [skip;aesop]
    unfold lookup!
    simp
    unfold State.insert
    dsimp

end

end Generated.erc20shim.ERC20Shim
