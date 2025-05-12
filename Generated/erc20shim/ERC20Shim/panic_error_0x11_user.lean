import Clear.ReasoningPrinciple


import Generated.erc20shim.ERC20Shim.panic_error_0x11_gen


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities

def A_panic_error_0x11   (s₀ s₉ : State) : Prop :=
  s₉.isOk ∧
  (--Case 1: No initial collision
    s₀.evm.hash_collision = false →
   (
    (-- Case 1.1 No hash collision in function
    let s_evm := EVMState.mstore s₀.evm 0 (Fin.shiftLeft 1313373041 224)
    let s'_evm := EVMState.mstore s_evm 4 17

    preservesEvm s₀ s₉ ∧
    s'_evm.evm_revert 0 36  = s₉.evm ∧
    s₀.store = s₉.store ∧
    s₉.evm.hash_collision = false
    )
    -- Case 1.2 collision in function
    ∨ s₉.evm.hash_collision = true
   )
  )
  ∧
  (-- Case 2: existing initial collision
     s₀.evm.hash_collision = true →
    s₉.evm.hash_collision = true
  )

lemma panic_error_0x11_abs_of_concrete {s₀ s₉ : State}  :
  Spec (panic_error_0x11_concrete_of_code.1  ) s₀ s₉ →
  Spec (A_panic_error_0x11  ) s₀ s₉ := by
  unfold panic_error_0x11_concrete_of_code A_panic_error_0x11
  rcases s₀ with ⟨evm₀, varstore₀⟩ | _ | _ <;> [simp only; aesop_spec; aesop_spec]
  apply spec_eq
  clr_funargs
  simp
  rintro hasFuel code

  unfold multifill at code
  simp at code
  unfold setEvm at code
  simp at code
  unfold State.insert at code
  simp at code

  generalize s0_all :
  (Ok evm₀ varstore₀) = s₀ at *
  have s0_evm : s₀.evm = evm₀ := by aesop

  split_ands
  · aesop
  ·
    intro h
    left
    split_ands
    · rw[←code, ←s0_all]
      have : Preserved evm₀ (((mstore evm₀ 0 (Fin.shiftLeft 1313373041 224)).mstore 4 17).evm_revert 0 36) := by
        simp[Preserved_def]
        unfold mstore updateMemory evm_revert evm_return
        dsimp
        simp
      unfold preservesEvm
      aesop
    · aesop
    · aesop
    · rw[←code]
      simp[s0_evm.symm]
      unfold mstore updateMemory evm_revert evm_return
      dsimp
      aesop
  · aesop


end

end Generated.erc20shim.ERC20Shim
