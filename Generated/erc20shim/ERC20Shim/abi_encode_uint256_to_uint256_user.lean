import Clear.ReasoningPrinciple


import Generated.erc20shim.ERC20Shim.abi_encode_uint256_to_uint256_gen


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities

def A_abi_encode_uint256_to_uint256  (value pos : Literal) (s₀ s₉ : State) : Prop :=
  s₉.isOk ∧
  (--Case 1: No initial collision
    s₀.evm.hash_collision = false →
   (
    (-- Case 1.1 No hash collision in function
    preservesEvm s₀ s₉ ∧
    (Ok (EVMState.mstore s₀.evm pos value) s₀.store) = s₉ ∧
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

lemma abi_encode_uint256_to_uint256_abs_of_concrete {s₀ s₉ : State} { value pos} :
  Spec (abi_encode_uint256_to_uint256_concrete_of_code.1  value pos) s₀ s₉ →
  Spec (A_abi_encode_uint256_to_uint256  value pos) s₀ s₉ := by
  unfold abi_encode_uint256_to_uint256_concrete_of_code A_abi_encode_uint256_to_uint256
  rcases s₀ with ⟨evm₀, varstore₀⟩ | _ | _ <;> [simp only; aesop_spec; aesop_spec]
  apply spec_eq
  clr_funargs
  rintro hasFuel code
  generalize s_inhabited_all :
  (Ok evm₀ Inhabited.default⟦"pos"↦pos⟧⟦"value"↦value⟧) = s_inhabited at *

  generalize s0_all :
  (Ok evm₀ varstore₀) = s₀ at *

  unfold reviveJump at code
  rw[←s_inhabited_all, ←s0_all] at code
  unfold setEvm at code
  unfold State.insert at code
  simp at code

  extract_goal
  have s0_s9_preservesEvm : preservesEvm s₀ s₉ := by
    rw [←s0_all, ←code]
    unfold preservesEvm
    have : Preserved evm₀ (mstore evm₀ pos value) := by
      apply mstore_preserved
    aesop

  split_ands

  · aesop
  · by_cases s0_collision : evm₀.hash_collision
    · intro s0_no_collision
      right
      aesop
    · intro s0_no_collision
      left
      split_ands
      · exact s0_s9_preservesEvm
      · aesop
      · aesop
  · aesop

end

end Generated.erc20shim.ERC20Shim
