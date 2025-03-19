import Clear.ReasoningPrinciple


import Generated.erc20shim.ERC20Shim.abi_encode_address_gen


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities

def A_abi_encode_address  (value pos : Literal) (s₀ s₉ : State) : Prop :=

  let address := Address.ofUInt256 value
  let position : UInt256 := pos
  preservesEvm s₀ s₉ ∧
  (s₀.evm.isEVMState → s₉.evm.isEVMState) ∧
  (s₀.evm.hash_collision = true → s₉.evm.hash_collision = true) ∧
  (
    ( Fin.land address (Fin.shiftLeft 1 160 - 1) = EVMState.mload s₉.evm position ∧
    s₉.evm.hash_collision = false)

    ∨ s₉.evm.hash_collision = true
  )

lemma abi_encode_address_abs_of_concrete {s₀ s₉ : State} { value pos} :
  Spec (abi_encode_address_concrete_of_code.1  value pos) s₀ s₉ →
  Spec (A_abi_encode_address  value pos) s₀ s₉ := by
  unfold abi_encode_address_concrete_of_code A_abi_encode_address
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
  rw[EVMShl'] at code
  unfold multifill at code
  unfold setEvm at code
  unfold lookup! at code
  simp at code
  rw [State.insert_of_ok] at code
  rw [State.insert_of_ok] at code
  rw [State.insert_of_ok] at code
  simp at code
  rw [State.insert_of_ok] at code
  simp at code
  generalize val_arg : (Fin.land value (Fin.shiftLeft 1 160 - 1)) = value_arg at *
  generalize lkup_arg : (Finmap.lookup "pos" _) = lookup_arg at *

  have s0_s9_preservesEvm : preservesEvm s₀ s₉ := by
    rw [←s0_all, ←code ]
    unfold preservesEvm
    have : Preserved evm₀ (mstore evm₀ lookup_arg.get! value_arg) := by
      apply mstore_preserved
    aesop

  split_ands

  · exact s0_s9_preservesEvm
  · aesop
  · aesop
  · aesop
  · by_cases s0_collision : evm₀.hash_collision
    · right
      aesop
    · left
      split_ands
      ·
        rw[←code]
        rw[←lkup_arg]
        have pos_get : lookup_arg.get! = pos := by
          aesop
        rw [←lkup_arg] at pos_get
        rw[pos_get]
        have value_get : EVMState.mload (Ok (mstore evm₀ pos value_arg) varstore₀).evm pos = value_arg := by
          unfold EVMState.mload
          apply lookup_mstore
        rw[value_get]

      · aesop

end

end Generated.erc20shim.ERC20Shim
