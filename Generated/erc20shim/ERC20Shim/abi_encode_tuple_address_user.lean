import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.abi_encode_address

import Generated.erc20shim.ERC20Shim.abi_encode_tuple_address_gen


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.erc20shim ERC20Shim

def A_abi_encode_tuple_address (tail : Identifier) (headStart value0 : Literal) (s₀ s₉ : State) : Prop :=

  preservesEvm s₀ s₉ ∧
  s₉.isOk ∧
  (s₀.evm.isEVMState → s₉.evm.isEVMState) ∧
  (s₀.evm.hash_collision = true → s₉.evm.hash_collision = true) ∧
  (
    (
       Fin.land value0 (Fin.shiftLeft 1 160 - 1) = EVMState.mload s₉.evm headStart ∧

      s₉.evm.hash_collision = false
      )
    ∨
    s₉.evm.hash_collision = true
  )

lemma abi_encode_tuple_address_abs_of_concrete {s₀ s₉ : State} {tail headStart value0} :
  Spec (abi_encode_tuple_address_concrete_of_code.1 tail headStart value0) s₀ s₉ →
  Spec (A_abi_encode_tuple_address tail headStart value0) s₀ s₉ := by
  unfold abi_encode_tuple_address_concrete_of_code A_abi_encode_tuple_address
  rcases s₀ with ⟨evm₀, varstore₀⟩ | _ | _ <;> [simp only; aesop_spec; aesop_spec]
  apply spec_eq
  clr_funargs
  rintro hasFuel ⟨s, call_encode_address, code⟩

  generalize s_inhabited_all :
  (Ok evm₀ Inhabited.default⟦"value0"↦value0⟧⟦"headStart"↦headStart⟧⟦"_1"↦32⟧⟦"tail"↦Ok evm₀
                    Inhabited.default⟦"value0"↦value0⟧⟦"headStart"↦headStart⟧⟦"_1"↦32⟧["headStart"]!! +
          (Ok evm₀ Inhabited.default⟦"value0"↦value0⟧⟦"headStart"↦headStart⟧⟦"_1"↦32⟧["_1"]!!)⟧) = s_inhabited at *

  generalize s0_all :
  (Ok evm₀ varstore₀) = s₀ at *

  unfold A_abi_encode_address at call_encode_address
  clr_spec at call_encode_address

  obtain ⟨s_preservesEvm, s_ok, sInhab_s_isEVM, sInhab_s_collision, ⟨pos_correct, s_no_collision⟩ | s_collision⟩
          := call_encode_address

  all_goals { obtain ⟨s_evm, ⟨s_varstore, s_all⟩⟩ := State_of_isOk s_ok; aesop }

end

end Generated.erc20shim.ERC20Shim
