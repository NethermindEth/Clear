import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.abi_encode_address

import Generated.erc20shim.ERC20Shim.abi_encode_tuple_address_gen


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.erc20shim ERC20Shim

def A_abi_encode_tuple_address (tail : Identifier) (headStart value0 : Literal) (s₀ s₉ : State) : Prop :=

  --Case of no collision
  s₉.isOk ∧
  (
  --Case of no collision
  let s := s₀⟦tail ↦ headStart + 32⟧
  (preservesEvm s₀ s₉ ∧
  (Ok (EVMState.mstore s₀.evm headStart (Fin.land value0 (Fin.shiftLeft 1 160 - 1))) s.store) = s₉ ∧
  s₉.evm.hash_collision = false)

  -- Case of collision
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

  have s0_ok : s₀.isOk := by aesop
  have sinhab_ok : s_inhabited.isOk := by aesop

  unfold A_abi_encode_address at call_encode_address
  clr_spec at call_encode_address

  obtain ⟨s_ok, s_no_collision, s_collision⟩
          := call_encode_address

  obtain ⟨s_evm, ⟨s_varstore, s_all⟩⟩ := State_of_isOk s_ok

  unfold reviveJump at code
  simp [s_all, ←s0_all] at code

  by_cases no_s_collision : s_inhabited.evm.hash_collision = false

  · have : s_inhabited.evm.hash_collision = false := by aesop
    simp [this] at s_no_collision
    obtain ⟨sinhab_s_preservesEvm,s_new, s_no_collision⟩ := s_no_collision
    all_goals aesop
  · aesop

end

end Generated.erc20shim.ERC20Shim
