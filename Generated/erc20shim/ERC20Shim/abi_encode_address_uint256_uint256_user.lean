import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.abi_encode_address
import Generated.erc20shim.ERC20Shim.abi_encode_uint256_to_uint256

import Generated.erc20shim.ERC20Shim.abi_encode_address_uint256_uint256_gen


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.erc20shim ERC20Shim

def A_abi_encode_address_uint256_uint256 (tail : Identifier) (headStart value0 value1 value2 : Literal) (s₀ s₉ : State) : Prop :=
  s₉.isOk ∧
  (
    (-- Case of no collision
    let s := s₀⟦tail ↦ headStart + 96⟧
    preservesEvm s₀ s₉ ∧
        -- Second encode int
    (Ok (EVMState.mstore
          -- First encode int
          (EVMState.mstore
             -- Encode address
            (EVMState.mstore s₀.evm headStart (Fin.land value0 (Fin.shiftLeft 1 160 - 1)))
            (headStart+32)
            value1)
          (headStart+64)
          value2)
    s.store) = s₉ ∧
    s₉.evm.hash_collision = false
    )
    -- Collision
    ∨ s₉.evm.hash_collision = true
  )

set_option maxHeartbeats 2500000
set_option maxRecDepth 1000

@[simp]
lemma abc {evm' : EVMState} {varstore' : VarStore} :
  (Ok evm' varstore').store = varstore' :=
  by simp [State.store]

@[simp]
lemma cba {evm' : EVMState} {varstore' : VarStore} :
  (Ok evm' varstore').evm = evm' :=
  by simp


lemma abi_encode_address_uint256_uint256_abs_of_concrete {s₀ s₉ : State} {tail headStart value0 value1 value2} :
  Spec (abi_encode_address_uint256_uint256_concrete_of_code.1 tail headStart value0 value1 value2) s₀ s₉ →
  Spec (A_abi_encode_address_uint256_uint256 tail headStart value0 value1 value2) s₀ s₉ := by
  unfold abi_encode_address_uint256_uint256_concrete_of_code A_abi_encode_address_uint256_uint256
  rcases s₀ with ⟨evm₀, varstore₀⟩ | _ | _ <;> [simp only; aesop_spec; aesop_spec]
  apply spec_eq
  clr_funargs
  rintro hasFuel ⟨s, call_encode_address, ⟨s', call_encode_uint, ⟨s'', call_encode_uint', code⟩⟩⟩
  clr_varstore,
  generalize s_inhabited_all :
  (Ok evm₀
    Inhabited.default⟦"value2"↦value2⟧⟦"value1"↦value1⟧⟦"value0"↦value0⟧⟦"headStart"↦headStart⟧⟦"_1"↦96⟧⟦"tail"↦headStart + 96⟧)
    = s_inhab at *

  generalize s0_all :
  (Ok evm₀ varstore₀) = s₀ at *

  generalize s_new_evm : (mstore s_inhab.evm headStart (Fin.land value0 (Fin.shiftLeft 1 160 - 1)))
                        = s_evm_ at *
  generalize s_new_varstore : s_inhab.store = s_varstore_ at *

  have sinhab_s0 : s_inhab.evm = s₀.evm := by aesop

  unfold A_abi_encode_address at call_encode_address
  apply Spec_ok_unfold (by sorry) (by sorry) at call_encode_address

  unfold A_abi_encode_uint256_to_uint256 at call_encode_uint
  have s_ok : s.isOk := by aesop
  obtain ⟨s_evm, ⟨s_varstore, s_all⟩⟩ := State_of_isOk s_ok
  unfold lookup! at call_encode_uint
  simp [s_all] at call_encode_uint
  apply Spec_ok_unfold (by sorry) (by sorry) at call_encode_uint

  unfold A_abi_encode_uint256_to_uint256 at call_encode_uint'
  have s'_ok : s'.isOk := by aesop
  obtain ⟨s'_evm, ⟨s'_varstore, s'_all⟩⟩ := State_of_isOk s'_ok
  unfold lookup! at call_encode_uint'
  simp [s'_all] at call_encode_uint'
  apply Spec_ok_unfold (by sorry) (by sorry) at call_encode_uint'

  unfold reviveJump at code
  have s''_ok : s''.isOk := by aesop
  obtain ⟨s''_evm, ⟨s''_varstore, s''_all⟩⟩ := State_of_isOk s''_ok
  unfold lookup! at code
  simp [s''_all, ←s0_all] at code

  generalize s'_new_evm :  (mstore
                            (Ok s_evm
                                (Finmap.insert "_3" ((Finmap.lookup "headStart" (Finmap.insert "_2" 32 s_varstore)).get! + 32)
                                  (Finmap.insert "_2" 32 s_varstore))).evm
                            ((Finmap.lookup "headStart" (Finmap.insert "_2" 32 s_varstore)).get! + 32)
                            (Finmap.lookup "value1"
                                (Finmap.insert "_3" ((Finmap.lookup "headStart" (Finmap.insert "_2" 32 s_varstore)).get! + 32)
                                  (Finmap.insert "_2" 32 s_varstore))).get!) = s'_evm_ at *
  generalize s'_new_varstore : (Ok s_evm
                                (Finmap.insert "_3" ((Finmap.lookup "headStart" (Finmap.insert "_2" 32 s_varstore)).get! + 32)
                                  (Finmap.insert "_2" 32 s_varstore))).store = s'_varstore_ at *

  generalize s''_new_evm : (mstore
                                (Ok s'_evm
                                    (Finmap.insert "_5" ((Finmap.lookup "headStart" (Finmap.insert "_4" 64 s'_varstore)).get! + 64)
                                      (Finmap.insert "_4" 64 s'_varstore))).evm
                                ((Finmap.lookup "headStart" (Finmap.insert "_4" 64 s'_varstore)).get! + 64)
                                (Finmap.lookup "value2"
                                    (Finmap.insert "_5" ((Finmap.lookup "headStart" (Finmap.insert "_4" 64 s'_varstore)).get! + 64)
                                      (Finmap.insert "_4" 64 s'_varstore))).get!) = s''_evm_ at *
  generalize s''_new_varstore : (Ok s'_evm
                                (Finmap.insert "_5" ((Finmap.lookup "headStart" (Finmap.insert "_4" 64 s'_varstore)).get! + 64)
                                  (Finmap.insert "_4" 64 s'_varstore))).store = s''_varstore_ at *

  obtain ⟨s_ok, ⟨sinhab_no_collision, sinhab_collision⟩⟩
          := call_encode_address

  by_cases no_sinhab_collision : s_inhab.evm.hash_collision = false

  · simp [no_sinhab_collision] at sinhab_no_collision
    obtain ⟨sinhab_s_preservesEvm, s_new, s_no_collision⟩ := sinhab_no_collision

    obtain ⟨s'_ok, ⟨s_no_collision, s_collision⟩⟩
          := call_encode_uint

    · by_cases no_s_collision : s.evm.hash_collision = false

      · have : s_evm.hash_collision = false := by aesop
        simp [this] at s_no_collision
        obtain ⟨s_s'_preservesEvm, s'_new, s'_no_collision⟩ := s_no_collision

        obtain ⟨s''_ok, ⟨s'_no_collision, s'_collision⟩⟩
          := call_encode_uint'

        · by_cases no_s'_collision : s'.evm.hash_collision = false

          · have : s'_evm.hash_collision = false := by aesop
            simp [this] at s'_no_collision
            obtain ⟨s'_s''_preservesEvm, s''_new, s''_no_collision⟩ := s'_no_collision
            ·
              split_ands
              · rw[←code]
                simp
              · left
                split_ands
                · rw[←code]
                  apply preservesEvm_trans s'_ok
                  · apply preservesEvm_trans s_ok
                    · aesop
                    · aesop
                  · aesop
                · rw[←code]
                  simp
                  split_ands
                  · aesop
                  · aesop
                · aesop
            · aesop
          · aesop
        · aesop
      · aesop
    · aesop
  · aesop

end

end Generated.erc20shim.ERC20Shim
