import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.abi_encode_address
import Generated.erc20shim.ERC20Shim.abi_encode_uint256_to_uint256

import Generated.erc20shim.ERC20Shim.abi_encode_address_uint256_uint256_gen

namespace ERC20Shim.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.erc20shim ERC20Shim

set_option maxHeartbeats 2500000
set_option maxRecDepth 1000

theorem Generated.erc20shim.ERC20Shim.extracted_1 {s₉ : State} {tail : Identifier}
  {headStart value0 value1 value2 : Literal} (evm₀ : EVM) (varstore₀ : VarStore) (hasFuel : ¬❓ s₉)
  (s s' s'' s_inhab : State)
  (s_inhabited_all :
    Ok evm₀
                    Inhabited.default⟦"value2"↦value2⟧⟦"value1"↦value1⟧⟦"value0"↦value0⟧⟦"headStart"↦headStart⟧⟦"_1"↦96⟧⟦"tail"↦headStart +
          96⟧ =
      s_inhab)
  (s₀ : State) (s0_all : Ok evm₀ varstore₀ = s₀)
  (call_encode_address :
    s.isOk ∧
      (preservesEvm s_inhab s ∧
          Fin.land value0 (Fin.shiftLeft 1 160 - 1) = EVMState.mload s.evm headStart ∧
            Ok (mstore s_inhab.evm headStart (Fin.land value0 (Fin.shiftLeft 1 160 - 1))) s_inhab.store = s ∧
              s.evm.hash_collision = false ∨
        s.evm.hash_collision = true))
  (s_ok : s.isOk) (s_evm : EVM) (s_varstore : VarStore) (s_all : s = Ok s_evm s_varstore)
  (call_encode_uint :
    s'.isOk ∧
      (preservesEvm
            (Ok s_evm
              (Finmap.insert "_3" ((Finmap.lookup "headStart" (Finmap.insert "_2" 32 s_varstore)).get! + 32)
                (Finmap.insert "_2" 32 s_varstore)))
            s' ∧
          (Finmap.lookup "value1"
                  (Finmap.insert "_3" ((Finmap.lookup "headStart" (Finmap.insert "_2" 32 s_varstore)).get! + 32)
                    (Finmap.insert "_2" 32 s_varstore))).get! =
              EVMState.mload s'.evm ((Finmap.lookup "headStart" (Finmap.insert "_2" 32 s_varstore)).get! + 32) ∧
            Ok
                  (mstore
                    (Ok s_evm
                        (Finmap.insert "_3" ((Finmap.lookup "headStart" (Finmap.insert "_2" 32 s_varstore)).get! + 32)
                          (Finmap.insert "_2" 32 s_varstore))).evm
                    ((Finmap.lookup "headStart" (Finmap.insert "_2" 32 s_varstore)).get! + 32)
                    (Finmap.lookup "value1"
                        (Finmap.insert "_3" ((Finmap.lookup "headStart" (Finmap.insert "_2" 32 s_varstore)).get! + 32)
                          (Finmap.insert "_2" 32 s_varstore))).get!)
                  (Ok s_evm
                      (Finmap.insert "_3" ((Finmap.lookup "headStart" (Finmap.insert "_2" 32 s_varstore)).get! + 32)
                        (Finmap.insert "_2" 32 s_varstore))).store =
                s' ∧
              s'.evm.hash_collision = false ∨
        s'.evm.hash_collision = true))
  (s'_ok : s'.isOk) (s'_evm : EVM) (s'_varstore : VarStore) (s'_all : s' = Ok s'_evm s'_varstore)
  (call_encode_uint' :
    s''.isOk ∧
      (preservesEvm
            (Ok s'_evm
              (Finmap.insert "_5" ((Finmap.lookup "headStart" (Finmap.insert "_4" 64 s'_varstore)).get! + 64)
                (Finmap.insert "_4" 64 s'_varstore)))
            s'' ∧
          (Finmap.lookup "value2"
                  (Finmap.insert "_5" ((Finmap.lookup "headStart" (Finmap.insert "_4" 64 s'_varstore)).get! + 64)
                    (Finmap.insert "_4" 64 s'_varstore))).get! =
              EVMState.mload s''.evm ((Finmap.lookup "headStart" (Finmap.insert "_4" 64 s'_varstore)).get! + 64) ∧
            Ok
                  (mstore
                    (Ok s'_evm
                        (Finmap.insert "_5" ((Finmap.lookup "headStart" (Finmap.insert "_4" 64 s'_varstore)).get! + 64)
                          (Finmap.insert "_4" 64 s'_varstore))).evm
                    ((Finmap.lookup "headStart" (Finmap.insert "_4" 64 s'_varstore)).get! + 64)
                    (Finmap.lookup "value2"
                        (Finmap.insert "_5" ((Finmap.lookup "headStart" (Finmap.insert "_4" 64 s'_varstore)).get! + 64)
                          (Finmap.insert "_4" 64 s'_varstore))).get!)
                  (Ok s'_evm
                      (Finmap.insert "_5" ((Finmap.lookup "headStart" (Finmap.insert "_4" 64 s'_varstore)).get! + 64)
                        (Finmap.insert "_4" 64 s'_varstore))).store =
                s'' ∧
              s''.evm.hash_collision = false ∨
        s''.evm.hash_collision = true))
  (s''_ok : s''.isOk) (s''_evm : EVM) (s''_varstore : VarStore) (s''_all : s'' = Ok s''_evm s''_varstore)
  (code : Ok s''_evm (Finmap.insert tail (Finmap.lookup "tail" s''_varstore).get! varstore₀) = s₉) :
  s₉.isOk ∧
    (preservesEvm s₀ s₉ ∧
        Ok (mstore s₀.evm headStart (Fin.land value0 (Fin.shiftLeft 1 160 - 1))) s₀.store = s₉ ∧
          Fin.land value0 (Fin.shiftLeft 1 160 - 1) = EVMState.mload s₉.evm headStart ∧
            value1 = EVMState.mload s₉.evm headStart + 32 ∧
              value2 = EVMState.mload s₉.evm headStart + 64 ∧ s₉.evm.hash_collision = false ∨
      s₉.evm.hash_collision = true) := by

      obtain ⟨s_ok, ⟨sInhab_s_preservesEvm, s_pos_correct, s_new, s_no_collision⟩| s_collision⟩
          := call_encode_address

      rw[s_all] at s_new
      · -- No collision at s
        obtain ⟨s'_ok, ⟨s_s'_preservesEvm, s'_pos_correct, s'_new, s'_no_collision⟩| s'_collision⟩
              := call_encode_uint


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
        have s'_evm_eq : s'_evm_ = s'_evm := by aesop
        have s'_varstore_eq : s'_varstore_ = s'_varstore := by
          rw [s'_all] at s'_new
          aesop
        #exit
        · -- No collision at s'
          obtain ⟨s''_ok, ⟨s'_s''_preservesEvm, s''_pos_correct, s''_new, s''_no_collision⟩| s''_collision⟩
              := call_encode_uint'

          rw[s''_all] at s''_new
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


          · -- No collision at s''
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
                sorry
              · rw[←code]
                simp
                sorry
              · rw[←code]
                simp

                sorry















end

end ERC20Shim.Common
