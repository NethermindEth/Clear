import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.mapping_index_access_mapping_address_uint256_of_address
import Generated.erc20shim.ERC20Shim.Common.if_3989404597755436942
import Generated.erc20shim.ERC20Shim.abi_encode_address_uint256_uint256
import Generated.erc20shim.ERC20Shim.update_storage_value_offsett_uint256_to_uint256
import Generated.erc20shim.ERC20Shim.checked_add_uint256

import Generated.erc20shim.ERC20Shim.Common.switch_2364266820542243941_gen


namespace ERC20Shim.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common Generated.erc20shim ERC20Shim

def A_switch_2364266820542243941 (s₀ s₉ : State) : Prop :=
  s₉.isOk ∧

  (--Case 1: No initial collision
    s₀.evm.hash_collision = false →
  (
    ( -- Case 1.1 : _3 = 0
      (-- Case 1.1.1: _7 = 1 (Reversion)
        (∃ slot value,
        let s:= (Ok (sstore s₀.evm slot value) s₀.store)
        preservesEvm s s₉) ∧
        s₉.evm.hash_collision = false
      )
      ∨
      (-- Case 1.1.2 _7 =/ 0 (Non Reversion)
        preservesEvm s₀ s₉ ∧
        s₉.evm.hash_collision = false
      )
    )
    ∨
    ( -- Case 1.2 : Default
      preservesEvm s₀ s₉ ∧
      s₉.evm.hash_collision = false
    )
    ∨
      -- Case 1.3 : Collision in function
      s₉.evm.hash_collision = true
  )
  )
  ∧
  (-- Case 2: existing initial collision
     s₀.evm.hash_collision = true →
    s₉.evm.hash_collision = true
  )

set_option maxHeartbeats 2000000
set_option maxRecDepth 1000


lemma lookupAcc_preserves_eq {evm evm' : EVMState} {varstore varstore' : VarStore} :
  preservesEvm (Ok evm varstore) (Ok evm' varstore') →
  evm.lookupAccount evm.execution_env.code_owner = evm'.lookupAccount evm'.execution_env.code_owner := by
  unfold lookupAccount
  intro preserves
  unfold preservesEvm at preserves
  simp [Preserved_def] at preserves
  have h1 : evm.execution_env.code_owner = evm'.execution_env.code_owner := by
    simp [preserves.2.2.1]
  have h2 : evm.account_map = evm'.account_map := by
    simp [preserves]
  rw[h1,h2]

lemma updateAcc_preserved_eq {evm evm' : EVMState} {varstore varstore' : VarStore} {slot value : UInt256} {act : Account}:
  preservesEvm (Ok evm varstore) (Ok evm' varstore') ∧
   evm.lookupAccount evm.execution_env.code_owner = act
  →
  Preserved (evm.updateAccount evm.execution_env.code_owner (act.updateStorage slot value))
            (evm'.updateAccount evm'.execution_env.code_owner (act.updateStorage slot value)) := by
  intro h
  obtain ⟨preserves, lookup⟩ := h

  have : evm.lookupAccount evm.execution_env.code_owner = evm'.lookupAccount evm'.execution_env.code_owner := by
    apply lookupAcc_preserves_eq preserves
  have : evm'.lookupAccount evm'.execution_env.code_owner = act := by
    rw[←this]
    exact lookup

  unfold preservesEvm at preserves
  simp [Preserved_def] at preserves
  have h1 : evm.execution_env.code_owner = evm'.execution_env.code_owner := by
    simp [preserves.2.2.1]
  rw[h1]
  simp[Preserved_def]
  unfold updateAccount
  simp
  obtain ⟨account, hash, exec, keccak⟩ := preserves
  aesop

lemma sstore_preserved_eq {evm evm' : EVMState} {varstore varstore' : VarStore} {slot value : UInt256} :
  preservesEvm (Ok evm varstore) (Ok evm' varstore') →
  preservesEvm (Ok (sstore evm slot value) varstore)
                (Ok (sstore evm' slot value) varstore') := by
  intro preserves
  unfold preservesEvm
  simp [Preserved_def]
  have : evm.lookupAccount evm.execution_env.code_owner =
          evm'.lookupAccount evm'.execution_env.code_owner := by
          apply lookupAcc_preserves_eq preserves
  have preserves_ : preservesEvm (Ok evm varstore) (Ok evm' varstore') :=
    by exact preserves
  unfold preservesEvm at preserves
  simp [Preserved_def] at preserves
  obtain ⟨account, hash, exec, keccak⟩ := preserves
  unfold sstore
  simp[this]

  cases  h: evm'.lookupAccount evm'.execution_env.code_owner with
  | none =>
    simp [account, hash, exec, keccak]
  | some act =>
    simp[h]
    have : Preserved (evm.updateAccount evm.execution_env.code_owner (act.updateStorage slot value))
              (evm'.updateAccount evm'.execution_env.code_owner (act.updateStorage slot value)) := by
              apply updateAcc_preserved_eq
              rw[←this] at h
              exact ⟨preserves_, h⟩
    simp[Preserved_def] at this
    exact this

lemma switch_2364266820542243941_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_2364266820542243941_concrete_of_code s₀ s₉ →
  Spec A_switch_2364266820542243941 s₀ s₉ := by

  unfold switch_2364266820542243941_concrete_of_code A_switch_2364266820542243941

  rcases s₀ with ⟨evm₀, varstore₀⟩ | _ | _ <;> [simp only; aesop_spec; aesop_spec]

  apply spec_eq

  rintro hasFuel ⟨s1, mapping1,
                  ⟨s2, if308,
                    ⟨s3, mapping2,
                      ⟨s4, update1,
                        ⟨s5, add,
                          ⟨s6, update2, code⟩⟩⟩⟩⟩⟩

  generalize s0_all :
  (Ok evm₀ varstore₀) = s₀ at *
  have s0_ok : s₀.isOk := by aesop

  by_cases _3 : s₀["_3"]!! = 0

  · -- _3 case
    simp[_3] at code

    clear update2 add

    clr_varstore mapping1,
    clr_varstore mapping2,

    unfold A_mapping_index_access_mapping_address_uint256_of_address at mapping1
    unfold A_mapping_index_access_mapping_address_uint256_of_address at mapping2
    unfold A_if_3989404597755436942 at if308
    unfold A_update_storage_value_offsett_uint256_to_uint256 at update1

    rw[←code] at hasFuel
    have s3_hasFuel: ¬❓ s3 := by
      apply not_isOutOfFuel_Spec update1 hasFuel
    have s2insert_hasFuel : ¬❓ (s2⟦"expr_4"↦s2["_6"]!! - (s2["var_value"]!!)⟧⟦"_15"↦s2["_4"]!!⟧) := by
      apply not_isOutOfFuel_Spec mapping2 s3_hasFuel
    have s2_hasFuel : ¬❓ s2 := by aesop

    have s1insert_hasFuel : ¬❓ (s1⟦"_6"↦sload s1.evm
                  (s1["_5"]!!)⟧⟦"var_fromBalance"↦s1⟦"_6"↦sload s1.evm
                    (s1["_5"]!!)⟧["_6"]!!⟧⟦"_7"↦(decide
                (s1⟦"_6"↦sload s1.evm (s1["_5"]!!)⟧⟦"var_fromBalance"↦s1⟦"_6"↦sload s1.evm (s1["_5"]!!)⟧["_6"]!!⟧["_6"]!! <
                  s1⟦"_6"↦sload s1.evm
                          (s1["_5"]!!)⟧⟦"var_fromBalance"↦s1⟦"_6"↦sload s1.evm
                            (s1["_5"]!!)⟧["_6"]!!⟧["var_value"]!!)).toUInt256⟧) := by
      apply not_isOutOfFuel_Spec if308 s2_hasFuel
    have s1_hasFuel : ¬❓ s1 := by aesop

    -- These all work, sorrys for speed
    apply Spec_ok_unfold (by sorry) (by sorry) at mapping1
    apply Spec_ok_unfold (by sorry) (by sorry) at if308
    apply Spec_ok_unfold (by sorry) (by sorry) at mapping2
    apply Spec_ok_unfold (by sorry) (by sorry) at update1

    clr_varstore if308,
    obtain ⟨s1_ok, ⟨s0s1_preserves, s0s1_state, s1_keccak, s1_no_collision⟩ | s1_collision, s0s1_collision⟩ := mapping1
    · -- NO collision in mapping1
        obtain ⟨s1_evm, ⟨s1_varstore, s1_all⟩⟩ := State_of_isOk s1_ok
        by_cases _7 : (decide (sload s1.evm (s1["_5"]!!) < s1["var_value"]!!)).toUInt256 = 1

        · -- _7 = 1 (Reversion)
          simp[s1_no_collision, _7] at if308
          obtain ⟨s2_ok, ⟨s1s2_preserves, s2_reverted⟩| s2_collision⟩ := if308

          · -- no Collision in if308
            obtain ⟨s2_evm, ⟨s2_varstore, s2_all⟩⟩ := State_of_isOk s2_ok
            obtain ⟨s3_ok, ⟨s2s3_preserves, s2s3_state, s3_keccak, s3_no_collision⟩ | s3_collision, s2s3_colliion⟩ := mapping2

            · -- No collision in mapping2
              obtain ⟨s3_evm, ⟨s3_varstore, s3_all⟩⟩ := State_of_isOk s3_ok
              have s3__ok : (Ok (sstore s3.evm (s3["_16"]!!) (s3["expr_4"]!!)) s3.store).isOk := by aesop
              simp[s3_no_collision, _7] at update1
              obtain ⟨s4_ok, s3s4_preserves | s4_collision⟩ := update1

              · -- No collision in update1
                obtain ⟨s4_evm, ⟨s4_varstore, s4_all⟩⟩ := State_of_isOk s4_ok
                rw[←code]
                split_ands
                · aesop
                · intro s0_no_collison

                  by_cases s9_no_collision : s₉.evm.hash_collision = false

                  · -- No collision in function
                    left
                    left
                    split_ands
                    · have s0s3_preserves : preservesEvm s₀ s3 := by
                        apply preservesEvm_trans s1_ok
                        · aesop
                        · apply preservesEvm_trans s2_ok
                          · aesop
                          · aesop
                      have : preservesEvm (Ok (sstore s₀.evm (s3["_16"]!!) (s3["expr_4"]!!)) s₀.store)
                                          (Ok (sstore s3.evm (s3["_16"]!!) (s3["expr_4"]!!)) s3.store) := by
                                          apply sstore_preserved_eq
                                          aesop

                      have : preservesEvm (Ok (sstore s₀.evm (s3["_16"]!!) (s3["expr_4"]!!)) s₀.store) s4 := by
                        apply preservesEvm_trans s3__ok
                        · aesop
                        · aesop
                      aesop
                    · aesop

                  · -- Collision in function
                    aesop

                · aesop

              · -- Collision in update 1
                aesop

            · -- Collision in mapping 2
              aesop

          · -- collision in if308
            aesop

        · -- _7 = 0 (No reversion)
          have : (decide (sload s1.evm (s1["_5"]!!) < s1["var_value"]!!)).toUInt256 = 0 := by
            unfold Bool.toUInt256
            unfold Bool.toUInt256 at _7
            aesop

          simp[s1_no_collision, this] at if308
          obtain ⟨s2_ok, s1s2_preserves| s2_collision⟩ := if308

          · -- no Collision in if308
            obtain ⟨s2_evm, ⟨s2_varstore, s2_all⟩⟩ := State_of_isOk s2_ok
            obtain ⟨s3_ok, ⟨s2s3_preserves, s2s3_state, s3_keccak, s3_no_collision⟩ | s3_collision, s2s3_colliion⟩ := mapping2

            · -- No collision in mapping2
              obtain ⟨s3_evm, ⟨s3_varstore, s3_all⟩⟩ := State_of_isOk s3_ok
              have s3__ok : (Ok (sstore s3.evm (s3["_16"]!!) (s3["expr_4"]!!)) s3.store).isOk := by aesop
              simp[s3_no_collision, _7] at update1
              obtain ⟨s4_ok, s3s4_preserves | s4_collision⟩ := update1

              · -- No collision in update1
                obtain ⟨s4_evm, ⟨s4_varstore, s4_all⟩⟩ := State_of_isOk s4_ok
                rw[←code]
                split_ands
                · aesop
                · intro s0_no_collison

                  by_cases s9_no_collision : s₉.evm.hash_collision = false

                  · -- No collision in function
                    left
                    left
                    split_ands
                    · have s0s3_preserves : preservesEvm s₀ s3 := by
                        apply preservesEvm_trans s1_ok
                        · aesop
                        · apply preservesEvm_trans s2_ok
                          · aesop
                          · aesop
                      have : preservesEvm (Ok (sstore s₀.evm (s3["_16"]!!) (s3["expr_4"]!!)) s₀.store)
                                          (Ok (sstore s3.evm (s3["_16"]!!) (s3["expr_4"]!!)) s3.store) := by
                                          apply sstore_preserved_eq
                                          aesop
                      have : preservesEvm (Ok (sstore s₀.evm (s3["_16"]!!) (s3["expr_4"]!!)) s₀.store) s4 := by
                        apply preservesEvm_trans s3__ok
                        · aesop
                        · aesop
                      aesop
                    · aesop

                  · -- Collision in function
                    aesop

                · aesop

              · -- Collision in update 1
                aesop

            · -- Collision in mapping 2
              aesop

          · -- collision in if308
            aesop
    · aesop

  · -- No _3 case
    clear update1 if308 mapping1 mapping2

    have : 0 ≠ s₀["_3"]!! := by aesop
    simp[this] at code
    clear this

    unfold A_checked_add_uint256 at add
    unfold A_update_storage_value_offsett_uint256_to_uint256 at update2
    clr_varstore,

    clr_spec at add
    clr_spec at update2

    by_cases s0_no_collision : s₀.evm.hash_collision = false

    · simp[s0_no_collision] at add
      obtain ⟨s5_ok,
        (⟨s0s5_preserves, s5_reverted, s5_load, s5_no_collision⟩ |
         ⟨s0s5_preserves, s5_load, s5_no_collision⟩ |
         s5_collision)⟩ := add
      · -- reversion in add
        obtain ⟨s5_evm, ⟨s5_varstore, s5_all⟩⟩ := State_of_isOk s5_ok

        simp[s5_no_collision] at update2
        obtain ⟨s6_ok, s5s6_preserves | s6_collision⟩ := update2

        · -- no collision at update2
          simp[s0_no_collision]
          split_ands
          · aesop
          · by_cases s9_no_collision : s₉.evm.hash_collision = false
            · left
              left
              split_ands
              · rw[←code]
                have : preservesEvm s₀ s5 := by aesop
                have : preservesEvm (Ok (sstore s₀.evm (s5["_17"]!!) (s5["_20"]!!)) s₀.store)
                                    (Ok (sstore s5.evm (s5["_17"]!!) (s5["_20"]!!)) (s5⟦"_21"↦s5["_17"]!!⟧.store)) := by
                                    apply sstore_preserved_eq
                                    aesop
                have s5__ok : (Ok (sstore s5.evm (s5["_17"]!!) (s5["_20"]!!)) (s5⟦"_21"↦s5["_17"]!!⟧.store)).isOk := by aesop
                have : preservesEvm (Ok (sstore s₀.evm (s5["_17"]!!) (s5["_20"]!!)) s₀.store)  s6 := by
                  apply preservesEvm_trans s5__ok
                  · aesop
                  · aesop
                aesop
              · aesop
            · aesop
        · aesop

      · -- No reversion in add
        obtain ⟨s5_evm, ⟨s5_varstore, s5_all⟩⟩ := State_of_isOk s5_ok

        simp[s5_no_collision] at update2
        obtain ⟨s6_ok, s5s6_preserves | s6_collision⟩ := update2

        · -- no collision at update2
          simp[s0_no_collision]
          split_ands
          · aesop
          · by_cases s9_no_collision : s₉.evm.hash_collision = false
            · left
              left
              split_ands
              · rw[←code]
                have : preservesEvm s₀ s5 := by aesop
                have : preservesEvm (Ok (sstore s₀.evm (s5["_17"]!!) (s5["_20"]!!)) s₀.store)
                                    (Ok (sstore s5.evm (s5["_17"]!!) (s5["_20"]!!)) (s5⟦"_21"↦s5["_17"]!!⟧.store)) := by
                                    apply sstore_preserved_eq
                                    aesop
                have s5__ok : (Ok (sstore s5.evm (s5["_17"]!!) (s5["_20"]!!)) (s5⟦"_21"↦s5["_17"]!!⟧.store)).isOk := by aesop
                have : preservesEvm (Ok (sstore s₀.evm (s5["_17"]!!) (s5["_20"]!!)) s₀.store)  s6 := by
                  apply preservesEvm_trans s5__ok
                  · aesop
                  · aesop
                aesop
              · aesop
            · aesop
        · aesop
      · aesop
    · aesop

end

end ERC20Shim.Common
