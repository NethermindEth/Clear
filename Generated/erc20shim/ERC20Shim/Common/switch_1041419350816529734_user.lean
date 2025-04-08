import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.mapping_index_access_mapping_address_uint256_of_address
import Generated.erc20shim.ERC20Shim.update_storage_value_offsett_uint256_to_uint256

import Generated.erc20shim.ERC20Shim.Common.switch_1041419350816529734_gen


namespace ERC20Shim.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.erc20shim ERC20Shim

def A_switch_1041419350816529734 (s₀ s₉ : State) : Prop :=
  s₉.isOk ∧

    (--Case 1: No initial collision
      s₀.evm.hash_collision = false →
      (
      -- Case 1.1 : _24 = 0
      (∃ slot value,
      let s:= (Ok (sstore s₀.evm slot value) s₀.store)
      preservesEvm s s₉) ∧
      s₉.evm.hash_collision = false

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
    ∧
    (-- Case 2: existing initial collision
      s₀.evm.hash_collision = true →
      s₉.evm.hash_collision = true
    )

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

lemma switch_1041419350816529734_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_1041419350816529734_concrete_of_code s₀ s₉ →
  Spec A_switch_1041419350816529734 s₀ s₉ := by
  unfold switch_1041419350816529734_concrete_of_code A_switch_1041419350816529734

  rcases s₀ with ⟨evm₀, varstore₀⟩ | _ | _ <;> [simp only; aesop_spec; aesop_spec]

  apply spec_eq
  clr_varstore,
  rintro hasFuel ⟨s1, mapping,
                  ⟨s2, update1,
                    ⟨s3, update2, code⟩⟩⟩


  generalize s0_all :
  (Ok evm₀ varstore₀) = s₀ at *
  have s0_ok : s₀.isOk := by aesop


  by_cases _24 : s₀["_24"]!! = 0

  · simp[_24] at code
    clear update2

    unfold A_mapping_index_access_mapping_address_uint256_of_address at mapping
    clr_spec at mapping
    unfold A_update_storage_value_offsett_uint256_to_uint256 at update1
    clr_spec at update1

    clr_varstore,

    obtain ⟨s1_ok, ⟨s0s1_preserves, s0s1_state, s1_keccak, s1_no_collision⟩ | s1_collision, s0s1_collision⟩ := mapping

    · -- no collision at s1 mapping
      obtain ⟨s1_evm, ⟨s1_varstore, s1_all⟩⟩ := State_of_isOk s1_ok

      obtain ⟨s2_ok, no_collision_s1, s1s2_collision⟩ := update1
      obtain ⟨s2_evm, ⟨s2_varstore, s2_all⟩⟩ := State_of_isOk s2_ok

      simp[s1_no_collision] at no_collision_s1

      have s0_no_collision : s₀.evm.hash_collision = false := by aesop
      simp[s0_no_collision]

      split_ands
      · aesop
      · by_cases s9_collision : s₉.evm.hash_collision = false
        · left
          split_ands
          · rw[←code]
            have s1__ok : (Ok (sstore s1.evm (s1["_26"]!!) (sload s1.evm (s1["_26"]!!) + (s1["var_value"]!!)))
                        (s1⟦"_27"↦sload s1.evm
                                  (s1["_26"]!!)⟧⟦"_28"↦sload s1.evm
                                (s1["_26"]!!)⟧⟦"_29"↦sload s1.evm (s1["_26"]!!) + (s1["var_value"]!!)⟧.store)).isOk := by aesop
            have h2 : preservesEvm
                      (Ok (sstore s1.evm (s1["_26"]!!) (sload s1.evm (s1["_26"]!!) + (s1["var_value"]!!)))
                        (s1⟦"_27"↦sload s1.evm
                                  (s1["_26"]!!)⟧⟦"_28"↦sload s1.evm
                                (s1["_26"]!!)⟧⟦"_29"↦sload s1.evm (s1["_26"]!!) + (s1["var_value"]!!)⟧.store))
                      s2 := by aesop
            have preserves_sstore : preservesEvm
                                    (Ok (sstore s₀.evm (s1["_26"]!!) (sload s1.evm (s1["_26"]!!) + (s1["var_value"]!!))) varstore₀)
                                      (Ok (sstore s1.evm (s1["_26"]!!) (sload s1.evm (s1["_26"]!!) + (s1["var_value"]!!)))
                                        (s1⟦"_27"↦sload s1.evm
                                                  (s1["_26"]!!)⟧⟦"_28"↦sload s1.evm
                                                (s1["_26"]!!)⟧⟦"_29"↦sload s1.evm (s1["_26"]!!) + (s1["var_value"]!!)⟧.store))
                                                := by
                apply sstore_preserved_eq
                aesop
            have s0s1_preservesEvm : preservesEvm s₀ s1 := by aesop
            have : preservesEvm (Ok (sstore s₀.evm (s1["_26"]!!) (sload s1.evm (s1["_26"]!!) + (s1["var_value"]!!))) s₀.store) s2 := by
              apply preservesEvm_trans s1__ok
              · aesop
              · aesop
            aesop
          · aesop
        · aesop
    · -- collision at s1 mapping
      aesop

  · -- Default case
    have : 0 ≠ s₀["_24"]!! := by aesop
    simp[this] at code

    clear mapping update1 this

    unfold A_update_storage_value_offsett_uint256_to_uint256 at update2
    clr_spec at update2

    obtain ⟨s3_ok, no_collision_s0, s0s3_collision⟩ := update2
    obtain ⟨s3_evm, ⟨s3_varstore, s3_all⟩⟩ := State_of_isOk s3_ok

    by_cases s0_collision : s₀.evm.hash_collision = false

    · split_ands
      · aesop
      · simp[s0_collision]
        by_cases s9_collision : s₉.evm.hash_collision = false
        · left
          split_ands
          · rw[←code]
            simp[s0_collision] at no_collision_s0
            aesop
          · aesop
        · aesop
      · aesop
    · aesop

end

end ERC20Shim.Common
