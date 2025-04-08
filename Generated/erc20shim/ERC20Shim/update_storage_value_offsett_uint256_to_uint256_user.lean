import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.update_byte_slice_shift

import Generated.erc20shim.ERC20Shim.update_storage_value_offsett_uint256_to_uint256_gen


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.erc20shim ERC20Shim

def A_update_storage_value_offsett_uint256_to_uint256  (slot value : Literal) (s₀ s₉ : State) : Prop :=
  s₉.isOk ∧

  (--Case 1: No initial collision
    s₀.evm.hash_collision = false →
    (
    -- Case 1.1 : collision in function
      (
        let s:= (Ok (sstore s₀.evm slot value) s₀.store)
        preservesEvm s s₉
      )
    ∨
    -- Case 1.2 : Collision in function
    s₉.evm.hash_collision = true
    )
  )
  ∧
  (-- Case 2: existing initial collision
     s₀.evm.hash_collision = true →
    s₉.evm.hash_collision = true
  )

lemma update_storage_value_offsett_uint256_to_uint256_abs_of_concrete {s₀ s₉ : State} { slot value} :
  Spec (update_storage_value_offsett_uint256_to_uint256_concrete_of_code.1  slot value) s₀ s₉ →
  Spec (A_update_storage_value_offsett_uint256_to_uint256  slot value) s₀ s₉ := by
  unfold update_storage_value_offsett_uint256_to_uint256_concrete_of_code A_update_storage_value_offsett_uint256_to_uint256
  rcases s₀ with ⟨evm₀, varstore₀⟩ | _ | _ <;> [simp only; aesop_spec; aesop_spec]
  apply spec_eq
  clr_funargs
  clr_varstore,
  rintro hasFuel ⟨s, call_byte, code⟩
  generalize s_inhabited_all :
    Ok evm₀ Inhabited.default⟦"value"↦value⟧⟦"slot"↦slot⟧ = s_inhab_all at *
  have s_inhab_ok : s_inhab_all.isOk := by aesop

  generalize s0_all :
  (Ok evm₀ varstore₀) = s₀ at *

  unfold reviveJump at code
  unfold setEvm at code

  clr_spec at call_byte
  unfold A_update_byte_slice_shift at call_byte

  obtain ⟨s_ok, ⟨sinhab_no_collision, sinhab_collision⟩⟩
          := call_byte
  obtain ⟨s_evm, ⟨s_varstore, s_all⟩⟩ := State_of_isOk s_ok

  simp [s_all, ←s0_all] at code

  have sinhab_evm_eq : s_inhab_all⟦"_1"↦sload s_inhab_all.evm slot⟧.evm = s_inhab_all.evm := by
    aesop

  have s0_sinhab_preservesEvm : preservesEvm s₀  s_inhab_all := by
    simp [←s0_all, ←s_inhabited_all]
    unfold preservesEvm
    unfold State.insert
    aesop

  have s0_sinhab__preservesEvm : preservesEvm s₀  (s_inhab_all⟦"_1"↦sload s_inhab_all.evm slot⟧) :=
     by aesop


  by_cases collision_sinhab : s_inhab_all⟦"_1"↦sload s_inhab_all.evm slot⟧.evm.hash_collision = false

  · have: s_inhab_all.evm.hash_collision = false := by aesop
    simp [this] at sinhab_no_collision
    split_ands
    · aesop
    · intro h
      cases sinhab_no_collision
      · left
        rw[←code]
        unfold lookup!
        simp
        have t : (Finmap.lookup "slot" s_varstore).get! = slot ∧
                (Finmap.lookup "_2" s_varstore).get! = value := by aesop
        rw[t.1, t.2]
        aesop
      · right
        rw[←code]
        simp
        unfold sstore
        aesop
    · aesop
  · simp at collision_sinhab
    split_ands
    · aesop
    · aesop
    · rw[←code]
      unfold sstore
      aesop
end

end Generated.erc20shim.ERC20Shim
