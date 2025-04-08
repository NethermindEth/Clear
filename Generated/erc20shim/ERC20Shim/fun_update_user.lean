import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.Common.switch_2364266820542243941
import Generated.erc20shim.ERC20Shim.mapping_index_access_mapping_address_uint256_of_address
import Generated.erc20shim.ERC20Shim.abi_encode_address_uint256_uint256
import Generated.erc20shim.ERC20Shim.update_storage_value_offsett_uint256_to_uint256
import Generated.erc20shim.ERC20Shim.checked_add_uint256
import Generated.erc20shim.ERC20Shim.Common.switch_1041419350816529734
import Generated.erc20shim.ERC20Shim.abi_encode_uint256

import Generated.erc20shim.ERC20Shim.fun_update_gen


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common Generated.erc20shim ERC20Shim

def A_fun_update  (var_from var_to var_value : Literal) (s₀ s₉ : State) : Prop :=
  let from_ := Address.ofUInt256 var_from
  let to_ := Address.ofUInt256 var_to
  let value_ : UInt256 := var_value

  s₉.isOk ∧

  (--Case 1: No initial collision
    s₀.evm.hash_collision = false →
  (
    ( -- Case 1.1 : _3 = 0 (Sender is not zero address)
      (-- Case 1.1.1: _7 = 1 (Reversion) (Balance is less than transfer value)
        ( -- Case 1.1.1.1: _24 = 0 (Receiver is not zero address)
          preservesEvm s₀ s₉ ∧
          s₉.evm.hash_collision = false ∧
          from_ ≠ 0 ∧
          to_ ≠ 0 ∧
          s₉["var_fromBalance"]!! < value_
        )
        ∨
        ( -- Case 1.1.1.2: _24 ≠ 0 (Receiver is zero address)
          preservesEvm s₀ s₉ ∧
          s₉.evm.hash_collision = false ∧
          from_ ≠ 0 ∧
          to_ = 0 ∧
          s₉["var_fromBalance"]!! < value_
        )
      )
      ∨
      (-- Case 1.1.2 _7 =/ 0 (Non Reversion) (balance ≥ trtansfer value )
        ( -- Case 1.1.2.1: _24 = 0 (Receiver is not zero address)

          preservesEvm s₀ s₉ ∧
          s₉.evm.hash_collision = false ∧
          from_ ≠ 0 ∧
          to_ ≠ 0 ∧
          s₉["var_fromBalance"]!! ≥ value_
        )
        ∨
        ( -- Case 1.1.2.2: _24 ≠ 0 (receiver is zero address)
          preservesEvm s₀ s₉ ∧
          s₉.evm.hash_collision = false ∧
          from_ ≠ 0 ∧
          to_ = 0 ∧
          s₉["var_fromBalance"]!! ≥ value_
        )
      )
    )
    ∨
    ( -- Case 1.2 : _3 ≠ 0 (Sender is zero address)
      ( -- Case 1.2.1 _24 = 0 (Receiver is not zero address)
        preservesEvm s₀ s₉ ∧
        s₉.evm.hash_collision = false ∧
          from_ = 0 ∧
          to_ ≠ 0
      )
      ∨
      ( -- Case 1.2.2 _24 ≠ 0 (Receiver is zero address)
        preservesEvm s₀ s₉ ∧
        s₉.evm.hash_collision = false ∧
        from_ = 0 ∧
        to_ = 0
      )
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

lemma fun_update_abs_of_concrete {s₀ s₉ : State} { var_from var_to var_value} :
  Spec (fun_update_concrete_of_code.1  var_from var_to var_value) s₀ s₉ →
  Spec (A_fun_update  var_from var_to var_value) s₀ s₉ := by
  unfold fun_update_concrete_of_code A_fun_update

  rcases s₀ with ⟨s0_evm, s0_varstore⟩ | _ | _ <;> [simp only; aesop_spec; aesop_spec]

  apply spec_eq
  clr_funargs


  generalize s_inhabited_all : (Ok s0_evm
                                    Inhabited.default⟦"var_value"↦var_value⟧⟦"var_to"↦var_to⟧⟦"var_from"↦var_from⟧⟦"expr"↦Ok
                                      s0_evm
                                      Inhabited.default⟦"var_value"↦var_value⟧⟦"var_to"↦var_to⟧⟦"var_from"↦var_from⟧["var_from"]!!⟧) = s_inhabited at *
  have s_inhabited_ok : s_inhabited.isOk := by
    aesop

  generalize s0__all :
                      (Finmap.lookup "var_from"
                        (Finmap.insert "_1" (Fin.shiftLeft 1 160 - 1)
                        (Finmap.insert "expr" var_from
                          (Finmap.insert "var_from" var_from
                            (Finmap.insert "var_to" var_to (Finmap.insert "var_value" var_value Inhabited.default)))))) = s0_ at *

  rintro hasFuel ⟨s, switch236, ⟨s', switch104, ⟨s'', encode, code⟩⟩⟩

  unfold multifill at *
  simp at *

  -- Assign s₀ state to tidy up goal
  generalize s0_all : Ok s0_evm s0_varstore = s₀ at *

  unfold A_switch_2364266820542243941 at switch236
  unfold primCall at switch236
  simp[←s_inhabited_all] at switch236
  unfold State.insert lookup! at switch236
  simp at switch236



  apply Spec_ok_unfold (by sorry) (by sorry) at switch236
  sorry

end

end Generated.erc20shim.ERC20Shim
