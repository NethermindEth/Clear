import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.fun_msgSender
import Generated.erc20shim.ERC20Shim.fun__transfer

import Generated.erc20shim.ERC20Shim.fun_transfer_gen


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.erc20shim ERC20Shim

def A_fun_transfer (var : Identifier) (var_to var_value : Literal) (s₀ s₉ : State) : Prop :=
  let recipient := Address.ofUInt256 var_to
  let amount : UInt256 := var_value
  let sender := s₀.evm.execution_env.source
  (∀ {erc20}, (IsERC20 erc20 s₀ ∧ s₀.evm.isEVMState ∧ s₀.evm.reverted = false) →
  -- Transfer succeeds
    (let balances := update_balances erc20 sender recipient amount
     IsERC20 ({ erc20 with balances }) s₉ ∧ preservesEvm s₀ s₉ ∧
        s₉.evm.hash_collision = false ∧ s₉[var]!! = 1 ∧ s₉.evm.reverted = false
    )
    ∨
  -- Transfer Fails
    (IsERC20 erc20 s₉ ∧ preservesEvm s₀ s₉ ∧ s₉.evm.hash_collision = false
    ∧ (recipient.1 = 0 ∨ balanceOf s₀.evm sender > amount) ∧  s₉[var]!! = 0 ∧ s₉.evm.reverted = true
    )
    -- Hash Collision
    ∨ s₉.evm.hash_collision = true
  )

-- set_option pp.notation false in

lemma fun_transfer_abs_of_concrete {s₀ s₉ : State} {var var_to var_value} :
  Spec (fun_transfer_concrete_of_code.1 var var_to var_value) s₀ s₉ →
  Spec (A_fun_transfer var var_to var_value) s₀ s₉ := by

  -- Unfold the definitions of the abstract and concrete specifications
  unfold fun_transfer_concrete_of_code A_fun_transfer
  -- Notice we now have two Specs in the tactic state - one for each specification

  -- Split s₀ into the 3 cases of OK, OutOfFuel, and Checkpoint
  -- Immediately prove the latter cases with simp and aesop
  -- Assign the initial state s₀
  rcases s₀ with ⟨s0_evm, s0_varstore⟩ | _ | _ <;> [simp only; aesop_spec; aesop_spec]

  -- applies the Spec
  apply spec_eq

  -- Unfolds initcall and setStore
  clr_funargs

  -- Assign s_inhabited state to tidy up goal
  set s_inhabited := (Ok s0_evm Inhabited.default⟦"var_value"↦var_value⟧⟦"var_to"↦var_to⟧) with eq1
  -- Show state is Ok
  have s_inhabited_ok : s_inhabited.isOk := by
    aesop_spec

  -- s₀ --> s using call_msgSender
  -- s --> s' using call_transfer
  -- s' --> s₉ using code
  rintro hasFuel ⟨s, call_msgSender, ⟨s', call_transfer, code⟩⟩

  -- Introduce hypotheses for s₀
  intro erc_20 isERC20_s0 evmState notReverted

  -- Assign s₀ state to tidy up goal
  generalize eq : Ok s0_evm s0_varstore = s₀ at *

  -- Clear specs at call_msgSender
  unfold A_fun_msgSender at call_msgSender
  clr_spec at call_msgSender


  obtain ⟨s_preservesEvm, ⟨s_ok, s_preserve_evmState, s_preserve_collision, ⟨⟨s_source, s_collision_false⟩⟩⟩⟩ := call_msgSender

  · -- No hash collision at state s


    -- Combine state s in s_all
    obtain ⟨s_evm, ⟨s_varstore, s_all⟩⟩ := State_of_isOk s_ok


    rw [preservesEvm_of_insert, preservesEvm_of_insert, s_all] at s_preservesEvm

    -- Obtain hypotheses for state s from state s₀
    have preservesEvm_s0_s : preservesEvm s₀ s := by aesop (add simp preservesEvm)
    have isERC20_s : IsERC20 erc_20 s := IsERC20_of_preservesEvm preservesEvm_s0_s isERC20_s0
    have isEvmState_s : isEVMState s.evm := by aesop

    unfold A_fun__transfer at call_transfer
    apply Spec_ok_unfold (by aesop_spec) at call_transfer

    swap

    · sorry
    ·
      specialize call_transfer ⟨isERC20_s, isEvmState_s⟩

      obtain (⟨s'_isERC20, s_s'_preservesEvm, s'_no_collision⟩
              | ⟨s'_isERC20, s_s'_preservesEvm, s'_no_collision, addr_zero⟩
              | s'_collision) := call_transfer

      · -- Transfer success case
        left

        have s'_ok : s'.isOk := sorry

        obtain ⟨s'_evm, s'_varstore, s'_eq_ok⟩ := State_of_isOk s'_ok

      · -- Transfer fail case
        right
        left
        sorry
      · -- Hash Collision Case
        right
        right
        sorry







    -- rcases call_transfer with ⟨balances, h_isERC20⟩ | ⟨h_isERC20, h_preservesEvm, h_no_collision, h_addr_zero⟩ | h_collision




    have h : ∀ {erc20 : ERC20}, IsERC20 erc20 s ∧ isEVMState s.evm →  preservesEvm s s' := by sorry




  · -- Hash collision at state s
    sorry

    #exit






    -- Want preservesEvm s0 s
    -- then IsERC20 erc20 s0 --> IsERC20 erc20 s using IsERC20_of_preservesEvm
    -- Problem is we have preservesEvm (Ok s0_evm Inhabited.default⟦"var_value"↦var_value⟧⟦"var_to"↦var_to⟧) s
    -- Something to do with match in msgSender?
    -- By preservesEVM definition, varstore variable is irrelevant
    -- So substitute Inhabited.default for s0_varstore?

    -- preserves s_inhabited s --> preserves s0 s
    have s0inhabited_preserveEvm : preservesEvm (Ok s0_evm s0_varstore) (Ok s0_evm Inhabited.default⟦"var_value"↦var_value⟧⟦"var_to"↦var_to⟧) := by
      exact Clear.Preserved.refl

    have : preservesEvm (Ok s0_evm s0_varstore) s := by
      exact Clear.Utilities.preservesEvm_trans  s_preservesEvm



    -- preservesEvm s0 s → IsERC20 erc20 s0 → IsERC20 erc20 s₁

    have : preservesEvm (Ok s0_evm s0_varstore) s_inhabited := by
      dsimp [s_inhabited]
      rw [preservesEvm_of_insert']
      rw [preservesEvm_of_insert']
      rcases s_inhabited with ⟨s_inhabited_evm, s_inhabited_varstore⟩
      · simp
      · simp
      · simp

    have : IsERC20 erc_20

    have : ∀ {erc20 : ERC20}, IsERC20 erc20 s ∧ isEVMState s.evm →  preservesEvm s s' := by
      specialize call_transfer ⟨is_erc20, s_preserve_evmState⟩
      exact call_transfer.1

    obtain ⟨erc20, ⟩ := call_transfer



  #exit

  -- assms
  intro erc_20 is_erc20 evmState notReverted

  obtain ⟨s_evm, s_varstore, s_ok⟩ := State_of_isOk s_isOk

  -- get underlying Preserved from preservesEVM
  rw [ s_ok, preservesEvm_of_insert, preservesEvm_of_insert ] at s_preservesEvm
  have Preserved := Preserved_of_preservesEvm_of_Ok s_preservesEvm








  /- rcases mapping with ⟨
    ⟨preservesEvm, s_isOk, s_isEVMStatePreserved,
    ⟨⟨keccak_value, keccak_using_keccak_value, hStore⟩,hHashCollision⟩⟩ | _, hHashCollision₁
  ⟩ <;> [left; rcases s <;> aesop_spec] -/
  #exit


  -- refine' ⟨IsERC20_of_preservesEvm (by aesop) is_erc20, (by aesop), ?returns_correct_value⟩
  refine' Or.inl ⟨?_, ?_, ?_, ?_, ?_⟩

  · sorry



  . -- Split on zero address case
    by_cases h_recipient : (Address.ofUInt256 var_to).1 = 0
    · -- Zero address case
      right; left
      -- Use refine to break up the conjunction into 6 subgoals
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩

      · apply IsERC20_of_preservesEvm ?_ isERC20
        unfold preservesEvm
        have : s₉.isOk := by
          exfalso




      -- Subgoal 1 - IsERC20 erc_20 s₉
      -- Examining the structure of ISERC20 it has 5 parts which we refine into 5 subgoals
      . refine ⟨?_, ?_, ?_, ?_, ?_⟩ -- #exit


        -- Subsubgoal 1 - sload s₉.evm ERC20Private.totalSupply = erc_20.supply

          -- We know that the total supply is the same as the initial supply at s₀
        . have  s_0_supply : sload s₀.evm ERC20Private.totalSupply = erc_20.supply := by
            dsimp [s₀] --unfold s₀ def
            rcases isERC20 with ⟨h, _, _, _, _⟩ -- Unfold isERC20 but only extract the first field which is hasSupply into h
            exact h

          -- If we know this holds for s₀ then it must hold for s using mapping
          have : sload s.evm ERC20Private.totalSupply = erc_20.supply := by
            unfold A_fun_msgSender at mapping
            unfold preservesEvm at mapping

            match s with
            | State.Ok evm' varstore' =>
              have map_1 := mapping.1

              have preserved_s : Preserved evm evm' := by
                simp at map_1
                exact map_1

              have preserved_eq : sload s₀.evm ERC20Private.totalSupply = sload (State.Ok evm' varstore).evm ERC20Private.totalSupply := by
                apply EVMState.sload_eq_of_preserved preserved_s

              rw [s_0_supply] at preserved_eq
              simp [preserved_eq]

          -- If it holds for s then it holds for s' using mapping'
          have : sload s'.evm ERC20Private.totalSupply = erc_20.supply := by
            unfold A_fun__transfer at mapping'

            -- Considering cases of A_fun__transfer we only need to look at the second case where address is 0
            -- But we must show IsERC20 erc20 s ∧ isEVMState s.evm
            -- from this we deduce preservesEVM s s'
            -- Similar to above we can use lemma Preserved_of_preservesEvm_of_Ok to get the desired result

          have : sload s₉.evm ERC20Private.totalSupply = erc_20.supply := by

    . -- Non-zero address case -/
      left
      constructor
      · sorry
      . sorry







end

end Generated.erc20shim.ERC20Shim
