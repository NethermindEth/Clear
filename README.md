# Clear.

<img width="600" alt="Clear - Github (1)" src="https://github.com/NethermindEth/Clear/assets/114106639/9d92cbbc-5a55-4808-ae48-525647c1c0d6">



Prove anything* about Yul programs.

There are two parts.
  - A Lean framework with a Yul model.
  - A verification condition generator.

## The Lean framework
Download and install Lean 4. One can follow https://lean-lang.org/lean4/doc/quickstart.html.

To obtain precompiled files for the dependency Mathlib, run the following in the root directory (this is optional, it saves time): 
```
lake exe cache get
```

Then simply run the following in the root directory:
```
lake build
```

## The verification condition generator (vc)

Download and install Stack. One can follow https://docs.haskellstack.org/en/stable/install_and_upgrade/.

Then simply run the following in the `vc` directory:
```
stack build
```

## Verifying it all works
In the `vc` directory, run:
```
stack run vc ../out/peano.yul
```

You should get a `Generated` folder corresponding with the structure of the Peano example
in the `out/peano.yul` file.
