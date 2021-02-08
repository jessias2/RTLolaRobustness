# RTLola Robustness

Robustness analysis for RTLola specifications.

## Dependencies
(see `Cargo.tml`)
* cargo (1.47.0)
* z3 (0.9.0)
* clap (3.0.0)
* rtlola-frontend (0.3.3)

## Command Line Usage

### Build
* build executable via `cargo build --release`
* build specification via `cargo doc --document-private-items --open`

### Run
run via `cargo run -- [FLAGS]`

#### Flags
* `-f | --file <PATH>`: path to RTLola secification
* `-i | --iteration <UINT>`: evaluation depth, iteration to which the specification should be analyzed
* concrete analysis:
    * required:
        * `-e | --epsilon <UINT>`: epsilon value which defines the allowed variation of the input streams
        * `-l | --lnorm <0|1>`: lnorm which should be used to analyze the variations (`0`: Chebyshev norm / Linf norm, `1`: Manhattan norm / L1 norm)
    * optional:
        * `-z | --z3`: execute z3 / solve builded constraint (otherwise just print formula)
* symbolic and concolic analysis:
    * required:
        * `-s | --symbolic`

Note that the concolic analysis is automatically applied to the recursive streams after the symbolic analysis was executed on the linear streams.
