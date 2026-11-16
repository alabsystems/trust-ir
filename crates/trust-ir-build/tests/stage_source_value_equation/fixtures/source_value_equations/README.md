# Actual Clean producer data

The boundActualEquation, boundField and boundMask files are the unchanged modules,
original custom declarations and proposed source-value theorems exported by
Clean's actual canonical source pipelines at
`5b8de1228598ac3fe06e43bdafbc8187362b6360`. `PRODUCER-DATA.json` records the
producer qualification and exact file hashes. Its status and digests carry no
consumer authority. All `.bin` expression fields use the existing canonical
Clean Expr v1 codec; `module.bin` is the complete canonical IR binary module,
including the generated boxed helper.

The consumer test constructs its original environment separately from the
expected source-definition data, kernel-checks those declarations, selects its
expected source name outside the theorem witness, validates the complete
module, independently reads the actual scalar IR body and rebuilds the goal.
It then checks the actual proposed proof. This tests interoperability and
precisely the supplied pair; it does not authenticate Lean/Rust source text or
the original environment, prove the IR reader's operational semantics, license
the boxed helper or establish runtime, ABI, NoUB or machine-code correctness.

The [conditionals](conditionals/README.md) subdirectory is a separate sealed
producer data set for the ordinary conditional pipeline at all four UInt widths.

The producer was rerun against the BitVec-enabled kernel. Original definition and theorem fields are byte-identical for the three cases; complete modules carry the newly minted context bindings. The previous bytes and consumer refusals remain in the cohort evidence. New producer status alone grants no consumer authority.
