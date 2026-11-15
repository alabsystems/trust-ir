# SemR fixtures in this snapshot

The development tree holds eight more files here: two u64-addition module
images (`original-u64-addition.bin`, `canonical-v63-u64-addition.bin`) and six
generic-profile images with their provenance manifest
(`generic-profile/`). They are exact compiler output, and a module image
records the absolute path of the source file it was compiled from on the
machine that produced it, so this snapshot leaves them out. It also leaves out
the one test module (`semr_u64_addition_tests`) whose job is to bind two of the
images to the byte literals in `../U64Addition.lean`.

Everything else under `lean/semr` is in this snapshot unchanged. Where a note
there cites `fixtures/generic-profile/MANIFEST.json` or one of the images, it
means the development tree.
