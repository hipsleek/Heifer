# Heifer

Heifer is a new verifier for effectful higher-order programs.

## Build

You will need OCaml 5.

```sh
opam install . --deps-only
```

Use `dune exec parsing/hip.exe $EXAMPLE` to run examples. Effect-related programs are in [src/evaluation](src/evaluation), higher-order programs are in [src/examples](src/examples).

## Docs

- [Development](docs/dev.md)
