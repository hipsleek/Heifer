# Heifer

Heifer is a new verifier for effectful, higher-order OCaml programs.

## Build

You will need OCaml 5.

```sh
opam install . --deps-only
```

Use `dune exec main/hip.exe $EXAMPLE` to run examples. Effect-related programs are in [test/evaluation](test/evaluation), higher-order programs are in [test/examples](test/examples).

## Docs

- [Development](docs/development.md)
- [Why3](docs/why3.md)
- [How the web build works](docs/web.md)
