
Run these using `ocaml-mdx test benchmarks/hoeval.md -v`.
It should take around 5 minutes.

Some sanity checks first:

```sh
$ dune exec parsing/hip.exe src/examples/calls.ml | grep Time | choose 2 | paste -s -d+ - | bc
```

```sh
$ DEBUG=0 hyperfine --warmup 2 'dune exec parsing/hip.exe src/examples/calls.ml'
```

```sh
$ DEBUG=0 time dune exec parsing/hip.exe src/examples/calls.ml > /dev/null
```

Project size:

```sh
$ loc parsing/{hipcore.ml,debug.ml,subst.ml,hiptypes.ml,common.ml,hiplib.ml,tests.ml,ProversEx.ml,Rewriting.ml,Pretty.ml,entail.ml,res.ml,forward_rules.ml,infer_types.ml,normalize.ml,hip.ml,hipjs.ml} provers/{native/provers.ml,js/provers.ml}
```

Stats:

(The following is generated using generate.sh)

```sh
$ DEBUG=0 hyperfine --warmup 2 'dune exec parsing/hip.exe src/examples/calls.ml'
$ loc src/examples/calls.ml

$ rg --multiline --multiline-dotall '(\*@.*?@\*)' src/examples/calls.ml

$ rg --multiline --multiline-dotall -c '(\*@.*?@\*)' src/examples/calls.ml

$ rg --multiline --multiline-dotall '(\*@.*?@\*)' src/examples/calls.ml | wc -l
```

```sh
$ DEBUG=0 hyperfine --warmup 2 'dune exec parsing/hip.exe src/examples/iter.ml'
$ loc src/examples/iter.ml

$ rg --multiline --multiline-dotall '(\*@.*?@\*)' src/examples/iter.ml

$ rg --multiline --multiline-dotall -c '(\*@.*?@\*)' src/examples/iter.ml

$ rg --multiline --multiline-dotall '(\*@.*?@\*)' src/examples/iter.ml | wc -l
```

```sh
$ DEBUG=0 hyperfine --warmup 2 'dune exec parsing/hip.exe src/examples/closure.ml'
$ loc src/examples/closure.ml

$ rg --multiline --multiline-dotall '(\*@.*?@\*)' src/examples/closure.ml

$ rg --multiline --multiline-dotall -c '(\*@.*?@\*)' src/examples/closure.ml

$ rg --multiline --multiline-dotall '(\*@.*?@\*)' src/examples/closure.ml | wc -l
```

```sh
$ DEBUG=0 hyperfine --warmup 2 'dune exec parsing/hip.exe src/examples/map.ml'
$ loc src/examples/map.ml

$ rg --multiline --multiline-dotall '(\*@.*?@\*)' src/examples/map.ml

$ rg --multiline --multiline-dotall -c '(\*@.*?@\*)' src/examples/map.ml

$ rg --multiline --multiline-dotall '(\*@.*?@\*)' src/examples/map.ml | wc -l
```

```sh
$ DEBUG=0 hyperfine --warmup 2 'dune exec parsing/hip.exe src/examples/fold.ml'
$ loc src/examples/fold.ml

$ rg --multiline --multiline-dotall '(\*@.*?@\*)' src/examples/fold.ml

$ rg --multiline --multiline-dotall -c '(\*@.*?@\*)' src/examples/fold.ml

$ rg --multiline --multiline-dotall '(\*@.*?@\*)' src/examples/fold.ml | wc -l
```

```sh
$ DEBUG=0 hyperfine --warmup 2 'dune exec parsing/hip.exe src/examples/compose.ml'
$ loc src/examples/compose.ml

$ rg --multiline --multiline-dotall '(\*@.*?@\*)' src/examples/compose.ml

$ rg --multiline --multiline-dotall -c '(\*@.*?@\*)' src/examples/compose.ml

$ rg --multiline --multiline-dotall '(\*@.*?@\*)' src/examples/compose.ml | wc -l
```

```sh
$ DEBUG=0 hyperfine --warmup 2 'dune exec parsing/hip.exe src/examples/applyN.ml'
$ loc src/examples/applyN.ml

$ rg --multiline --multiline-dotall '(\*@.*?@\*)' src/examples/applyN.ml

$ rg --multiline --multiline-dotall -c '(\*@.*?@\*)' src/examples/applyN.ml

$ rg --multiline --multiline-dotall '(\*@.*?@\*)' src/examples/applyN.ml | wc -l
```

```sh
$ DEBUG=0 hyperfine --warmup 2 'dune exec parsing/hip.exe src/examples/all.ml'
$ loc src/examples/all.ml

$ rg --multiline --multiline-dotall '(\*@.*?@\*)' src/examples/all.ml

$ rg --multiline --multiline-dotall -c '(\*@.*?@\*)' src/examples/all.ml

$ rg --multiline --multiline-dotall '(\*@.*?@\*)' src/examples/all.ml | wc -l
```
