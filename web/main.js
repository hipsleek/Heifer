// This file is built into bundle.js via browserify

// import { init } from 'z3-solver';
const { init } = require("z3-solver");
// const process = require('process');
// import process from 'process';

var z3;

init().then((a) => {
  z3 = a;
  ocaml_ready();
  enable_buttons();
});

// function new_ctx(s) { return new Context('main'); }
// function int(ctx, n) { return ctx.Int.const(n); }
// function and(ctx, a, b) { return ctx.And(a, b); }
// function or(ctx, a, b) { return ctx.Or(a, b); }
// function implies(ctx, a, b) { return ctx.Implies(a, b); }
// function ge(ctx, a, b) { return ctx.Implies(a, b); }
// function le(ctx, a, b) { return ctx.Implies(a, b); }

function solve(f, k) {
  // console.log('solve arg', arg);
  const { Context } = z3;
  // console.log(Context);

  // const { Context } = init();
  const ctx = new Context("main");
  // const { Solver, Int, And } = ctx;
  // const x = Int.const('x');
  const solver = new ctx.Solver();
  solver.add(f(ctx));
  // solver.add(And(x.ge(0), x.le(9)));
  solver.check().then((res) => {
    k(res === "sat");
    // console.log(res);
    // console.log(typeof res);
  });
}
module.exports = { solve };
// window.solve = solve;

// console.log('hi');
// process.exit(0);
