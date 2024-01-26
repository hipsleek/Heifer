
use prusti_contracts::*;

// error: [Prusti: unsupported feature] unsupported type Opaque(DefId(0:12 ~ lambda[317d]::f1::{opaque#0}), [])

// #[requires(f |= |arg: i32| -> i32 [ requires(vec_contains(v, arg)) ])]
// #[ensures(vec_len(&result) == old(vec_len(v)))]
// #[ensures(
//     forall(|idx: usize| 0 <= idx && idx < vec_len(v)
//         ==> f ~> |arg: i32| -> i32
//             { arg == vec_lookup(v, idx) }
//             { cl_result == vec_lookup(&result, idx) })
// )]

// #[requires(f |= |arg: i32| -> i32 [ ensures (cl_result == arg) ])]
#[ensures(
  result |= |arg: i32| -> i32 [ ensures (cl_result == arg) ]
    // forall(|idx: usize| 0 <= idx && idx < vec_len(v)
    //     ==> f ~> |arg: i32| -> i32
    //         { arg == vec_lookup(v, idx) }
    //         { cl_result == vec_lookup(&result, idx) })
)]
// f: F
// fn f1<F: Fn(i32) -> i32>() -> F {
fn f1() -> impl Fn(i32) -> i32 {
  |a| { a }
}

fn main() {}
