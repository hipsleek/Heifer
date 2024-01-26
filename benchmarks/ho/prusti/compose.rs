use prusti_contracts::*;

// https://stackoverflow.com/a/45792463

// thread 'rustc' panicked at 'not implemented: encoding of 'move _4 as std::boxed::Box<dyn std::ops::Fn(A) -> C> (Pointer(Unsize))'', prusti-viper/src/encoder/procedure_encoder.rs:1218:25
// fn compose<'a, A, B, C, G, F>(f: F, g: G) -> Box<Fn(A) -> C + 'a>
// where
//     F: 'a + Fn(A) -> B + Sized,
//     G: 'a + Fn(B) -> C + Sized,
// {
//     Box::new(move |x| g(f(x)))
// }

// error: [Prusti: unsupported feature] unsupported type Opaque(DefId(0:10 ~ compose[317d]::compose::{opaque#0}), [A, B, C, G, F])
// fn compose<A, B, C, G, F>(f: F, g: G) -> impl Fn(A) -> C
// where
//     F: Fn(A) -> B,
//     G: Fn(B) -> C,
// {
//     move |x| g(f(x))
// }

fn main() {}